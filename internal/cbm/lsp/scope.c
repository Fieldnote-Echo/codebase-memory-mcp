#include "scope.h"
#include <stdint.h>
#include <string.h>

#ifdef CBM_ENABLE_TEST_SEAMS
static _Thread_local uint64_t g_scope_test_name_compares;

void cbm_scope_test_reset(void) {
    g_scope_test_name_compares = 0;
}

uint64_t cbm_scope_test_name_compares(void) {
    return g_scope_test_name_compares;
}

static void scope_test_note_compare(void) {
    g_scope_test_name_compares++;
}
#else
static void scope_test_note_compare(void) {}
#endif

CBMScope* cbm_scope_push(CBMArena* a, CBMScope* current) {
    CBMScope* scope = (CBMScope*)cbm_arena_alloc(a, sizeof(CBMScope));
    if (!scope) {
        return current;
    }
    memset(scope, 0, sizeof(CBMScope));
    scope->parent = current;
    scope->arena = a;
    return scope;
}

CBMScope* cbm_scope_pop(CBMScope* scope) {
    if (!scope) {
        return NULL;
    }
    return scope->parent;
}

static CBMScopeChunk* alloc_chunk(CBMScope* scope) {
    if (!scope->arena) {
        return NULL;
    }
    CBMScopeChunk* c = (CBMScopeChunk*)cbm_arena_alloc(scope->arena, sizeof(CBMScopeChunk));
    if (!c) {
        return NULL;
    }
    memset(c, 0, sizeof(CBMScopeChunk));
    c->next = scope->chunks;
    scope->chunks = c;
    return c;
}

static bool binding_named(const CBMVarBinding *binding, const char *name) {
    scope_test_note_compare();
    return binding->name && strcmp(binding->name, name) == 0;
}

enum {
    SCOPE_INDEX_SPREAD = 2, /* slots per binding at least: the index stays half empty */
    SCOPE_INDEX_GROWTH = 2,
    SCOPE_INDEX_FAILED = -1, /* index_cap after a failed allocation: scan this frame */
};
#define SCOPE_PROBE_STEP 1U
#define SCOPE_FNV_OFFSET 2166136261U
#define SCOPE_FNV_PRIME 16777619U

static uint32_t scope_name_hash(const char *name) {
    uint32_t hash = SCOPE_FNV_OFFSET; /* FNV-1a */
    for (const unsigned char *p = (const unsigned char *)name; *p; p++) {
        hash = (hash ^ *p) * SCOPE_FNV_PRIME;
    }
    return hash;
}

/* The index is an open-addressing table of pointers into the frame's chunks,
 * kept at most half full, so every probe sequence reaches an empty slot. */
static void scope_index_put(CBMVarBinding **index, int cap, CBMVarBinding *binding) {
    uint32_t mask = (uint32_t)cap - SCOPE_PROBE_STEP;
    uint32_t slot = scope_name_hash(binding->name) & mask;
    while (index[slot]) {
        slot = (slot + SCOPE_PROBE_STEP) & mask;
    }
    index[slot] = binding;
}

static void scope_index_rebuild(CBMScope *scope) {
    int cap = SCOPE_INDEX_SPREAD * CBM_SCOPE_INDEX_MIN_BINDINGS;
    while (cap < SCOPE_INDEX_SPREAD * scope->binding_count) {
        cap *= SCOPE_INDEX_GROWTH;
    }
    CBMVarBinding **index =
        (CBMVarBinding **)cbm_arena_alloc(scope->arena, (size_t)cap * sizeof(CBMVarBinding *));
    if (!index) {
        scope->index = NULL;
        scope->index_cap = SCOPE_INDEX_FAILED;
        return;
    }
    memset(index, 0, (size_t)cap * sizeof(CBMVarBinding *));
    for (CBMScopeChunk *c = scope->chunks; c != NULL; c = c->next) {
        for (int i = 0; i < c->used; i++) {
            scope_index_put(index, cap, &c->bindings[i]);
        }
    }
    scope->index = index;
    scope->index_cap = cap;
}

/* A binding was just appended to the frame. */
static void scope_index_note(CBMScope *scope, CBMVarBinding *binding) {
    if (scope->index_cap == SCOPE_INDEX_FAILED ||
        scope->binding_count <= CBM_SCOPE_INDEX_MIN_BINDINGS) {
        return;
    }
    if (!scope->index || SCOPE_INDEX_SPREAD * scope->binding_count > scope->index_cap) {
        scope_index_rebuild(scope);
        return;
    }
    scope_index_put(scope->index, scope->index_cap, binding);
}

/* The frame's binding for name (names are unique within a frame), or NULL. */
static CBMVarBinding *scope_find_local(const CBMScope *scope, const char *name) {
    if (scope->index) {
        uint32_t mask = (uint32_t)scope->index_cap - SCOPE_PROBE_STEP;
        for (uint32_t slot = scope_name_hash(name) & mask; scope->index[slot];
             slot = (slot + SCOPE_PROBE_STEP) & mask) {
            if (binding_named(scope->index[slot], name)) {
                return scope->index[slot];
            }
        }
        return NULL;
    }
    for (CBMScopeChunk *c = scope->chunks; c != NULL; c = c->next) {
        for (int i = 0; i < c->used; i++) {
            if (binding_named(&c->bindings[i], name)) {
                return &c->bindings[i];
            }
        }
    }
    return NULL;
}

/* Returns false when the binding could NOT be recorded in THIS frame.
 *
 * The failure that matters is arena exhaustion in alloc_chunk: the old void
 * form returned silently, so a caller that then consulted the scope CHAIN saw
 * the parent's binding for the same name and concluded the child had been
 * bound. For callable-value proof that is a fabricated identity -- the shadow
 * never took effect, yet the parent's callable looks like the child's. Callers
 * needing that distinction must use the checked form and consult the LOCAL
 * result, not a chain lookup. */
static bool cbm_scope_bind_value(CBMScope *scope, const char *name, const CBMType *type,
                                 const char *callable_qn) {
    if (!scope || !name) {
        return false;
    }
    CBMVarBinding *existing = scope_find_local(scope, name);
    if (existing) {
        existing->type = type;
        existing->callable_qn = callable_qn;
        return true;
    }
    CBMScopeChunk* head = scope->chunks;
    if (!head || head->used >= CBM_SCOPE_CHUNK_BINDINGS) {
        head = alloc_chunk(scope);
        if (!head) {
            return false; /* arena exhausted: the shadow did NOT take effect */
        }
    }
    CBMVarBinding *binding = &head->bindings[head->used];
    binding->name = name;
    binding->type = type;
    binding->callable_qn = callable_qn;
    head->used++;
    scope->binding_count++;
    scope_index_note(scope, binding);
    return true;
}

void cbm_scope_bind(CBMScope *scope, const char *name, const CBMType *type) {
    (void)cbm_scope_bind_value(scope, name, type, NULL);
}

bool cbm_scope_bind_checked(CBMScope *scope, const char *name, const CBMType *type) {
    return cbm_scope_bind_value(scope, name, type, NULL);
}

void cbm_scope_bind_callable(CBMScope *scope, const char *name, const CBMType *type,
                             const char *callable_qn) {
    (void)cbm_scope_bind_value(scope, name, type, callable_qn);
}

bool cbm_scope_bind_callable_checked(CBMScope *scope, const char *name, const CBMType *type,
                                     const char *callable_qn) {
    return cbm_scope_bind_value(scope, name, type, callable_qn);
}

const CBMType* cbm_scope_lookup(const CBMScope* scope, const char* name) {
    if (!name) {
        return cbm_type_unknown();
    }
    for (const CBMScope* s = scope; s != NULL; s = s->parent) {
        const CBMVarBinding *binding = scope_find_local(s, name);
        if (binding) {
            return binding->type;
        }
    }
    return cbm_type_unknown();
}

bool cbm_scope_contains(const CBMScope *scope, const char *name) {
    if (!name) {
        return false;
    }
    for (const CBMScope *s = scope; s != NULL; s = s->parent) {
        if (scope_find_local(s, name)) {
            return true;
        }
    }
    return false;
}

const char *cbm_scope_lookup_callable(const CBMScope *scope, const char *name) {
    if (!name) {
        return NULL;
    }
    for (const CBMScope *s = scope; s != NULL; s = s->parent) {
        const CBMVarBinding *binding = scope_find_local(s, name);
        if (binding) {
            return binding->callable_qn;
        }
    }
    return NULL;
}

bool cbm_scope_update_callable(CBMScope *scope, const char *name, const char *callable_qn) {
    if (!name) {
        return false;
    }
    for (CBMScope *s = scope; s != NULL; s = s->parent) {
        CBMVarBinding *binding = scope_find_local(s, name);
        if (binding) {
            binding->callable_qn = callable_qn;
            return true;
        }
    }
    return false;
}
