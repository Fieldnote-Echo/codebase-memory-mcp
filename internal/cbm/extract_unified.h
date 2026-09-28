#ifndef CBM_EXTRACT_UNIFIED_H
#define CBM_EXTRACT_UNIFIED_H

#include "cbm.h"
#include "lang_specs.h"

// Scope kinds for the walk state stack.
#define SCOPE_FUNC 1
#define SCOPE_CLASS 2
#define SCOPE_CALL 3
#define SCOPE_IMPORT 4
#define SCOPE_LOOP 5
#define SCOPE_BRANCH 6
#define SCOPE_LEXICAL 7
#define SCOPE_NAMESPACE 8

#define MAX_SCOPES 64
#define INLINE_LEXICAL_SCOPES 64
#define INLINE_LEXICAL_BINDINGS 64
#define INLINE_PYTHON_DIRECTIVES 16
#define INLINE_PY_PARAM_SLOTS 64
#define INLINE_PY_PARAM_STACK 64

// ObjectScript type map: variable name → class name (for instance_method_call
// resolution). Stack-allocated, per-method scope. Overflow is silent (no crash).
#define OS_TYPE_MAP_CAP 64
typedef struct {
    const char *var_name;
    const char *class_name;
} os_type_entry_t;

typedef struct {
    os_type_entry_t entries[OS_TYPE_MAP_CAP];
    int count;
    int class_base_count; // entries [0,class_base_count) survive method-scope resets
} os_type_map_t;

// A call consumes only the exact AST occurrence that denotes its callee.  The
// rest of the call subtree (receiver, computed key, arguments, callback body)
// remains ordinary expression input and is eligible for USAGE extraction.
typedef enum {
    CBM_INVOCATION_NONE = 0,
    CBM_INVOCATION_PRIMARY,
    CBM_INVOCATION_CALLABLE_REFERENCE,
} CBMInvocationKind;

typedef struct {
    CBMInvocationKind kind;
    TSNode site;
    TSNode callee_expr;
    TSNode callee_leaf;
    const char *callee_name;
    bool raw_call_emitted;
} CBMInvocationDescriptor;

/* One name bound as a function/lambda parameter by a scope currently OPEN on
 * the walk stack. A count, not a flag: `def outer(run): def inner(run):` binds
 * the same name twice and the inner pop must not unbind the outer. */
typedef struct {
    const char *name;
    uint32_t hash;
    int count;
} CBMParamSlot;

typedef struct {
    const char *qn;
    uint32_t depth;
    uint32_t lexical_scope_id;
    /* lexical_scope_id of the nearest frame at or below this one that has one
     * (0: none), so the innermost lexical scope is found in O(1). Scanning
     * down for it passes every call frame, and a nested call f(f(f(...)))
     * stacks one per level: O(depth) for every node the walk visits. */
    uint32_t active_lexical_scope_id;
    uint8_t kind;
    CBMInvocationKind invocation_kind;
    TSNode callee_expr;
    TSNode callee_leaf;
    /* The complete walk-state tuple this frame displaced, restored verbatim on
     * pop. Saving the full tuple makes push and pop O(1) and kind-agnostic;
     * the previous design recomputed the state by iterating the WHOLE scope
     * stack on every code-bearing node, which is O(depth) per node and turned
     * the deep-nesting torture tests quadratic (0-1s on main, 39-119s here,
     * suite-budget kills on every non-M4 venue). */
    const char *prev_enclosing_func_qn;
    const char *prev_enclosing_class_qn;
    CBMInvocationKind prev_invocation_kind;
    TSNode prev_callee_expr;
    TSNode prev_callee_leaf;
    bool prev_inside_import;
    int prev_loop_depth;
    int prev_branch_depth;
    /* #1912: py_param_stack height on entry. Pop unwinds back to it, so a
     * frame unbinds exactly the parameters it bound and nothing else. */
    int prev_py_param_stack_count;
} CBMWalkScope;

typedef enum {
    CBM_LEXICAL_SCOPE_MODULE = 0,
    CBM_LEXICAL_SCOPE_CLASS,
    CBM_LEXICAL_SCOPE_FUNCTION,
    CBM_LEXICAL_SCOPE_BLOCK,
    CBM_LEXICAL_SCOPE_COMPREHENSION,
} CBMLexicalScopeKind;

/* Concrete AST scope identity. QNs remain graph-attribution metadata only;
 * overloads, lambdas and sibling blocks therefore never share binding facts. */
typedef struct {
    uint32_t id;
    uint32_t parent_id;
    uint32_t lookup_parent_id;
    uint32_t start_byte;
    uint32_t end_byte;
    uint8_t kind;
} CBMLexicalScope;

/* Deferred binding event. Applying these after the walk represents hoisted
 * and whole-scope rules without depending on traversal order. */
typedef struct {
    uint32_t scope_id;
    uint32_t active_start;
    uint32_t active_end;
    const char *name;
} CBMLexicalBinding;

typedef enum {
    CBM_PYTHON_DIRECTIVE_GLOBAL = 1,
    CBM_PYTHON_DIRECTIVE_NONLOCAL,
} CBMPythonDirectiveKind;

typedef struct {
    uint32_t function_scope_id;
    const char *name;
    uint8_t kind;
} CBMPythonDirective;

/* Ancestor context for the usage classifiers (extract_usages.c).
 *
 * Classifying an occurrence means asking about its ANCESTORS: is it in a
 * binding position, an assignment target, a call-argument label, a Python
 * default value, under a global statement? Tree-sitter nodes have no parent
 * pointer. ts_node_parent re-descends from the root, and a climb on a copy of
 * the walk cursor first copies the cursor's whole stack, so every climb costs
 * at least O(depth). One climb per identifier made a long left-nested
 * expression quadratic or worse: a 128 KB cargo dep-info file read as D spent
 * 13-15 s in the walk.
 *
 * So the walk answers these questions on the way down. frames[d] describes the
 * node at visible depth d of the current path. The walk is pre-order, so
 * frames[0..depth] is always exactly that path: a sibling overwrites its
 * predecessor's slot and nothing is ever popped. Each answer is an inherited
 * attribute, one O(1) transition per edge from the parent's answer, the
 * parent's role and the edge. The transition takes the first decisive ancestor,
 * the same one the upward climb would have stopped at. */
/* Other climbs stop at the NEAREST ancestor of some description and decide
 * there: a language's binding policy (Lisp definition forms, Elixir def calls,
 * TLA+ binders, and its second search), the call-side definition role, the
 * import statement. frames[d].nearest[slot] is the frames index of the nearest
 * strict ancestor of frames[d] that decides for `slot`, so finding it is one
 * lookup; the decision at that ancestor is the climb's own code. */
enum {
    CBM_USAGE_NEAREST_POLICY = 0,
    CBM_USAGE_NEAREST_POLICY_AUX,
    CBM_USAGE_NEAREST_CALL_ROLE,
    CBM_USAGE_NEAREST_IMPORT,
    CBM_USAGE_NEAREST_COUNT,
};

#define CBM_USAGE_NO_NEAREST UINT32_MAX

typedef struct {
    TSNode node;
    uint32_t roles;       /* node's CBM_USAGE_ROLE_* as a parent; resolved at its first child */
    uint32_t targets;     /* node's CBMUsageTargets record, or CBM_USAGE_NO_TARGETS */
    uint32_t targets_end; /* target records in use by node and its ancestors */
    uint32_t context;     /* CBM_USAGE_CONTEXT_* answers for node itself */
    uint32_t nearest[CBM_USAGE_NEAREST_COUNT]; /* or CBM_USAGE_NO_NEAREST */
    TSFieldId field_id; /* the field node occupies in its parent; 0 for none */
} CBMUsageFrame;

#define CBM_USAGE_NO_TARGETS UINT32_MAX

/* Children of a declaration or assignment that the classifiers compare with
 * the path. ts_node_child_by_field_id scans the parent's children, so these
 * are resolved once per parent rather than once per descendant. The first
 * CBM_USAGE_FIELD_TARGET_COUNT slots are field children, in this order.
 *
 * A field target is usually a direct child of the parent. A field inherited
 * through a child that an alias made visible (Lua's `local x` declares
 * variable_declaration > variable_list > name: identifier) resolves to a
 * deeper node; `via` then holds the direct child on the way to it. */
enum {
    CBM_USAGE_TARGET_NAME = 0,
    CBM_USAGE_TARGET_PATTERN,
    CBM_USAGE_TARGET_DECLARATOR,
    CBM_USAGE_TARGET_PARAMETER,
    CBM_USAGE_TARGET_PARAMETERS,
    CBM_USAGE_TARGET_LEFT,
    CBM_USAGE_TARGET_VARIABLE,
    CBM_USAGE_TARGET_VARIABLES,
    CBM_USAGE_TARGET_KEY,
    CBM_USAGE_TARGET_TARGET,
    CBM_USAGE_TARGET_DESTINATION,
    CBM_USAGE_TARGET_VALUE,
    CBM_USAGE_TARGET_DEFAULT,
    CBM_USAGE_TARGET_ALIAS,
    CBM_USAGE_FIELD_TARGET_COUNT,
    CBM_USAGE_TARGET_FIRST_CHILD = CBM_USAGE_FIELD_TARGET_COUNT,
    CBM_USAGE_TARGET_FIRST_NAMED_CHILD,
    CBM_USAGE_TARGET_COUNT,
};

typedef struct {
    const void *id[CBM_USAGE_TARGET_COUNT];  /* the target, when a direct child */
    const void *via[CBM_USAGE_TARGET_COUNT]; /* the direct child above a deeper target */
} CBMUsageTargets;

typedef struct {
    CBMUsageFrame *frames;
    uint32_t frame_capacity;
    uint32_t depth; /* frames[depth] is the walk's current node */
    CBMUsageTargets *targets;
    uint32_t target_capacity;
    uint32_t *symbol_roles; /* per-walk cache of kind roles, by ts_node_symbol */
    uint32_t symbol_count;
    uint8_t *field_flags; /* CBM_USAGE_FIELD_* by field id */
    uint32_t field_count;
    TSFieldId target_fields[CBM_USAGE_FIELD_TARGET_COUNT]; /* resolved at first use */
    bool target_fields_resolved;
    bool nearest_kept[CBM_USAGE_NEAREST_COUNT]; /* the slots this walk keeps */
    /* An allocation failed: frames stop being maintained and every classifier
     * climbs, exactly as before the frames existed. */
    bool failed;
    /* Test seams (CBM_ENABLE_TEST_SEAMS). check_mode 1 answers from the frames
     * and verifies every answer against the climb, logging and counting any
     * disagreement; 2 also aborts. climb_only answers every query by climbing. */
    uint8_t check_mode;
    bool climb_only;
    uint64_t checks;
    uint64_t fallbacks;
    uint64_t mismatches;
} CBMUsageContext;

/* An upward walk from the walk's current node. Stepping the frames is the walk
 * cursor climb without copying the cursor first; the cursor copy remains for
 * a walk whose frames are unavailable. */
typedef struct {
    const CBMUsageFrame *frames; /* non-NULL: step through frames */
    uint32_t level;              /* frames index of the node the climb stands on */
    TSTreeCursor *cursor;        /* frames == NULL: a copy of the walk cursor */
} CBMOccurrenceClimb;

// WalkState tracks scope context during the unified cursor walk.
// Replaces parent-chain walks for enclosing_func_qn, import context, etc.
typedef struct {
    const char *enclosing_func_qn;      // current function QN (module_qn at top level)
    const char *enclosing_class_qn;     // current class QN (NULL outside class)
    const TSTreeCursor *current_cursor; // unified walk cursor at the current node
    TSTreeCursor *occurrence_cursor;    // reusable parent-preserving classifier cursor
    CBMInvocationKind invocation_kind;  // exact active invocation/reference role
    TSNode callee_expr;                 // exact active callee expression, if any
    TSNode callee_leaf;                 // exact active terminal callee, if any
    bool inside_import;                 // within an import_node_types subtree
    int loop_depth;                     // count of enclosing loop scopes (for bottleneck metrics)
    int branch_depth;                   // count of enclosing branch scopes

    /* Ancestor answers carried down by the walk, and the classifiers' one
     * upward walk in progress (extract_usages.c). */
    CBMUsageContext usage_context;
    CBMOccurrenceClimb occurrence_climb;

    CBMArena *arena;
    CBMWalkScope *scopes;
    CBMWalkScope inline_scopes[MAX_SCOPES];
    int scope_capacity;
    int scope_top;
    int function_scope_count; /* SCOPE_FUNC frames among them */

    CBMLexicalScope *lexical_scopes;
    CBMLexicalScope inline_lexical_scopes[INLINE_LEXICAL_SCOPES];
    int lexical_scope_capacity;
    int lexical_scope_count;
    uint32_t root_lexical_scope_id;
    uint32_t split_function_scope_id;
    uint32_t split_signature_start_byte;
    uint32_t split_signature_end_byte;
    const char *split_function_qn;
    uint32_t flat_function_scope_id;
    uint32_t flat_anchor_start_byte;
    uint32_t flat_anchor_end_byte;
    const char *flat_function_qn;

    CBMLexicalBinding *lexical_bindings;
    CBMLexicalBinding inline_lexical_bindings[INLINE_LEXICAL_BINDINGS];
    int lexical_binding_capacity;
    int lexical_binding_count;
    int usage_start_index;
    bool lexical_binding_tracking_failed;
    CBMPythonDirective *python_directives;
    CBMPythonDirective inline_python_directives[INLINE_PYTHON_DIRECTIVES];
    int python_directive_capacity;
    int python_directive_count;
    /* #1912 -- Python bare-call shadowing. A name bound as a parameter by ANY
     * enclosing function or lambda shadows every project function, so a bare
     * `run()` under `def outer(run)` cannot honestly resolve by short name.
     *
     * Maintained as a live name->count map pushed and popped BY THE WALK, not
     * recomputed per call. Walking ancestors (either ts_node_parent or a
     * cursor) and scanning the frame stack are both O(depth) per call, and
     * since every level of f(f(f(...))) is itself a bare call that is
     * quadratic across the file -- the same trap CBMWalkScope records above.
     * Lookup here is O(1), so no hop cap and no fail-open cap are needed.
     *
     * The other binding table (CBMLexicalBinding) cannot serve this: it is
     * qsort-ed in cbm_finalize_lexical_usages AFTER the walk and its
     * active_end stays 0 until then, so its binary search is invalid from
     * handle_calls, which runs mid-walk and before handle_usages. */
    CBMParamSlot *py_param_slots;
    CBMParamSlot inline_py_param_slots[INLINE_PY_PARAM_SLOTS];
    int py_param_slot_capacity;
    int py_param_slot_used;
    const char **py_param_stack;
    const char *inline_py_param_stack[INLINE_PY_PARAM_STACK];
    int py_param_stack_capacity;
    int py_param_stack_count;
    /* Allocation failure: stop tracking and answer "not bound" forever after,
     * which can only cost a suppression, never a true edge. */
    bool py_param_tracking_failed;

    CBMLanguage language;

    os_type_map_t os_type_map; // ObjectScript variable → type mapping
} WalkState;

/* #1912: is `name` bound as a parameter by a Python function or lambda scope
 * currently open on the walk stack? O(1). Answers false on any failure, so a
 * caller can only ever lose a suppression, never a true edge. */
bool cbm_walk_python_param_is_bound(const WalkState *state, const char *name);

// Per-node handler prototypes. Each is called once per node during the
// unified cursor walk, replacing the old recursive walk_* functions.
CBMInvocationDescriptor handle_calls(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                                     WalkState *state);
void handle_usages(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec, WalkState *state);
void cbm_finalize_lexical_usages(CBMExtractCtx *ctx, WalkState *state);

// Usage ancestor context. init before the walk; enter for EVERY node the walk
// visits (trivia included), with its visible depth and the field the walk
// cursor reports for it; free after the walk.
void cbm_usage_context_init(CBMExtractCtx *ctx, const CBMLangSpec *spec, WalkState *state);
void cbm_usage_context_enter(CBMExtractCtx *ctx, const CBMLangSpec *spec, WalkState *state,
                             uint32_t depth, TSNode node, TSFieldId field_id);
void cbm_usage_context_free(CBMExtractCtx *ctx, WalkState *state);
/* One step of an ancestor climb outside extract_usages.c, for the step
 * counter its linearity tests read (a no-op without that test API). */
void cbm_usage_ancestor_step_note(void);
/* The nearest strict ancestor of the walk's current node `node` that decides
 * for `slot` (CBM_USAGE_NEAREST_*), from the frames: true with *ancestor set
 * (null when none decides), false when the caller must climb. */
bool cbm_usage_nearest_ancestor(WalkState *state, TSNode node, int slot, TSNode *ancestor);
/* The usage-context cross-check (CBM_TEST_USAGE_CONTEXT_CHECK) for an answer
 * taken from the frames outside extract_usages.c. */
bool cbm_usage_context_checking(const WalkState *state);
void cbm_usage_context_verify(CBMExtractCtx *ctx, WalkState *state, TSNode node, const char *answer,
                              bool carried, bool climbed);
/* Where the call-side definition-role climb (extract_calls.c) stops, for
 * CBM_USAGE_NEAREST_CALL_ROLE, and the languages it climbs in. */
bool cbm_call_role_ancestor_decides(CBMLanguage language, TSNode ancestor, const char *source);
bool cbm_call_role_language(CBMLanguage language);
void handle_throws(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec, WalkState *state);
void handle_readwrites(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec, WalkState *state);
void handle_type_refs(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec, WalkState *state);
void handle_env_accesses(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                         WalkState *state);
void handle_type_assigns(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                         WalkState *state);

// Single-pass extraction using TSTreeCursor. Visits every node once,
// dispatching to all handlers per node. Replaces the 7 separate walk_*
// functions for calls/usages/throws/readwrites/type_refs/env_accesses/type_assigns.
// Definitions and imports stay as separate passes (different recursion patterns).
void cbm_extract_unified(CBMExtractCtx *ctx);

#endif // CBM_EXTRACT_UNIFIED_H
