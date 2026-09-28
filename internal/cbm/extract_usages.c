#include "cbm.h"
#include "helpers.h"
#include "lang_specs.h"
#include "extract_unified.h"
#include "tree_sitter/api.h" // TSNode, ts_node_*
#include "foundation/constants.h"
#include "foundation/mem_core.h" // cbm_realloc -- usage context frames
#include "extract_node_stack.h"
#ifdef CBM_ENABLE_TEST_SEAMS
#include "foundation/log.h" // cbm_log -- usage_context.* (cross-check seam)
#endif

enum { LAST_IDX = 1 };
#include <stdint.h> // uint32_t
#include <stdio.h>  // snprintf
#include <stdlib.h> // qsort
#include <string.h>
#include <strings.h>
#include <ctype.h>

#if (defined(CBM_CALL_REFERENCE_LOOKUP_TEST_API) && CBM_CALL_REFERENCE_LOOKUP_TEST_API) || \
    defined(CBM_ENABLE_TEST_SEAMS)
#include <stdatomic.h>
#endif

#if defined(CBM_CALL_REFERENCE_LOOKUP_TEST_API) && CBM_CALL_REFERENCE_LOOKUP_TEST_API
static _Atomic uint64_t g_usage_field_lookup_work = 0;
static _Atomic uint64_t g_usage_slow_parent_fallbacks = 0;
static _Atomic uint64_t g_usage_ancestor_steps = 0;
static _Atomic uint64_t g_usage_cursor_copy_entries = 0;

void cbm_usage_field_lookup_test_reset(void) {
    atomic_store_explicit(&g_usage_field_lookup_work, 0, memory_order_relaxed);
    atomic_store_explicit(&g_usage_slow_parent_fallbacks, 0, memory_order_relaxed);
    atomic_store_explicit(&g_usage_ancestor_steps, 0, memory_order_relaxed);
    atomic_store_explicit(&g_usage_cursor_copy_entries, 0, memory_order_relaxed);
}

uint64_t cbm_usage_field_lookup_test_work(void) {
    return atomic_load_explicit(&g_usage_field_lookup_work, memory_order_relaxed);
}

uint64_t cbm_usage_slow_parent_fallback_test_count(void) {
    return atomic_load_explicit(&g_usage_slow_parent_fallbacks, memory_order_relaxed);
}

uint64_t cbm_usage_ancestor_step_test_count(void) {
    return atomic_load_explicit(&g_usage_ancestor_steps, memory_order_relaxed);
}

uint64_t cbm_usage_cursor_copy_test_entries(void) {
    return atomic_load_explicit(&g_usage_cursor_copy_entries, memory_order_relaxed);
}

static void usage_field_lookup_test_note_work(void) {
    atomic_fetch_add_explicit(&g_usage_field_lookup_work, 1, memory_order_relaxed);
}

static void usage_slow_parent_fallback_test_note(void) {
    atomic_fetch_add_explicit(&g_usage_slow_parent_fallbacks, 1, memory_order_relaxed);
}

static void usage_ancestor_step_test_note(void) {
    atomic_fetch_add_explicit(&g_usage_ancestor_steps, 1, memory_order_relaxed);
}

static void usage_cursor_copy_test_note(uint32_t entries) {
    atomic_fetch_add_explicit(&g_usage_cursor_copy_entries, entries, memory_order_relaxed);
}
#else
static void usage_field_lookup_test_note_work(void) {}
static void usage_slow_parent_fallback_test_note(void) {}
static void usage_ancestor_step_test_note(void) {}
static void usage_cursor_copy_test_note(uint32_t entries) {
    (void)entries;
}
#endif

void cbm_usage_ancestor_step_note(void) {
    usage_ancestor_step_test_note();
}

// Forward declaration
static void walk_usages(CBMExtractCtx *ctx, TSNode root, const CBMLangSpec *spec);
static bool is_direct_argument_value(TSNode node);
static TSNode python_direct_callable_attribute_site(TSNode node);
static TSNode usage_walk_parent(CBMExtractCtx *ctx, WalkState *state, TSNode node);
static TSNode usage_walk_owner_parent(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                      uint32_t up, TSNode owner);
static TSNode usage_walk_next_named_sibling(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                            uint32_t up, TSNode owner);
static TSNode python_attribute_site_walk(CBMExtractCtx *ctx, WalkState *state, TSNode node);

// Is this an identifier-like node that represents a reference?
static bool is_reference_node(CBMExtractCtx *ctx, TSNode node, WalkState *state) {
    CBMLanguage lang = ctx->language;
    const char *kind = ts_node_type(node);

    /* Python's attribute node and its terminal identifier describe the same
     * source occurrence. For a direct callable-value argument, keep the leaf
     * as the raw carrier (so unresolved cases retain a useful short-name
     * USAGE) and stamp it with the full attribute span below. Receivers remain
     * independent value references. */
    if (lang == CBM_LANG_PYTHON && strcmp(kind, "attribute") == 0 &&
        !ts_node_is_null(python_attribute_site_walk(ctx, state, node))) {
        return false;
    }

    /* A Rust scoped_identifier owns the complete path occurrence. Its nested
     * path/identifier children are grammar structure, not additional value
     * references; keeping them would let a short-name fallback bind a decoy. */
    if (lang == CBM_LANG_RUST &&
        (strcmp(kind, "identifier") == 0 || strcmp(kind, "scoped_identifier") == 0)) {
        TSNode parent = usage_walk_parent(ctx, state, node);
        if (!ts_node_is_null(parent) && strcmp(ts_node_type(parent), "scoped_identifier") == 0) {
            return false;
        }
    }

    /* Some grammars expose the sigil/scope as a named wrapper around a generic
     * identifier. Keep exactly one occurrence: the wrapper carries the source
     * spelling that resolution needs (`$watched`, `a:watched`).
     *
     * The language gate MUST precede the parent fetch: ts_node_parent descends
     * from the root (O(depth)), and fetching it for every identifier in every
     * language made deep-nesting extraction quadratic across the board (the
     * stack_overflow deep tests went 0-1s -> 39-119s and blew the suite
     * budget on every non-M4 venue). */
    if ((lang == CBM_LANG_PUPPET || lang == CBM_LANG_VIMSCRIPT) &&
        strcmp(kind, "identifier") == 0) {
        TSNode parent = usage_walk_parent(ctx, state, node);
        if (!ts_node_is_null(parent) &&
            ((lang == CBM_LANG_PUPPET && strcmp(ts_node_type(parent), "variable") == 0) ||
             (lang == CBM_LANG_VIMSCRIPT && strcmp(ts_node_type(parent), "argument") == 0))) {
            return false;
        }
    }

    // Common identifier types across languages
    if (strcmp(kind, "identifier") == 0 || strcmp(kind, "simple_identifier") == 0 ||
        strcmp(kind, "type_identifier") == 0) {
        return true;
    }

    // Language-specific reference types
    switch (lang) {
    case CBM_LANG_JAVASCRIPT:
    case CBM_LANG_TYPESCRIPT:
    case CBM_LANG_TSX:
    case CBM_LANG_ARKTS:
    case CBM_LANG_QML:
    case CBM_LANG_CFSCRIPT:
        return strcmp(kind, "property_identifier") == 0 ||
               strcmp(kind, "private_property_identifier") == 0;
    case CBM_LANG_GO:
        return strcmp(kind, "field_identifier") == 0 || strcmp(kind, "package_identifier") == 0;
    case CBM_LANG_PYTHON:
        return strcmp(kind, "attribute") == 0;
    case CBM_LANG_RUST:
        return strcmp(kind, "field_identifier") == 0 || strcmp(kind, "scoped_identifier") == 0;
    case CBM_LANG_C:
    case CBM_LANG_CPP:
    case CBM_LANG_CUDA:
        return strcmp(kind, "field_identifier") == 0;
    case CBM_LANG_PHP:
        return strcmp(kind, "name") == 0 || strcmp(kind, "variable_name") == 0;
    case CBM_LANG_HASKELL:
        return strcmp(kind, "variable") == 0 || strcmp(kind, "constructor") == 0;
    case CBM_LANG_OCAML:
        return strcmp(kind, "value_path") == 0 || strcmp(kind, "constructor_path") == 0;
    case CBM_LANG_ERLANG:
        return strcmp(kind, "atom") == 0 || strcmp(kind, "var") == 0;
    case CBM_LANG_CSS:
        /* Custom-property reads inside `var(...)` are exposed as plain_value;
         * declarations use the separate property_name alias. */
        return strcmp(kind, "plain_value") == 0;
    case CBM_LANG_SCSS:
        /* SCSS value occurrences retain their `$` spelling in variable_value;
         * declaration parameters use the distinct variable_name node. */
        return strcmp(kind, "variable_value") == 0;
    case CBM_LANG_LLVM_IR:
        return strcmp(kind, "local_var") == 0 || strcmp(kind, "global_var") == 0;
    case CBM_LANG_PUPPET:
    case CBM_LANG_POWERSHELL:
        /* Puppet keeps the sigil in a dedicated `variable` node (`$watched`). */
        return strcmp(kind, "variable") == 0;
    case CBM_LANG_BASH:
    case CBM_LANG_FISH:
    case CBM_LANG_ZSH:
        /* Expansion wrappers retain `$`; their named leaf is the bare variable name. */
        return strcmp(kind, "variable_name") == 0;
    case CBM_LANG_PERL:
        /* Perl's named scalar node retains its sigil (`$watched`). */
        return strcmp(kind, "scalar") == 0;
    case CBM_LANG_CLOJURE:
    case CBM_LANG_COMMONLISP:
        return strcmp(kind, "sym_lit") == 0;
    case CBM_LANG_VIMSCRIPT:
        return strcmp(kind, "scoped_identifier") == 0 || strcmp(kind, "argument") == 0;
    case CBM_LANG_ELM:
        return strcmp(kind, "lower_case_identifier") == 0;
    case CBM_LANG_COBOL:
        return strcmp(kind, "qualified_word") == 0;
    case CBM_LANG_EMACSLISP:
    case CBM_LANG_SCHEME:
    case CBM_LANG_FENNEL:
    case CBM_LANG_RACKET:
    case CBM_LANG_CHIALISP:
    case CBM_LANG_LINKERSCRIPT:
        return strcmp(kind, "symbol") == 0;
    case CBM_LANG_MAKEFILE:
        return strcmp(kind, "variable_reference") == 0;
    case CBM_LANG_CMAKE:
        /* `${watched}` contains a named `variable` leaf spanning only `watched`. */
        return strcmp(kind, "variable") == 0;
    case CBM_LANG_WOLFRAM:
        return strcmp(kind, "user_symbol") == 0;
    case CBM_LANG_TYPST:
        return strcmp(kind, "ident") == 0;
    case CBM_LANG_TCL:
        /* Tcl's value spelling includes the sigil, so retain the substitution wrapper. */
        return strcmp(kind, "variable_substitution") == 0;
    case CBM_LANG_TLAPLUS:
        /* Definition-side names/parameters are `identifier`; expression-side
         * values and operator arguments use the distinct `identifier_ref`. */
        return strcmp(kind, "identifier_ref") == 0;
    case CBM_LANG_AGDA:
        /* `_qid` is hidden and aliases its public expression leaf to `qid`. */
        return strcmp(kind, "qid") == 0;
    case CBM_LANG_RESCRIPT:
        return strcmp(kind, "value_identifier") == 0;
    case CBM_LANG_PURESCRIPT:
        return strcmp(kind, "variable") == 0;
    case CBM_LANG_NICKEL:
        return strcmp(kind, "ident") == 0;
    case CBM_LANG_JSONNET:
        return strcmp(kind, "id") == 0;
    case CBM_LANG_CFML:
        return strcmp(kind, "property_identifier") == 0;
    case CBM_LANG_OBJECTSCRIPT_UDL:
    case CBM_LANG_OBJECTSCRIPT_ROUTINE:
        return strcmp(kind, "objectscript_identifier") == 0 ||
               strcmp(kind, "objectscript_identifier_special") == 0;
    case CBM_LANG_PLSQL:
        return strcmp(kind, "identifier") == 0;
    default:
        return false;
    }
}

static bool node_contains(TSNode outer, TSNode inner) {
    return !ts_node_is_null(outer) && !ts_node_is_null(inner) &&
           ts_node_start_byte(outer) <= ts_node_start_byte(inner) &&
           ts_node_end_byte(outer) >= ts_node_end_byte(inner);
}

static bool vhdl_forward_callee_wrapper(TSNode node) {
    const char *kind = ts_node_type(node);
    return strcmp(kind, "identifier") == 0 || strcmp(kind, "simple_identifier") == 0 ||
           strcmp(kind, "library_function") == 0 || strcmp(kind, "name") == 0 ||
           strcmp(kind, "simple_name") == 0;
}

static TSNode terminal_vhdl_identifier(TSNode node, int remaining_depth) {
    if (ts_node_is_null(node) || remaining_depth < 0) {
        return (TSNode){0};
    }
    uint32_t count = ts_node_named_child_count(node);
    for (uint32_t i = count; i > 0; i--) {
        TSNode found =
            terminal_vhdl_identifier(ts_node_named_child(node, i - 1), remaining_depth - 1);
        if (!ts_node_is_null(found)) {
            return found;
        }
    }
    const char *kind = ts_node_type(node);
    return strcmp(kind, "identifier") == 0 || strcmp(kind, "simple_identifier") == 0 ? node
                                                                                     : (TSNode){0};
}

// Dart and VHDL represent some calls as a callee node immediately followed by
// the invocation node. The unified pre-order walk has already visited that
// callee when the call descriptor is created, so suppress only the exact
// language-specific preceding occurrence. Do not generalize this to arbitrary
// identifiers: a sibling selector/parenthesis group is the grammar contract.
static bool is_forward_sibling_callee(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    CBMLanguage language = ctx->language;
    if (language == CBM_LANG_DART && strcmp(ts_node_type(node), "identifier") == 0) {
        TSNode next = usage_walk_next_named_sibling(ctx, state, node, 0, node);
        return !ts_node_is_null(next) && strcmp(ts_node_type(next), "selector") == 0;
    }

    if (language != CBM_LANG_VHDL) {
        return false;
    }

    TSNode owner = node;
    for (int depth = 0; depth < 4 && vhdl_forward_callee_wrapper(owner); depth++) {
        TSNode next = usage_walk_next_named_sibling(ctx, state, node, (uint32_t)depth, owner);
        if (!ts_node_is_null(next) && strcmp(ts_node_type(next), "parenthesis_group") == 0) {
            TSNode leaf = terminal_vhdl_identifier(owner, 8);
            return !ts_node_is_null(leaf) && ts_node_eq(node, leaf);
        }
        TSNode parent = usage_walk_owner_parent(ctx, state, node, (uint32_t)depth, owner);
        if (ts_node_is_null(parent) || !vhdl_forward_callee_wrapper(parent)) {
            break;
        }
        owner = parent;
    }
    return false;
}

static const char *field_name_for_node(TSNode parent, TSNode child) {
    const char *field = NULL;
    TSTreeCursor cursor = ts_tree_cursor_new(parent);
    if (ts_tree_cursor_goto_first_child(&cursor)) {
        do {
            usage_field_lookup_test_note_work();
            if (ts_node_eq(ts_tree_cursor_current_node(&cursor), child)) {
                field = ts_tree_cursor_current_field_name(&cursor);
                break;
            }
        } while (ts_tree_cursor_goto_next_sibling(&cursor));
    }
    ts_tree_cursor_delete(&cursor);
    return field;
}

/* CBMUsageContext.check_mode (CBM_TEST_USAGE_CONTEXT_CHECK). */
enum { USAGE_CHECK_REPORT = 1, USAGE_CHECK_ABORT = 2 };

/* Answers the walk carries for a node about its ancestors (see CBMUsageFrame).
 * Each bit is exactly what the named climb below returns for that node. */
enum {
    CBM_USAGE_CONTEXT_BINDING = 1U << 0,          /* standard_binding_climb */
    CBM_USAGE_CONTEXT_WRITE = 1U << 1,            /* write_climb */
    CBM_USAGE_CONTEXT_ARGUMENT_LABEL = 1U << 2,   /* call_argument_label_climb */
    CBM_USAGE_CONTEXT_PY_DEFAULT_VALUE = 1U << 3, /* python_default_value_climb */
    CBM_USAGE_CONTEXT_IN_GLOBAL = 1U << 4,        /* lexical_ancestor_kind(global_statement) */
    CBM_USAGE_CONTEXT_IN_NONLOCAL = 1U << 5,      /* lexical_ancestor_kind(nonlocal_statement) */
    CBM_USAGE_CONTEXT_PARAMETER = 1U << 6,        /* binding_is_parameter_climb */
    CBM_USAGE_CONTEXT_FUNCTION_NAME = 1U << 7,    /* declared_function_name_owner */
    CBM_USAGE_CONTEXT_CLASS_NAME = 1U << 8,       /* declared_class_name_owner */
    CBM_USAGE_CONTEXT_JS_VAR = 1U << 9,           /* js_var_binding_climb */
    CBM_USAGE_CONTEXT_PERL_CODEREF = 1U << 10,    /* direct_perl_coderef_climb */
    CBM_USAGE_CONTEXT_IMPORT_ALIAS = 1U << 11,    /* an alias field up to the import contains it */
};

/* The answer is decided by where the node sits inside a field target deeper
 * than the path child (CBMUsageTargets.via), so the frames cannot say; the
 * query climbs. One such bit per containment answer, CBM_USAGE_CONTEXT_* shifted. */
enum { CBM_USAGE_CONTEXT_UNKNOWN_SHIFT = 16 };

static uint32_t usage_unknown(uint32_t answer) {
    return answer << CBM_USAGE_CONTEXT_UNKNOWN_SHIFT;
}

#ifdef CBM_ENABLE_TEST_SEAMS
static _Atomic uint64_t g_usage_context_checks = 0;
static _Atomic uint64_t g_usage_context_mismatches = 0;
static _Atomic uint64_t g_usage_context_fallbacks = 0;

void cbm_usage_context_test_reset(void) {
    atomic_store_explicit(&g_usage_context_checks, 0, memory_order_relaxed);
    atomic_store_explicit(&g_usage_context_mismatches, 0, memory_order_relaxed);
    atomic_store_explicit(&g_usage_context_fallbacks, 0, memory_order_relaxed);
}

uint64_t cbm_usage_context_test_checks(void) {
    return atomic_load_explicit(&g_usage_context_checks, memory_order_relaxed);
}

uint64_t cbm_usage_context_test_mismatches(void) {
    return atomic_load_explicit(&g_usage_context_mismatches, memory_order_relaxed);
}

uint64_t cbm_usage_context_test_fallbacks(void) {
    return atomic_load_explicit(&g_usage_context_fallbacks, memory_order_relaxed);
}

static void usage_context_note_fallback(WalkState *state) {
    state->usage_context.fallbacks++;
    atomic_fetch_add_explicit(&g_usage_context_fallbacks, 1, memory_order_relaxed);
}

static bool usage_context_checking(const WalkState *state) {
    return state && state->usage_context.check_mode != 0;
}

/* One carried answer against the climb it replaces (`agree`; the values are
 * for the report). A disagreement means the frames are wrong, so it is always
 * reported, and fatal at USAGE_CHECK_ABORT. */
static void usage_context_report(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                 const char *answer, bool agree, uint64_t carried,
                                 uint64_t climbed) {
    state->usage_context.checks++;
    atomic_fetch_add_explicit(&g_usage_context_checks, 1, memory_order_relaxed);
    if (agree) {
        return;
    }
    state->usage_context.mismatches++;
    atomic_fetch_add_explicit(&g_usage_context_mismatches, 1, memory_order_relaxed);
    char language[16];
    char bytes[32];
    char values[48];
    snprintf(language, sizeof(language), "%d", (int)ctx->language);
    snprintf(bytes, sizeof(bytes), "%u-%u", ts_node_start_byte(node), ts_node_end_byte(node));
    snprintf(values, sizeof(values), "%llu/%llu", (unsigned long long)carried,
             (unsigned long long)climbed);
    cbm_log_error("usage_context.mismatch", "path", ctx->rel_path ? ctx->rel_path : "", "lang",
                  language, "answer", answer, "kind", ts_node_type(node), "bytes", bytes,
                  "carried_climbed", values);
    if (state->usage_context.check_mode >= USAGE_CHECK_ABORT) {
        abort();
    }
}
#else
static void usage_context_note_fallback(WalkState *state) {
    state->usage_context.fallbacks++;
}

static bool usage_context_checking(const WalkState *state) {
    (void)state;
    return false;
}

static void usage_context_report(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                 const char *answer, bool agree, uint64_t carried,
                                 uint64_t climbed) {
    (void)ctx;
    (void)state;
    (void)node;
    (void)answer;
    (void)agree;
    (void)carried;
    (void)climbed;
}
#endif

static void usage_context_verify(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                 const char *answer, bool carried, bool climbed) {
    usage_context_report(ctx, state, node, answer, carried == climbed, (uint64_t)carried,
                         (uint64_t)climbed);
}

/* The frame describing `node` when it is the walk's current node and the walk
 * keeps frames; NULL sends the caller to its climb. */
static const CBMUsageFrame *usage_frame_for(const WalkState *state, TSNode node) {
    if (!state) {
        return NULL;
    }
    const CBMUsageContext *context = &state->usage_context;
    if (!context->frames || context->failed || context->climb_only) {
        return NULL;
    }
    const CBMUsageFrame *frame = &context->frames[context->depth];
    return ts_node_eq(frame->node, node) ? frame : NULL;
}

/* The frame carrying `answer` about `node`, or NULL when the caller must climb.
 *
 * Most climbs test byte-range containment (field_contains_node): does the
 * ancestor's field child contain the node? For a node with a non-empty range
 * and a field child that is a direct child of the ancestor, it does exactly
 * when that child IS the path child at that level: siblings never overlap,
 * and an empty sibling cannot contain a non-empty range. That identity is what
 * the frames compare. Two cases still climb:
 *   - an empty node (a MISSING token, an empty production) can sit on a
 *     sibling's boundary, and ts_node_parent takes a separate path for it too,
 *     unless the answer needs no containment and came from the walk cursor's
 *     own chain (`exact_for_empty`);
 *   - a node below a field target deeper than the path child, where the
 *     answer depends on the node's own range (usage_unknown). */
static const CBMUsageFrame *usage_carried_frame(WalkState *state, TSNode node, bool exact_for_empty,
                                                uint32_t answer) {
    const CBMUsageFrame *frame = state ? usage_frame_for(state, node) : NULL;
    if (!frame) {
        return NULL;
    }
    if ((!exact_for_empty && ts_node_start_byte(node) == ts_node_end_byte(node)) ||
        (frame->context & usage_unknown(answer))) {
        usage_context_note_fallback(state);
        return NULL;
    }
    /* The O(1) lookup that replaced the climb still counts as classifier work,
     * which keeps the work floors in the linearity tests meaningful. */
    usage_field_lookup_test_note_work();
    return frame;
}

/* The walk keeps frames for `node` and they give its ts_node_parent chain: for
 * an empty node (a MISSING token, an empty production) ts_node_parent takes a
 * path of its own, so that one climbs as before. */
static const CBMUsageFrame *usage_ancestry_frame(WalkState *state, TSNode node) {
    const CBMUsageFrame *frame = usage_frame_for(state, node);
    if (frame && ts_node_start_byte(node) == ts_node_end_byte(node)) {
        usage_context_note_fallback(state);
        return NULL;
    }
    return frame;
}

/* The frames index of `owner`: the walk's current node `node` (up 0) or its
 * ancestor `up` levels above. CBM_USAGE_NO_NEAREST when the caller must climb. */
static uint32_t usage_walk_level(WalkState *state, TSNode node, uint32_t up, TSNode owner) {
    if (!usage_ancestry_frame(state, node) || state->usage_context.depth < up) {
        return CBM_USAGE_NO_NEAREST;
    }
    uint32_t level = state->usage_context.depth - up;
    return ts_node_eq(state->usage_context.frames[level].node, owner) ? level
                                                                      : CBM_USAGE_NO_NEAREST;
}

/* ts_node_parent(owner), for an owner that usage_walk_level places, read from
 * the frames: ts_node_parent descends from the root, O(depth) a call. */
static TSNode usage_walk_owner_parent(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                      uint32_t up, TSNode owner) {
    uint32_t level = usage_walk_level(state, node, up, owner);
    if (level == CBM_USAGE_NO_NEAREST) {
        usage_slow_parent_fallback_test_note();
        return ts_node_parent(owner);
    }
    usage_field_lookup_test_note_work();
    TSNode parent = level > 0 ? state->usage_context.frames[level - SKIP_ONE].node : (TSNode){0};
    if (usage_context_checking(state)) {
        TSNode climbed = ts_node_parent(owner);
        usage_context_report(ctx, state, owner, "walk_parent", ts_node_eq(parent, climbed),
                             ts_node_start_byte(parent), ts_node_start_byte(climbed));
    }
    return parent;
}

/* ts_node_parent(node), read from the frames when node is the walk's current node. */
static TSNode usage_walk_parent(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    return usage_walk_owner_parent(ctx, state, node, 0, node);
}

/* ts_node_next_named_sibling(node) given node's parent. The runtime first
 * finds the parent with ts_node_parent, a descent from the root, then scans the
 * parent's children for the first named node after `node`, looking through
 * hidden nodes; this is that scan. It declines (false) for an empty node and
 * wherever the runtime's scan has rules of its own: an empty node after
 * `node` (skipped there) or an anonymous node with named children (searched
 * there). */
static bool next_named_sibling_below(TSNode parent, TSNode node, TSNode *next) {
    uint32_t start = ts_node_start_byte(node);
    if (start == ts_node_end_byte(node)) {
        return false;
    }
    *next = (TSNode){0};
    bool decided = false;
    TSTreeCursor cursor = ts_tree_cursor_new(parent);
    if (ts_tree_cursor_goto_first_child_for_byte(&cursor, start) >= 0 &&
        ts_node_eq(ts_tree_cursor_current_node(&cursor), node)) {
        decided = true;
        while (ts_tree_cursor_goto_next_sibling(&cursor)) {
            TSNode sibling = ts_tree_cursor_current_node(&cursor);
            bool named = ts_node_is_named(sibling);
            if (ts_node_start_byte(sibling) == ts_node_end_byte(sibling) ||
                (!named && ts_node_named_child_count(sibling) > 0)) {
                decided = false;
                break;
            }
            if (named) {
                *next = sibling;
                break;
            }
        }
    }
    ts_tree_cursor_delete(&cursor);
    return decided;
}

/* ts_node_next_named_sibling(owner), for an owner that usage_walk_level
 * places, with its parent from the frames. */
static TSNode usage_walk_next_named_sibling(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                            uint32_t up, TSNode owner) {
    uint32_t level = usage_walk_level(state, node, up, owner);
    TSNode next = {0};
    if (level == CBM_USAGE_NO_NEAREST || level == 0 ||
        !next_named_sibling_below(state->usage_context.frames[level - SKIP_ONE].node, owner,
                                  &next)) {
        if (level != CBM_USAGE_NO_NEAREST) {
            usage_context_note_fallback(state);
        }
        usage_slow_parent_fallback_test_note();
        return ts_node_next_named_sibling(owner);
    }
    usage_field_lookup_test_note_work();
    if (usage_context_checking(state)) {
        TSNode climbed = ts_node_next_named_sibling(owner);
        usage_context_report(ctx, state, owner, "next_named_sibling", ts_node_eq(next, climbed),
                             ts_node_start_byte(next), ts_node_start_byte(climbed));
    }
    return next;
}

/* The nearest strict ancestor of node that decides for `slot`, and its frames
 * level (CBM_USAGE_NO_NEAREST and a null node when none does). False when the
 * caller must climb: no frames, a slot this walk does not keep, an empty node. */
static bool usage_nearest(WalkState *state, TSNode node, int slot, TSNode *ancestor,
                          uint32_t *level) {
    const CBMUsageFrame *frame = usage_ancestry_frame(state, node);
    if (!frame || !state->usage_context.nearest_kept[slot]) {
        return false;
    }
    usage_field_lookup_test_note_work();
    *level = frame->nearest[slot];
    *ancestor =
        *level == CBM_USAGE_NO_NEAREST ? (TSNode){0} : state->usage_context.frames[*level].node;
    return true;
}

bool cbm_usage_nearest_ancestor(WalkState *state, TSNode node, int slot, TSNode *ancestor) {
    uint32_t level;
    return usage_nearest(state, node, slot, ancestor, &level);
}

bool cbm_usage_context_checking(const WalkState *state) {
    return usage_context_checking(state);
}

void cbm_usage_context_verify(CBMExtractCtx *ctx, WalkState *state, TSNode node, const char *answer,
                              bool carried, bool climbed) {
    usage_context_verify(ctx, state, node, answer, carried, climbed);
}

/* An upward walk over node's ts_node_parent chain: from the frames in O(1) a
 * step when usage_ancestry_frame allows, else by ts_node_parent. */
typedef struct {
    const CBMUsageFrame *frames; /* NULL: ts_node_parent */
    uint32_t level;              /* frames index of the node the walk stands on */
} CBMUsageAncestors;

static CBMUsageAncestors usage_ancestors(WalkState *state, TSNode node) {
    CBMUsageAncestors ancestors = {NULL, 0};
    if (usage_ancestry_frame(state, node)) {
        ancestors.frames = state->usage_context.frames;
        ancestors.level = state->usage_context.depth;
    }
    return ancestors;
}

/* The parent of `current`, where the walk stands. */
static TSNode usage_ancestors_next(CBMUsageAncestors *ancestors, TSNode current) {
    usage_ancestor_step_test_note();
    if (!ancestors->frames) {
        return ts_node_parent(current);
    }
    if (ancestors->level == 0) {
        return (TSNode){0};
    }
    ancestors->level--;
    return ancestors->frames[ancestors->level].node;
}

/* Start the classifiers' upward walk at `node`, which must be the unified
 * walk's current node; any other node (and a legacy walk) gets NULL and climbs
 * with ts_node_parent. The frames hold exactly the path the walk cursor holds,
 * so stepping them is the cursor climb without first copying the cursor's
 * O(depth) stack. The copy remains for a walk without frames. There is one
 * climb per walk, as there was one cursor: starting a climb abandons any other
 * in progress. */
static CBMOccurrenceClimb *begin_occurrence_climb(WalkState *state, TSNode node) {
    if (!state || !state->current_cursor || !state->occurrence_cursor) {
        return NULL;
    }
    CBMOccurrenceClimb *climb = &state->occurrence_climb;
    if (usage_frame_for(state, node)) {
        climb->frames = state->usage_context.frames;
        climb->level = state->usage_context.depth;
        climb->cursor = NULL;
        return climb;
    }
    if (!ts_node_eq(ts_tree_cursor_current_node(state->current_cursor), node)) {
        return NULL;
    }
    usage_cursor_copy_test_note(ts_tree_cursor_current_depth(state->current_cursor) + SKIP_ONE);
    ts_tree_cursor_reset_to(state->occurrence_cursor, state->current_cursor);
    climb->frames = NULL;
    climb->level = 0;
    climb->cursor = state->occurrence_cursor;
    return climb;
}

static const char *usage_field_name(TSNode node, TSFieldId field_id) {
    return field_id ? ts_language_field_name_for_id(ts_node_language(node), field_id) : NULL;
}

/* One step up: the parent of `current` and the field `current` occupies in it.
 * With a climb, `current` must be where the climb stands. */
static bool occurrence_parent(CBMOccurrenceClimb *climb, TSNode current, TSNode *parent,
                              const char **field) {
    usage_ancestor_step_test_note();
    if (climb && climb->frames) {
        const CBMUsageFrame *frame = &climb->frames[climb->level];
        *field = usage_field_name(frame->node, frame->field_id);
        usage_field_lookup_test_note_work();
        if (climb->level == 0) {
            *parent = (TSNode){0};
            return false;
        }
        climb->level--;
        *parent = climb->frames[climb->level].node;
        return true;
    }
    if (climb) {
        *field = ts_tree_cursor_current_field_name(climb->cursor);
        usage_field_lookup_test_note_work();
        if (!ts_tree_cursor_goto_parent(climb->cursor)) {
            *parent = (TSNode){0};
            return false;
        }
        *parent = ts_tree_cursor_current_node(climb->cursor);
        return true;
    }

    *parent = ts_node_parent(current);
    if (ts_node_is_null(*parent)) {
        *field = NULL;
        return false;
    }
    *field = field_name_for_node(*parent, current);
    return true;
}

static const char *field_name_for_walk_node(WalkState *state, TSNode parent, TSNode node) {
    if (state && state->current_cursor &&
        ts_node_eq(ts_tree_cursor_current_node(state->current_cursor), node)) {
        usage_field_lookup_test_note_work();
        return ts_tree_cursor_current_field_name(state->current_cursor);
    }
    return field_name_for_node(parent, node);
}

static bool is_value_field(const char *field) {
    return field && (strcmp(field, "value") == 0 || strcmp(field, "right") == 0 ||
                     strcmp(field, "initializer") == 0 || strcmp(field, "default") == 0 ||
                     strcmp(field, "default_value") == 0 || strcmp(field, "body") == 0 ||
                     strcmp(field, "arguments") == 0 || strcmp(field, "condition") == 0 ||
                     strcmp(field, "consequence") == 0 || strcmp(field, "alternative") == 0 ||
                     strcmp(field, "expression") == 0 || strcmp(field, "result") == 0);
}

static bool kind_in_exact_set(const char *kind, const char *const *set) {
    if (!kind || !set) {
        return false;
    }
    for (const char *const *candidate = set; *candidate; candidate++) {
        if (strcmp(kind, *candidate) == 0) {
            return true;
        }
    }
    return false;
}

static bool field_contains_node(TSNode parent, const char *field, TSNode node) {
    TSNode value = ts_node_child_by_field_name(parent, field, (uint32_t)strlen(field));
    return node_contains(value, node);
}

typedef enum {
    CBM_OCCURRENCE_STANDARD = 0,
    CBM_OCCURRENCE_LISP_DEF,
    CBM_OCCURRENCE_COMMONLISP_DEFUN,
    CBM_OCCURRENCE_FENNEL_FN,
    CBM_OCCURRENCE_ELIXIR_DEF,
    CBM_OCCURRENCE_JULIA_FUNCTION,
    CBM_OCCURRENCE_WOLFRAM_SET,
    CBM_OCCURRENCE_TYPST_LET,
    CBM_OCCURRENCE_AGDA_FUNCTION,
    CBM_OCCURRENCE_TLAPLUS_OPERATOR,
    CBM_OCCURRENCE_COBOL_MOVE,
    CBM_OCCURRENCE_HCL_ATTRIBUTE,
    CBM_OCCURRENCE_ELM_VALUE,
    CBM_OCCURRENCE_RESCRIPT_LET,
    CBM_OCCURRENCE_PURESCRIPT_LHS,
    CBM_OCCURRENCE_NICKEL_LET,
    CBM_OCCURRENCE_ERLANG_CLAUSE,
    CBM_OCCURRENCE_NIX_FUNCTION,
    CBM_OCCURRENCE_MATLAB_ARGUMENTS,
    CBM_OCCURRENCE_LEAN_BINDER,
    CBM_OCCURRENCE_PASCAL_PROC,
    CBM_OCCURRENCE_TEAL_FUNCTION,
    CBM_OCCURRENCE_VHDL_INTERFACE,
    CBM_OCCURRENCE_PINE_FUNCTION,
    CBM_OCCURRENCE_LLVM_FUNCTION,
    CBM_OCCURRENCE_PKL_DECLARATION,
} CBMOccurrencePolicy;

typedef struct {
    const char *const *whole_binding_nodes;
    const char *const *write_nodes;
    CBMOccurrencePolicy policy;
    bool first_named_child_is_write;
} CBMOccurrenceSpec;

/* These are exact grammar roles, not name fragments.  Default/value/body
 * fields are barriers, so an initializer nested below one of these containers
 * remains a read. */
static const char *const common_whole_binding_nodes[] = {"formal_parameter",
                                                         "formal_parameters",
                                                         "parameter",
                                                         "parameters",
                                                         "parameter_list",
                                                         "parameter_declaration",
                                                         "parameter_specification",
                                                         "required_parameter",
                                                         "optional_parameter",
                                                         "default_parameter",
                                                         "typed_parameter",
                                                         "function_value_parameter",
                                                         "function_value_parameters",
                                                         "lambda_parameter",
                                                         "lambda_parameters",
                                                         "function_parameter_declaration",
                                                         "closure_parameters",
                                                         "block_parameters",
                                                         "receiver",
                                                         NULL};

static const char *const field_binding_nodes[] = {"variable_declarator",
                                                  "init_declarator",
                                                  "variable_declaration",
                                                  "const_declaration",
                                                  "lexical_declaration",
                                                  "short_var_declaration",
                                                  "local_variable_declaration",
                                                  "property_declaration",
                                                  "field_declaration",
                                                  "value_declaration",
                                                  "val_definition",
                                                  "var_definition",
                                                  "let_declaration",
                                                  "local_bind",
                                                  "let_binding",
                                                  "data_declaration",
                                                  "net_declaration",
                                                  "object_declaration",
                                                  "number_declaration",
                                                  "typed_binding",
                                                  "variable_assignment",
                                                  NULL};

static const char *const binding_fields[] = {"name",       "pattern", "declarator", "parameter",
                                             "parameters", "left",    "variable",   "variables",
                                             "key",        NULL};

static const char *const sql_binding_nodes[] = {"function_argument", NULL};
static const char *const haskell_binding_nodes[] = {"patterns", NULL};
static const char *const fsharp_binding_nodes[] = {
    "function_declaration_left", "value_declaration_left", "argument_patterns", NULL};
static const char *const crystal_binding_nodes[] = {"param_list", NULL};
static const char *const awk_binding_nodes[] = {"param_list", NULL};
static const char *const teal_binding_nodes[] = {"function_signature", NULL};
static const char *const systemverilog_binding_nodes[] = {"tf_port_item", "tf_port_item1", NULL};
static const char *const rescript_binding_nodes[] = {"formal_parameters", "labeled_parameter",
                                                     "parameter", NULL};
static const char *const purescript_binding_nodes[] = {"bind_pattern", "pattern", "patterns", NULL};
static const char *const nickel_binding_nodes[] = {"pattern_fun", NULL};
static const char *const jsonnet_binding_nodes[] = {"param", NULL};
static const char *const llvm_binding_nodes[] = {"function_header", NULL};
static const char *const linkerscript_write_nodes[] = {"assignment", NULL};
static const char *const meson_write_nodes[] = {"operatorunit", NULL};
static const char *const gn_write_nodes[] = {"assignment_statement", NULL};
static const char *const objectscript_binding_nodes[] = {"argument", "tag_parameter", NULL};
static const char *const objectscript_write_nodes[] = {"set_argument", NULL};

/* Parallel to lang_specs: occurrence semantics evolve without adding fields to
 * the positional CBMLangSpec initializer used by every language. */
static const CBMOccurrenceSpec occurrence_specs[CBM_LANG_COUNT] = {
    [CBM_LANG_SQL] = {sql_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_CLOJURE] = {NULL, NULL, CBM_OCCURRENCE_LISP_DEF, false},
    [CBM_LANG_SCHEME] = {NULL, NULL, CBM_OCCURRENCE_LISP_DEF, false},
    [CBM_LANG_RACKET] = {NULL, NULL, CBM_OCCURRENCE_LISP_DEF, false},
    [CBM_LANG_CHIALISP] = {NULL, NULL, CBM_OCCURRENCE_LISP_DEF, false},
    [CBM_LANG_COMMONLISP] = {NULL, NULL, CBM_OCCURRENCE_COMMONLISP_DEFUN, false},
    [CBM_LANG_FENNEL] = {NULL, NULL, CBM_OCCURRENCE_FENNEL_FN, false},
    [CBM_LANG_ELIXIR] = {NULL, NULL, CBM_OCCURRENCE_ELIXIR_DEF, false},
    [CBM_LANG_JULIA] = {NULL, NULL, CBM_OCCURRENCE_JULIA_FUNCTION, false},
    [CBM_LANG_WOLFRAM] = {NULL, NULL, CBM_OCCURRENCE_WOLFRAM_SET, false},
    [CBM_LANG_TYPST] = {NULL, NULL, CBM_OCCURRENCE_TYPST_LET, false},
    [CBM_LANG_AGDA] = {NULL, NULL, CBM_OCCURRENCE_AGDA_FUNCTION, false},
    [CBM_LANG_TLAPLUS] = {NULL, NULL, CBM_OCCURRENCE_TLAPLUS_OPERATOR, false},
    [CBM_LANG_COBOL] = {NULL, NULL, CBM_OCCURRENCE_COBOL_MOVE, false},
    [CBM_LANG_HCL] = {NULL, NULL, CBM_OCCURRENCE_HCL_ATTRIBUTE, false},
    [CBM_LANG_ELM] = {NULL, NULL, CBM_OCCURRENCE_ELM_VALUE, false},
    [CBM_LANG_RESCRIPT] = {rescript_binding_nodes, NULL, CBM_OCCURRENCE_RESCRIPT_LET, false},
    [CBM_LANG_PURESCRIPT] = {purescript_binding_nodes, NULL, CBM_OCCURRENCE_PURESCRIPT_LHS, false},
    [CBM_LANG_NICKEL] = {nickel_binding_nodes, NULL, CBM_OCCURRENCE_NICKEL_LET, false},
    [CBM_LANG_JSONNET] = {jsonnet_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_HASKELL] = {haskell_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_ERLANG] = {NULL, NULL, CBM_OCCURRENCE_ERLANG_CLAUSE, false},
    [CBM_LANG_FSHARP] = {fsharp_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_NIX] = {NULL, NULL, CBM_OCCURRENCE_NIX_FUNCTION, false},
    [CBM_LANG_MATLAB] = {NULL, NULL, CBM_OCCURRENCE_MATLAB_ARGUMENTS, false},
    [CBM_LANG_LEAN] = {NULL, NULL, CBM_OCCURRENCE_LEAN_BINDER, false},
    [CBM_LANG_PASCAL] = {NULL, NULL, CBM_OCCURRENCE_PASCAL_PROC, false},
    [CBM_LANG_VERILOG] = {systemverilog_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_AWK] = {awk_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_CRYSTAL] = {crystal_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_TEAL] = {teal_binding_nodes, NULL, CBM_OCCURRENCE_TEAL_FUNCTION, false},
    [CBM_LANG_VHDL] = {NULL, NULL, CBM_OCCURRENCE_VHDL_INTERFACE, false},
    [CBM_LANG_SYSTEMVERILOG] = {systemverilog_binding_nodes, NULL, CBM_OCCURRENCE_STANDARD, false},
    [CBM_LANG_PINE] = {NULL, NULL, CBM_OCCURRENCE_PINE_FUNCTION, false},
    [CBM_LANG_PUPPET] = {NULL, NULL, CBM_OCCURRENCE_STANDARD, true},
    [CBM_LANG_LLVM_IR] = {llvm_binding_nodes, NULL, CBM_OCCURRENCE_LLVM_FUNCTION, false},
    [CBM_LANG_PKL] = {NULL, NULL, CBM_OCCURRENCE_PKL_DECLARATION, false},
    [CBM_LANG_MESON] = {NULL, meson_write_nodes, CBM_OCCURRENCE_STANDARD, true},
    [CBM_LANG_GN] = {NULL, gn_write_nodes, CBM_OCCURRENCE_STANDARD, true},
    [CBM_LANG_LINKERSCRIPT] = {NULL, linkerscript_write_nodes, CBM_OCCURRENCE_STANDARD, true},
    [CBM_LANG_OBJECTSCRIPT_UDL] = {objectscript_binding_nodes, objectscript_write_nodes,
                                   CBM_OCCURRENCE_STANDARD, true},
    [CBM_LANG_OBJECTSCRIPT_ROUTINE] = {objectscript_binding_nodes, objectscript_write_nodes,
                                       CBM_OCCURRENCE_STANDARD, true},
};

static bool text_equals(CBMExtractCtx *ctx, TSNode node, const char *expected) {
    char *text = cbm_node_text(ctx->arena, node, ctx->source);
    return text && strcmp(text, expected) == 0;
}

static bool named_child_contains(TSNode parent, uint32_t index, TSNode node) {
    return ts_node_named_child_count(parent) > index &&
           node_contains(ts_node_named_child(parent, index), node);
}

static bool lisp_def_head(const char *text) {
    static const char *const heads[] = {"defn",
                                        "defn-",
                                        "def",
                                        "defmacro",
                                        "defmulti",
                                        "defmethod",
                                        "defprotocol",
                                        "defrecord",
                                        "deftype",
                                        "definterface",
                                        "defonce",
                                        "define",
                                        "define-syntax",
                                        "define-values",
                                        "define-struct",
                                        "define-record-type",
                                        "define/contract",
                                        "struct",
                                        NULL};
    return kind_in_exact_set(text, heads);
}

/* Chialisp heads whose THIRD form is a parameter list, so the symbols in it
 * bind rather than refer: `(defun NAME (params) body)`. Deliberately not
 * `defconstant` — its third form is the VALUE expression, whose symbols are
 * genuine usages — and not `mod`, whose binder is the second form and is
 * already covered by the shared named_child(1) rule below. */
static bool chialisp_head_binds_params_at_2(const char *head) {
    return head && (strcmp(head, "defun") == 0 || strcmp(head, "defun-inline") == 0 ||
                    strcmp(head, "defmacro") == 0 || strcmp(head, "defmac") == 0);
}

/* Room for the longest head text a policy compares, plus its terminator. */
enum { USAGE_HEAD_TEXT_MAX = 32 };

/* node's text as text_equals compares it (a C string: up to any NUL), when it
 * fits in `size` bytes. No head compared is that long, so longer text is known
 * not to match without the arena copy text_equals makes -- per ancestor form
 * of every leaf, that copy grew the arena quadratically on nested forms. */
static bool usage_short_text(CBMExtractCtx *ctx, TSNode node, char *text, size_t size) {
    uint32_t end = ts_node_end_byte(node);
    size_t length = 0;
    for (uint32_t at = ts_node_start_byte(node); at < end && ctx->source[at] != '\0'; at++) {
        if (length + SKIP_ONE >= size) {
            return false;
        }
        text[length++] = ctx->source[at];
    }
    text[length] = '\0';
    return true;
}

/* Named children of a definition form `(head name params ...)`. */
enum { LISP_DEF_NAME = 1, LISP_DEF_PARAMS = 2 };

static TSNode lisp_def_head_node(CBMExtractCtx *ctx, TSNode form) {
    return ctx->language == CBM_LANG_CHIALISP ? cbm_lisp_named_child_skip_comments(form, 0)
                                              : ts_node_named_child(form, 0);
}

/* A form is_lisp_def_binding stops at: a list whose head names a definition. */
static bool lisp_def_form(CBMExtractCtx *ctx, TSNode form) {
    const char *kind = ts_node_type(form);
    if ((strcmp(kind, "list") != 0 && strcmp(kind, "list_lit") != 0) ||
        ts_node_named_child_count(form) <= LISP_DEF_NAME) {
        return false;
    }
    TSNode head_node = lisp_def_head_node(ctx, form);
    char head[USAGE_HEAD_TEXT_MAX];
    if (ts_node_is_null(head_node) || !usage_short_text(ctx, head_node, head, sizeof(head))) {
        return false;
    }
    return ctx->language == CBM_LANG_CHIALISP ? cbm_chialisp_is_def_head(head)
                                              : lisp_def_head(head);
}

/* The definition form binds its head, its second form, and in Clojure (or
 * under a Chialisp head with parameters third) its third form. */
static bool lisp_def_form_binds(CBMExtractCtx *ctx, TSNode form, TSNode node) {
    TSNode head_node = lisp_def_head_node(ctx, form);
    if (node_contains(head_node, node) || named_child_contains(form, LISP_DEF_NAME, node)) {
        return true;
    }
    char head[USAGE_HEAD_TEXT_MAX];
    bool third_binds = ctx->language == CBM_LANG_CLOJURE ||
                       (ctx->language == CBM_LANG_CHIALISP &&
                        usage_short_text(ctx, head_node, head, sizeof(head)) &&
                        chialisp_head_binds_params_at_2(head));
    return third_binds && ts_node_named_child_count(form) > LISP_DEF_PARAMS &&
           named_child_contains(form, LISP_DEF_PARAMS, node);
}

static bool is_lisp_def_binding(CBMExtractCtx *ctx, TSNode node) {
    for (TSNode form = ts_node_parent(node); !ts_node_is_null(form); form = ts_node_parent(form)) {
        usage_ancestor_step_test_note();
        if (lisp_def_form(ctx, form)) {
            return lisp_def_form_binds(ctx, form, node);
        }
    }
    return false;
}

static bool is_fennel_fn_binding(CBMExtractCtx *ctx, TSNode node) {
    for (TSNode form = ts_node_parent(node); !ts_node_is_null(form); form = ts_node_parent(form)) {
        if (strcmp(ts_node_type(form), "list") != 0 || ts_node_named_child_count(form) < 2 ||
            !text_equals(ctx, ts_node_named_child(form, 0), "fn")) {
            continue;
        }
        TSNode first = ts_node_named_child(form, 1);
        const char *first_kind = ts_node_type(first);
        bool anonymous = strcmp(first_kind, "sequence") == 0 || strcmp(first_kind, "table") == 0 ||
                         strcmp(first_kind, "vector") == 0;
        if (anonymous) {
            return named_child_contains(form, 0, node) || node_contains(first, node);
        }
        return named_child_contains(form, 0, node) || node_contains(first, node) ||
               (ts_node_named_child_count(form) > 2 && named_child_contains(form, 2, node));
    }
    return false;
}

/* The named child of a definition call `def name(args)` after its head. */
enum { ELIXIR_DEF_ARGUMENTS = 1 };

/* A form is_elixir_def_binding stops at: a def, defp or defmacro call. */
static bool elixir_def_form(CBMExtractCtx *ctx, TSNode form) {
    if (strcmp(ts_node_type(form), "call") != 0 ||
        ts_node_named_child_count(form) <= ELIXIR_DEF_ARGUMENTS) {
        return false;
    }
    char head[USAGE_HEAD_TEXT_MAX];
    return usage_short_text(ctx, ts_node_named_child(form, 0), head, sizeof(head)) &&
           (strcmp(head, "def") == 0 || strcmp(head, "defp") == 0 || strcmp(head, "defmacro") == 0);
}

/* The definition binds its head and its signature, not its body. */
static bool elixir_def_form_binds(TSNode form, TSNode node) {
    TSNode head = ts_node_named_child(form, 0);
    TSNode arguments = ts_node_child_by_field_name(form, TS_FIELD("arguments"));
    if (ts_node_is_null(arguments) || ts_node_named_child_count(arguments) == 0) {
        arguments = ts_node_named_child(form, ELIXIR_DEF_ARGUMENTS);
    }
    TSNode signature =
        ts_node_named_child_count(arguments) > 0 ? ts_node_named_child(arguments, 0) : arguments;
    return node_contains(head, node) || node_contains(signature, node);
}

static bool is_elixir_def_binding(CBMExtractCtx *ctx, TSNode node) {
    for (TSNode form = ts_node_parent(node); !ts_node_is_null(form); form = ts_node_parent(form)) {
        usage_ancestor_step_test_note();
        if (elixir_def_form(ctx, form)) {
            return elixir_def_form_binds(form, node);
        }
    }
    return false;
}

static bool is_first_named_part_of(TSNode node, const char *container_kind) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (strcmp(ts_node_type(parent), container_kind) == 0) {
            return named_child_contains(parent, 0, node);
        }
    }
    return false;
}

static bool is_wolfram_lhs(TSNode node) {
    static const char *const set_nodes[] = {
        "set",     "set_top",     "set_delayed",     "set_delayed_top",
        "tag_set", "tag_set_top", "tag_set_delayed", "tag_set_delayed_top",
        "up_set",  "up_set_top",  "up_set_delayed",  "up_set_delayed_top",
        NULL};
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (kind_in_exact_set(ts_node_type(parent), set_nodes)) {
            return named_child_contains(parent, 0, node);
        }
    }
    return false;
}

static bool any_field_contains_node(TSNode parent, const char *field, TSNode node);

/* A binder is_tlaplus_binding stops at. */
static bool tlaplus_binder_form(TSNode node) {
    const char *kind = ts_node_type(node);
    return strcmp(kind, "operator_definition") == 0 || strcmp(kind, "function_definition") == 0 ||
           strcmp(kind, "bounded_quantification") == 0 ||
           strcmp(kind, "unbounded_quantification") == 0;
}

/* Does the binder bind node? `bound` is the nearest quantifier_bound strictly
 * between them (null if none), which decides under a function definition or a
 * bounded quantification. */
static bool tlaplus_binder_binds(TSNode binder, TSNode bound, TSNode node) {
    const char *kind = ts_node_type(binder);
    if (strcmp(kind, "operator_definition") == 0) {
        /* `name:` is the callable declaration, while every repeated
         * `parameter:` field is a function-wide lexical binder. */
        return any_field_contains_node(binder, "parameter", node);
    }
    if (strcmp(kind, "unbounded_quantification") == 0) {
        return any_field_contains_node(binder, "intro", node);
    }
    /* `F[x \in S] == ...`: only quantifier_bound.intro binds. The set
     * expression S remains an ordinary identifier_ref usage. */
    return !ts_node_is_null(bound) && any_field_contains_node(bound, "intro", node);
}

static bool is_tlaplus_binding(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (!tlaplus_binder_form(parent)) {
            continue;
        }
        TSNode bound = {0};
        const char *kind = ts_node_type(parent);
        if (strcmp(kind, "function_definition") == 0 ||
            strcmp(kind, "bounded_quantification") == 0) {
            for (TSNode above = ts_node_parent(node);
                 !ts_node_is_null(above) && !ts_node_eq(above, parent);
                 above = ts_node_parent(above)) {
                usage_ancestor_step_test_note();
                if (strcmp(ts_node_type(above), "quantifier_bound") == 0) {
                    bound = above;
                    break;
                }
            }
        }
        return tlaplus_binder_binds(parent, bound, node);
    }
    return false;
}

static bool is_cobol_move_destination(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (strcmp(ts_node_type(parent), "move_statement") != 0) {
            continue;
        }
        if (field_contains_node(parent, "destination", node) ||
            field_contains_node(parent, "target", node)) {
            return true;
        }
        uint32_t count = ts_node_named_child_count(parent);
        return count > 1 && named_child_contains(parent, count - 1, node);
    }
    return false;
}

/* Some grammars expose declaration roles as repeated/inherited fields. The
 * public child-by-field helper returns only one match, so inspect every direct
 * child and preserve the exact field role while allowing nested wrappers. */
static bool any_field_contains_node(TSNode parent, const char *field, TSNode node) {
    uint32_t count = ts_node_child_count(parent);
    for (uint32_t i = 0; i < count; i++) {
        const char *child_field = ts_node_field_name_for_child(parent, i);
        if (child_field && strcmp(child_field, field) == 0 &&
            node_contains(ts_node_child(parent, i), node)) {
            return true;
        }
    }
    return false;
}

static bool is_perl_lexical_declaration_binding(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (strcmp(ts_node_type(parent), "variable_declaration") == 0) {
            /* Perl permits repeated `variables:` fields for `my ($a, $b)`;
             * inspect all direct field instances, not only the first. */
            return any_field_contains_node(parent, "variables", node);
        }
        if (strcmp(ts_node_type(parent), "assignment_expression") == 0) {
            return false;
        }
    }
    return false;
}

static bool is_cmake_function_parameter(TSNode node) {
    if (strcmp(ts_node_type(node), "unquoted_argument") != 0) {
        return false;
    }
    TSNode argument = ts_node_parent(node);
    TSNode arguments = ts_node_parent(argument);
    TSNode command = ts_node_parent(arguments);
    if (ts_node_is_null(argument) || strcmp(ts_node_type(argument), "argument") != 0 ||
        ts_node_is_null(arguments) || strcmp(ts_node_type(arguments), "argument_list") != 0 ||
        ts_node_is_null(command) ||
        (strcmp(ts_node_type(command), "function_command") != 0 &&
         strcmp(ts_node_type(command), "macro_command") != 0)) {
        return false;
    }
    uint32_t count = ts_node_named_child_count(arguments);
    for (uint32_t i = 1; i < count; i++) {
        if (node_contains(ts_node_named_child(arguments, i), node)) {
            return true;
        }
    }
    return false;
}

static bool fish_argument_marker(CBMExtractCtx *ctx, TSNode node) {
    char *text = cbm_node_text(ctx->arena, node, ctx->source);
    return text && (strcmp(text, "-a") == 0 || strcmp(text, "--argument") == 0 ||
                    strcmp(text, "--argument-names") == 0);
}

static bool is_fish_function_parameter(CBMExtractCtx *ctx, TSNode node, WalkState *state) {
    if (strcmp(ts_node_type(node), "word") != 0) {
        return false;
    }
    TSNode definition = ts_node_parent(node);
    const char *field =
        ts_node_is_null(definition) ? NULL : field_name_for_walk_node(state, definition, node);
    if (!field || strcmp(field, "option") != 0 ||
        strcmp(ts_node_type(definition), "function_definition") != 0) {
        return false;
    }
    for (TSNode previous = ts_node_prev_named_sibling(node); !ts_node_is_null(previous);
         previous = ts_node_prev_named_sibling(previous)) {
        char *text = cbm_node_text(ctx->arena, previous, ctx->source);
        if (!text || text[0] != '-') {
            continue;
        }
        return fish_argument_marker(ctx, previous);
    }
    return false;
}

static bool is_tcl_procedure_parameter(TSNode node) {
    TSNode argument = ts_node_parent(node);
    if (ts_node_is_null(argument) || strcmp(ts_node_type(argument), "argument") != 0 ||
        !any_field_contains_node(argument, "name", node)) {
        return false;
    }
    TSNode arguments = ts_node_parent(argument);
    TSNode procedure = ts_node_parent(arguments);
    return !ts_node_is_null(arguments) && strcmp(ts_node_type(arguments), "arguments") == 0 &&
           !ts_node_is_null(procedure) && strcmp(ts_node_type(procedure), "procedure") == 0 &&
           any_field_contains_node(procedure, "arguments", node);
}

static bool cfml_argument_tag_name_binding(CBMExtractCtx *ctx, TSNode node) {
    if (strcmp(ts_node_type(node), "attribute_value") != 0) {
        return false;
    }
    TSNode quoted = ts_node_parent(node);
    TSNode attribute = ts_node_parent(quoted);
    if (ts_node_is_null(attribute) || strcmp(ts_node_type(attribute), "cf_attribute") != 0) {
        return false;
    }
    TSNode attribute_name = cbm_find_child_by_kind(attribute, "cf_attribute_name");
    char *name_text = cbm_node_text(ctx->arena, attribute_name, ctx->source);
    if (!name_text || strcasecmp(name_text, "name") != 0) {
        return false;
    }
    TSNode tag = ts_node_parent(attribute);
    if (ts_node_is_null(tag) || strcmp(ts_node_type(tag), "cf_selfclose_tag") != 0) {
        return false;
    }
    char *tag_text = cbm_node_text(ctx->arena, tag, ctx->source);
    static const char argument_tag[] = "<cfargument";
    size_t prefix_length = sizeof(argument_tag) - 1U;
    if (!tag_text || strncasecmp(tag_text, argument_tag, prefix_length) != 0 ||
        (tag_text[prefix_length] != '\0' && !isspace((unsigned char)tag_text[prefix_length]) &&
         tag_text[prefix_length] != '>' && tag_text[prefix_length] != '/')) {
        return false;
    }
    for (TSNode parent = ts_node_parent(tag); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (strcmp(ts_node_type(parent), "cf_function_tag") == 0) {
            return true;
        }
    }
    return false;
}

static bool is_exact_language_binding(CBMExtractCtx *ctx, TSNode node, WalkState *state) {
    const char *kind = ts_node_type(node);
    switch (ctx->language) {
    case CBM_LANG_OCAML: {
        if (strcmp(kind, "value_pattern") != 0) {
            return false;
        }
        TSNode parameter = ts_node_parent(node);
        return !ts_node_is_null(parameter) && strcmp(ts_node_type(parameter), "parameter") == 0 &&
               field_contains_node(parameter, "pattern", node);
    }
    case CBM_LANG_SCSS: {
        if (strcmp(kind, "variable_name") != 0) {
            return false;
        }
        TSNode parameter = ts_node_parent(node);
        return !ts_node_is_null(parameter) && strcmp(ts_node_type(parameter), "parameter") == 0;
    }
    case CBM_LANG_FORM: {
        if (strcmp(kind, "parameter") != 0) {
            return false;
        }
        TSNode parameters = ts_node_parent(node);
        return !ts_node_is_null(parameters) &&
               strcmp(ts_node_type(parameters), "parameter_list") == 0;
    }
    case CBM_LANG_FUNC: {
        if (strcmp(kind, "parameter") != 0) {
            return false;
        }
        TSNode declaration = ts_node_parent(node);
        return !ts_node_is_null(declaration) &&
               strcmp(ts_node_type(declaration), "parameter_declaration") == 0 &&
               field_contains_node(declaration, "name", node);
    }
    case CBM_LANG_PERL:
        return is_perl_lexical_declaration_binding(node);
    case CBM_LANG_CMAKE:
        return is_cmake_function_parameter(node);
    case CBM_LANG_FISH:
        return is_fish_function_parameter(ctx, node, state);
    case CBM_LANG_TCL:
        return is_tcl_procedure_parameter(node);
    case CBM_LANG_CFML:
        return cfml_argument_tag_name_binding(ctx, node);
    default:
        return false;
    }
}

static bool ancestor_field_binds(TSNode node, const char *container_kind,
                                 const char *const *fields) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (strcmp(ts_node_type(parent), container_kind) != 0) {
            continue;
        }
        for (const char *const *field = fields; *field; field++) {
            if (any_field_contains_node(parent, *field, node)) {
                return true;
            }
        }
        return false;
    }
    return false;
}

static bool is_erlang_clause_binding(TSNode node) {
    static const char *const fields[] = {"args", NULL};
    return ancestor_field_binds(node, "function_clause", fields);
}

static bool is_nix_function_binding(TSNode node) {
    /* tree-sitter-nix names a simple `x: body` binder `universal`; set
     * destructuring uses the distinct `formals` field. */
    static const char *const fields[] = {"universal", "formals", NULL};
    return ancestor_field_binds(node, "function_expression", fields);
}

static bool is_lean_binder_name(TSNode node) {
    static const char *const binder_kinds[] = {"explicit_binder", "implicit_binder",
                                               "instance_binder", NULL};
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (kind_in_exact_set(ts_node_type(parent), binder_kinds)) {
            return any_field_contains_node(parent, "name", node);
        }
    }
    return false;
}

static bool is_pascal_proc_binding(TSNode node) {
    static const char *const fields[] = {"args", NULL};
    return ancestor_field_binds(node, "declProc", fields) ||
           ancestor_field_binds(node, "defProc", fields);
}

static bool is_teal_function_binding(TSNode node) {
    TSNode arguments = {0};
    for (TSNode current = ts_node_parent(node); !ts_node_is_null(current);
         current = ts_node_parent(current)) {
        const char *kind = ts_node_type(current);
        if (ts_node_is_null(arguments) && strcmp(kind, "arguments") == 0) {
            arguments = current;
            continue;
        }
        if (strcmp(kind, "function_signature") == 0) {
            return !ts_node_is_null(arguments) &&
                   any_field_contains_node(current, "arguments", node);
        }
        if (strcmp(kind, "function_statement") == 0) {
            if (ts_node_is_null(arguments)) {
                return false;
            }
            TSNode signature = ts_node_child_by_field_name(current, TS_FIELD("signature"));
            return node_contains(signature, arguments);
        }
    }
    return false;
}

/* The defun_header binds the function's name and its lambda list. */
static bool commonlisp_defun_header_binds(TSNode header, TSNode node) {
    return field_contains_node(header, "function_name", node) ||
           field_contains_node(header, "lambda_list", node);
}

static bool is_commonlisp_defun_binding(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (strcmp(ts_node_type(parent), "defun_header") != 0) {
            continue;
        }
        return commonlisp_defun_header_binds(parent, node);
    }
    return false;
}

static bool is_hcl_attribute_binding(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (strcmp(ts_node_type(parent), "attribute") == 0) {
            /* HCL's attribute production exposes no fields. The first named
             * child is its key; the expression is the second named child. */
            return named_child_contains(parent, 0, node);
        }
    }
    return false;
}

static bool is_matlab_argument_binding(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        const char *kind = ts_node_type(parent);
        if (strcmp(kind, "function_arguments") == 0 || strcmp(kind, "lambda_arguments") == 0) {
            return true;
        }
    }
    return false;
}

static bool is_vhdl_interface_binding(TSNode node) {
    static const char *const interface_kinds[] = {
        "interface_constant_declaration", "interface_signal_declaration",
        "interface_variable_declaration", "interface_declaration", NULL};
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (kind_in_exact_set(ts_node_type(parent), interface_kinds)) {
            /* FIELD_COUNT does not name this role; every interface production
             * starts with its identifier_list before mode/type/default. */
            return named_child_contains(parent, 0, node);
        }
    }
    return false;
}

static bool is_pine_function_binding(TSNode node) {
    static const char *const fields[] = {"argument", NULL};
    return ancestor_field_binds(node, "function_declaration_statement", fields);
}

/* Pkl declares names positionally: no production labels the declared identifier
 * with a `name` field, so the generic declared-container rule never binds them
 * and every method name, parameter name, and property name would be re-emitted
 * as an ordinary read of itself. Each container below holds its declared name
 * as named child 0; annotations, defaults, and bodies follow it and stay reads.
 * Resolve against the NEAREST container so a nested declaration's own name is
 * the only occurrence its parent can bind. */
static bool is_pkl_declaration_binding(TSNode node) {
    static const char *const declaration_kinds[] = {"methodHeader",
                                                    "typedIdentifier",
                                                    "classProperty",
                                                    "objectProperty",
                                                    "clazz",
                                                    "typeAlias",
                                                    NULL};
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        if (kind_in_exact_set(ts_node_type(parent), declaration_kinds)) {
            return named_child_contains(parent, 0, node);
        }
    }
    return false;
}

/* The language's binding policy, by climbing from `node`. */
static bool policy_binding_climb(CBMExtractCtx *ctx, TSNode node,
                                 const CBMOccurrenceSpec *occurrence) {
    switch (occurrence->policy) {
    case CBM_OCCURRENCE_LISP_DEF:
        return is_lisp_def_binding(ctx, node);
    case CBM_OCCURRENCE_COMMONLISP_DEFUN:
        return is_commonlisp_defun_binding(node);
    case CBM_OCCURRENCE_FENNEL_FN:
        return is_fennel_fn_binding(ctx, node);
    case CBM_OCCURRENCE_ELIXIR_DEF:
        return is_elixir_def_binding(ctx, node);
    case CBM_OCCURRENCE_JULIA_FUNCTION:
        return is_first_named_part_of(node, "function_definition");
    case CBM_OCCURRENCE_WOLFRAM_SET:
        return is_wolfram_lhs(node);
    case CBM_OCCURRENCE_TYPST_LET:
        return is_first_named_part_of(node, "let");
    case CBM_OCCURRENCE_AGDA_FUNCTION:
        for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
             parent = ts_node_parent(parent)) {
            if (strcmp(ts_node_type(parent), "lhs") == 0) {
                return true;
            }
        }
        return false;
    case CBM_OCCURRENCE_TLAPLUS_OPERATOR:
        return is_tlaplus_binding(node);
    case CBM_OCCURRENCE_COBOL_MOVE:
        return is_cobol_move_destination(node);
    case CBM_OCCURRENCE_HCL_ATTRIBUTE:
        return is_hcl_attribute_binding(node);
    case CBM_OCCURRENCE_ELM_VALUE:
        return is_first_named_part_of(node, "value_declaration");
    case CBM_OCCURRENCE_RESCRIPT_LET:
        return is_first_named_part_of(node, "let_binding");
    case CBM_OCCURRENCE_PURESCRIPT_LHS:
        return is_first_named_part_of(node, "function");
    case CBM_OCCURRENCE_NICKEL_LET:
        return is_first_named_part_of(node, "let_binding") ||
               is_first_named_part_of(node, "pattern_fun");
    case CBM_OCCURRENCE_ERLANG_CLAUSE:
        return is_erlang_clause_binding(node);
    case CBM_OCCURRENCE_NIX_FUNCTION:
        return is_nix_function_binding(node);
    case CBM_OCCURRENCE_MATLAB_ARGUMENTS:
        return is_matlab_argument_binding(node);
    case CBM_OCCURRENCE_LEAN_BINDER:
        return is_lean_binder_name(node);
    case CBM_OCCURRENCE_PASCAL_PROC:
        return is_pascal_proc_binding(node);
    case CBM_OCCURRENCE_TEAL_FUNCTION:
        return is_teal_function_binding(node);
    case CBM_OCCURRENCE_VHDL_INTERFACE:
        return is_vhdl_interface_binding(node);
    case CBM_OCCURRENCE_PINE_FUNCTION:
        return is_pine_function_binding(node);
    case CBM_OCCURRENCE_PKL_DECLARATION:
        return is_pkl_declaration_binding(node);
    case CBM_OCCURRENCE_LLVM_FUNCTION:
        for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
             parent = ts_node_parent(parent)) {
            if (strcmp(ts_node_type(parent), "function_header") == 0) {
                return field_contains_node(parent, "arguments", node);
            }
        }
        return false;
    case CBM_OCCURRENCE_STANDARD:
    default:
        return false;
    }
}

/* Most policies climb to the NEAREST ancestor of some description and decide
 * there. The walk keeps that ancestor on its frames (CBM_USAGE_NEAREST_POLICY,
 * and _POLICY_AUX for a policy's second search), so the climbs below become a
 * lookup; each still decides at its ancestor with its own code. Every named
 * leaf asks, twice, so a nested chain of forms made the climb O(depth) root
 * descents per leaf: cubic overall. */

/* The container is_first_named_part_of looks for under `policy` (Nickel's
 * first of two), or NULL. */
static const char *policy_first_named_part_kind(CBMOccurrencePolicy policy) {
    switch (policy) {
    case CBM_OCCURRENCE_JULIA_FUNCTION:
        return "function_definition";
    case CBM_OCCURRENCE_TYPST_LET:
        return "let";
    case CBM_OCCURRENCE_ELM_VALUE:
        return "value_declaration";
    case CBM_OCCURRENCE_RESCRIPT_LET:
    case CBM_OCCURRENCE_NICKEL_LET:
        return "let_binding";
    case CBM_OCCURRENCE_PURESCRIPT_LHS:
        return "function";
    default:
        return NULL;
    }
}

/* Where the policy's climb stops (CBM_USAGE_NEAREST_POLICY). */
static bool policy_ancestor_decides(CBMExtractCtx *ctx, TSNode ancestor) {
    CBMOccurrencePolicy policy = occurrence_specs[ctx->language].policy;
    switch (policy) {
    case CBM_OCCURRENCE_LISP_DEF:
        return lisp_def_form(ctx, ancestor);
    case CBM_OCCURRENCE_COMMONLISP_DEFUN:
        return strcmp(ts_node_type(ancestor), "defun_header") == 0;
    case CBM_OCCURRENCE_ELIXIR_DEF:
        return elixir_def_form(ctx, ancestor);
    case CBM_OCCURRENCE_TLAPLUS_OPERATOR:
        return tlaplus_binder_form(ancestor);
    default: {
        const char *kind = policy_first_named_part_kind(policy);
        return kind && strcmp(ts_node_type(ancestor), kind) == 0;
    }
    }
}

/* The policy's second search (CBM_USAGE_NEAREST_POLICY_AUX): the quantifier
 * bound under a TLA+ binder, Nickel's pattern_fun. */
static bool policy_aux_ancestor_decides(CBMExtractCtx *ctx, TSNode ancestor) {
    switch (occurrence_specs[ctx->language].policy) {
    case CBM_OCCURRENCE_TLAPLUS_OPERATOR:
        return strcmp(ts_node_type(ancestor), "quantifier_bound") == 0;
    case CBM_OCCURRENCE_NICKEL_LET:
        return strcmp(ts_node_type(ancestor), "pattern_fun") == 0;
    default:
        return false;
    }
}

/* Does is_policy_binding read CBM_USAGE_NEAREST_POLICY under `policy`? */
static bool policy_uses_nearest(CBMOccurrencePolicy policy) {
    switch (policy) {
    case CBM_OCCURRENCE_LISP_DEF:
    case CBM_OCCURRENCE_COMMONLISP_DEFUN:
    case CBM_OCCURRENCE_ELIXIR_DEF:
    case CBM_OCCURRENCE_TLAPLUS_OPERATOR:
        return true;
    default:
        return policy_first_named_part_kind(policy) != NULL;
    }
}

/* The policy's answer for node at the nearest deciding ancestor (at frames
 * `level`) and the nearest ancestor of its second search (at `aux_level`). */
static bool policy_binding_at(CBMExtractCtx *ctx, TSNode node, TSNode ancestor, uint32_t level,
                              TSNode aux, uint32_t aux_level) {
    CBMOccurrencePolicy policy = occurrence_specs[ctx->language].policy;
    if (policy == CBM_OCCURRENCE_NICKEL_LET && !ts_node_is_null(aux) &&
        named_child_contains(aux, 0, node)) {
        return true;
    }
    if (ts_node_is_null(ancestor)) {
        return false;
    }
    switch (policy) {
    case CBM_OCCURRENCE_LISP_DEF:
        return lisp_def_form_binds(ctx, ancestor, node);
    case CBM_OCCURRENCE_COMMONLISP_DEFUN:
        return commonlisp_defun_header_binds(ancestor, node);
    case CBM_OCCURRENCE_ELIXIR_DEF:
        return elixir_def_form_binds(ancestor, node);
    case CBM_OCCURRENCE_TLAPLUS_OPERATOR:
        /* Only a quantifier bound strictly below the binder counts. */
        return tlaplus_binder_binds(
            ancestor, aux_level != CBM_USAGE_NO_NEAREST && aux_level > level ? aux : (TSNode){0},
            node);
    default:
        return named_child_contains(ancestor, 0, node);
    }
}

static bool is_policy_binding(CBMExtractCtx *ctx, TSNode node, const CBMOccurrenceSpec *occurrence,
                              WalkState *state) {
    TSNode ancestor;
    uint32_t level;
    if (!usage_nearest(state, node, CBM_USAGE_NEAREST_POLICY, &ancestor, &level)) {
        return policy_binding_climb(ctx, node, occurrence);
    }
    TSNode aux = {0};
    uint32_t aux_level = CBM_USAGE_NO_NEAREST;
    if (!usage_nearest(state, node, CBM_USAGE_NEAREST_POLICY_AUX, &aux, &aux_level)) {
        aux = (TSNode){0};
        aux_level = CBM_USAGE_NO_NEAREST;
    }
    bool carried = policy_binding_at(ctx, node, ancestor, level, aux, aux_level);
    if (usage_context_checking(state)) {
        usage_context_verify(ctx, state, node, "policy_binding", carried,
                             policy_binding_climb(ctx, node, occurrence));
    }
    return carried;
}

static bool elixir_binary_operator_binds(CBMExtractCtx *ctx, TSNode node) {
    if (ctx->language != CBM_LANG_ELIXIR || strcmp(ts_node_type(node), "binary_operator") != 0) {
        return false;
    }
    TSNode operator_node = ts_node_child_by_field_name(node, TS_FIELD("operator"));
    return text_equals(ctx, operator_node, "=") || text_equals(ctx, operator_node, "<-") ||
           text_equals(ctx, operator_node, "->") || text_equals(ctx, operator_node, "\\\\");
}

/* A declaration whose binding fields bind (standard_binding_climb). Elixir's
 * binary_operator binds by its operator text instead of by the variable kinds. */
static bool binding_declared_container(CBMExtractCtx *ctx, const CBMLangSpec *spec, TSNode parent,
                                       const char *kind) {
    bool variable_container =
        spec->variable_node_types && cbm_kind_in_set(parent, spec->variable_node_types);
    if (ctx->language == CBM_LANG_ELIXIR && strcmp(kind, "binary_operator") == 0) {
        variable_container = elixir_binary_operator_binds(ctx, parent);
    }
    return kind_in_exact_set(kind, field_binding_nodes) ||
           (spec->function_node_types && cbm_kind_in_set(parent, spec->function_node_types)) ||
           (spec->class_node_types && cbm_kind_in_set(parent, spec->class_node_types)) ||
           (spec->field_node_types && cbm_kind_in_set(parent, spec->field_node_types)) ||
           variable_container;
}

/* The standard binding rules, by climbing from `node`: the nearest ancestor
 * that decides, decides. The walk carries the same answer down
 * (CBM_USAGE_CONTEXT_BINDING); this climb answers when it cannot. */
static bool standard_binding_climb(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                                   CBMOccurrenceClimb *climb) {
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    TSNode current = node;
    while (!ts_node_is_null(current)) {
        TSNode parent;
        const char *field;
        if (!occurrence_parent(climb, current, &parent, &field)) {
            break;
        }
        if (is_value_field(field)) {
            return false;
        }
        /* A declaration container binds its name/pattern, not the symbols used
         * by its type annotation.  Both TypeScript (`cfg: Config`) and Go
         * (`cfg Config`) expose that annotation through the exact `type` field;
         * stop before the whole-parameter binding rule can swallow `Config`.
         * The emitted occurrence remains an ordinary USAGE, never a callable
         * reference merely because the target happens to be a type. */
        if (field && strcmp(field, "type") == 0) {
            return false;
        }

        const char *kind = ts_node_type(parent);
        /* PL/SQL: `parameter` is a ref_call ARGUMENT wrapper (upstream grammar
         * naming), not a declaration; definition-side bindings use the distinct
         * parameter_declaration kind. Skip it so call arguments stay ordinary
         * value usages. */
        if (ctx->language == CBM_LANG_PLSQL && strcmp(kind, "parameter") == 0) {
            current = parent;
            continue;
        }
        if (kind_in_exact_set(kind, common_whole_binding_nodes) ||
            kind_in_exact_set(kind, occurrence->whole_binding_nodes)) {
            return true;
        }

        if (binding_declared_container(ctx, spec, parent, kind)) {
            for (const char *const *binding_field = binding_fields; *binding_field;
                 binding_field++) {
                if (field_contains_node(parent, *binding_field, node)) {
                    return true;
                }
            }
        }
        current = parent;
    }
    return false;
}

static bool is_binding_occurrence(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                                  WalkState *state) {
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    if (is_exact_language_binding(ctx, node, state)) {
        return true;
    }
    if (is_policy_binding(ctx, node, occurrence, state)) {
        return true;
    }
    const CBMUsageFrame *frame = usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_BINDING);
    if (!frame) {
        return standard_binding_climb(ctx, node, spec, begin_occurrence_climb(state, node));
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_BINDING) != 0;
    if (usage_context_checking(state)) {
        state->usage_context.climb_only = true;
        bool climbed = standard_binding_climb(ctx, node, spec, begin_occurrence_climb(state, node));
        state->usage_context.climb_only = false;
        usage_context_verify(ctx, state, node, "binding", carried, climbed);
    }
    return carried;
}

static bool assignment_reads_target(TSNode assignment) {
    static const char *const read_write_nodes[] = {"augmented_assignment",
                                                   "augmented_assignment_expression",
                                                   "compound_assignment_expr",
                                                   "compound_assignment_expression",
                                                   "operator_assignment",
                                                   "operator_assign",
                                                   "update_exp",
                                                   "postfix_unary_expression",
                                                   "prefix_unary_expression",
                                                   NULL};
    if (kind_in_exact_set(ts_node_type(assignment), read_write_nodes)) {
        return true;
    }
    static const char *const read_write_operators[] = {"+=",
                                                       "-=",
                                                       "*=",
                                                       "/=",
                                                       "%=",
                                                       "&=",
                                                       "|=",
                                                       "^=",
                                                       "<<=",
                                                       ">>=",
                                                       "?"
                                                       "?=",
                                                       "++",
                                                       "--",
                                                       NULL};
    uint32_t count = ts_node_child_count(assignment);
    for (uint32_t i = 0; i < count; i++) {
        if (kind_in_exact_set(ts_node_type(ts_node_child(assignment, i)), read_write_operators)) {
            return true;
        }
    }
    return false;
}

/* Assignment-target rules, by climbing from `node`. Carried down as
 * CBM_USAGE_CONTEXT_WRITE. */
static bool write_climb(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                        CBMOccurrenceClimb *climb) {
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    TSNode current = node;
    while (!ts_node_is_null(current)) {
        TSNode parent;
        const char *field;
        if (!occurrence_parent(climb, current, &parent, &field)) {
            break;
        }
        if (is_value_field(field)) {
            return false;
        }
        bool assignment =
            (spec->assignment_node_types && cbm_kind_in_set(parent, spec->assignment_node_types)) ||
            kind_in_exact_set(ts_node_type(parent), occurrence->write_nodes);
        if (ctx->language == CBM_LANG_ELIXIR &&
            strcmp(ts_node_type(parent), "binary_operator") == 0) {
            assignment = elixir_binary_operator_binds(ctx, parent);
        }
        if (assignment) {
            if (assignment_reads_target(parent)) {
                return false;
            }
            if (ctx->language == CBM_LANG_LINKERSCRIPT &&
                strcmp(ts_node_type(parent), "assignment") == 0) {
                /* This grammar's assignment production has no field map. Its
                 * first direct child is the lhs, even when that child is the
                 * anonymous location-counter token `.`. */
                return ts_node_child_count(parent) > 0 &&
                       node_contains(ts_node_child(parent, 0), node);
            }
            TSNode left = ts_node_child_by_field_name(parent, TS_FIELD("left"));
            if (node_contains(left, node) || field_contains_node(parent, "target", node) ||
                field_contains_node(parent, "destination", node)) {
                return true;
            }
            return occurrence->first_named_child_is_write && named_child_contains(parent, 0, node);
        }
        current = parent;
    }
    return false;
}

static bool is_write_occurrence(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                                WalkState *state) {
    const CBMUsageFrame *frame = usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_WRITE);
    if (!frame) {
        return write_climb(ctx, node, spec, begin_occurrence_climb(state, node));
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_WRITE) != 0;
    if (usage_context_checking(state)) {
        state->usage_context.climb_only = true;
        bool climbed = write_climb(ctx, node, spec, begin_occurrence_climb(state, node));
        state->usage_context.climb_only = false;
        usage_context_verify(ctx, state, node, "write", carried, climbed);
    }
    return carried;
}

static bool is_argument_container_kind(const char *kind) {
    return kind && (strcmp(kind, "arguments") == 0 || strcmp(kind, "argument_list") == 0 ||
                    strcmp(kind, "value_arguments") == 0);
}

static bool is_labeled_argument_kind(const char *kind) {
    return kind && (strcmp(kind, "keyword_argument") == 0 || strcmp(kind, "named_argument") == 0 ||
                    strcmp(kind, "labeled_argument") == 0);
}

/* A named/labeled argument's key describes the callee parameter; it is not a
 * value read in the caller. Keep this separate from binding detection: the
 * label must neither emit USAGE nor create a caller-local lexical binding. */
static bool is_call_argument_label(TSNode node) {
    usage_slow_parent_fallback_test_note();
    for (TSNode current = node; !ts_node_is_null(current);) {
        TSNode parent = ts_node_parent(current);
        if (ts_node_is_null(parent)) {
            return false;
        }
        const char *parent_kind = ts_node_type(parent);
        if (is_labeled_argument_kind(parent_kind)) {
            return field_contains_node(parent, "name", node) ||
                   field_contains_node(parent, "label", node) ||
                   field_contains_node(parent, "key", node);
        }
        if (is_argument_container_kind(parent_kind)) {
            return false;
        }
        current = parent;
    }
    return false;
}

/* Carried down as CBM_USAGE_CONTEXT_ARGUMENT_LABEL. Edge fields and kinds only,
 * no containment, so the carried answer holds for empty nodes too. */
static bool call_argument_label_climb(TSNode node, CBMOccurrenceClimb *climb) {
    if (!climb) {
        return is_call_argument_label(node);
    }
    TSNode current = node;
    while (!ts_node_is_null(current)) {
        TSNode parent;
        const char *field;
        if (!occurrence_parent(climb, current, &parent, &field)) {
            return false;
        }
        const char *parent_kind = ts_node_type(parent);
        if (is_labeled_argument_kind(parent_kind)) {
            return field && (strcmp(field, "name") == 0 || strcmp(field, "label") == 0 ||
                             strcmp(field, "key") == 0);
        }
        if (is_argument_container_kind(parent_kind))
            return false;
        current = parent;
    }
    return false;
}

static bool is_call_argument_label_walk(CBMExtractCtx *ctx, TSNode node, WalkState *state) {
    const CBMUsageFrame *frame =
        usage_carried_frame(state, node, true, CBM_USAGE_CONTEXT_ARGUMENT_LABEL);
    if (!frame) {
        return call_argument_label_climb(node, begin_occurrence_climb(state, node));
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_ARGUMENT_LABEL) != 0;
    if (usage_context_checking(state)) {
        state->usage_context.climb_only = true;
        bool climbed = call_argument_label_climb(node, begin_occurrence_climb(state, node));
        state->usage_context.climb_only = false;
        usage_context_verify(ctx, state, node, "argument_label", carried, climbed);
    }
    return carried;
}

static bool is_direct_argument_value(TSNode node) {
    usage_slow_parent_fallback_test_note();
    TSNode parent = ts_node_parent(node);
    if (ts_node_is_null(parent)) {
        return false;
    }
    if (is_labeled_argument_kind(ts_node_type(parent))) {
        TSNode value = ts_node_child_by_field_name(parent, TS_FIELD("value"));
        return !ts_node_is_null(value) && ts_node_eq(value, node) &&
               is_direct_argument_value(parent);
    }
    TSNode direct_arguments = ts_node_child_by_field_name(parent, TS_FIELD("arguments"));
    if (!ts_node_is_null(direct_arguments) && ts_node_eq(direct_arguments, node)) {
        return true;
    }
    if (is_argument_container_kind(ts_node_type(parent))) {
        return true;
    }
    const char *parent_kind = ts_node_type(parent);
    if (strcmp(parent_kind, "list_expression") == 0) {
        TSNode call = ts_node_parent(parent);
        if (!ts_node_is_null(call)) {
            TSNode arguments = ts_node_child_by_field_name(call, TS_FIELD("arguments"));
            return !ts_node_is_null(arguments) && ts_node_eq(arguments, parent);
        }
        return false;
    }
    if (strcmp(parent_kind, "argument") != 0 && strcmp(parent_kind, "value_argument") != 0) {
        return false;
    }
    TSNode grandparent = ts_node_parent(parent);
    return !ts_node_is_null(grandparent) && is_argument_container_kind(ts_node_type(grandparent));
}

/* The body of the walk above, entered one level in: for a caller that has
 * ALREADY stepped its climb onto `parent` and knows which `field` of it the
 * node below occupies. A caller that climbed to find its site has that pair in
 * hand, and re-deriving it would mean either stepping the climb twice or
 * paying ts_node_parent for what the climb just told us. */
static bool is_direct_argument_value_from(TSNode parent, const char *field,
                                          CBMOccurrenceClimb *climb) {
    for (;;) {
        const char *parent_kind = ts_node_type(parent);
        if (is_labeled_argument_kind(parent_kind)) {
            if (!field || strcmp(field, "value") != 0)
                return false;
            /* The labeled argument now has to be the argument value itself. */
            if (!occurrence_parent(climb, parent, &parent, &field)) {
                return false;
            }
            continue;
        }
        if (field && strcmp(field, "arguments") == 0)
            return true;
        if (is_argument_container_kind(parent_kind))
            return true;
        if (strcmp(parent_kind, "list_expression") == 0) {
            TSNode call;
            const char *list_field;
            return occurrence_parent(climb, parent, &call, &list_field) && list_field &&
                   strcmp(list_field, "arguments") == 0;
        }
        if (strcmp(parent_kind, "argument") != 0 && strcmp(parent_kind, "value_argument") != 0) {
            return false;
        }
        TSNode grandparent;
        const char *argument_field;
        return occurrence_parent(climb, parent, &grandparent, &argument_field) &&
               is_argument_container_kind(ts_node_type(grandparent));
    }
}

/* Climb-backed counterpart for the unified walker. `climb` must currently
 * stand at `node`; it is consumed while walking toward the argument owner. */
static bool is_direct_argument_value_climb(TSNode node, CBMOccurrenceClimb *climb) {
    TSNode parent;
    const char *field;
    if (!occurrence_parent(climb, node, &parent, &field)) {
        return false;
    }
    return is_direct_argument_value_from(parent, field, climb);
}

static bool is_direct_argument_value_walk(TSNode node, WalkState *state) {
    CBMOccurrenceClimb *climb = begin_occurrence_climb(state, node);
    return climb ? is_direct_argument_value_climb(node, climb) : is_direct_argument_value(node);
}

/* The parenthesized_expression holds exactly `site`: in its expression field,
 * or as its only named child where the grammar gives no field. */
static bool python_parentheses_wrap(TSNode parenthesized, TSNode site) {
    TSNode inner = ts_node_child_by_field_name(parenthesized, TS_FIELD("expression"));
    if (ts_node_is_null(inner) && ts_node_named_child_count(parenthesized) == SKIP_ONE) {
        inner = ts_node_named_child(parenthesized, 0);
    }
    return !ts_node_is_null(inner) && ts_node_eq(inner, site);
}

static TSNode python_direct_callable_attribute_site(TSNode node) {
    usage_slow_parent_fallback_test_note();
    if (ts_node_is_null(node) || strcmp(ts_node_type(node), "attribute") != 0) {
        return (TSNode){0};
    }
    TSNode site = node;
    TSNode parent = ts_node_parent(site);
    while (!ts_node_is_null(parent) &&
           strcmp(ts_node_type(parent), "parenthesized_expression") == 0) {
        if (!python_parentheses_wrap(parent, site)) {
            return (TSNode){0};
        }
        site = parent;
        parent = ts_node_parent(site);
    }
    return is_direct_argument_value(site) ? site : (TSNode){0};
}

/* The same site walk on a climb over the frames that stands at the attribute
 * `node`. The ts_node_parent version pays a root descent per step, and every
 * attribute of a chain `a.b.b...` asks: O(depth) per node, quadratic overall. */
static TSNode python_direct_callable_attribute_site_climb(TSNode node, CBMOccurrenceClimb *climb) {
    if (strcmp(ts_node_type(node), "attribute") != 0) {
        return (TSNode){0};
    }
    TSNode site = node;
    TSNode parent;
    const char *field;
    if (!occurrence_parent(climb, site, &parent, &field)) {
        return (TSNode){0};
    }
    while (strcmp(ts_node_type(parent), "parenthesized_expression") == 0) {
        if (!python_parentheses_wrap(parent, site)) {
            return (TSNode){0};
        }
        site = parent;
        if (!occurrence_parent(climb, site, &parent, &field)) {
            return (TSNode){0};
        }
    }
    return is_direct_argument_value_from(parent, field, climb) ? site : (TSNode){0};
}

/* The site walk from the attribute a climb has just stepped onto. */
static TSNode python_direct_callable_attribute_site_from(TSNode attribute,
                                                         CBMOccurrenceClimb *climb) {
    /* An empty attribute and a climb on a cursor copy take the old walk. */
    return climb && climb->frames && ts_node_start_byte(attribute) < ts_node_end_byte(attribute)
               ? python_direct_callable_attribute_site_climb(attribute, climb)
               : python_direct_callable_attribute_site(attribute);
}

/* python_direct_callable_attribute_site for the walk's current node. */
static TSNode python_attribute_site_walk(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    if (!usage_ancestry_frame(state, node)) {
        return python_direct_callable_attribute_site(node);
    }
    TSNode site =
        python_direct_callable_attribute_site_climb(node, begin_occurrence_climb(state, node));
    if (usage_context_checking(state)) {
        TSNode climbed = python_direct_callable_attribute_site(node);
        usage_context_report(ctx, state, node, "python_attribute_site", ts_node_eq(site, climbed),
                             ts_node_start_byte(site), ts_node_start_byte(climbed));
    }
    return site;
}

static bool language_may_stamp_exact_callable_value_candidate(CBMLanguage language) {
    switch (language) {
    case CBM_LANG_JAVASCRIPT:
    case CBM_LANG_TYPESCRIPT:
    case CBM_LANG_TSX:
    case CBM_LANG_ARKTS:
    case CBM_LANG_GO:
    case CBM_LANG_PYTHON:
    case CBM_LANG_C:
    case CBM_LANG_CPP:
    case CBM_LANG_CUDA:
    case CBM_LANG_RUST:
    case CBM_LANG_CSHARP:
    case CBM_LANG_KOTLIN:
        return true;
    default:
        return false;
    }
}

/* Direct identifiers and direct, statically-named TS member values passed as
 * arguments are narrow syntactic candidates only. A language LSP must still
 * prove one target at this exact occurrence before the graph upgrades USAGE to
 * CALL_REFERENCE; unresolved, reassigned, and composite expressions stay USAGE. */
/* One step up from `site`, on the caller's climb when it has one. Every
 * other language branch in call_reference_candidate_site climbs this way; C#
 * used ts_node_parent, which tree-sitter answers by descending from the ROOT,
 * so each step costs O(depth) with a child scan at every level. On the
 * generated .NET JIT tests — single expressions megabytes deep — that was
 * 18-48 us per visited node and ~85% of the whole unified walk (sampled
 * 2026-09-19: stamp_usage_site -> ts_node_parent ->
 * ts_node_child_with_descendant). Those files are also the ones the old CPU
 * deadline used to cut off mid-walk, so the slow path and the nondeterminism
 * it forced were the same defect seen from two ends. */
static bool csharp_site_parent(CBMOccurrenceClimb *climb, TSNode site, TSNode *parent,
                               const char **field) {
    if (!climb) {
        usage_slow_parent_fallback_test_note();
    }
    return occurrence_parent(climb, site, parent, field);
}

static TSNode csharp_callable_value_site(TSNode node, TSNode parent, const char *parent_field,
                                         CBMOccurrenceClimb *climb) {
    const char *kind = ts_node_type(node);
    if (strcmp(kind, "identifier") != 0 && strcmp(kind, "simple_identifier") != 0) {
        return (TSNode){0};
    }

    /* The caller has already resolved node's parent (and the field it occupies)
     * on its climb, so the climb starts from that pair instead of asking for
     * it again. Invariant below: `parent`/`field` always describe `site`. */
    TSNode site = node;
    const char *field = parent_field;
    if (!ts_node_is_null(parent) && strcmp(ts_node_type(parent), "generic_name") == 0) {
        TSNode name = ts_node_child_by_field_name(parent, TS_FIELD("name"));
        if (ts_node_is_null(name) && ts_node_named_child_count(parent) > 0) {
            name = ts_node_named_child(parent, 0);
        }
        if (ts_node_is_null(name) || !ts_node_eq(name, node)) {
            return (TSNode){0};
        }
        site = parent;
        if (!csharp_site_parent(climb, site, &parent, &field)) {
            return (TSNode){0};
        }
    }

    if (!ts_node_is_null(parent) && strcmp(ts_node_type(parent), "member_access_expression") == 0) {
        TSNode member = ts_node_child_by_field_name(parent, TS_FIELD("name"));
        if (ts_node_is_null(member) || !ts_node_eq(member, site)) {
            return (TSNode){0};
        }
        site = parent;
        if (!csharp_site_parent(climb, site, &parent, &field)) {
            return (TSNode){0};
        }
    }

    while (!ts_node_is_null(parent) &&
           strcmp(ts_node_type(parent), "parenthesized_expression") == 0) {
        TSNode inner = ts_node_child_by_field_name(parent, TS_FIELD("expression"));
        if (ts_node_is_null(inner) && ts_node_named_child_count(parent) == 1) {
            inner = ts_node_named_child(parent, 0);
        }
        if (ts_node_is_null(inner) || !ts_node_eq(inner, site)) {
            return (TSNode){0};
        }
        site = parent;
        if (!csharp_site_parent(climb, site, &parent, &field)) {
            return (TSNode){0};
        }
    }

    /* The wrapper chain proves admission, but the semantic row is keyed to the
     * terminal method-name identifier. Keep the raw carrier on that leaf. */
    if (ts_node_is_null(parent)) {
        return (TSNode){0};
    }
    return is_direct_argument_value_from(parent, field, climb) ? node : (TSNode){0};
}

/* Climb out of the parentheses wrapping a direct argument and return the
 * outermost wrapper, or null when the node is not a parenthesised direct
 * argument. Mirrors python_direct_callable_attribute_site so the bare
 * identifier and bound method forms agree on one occurrence. */
static TSNode paren_wrapped_direct_argument_site(TSNode node, TSNode parent,
                                                 CBMOccurrenceClimb *climb, WalkState *state) {
    /* The caller already resolved `parent`; checking its kind first keeps the
     * common case (an identifier that is not parenthesised at all) free of any
     * extra parent resolution. Walking up with ts_node_parent here instead
     * costs one slow fallback per identifier in the file, which the linearity
     * guard in test_extraction.c rightly rejects. */
    if (ts_node_is_null(parent) || strcmp(ts_node_type(parent), "parenthesized_expression") != 0) {
        return (TSNode){0};
    }
    TSNode site = node;
    TSNode wrapper = parent;
    for (int depth = 0; depth < 64; depth++) {
        TSNode inner = ts_node_child_by_field_name(wrapper, TS_FIELD("expression"));
        if (ts_node_is_null(inner) && ts_node_named_child_count(wrapper) == 1) {
            inner = ts_node_named_child(wrapper, 0);
        }
        if (ts_node_is_null(inner) || !ts_node_eq(inner, site)) {
            return (TSNode){0};
        }
        site = wrapper;
        TSNode next = {0};
        const char *field = NULL;
        if (climb) {
            if (!occurrence_parent(climb, site, &next, &field)) {
                next = (TSNode){0};
            }
        } else {
            usage_slow_parent_fallback_test_note();
            next = ts_node_parent(site);
        }
        if (ts_node_is_null(next) || strcmp(ts_node_type(next), "parenthesized_expression") != 0) {
            break;
        }
        wrapper = next;
    }
    return is_direct_argument_value_walk(site, state) ? site : (TSNode){0};
}

static TSNode call_reference_candidate_site(CBMExtractCtx *ctx, TSNode node, const char *name,
                                            WalkState *state) {
    if (!ctx || !name || !language_may_stamp_exact_callable_value_candidate(ctx->language)) {
        return (TSNode){0};
    }
    const char *kind = ts_node_type(node);
    CBMOccurrenceClimb *climb = begin_occurrence_climb(state, node);
    TSNode parent = {0};
    const char *parent_field = NULL;
    if (!climb) {
        usage_slow_parent_fallback_test_note();
    }
    /* Resolve the parent AND the field node occupies in it, on both paths. The
     * C# site walk below carries that field into the argument test, and
     * ts_node_parent on its own would leave it NULL there — silently losing the
     * "this node IS the arguments" case whenever no climb is available. */
    (void)occurrence_parent(climb, node, &parent, &parent_field);
    bool ts_family = ctx->language == CBM_LANG_JAVASCRIPT || ctx->language == CBM_LANG_TYPESCRIPT ||
                     ctx->language == CBM_LANG_TSX || ctx->language == CBM_LANG_ARKTS;
    if (ts_family && strcmp(kind, "property_identifier") == 0 && !ts_node_is_null(parent) &&
        strcmp(ts_node_type(parent), "member_expression") == 0) {
        TSNode property = ts_node_child_by_field_name(parent, TS_FIELD("property"));
        TSNode arguments = {0};
        const char *member_field = NULL;
        if (climb) {
            (void)occurrence_parent(climb, parent, &arguments, &member_field);
        } else {
            usage_slow_parent_fallback_test_note();
            arguments = ts_node_parent(parent);
        }
        return !ts_node_is_null(property) && ts_node_eq(property, node) &&
                       !ts_node_is_null(arguments) &&
                       strcmp(ts_node_type(arguments), "arguments") == 0
                   ? node
                   : (TSNode){0};
    }
    if (ctx->language == CBM_LANG_PYTHON && strcmp(kind, "identifier") == 0 &&
        !ts_node_is_null(parent) && strcmp(ts_node_type(parent), "attribute") == 0) {
        TSNode attribute = ts_node_child_by_field_name(parent, TS_FIELD("attribute"));
        return !ts_node_is_null(attribute) && ts_node_eq(attribute, node)
                   ? python_direct_callable_attribute_site_from(parent, climb)
                   : (TSNode){0};
    }
    if (ctx->language == CBM_LANG_GO && strcmp(kind, "field_identifier") == 0 &&
        !ts_node_is_null(parent) && strcmp(ts_node_type(parent), "selector_expression") == 0) {
        TSNode field = ts_node_child_by_field_name(parent, TS_FIELD("field"));
        return !ts_node_is_null(field) && ts_node_eq(field, node) &&
                       (climb ? is_direct_argument_value_climb(parent, climb)
                              : is_direct_argument_value(parent))
                   ? parent
                   : (TSNode){0};
    }
    if (ctx->language == CBM_LANG_RUST && strcmp(kind, "scoped_identifier") == 0) {
        return is_direct_argument_value_walk(node, state) ? node : (TSNode){0};
    }
    if (ctx->language == CBM_LANG_CSHARP) {
        return csharp_callable_value_site(node, parent, parent_field, climb);
    }
    if (strcmp(kind, "identifier") != 0 && strcmp(kind, "simple_identifier") != 0) {
        return (TSNode){0};
    }
    /* Kotlin: a navigation member read (`obj.member`, and `value::member`,
     * which the vendored grammar also parses as navigation) is a candidate at
     * the member occurrence, so a receiver-typed LSP row can claim it instead
     * of the name-only registry fallback (maintainer decision, option B). With
     * no row at the occurrence the join finds nothing and behavior is exactly
     * as before. */
    if (ctx->language == CBM_LANG_KOTLIN && !ts_node_is_null(parent) &&
        strcmp(ts_node_type(parent), "navigation_suffix") == 0) {
        return node;
    }
    /* Python: the right-hand side of `callback = handler` is a genuine value
     * occurrence of handler, and when the LSP proves its exact callable
     * identity it becomes a CALL_REFERENCE like any proven argument value
     * (maintainer decision on the local-alias fixture). Bare identifier RHS
     * only, in lockstep with the row py_lsp.c emits -- a candidate the LSP
     * never matches would change nothing, but the asymmetry would be a trap. */
    if (ctx->language == CBM_LANG_PYTHON && !ts_node_is_null(parent) &&
        strcmp(ts_node_type(parent), "assignment") == 0) {
        TSNode right = ts_node_child_by_field_name(parent, TS_FIELD("right"));
        return !ts_node_is_null(right) && ts_node_eq(right, node) ? node : (TSNode){0};
    }
    if (is_direct_argument_value_walk(node, state)) {
        return node;
    }
    /* `f((handler))` passes handler just as directly as `f(handler)`. The
     * semantic row is recorded on the outermost parenthesised wrapper -- the
     * site python_direct_callable_attribute_site already returns for the bound
     * method form -- so climb to that same wrapper here. A bare identifier
     * previously stopped at the parentheses and became no candidate at all, so
     * the occurrence-exact join had nothing to join and a parenthesised
     * callable argument produced no reference. */
    return paren_wrapped_direct_argument_site(node, parent, climb, state);
}

static char *reference_name(CBMExtractCtx *ctx, TSNode node) {
    char *name = cbm_node_text(ctx->arena, node, ctx->source);
    if (!name || ctx->language != CBM_LANG_MAKEFILE ||
        strcmp(ts_node_type(node), "variable_reference") != 0) {
        return name;
    }

    /* Make exposes `$(watched)` as one named reference node.
     * Normalize only that grammar wrapper; the recorded site still spans the
     * exact source occurrence for occurrence-sensitive resolution. */
    size_t length = strlen(name);
    bool parenthesized = length > 3 && name[0] == '$' && name[1] == '(' && name[length - 1] == ')';
    return parenthesized ? cbm_arena_strndup(ctx->arena, name + 2, length - 3) : name;
}

static bool lexical_identifier_case_insensitive(CBMLanguage language) {
    switch (language) {
    case CBM_LANG_POWERSHELL:
    case CBM_LANG_FORTRAN:
    case CBM_LANG_ADA:
    case CBM_LANG_PASCAL:
    case CBM_LANG_COBOL:
    case CBM_LANG_VHDL:
        return true;
    default:
        return false;
    }
}

static const char *lexical_binding_key(CBMExtractCtx *ctx, WalkState *state, const char *name) {
    if (!ctx || !name) {
        return name;
    }
    /* Preserve language namespaces: Perl sigils and Vim prefixes distinguish
     * different variables. Tcl's grammar is asymmetric (`name` versus
     * `$name`), so unwrap only that language-defined reference sigil. */
    if (ctx->language == CBM_LANG_TCL && name[0] == '$') {
        name++;
    }
    if (!lexical_identifier_case_insensitive(ctx->language)) {
        return name;
    }
    size_t n = strlen(name);
    char *folded = (char *)cbm_arena_alloc(ctx->arena, n + 1U);
    if (!folded) {
        if (state) {
            state->lexical_binding_tracking_failed = true;
        }
        return NULL;
    }
    for (size_t i = 0; i < n; i++) {
        folded[i] = (char)tolower((unsigned char)name[i]);
    }
    folded[n] = '\0';
    return folded;
}

static void stamp_usage_site(CBMExtractCtx *ctx, CBMUsage *usage, TSNode node, const char *name,
                             WalkState *state) {
    TSNode candidate_site = call_reference_candidate_site(ctx, node, name, state);
    if (usage_context_checking(state) && usage_frame_for(state, node)) {
        /* The site walk stepped the frames; the reference copies the cursor. */
        state->usage_context.climb_only = true;
        TSNode climbed = call_reference_candidate_site(ctx, node, name, state);
        state->usage_context.climb_only = false;
        usage_context_report(ctx, state, node, "call_reference_site",
                             ts_node_eq(candidate_site, climbed) ||
                                 (ts_node_is_null(candidate_site) && ts_node_is_null(climbed)),
                             ts_node_start_byte(candidate_site), ts_node_start_byte(climbed));
    }
    TSNode site = ts_node_is_null(candidate_site) ? node : candidate_site;
    usage->site_start_byte = ts_node_start_byte(site);
    usage->site_end_byte = ts_node_end_byte(site);
    usage->may_be_call_reference = !ts_node_is_null(candidate_site);
}

static const CBMLexicalScope *usage_lexical_scope(const WalkState *state, uint32_t id) {
    return state && id > 0 && id <= (uint32_t)state->lexical_scope_count
               ? &state->lexical_scopes[id - 1U]
               : NULL;
}

static uint32_t active_lexical_scope_id(const WalkState *state) {
    if (!state) {
        return 0;
    }
    uint32_t id = state->scope_top > 0
                      ? state->scopes[state->scope_top - SKIP_ONE].active_lexical_scope_id
                      : 0;
    return id ? id : state->root_lexical_scope_id;
}

static uint32_t lexical_ancestor_of_kind(const WalkState *state, uint32_t start_id,
                                         bool want_function, bool want_block);

/* Carried down as CBM_USAGE_CONTEXT_PY_DEFAULT_VALUE. */
static bool python_default_value_climb(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        const char *kind = ts_node_type(parent);
        /* A nested executable scope inside the default owns its own lookups;
         * only a direct default expression is evaluated in the declaring
         * function's structural parent namespace. */
        if (strcmp(kind, "lambda") == 0 || strcmp(kind, "list_comprehension") == 0 ||
            strcmp(kind, "set_comprehension") == 0 ||
            strcmp(kind, "dictionary_comprehension") == 0 ||
            strcmp(kind, "generator_expression") == 0) {
            return false;
        }
        if ((strcmp(kind, "default_parameter") == 0 ||
             strcmp(kind, "typed_default_parameter") == 0) &&
            (field_contains_node(parent, "value", node) ||
             field_contains_node(parent, "default", node))) {
            return true;
        }
    }
    return false;
}

static bool python_default_value_reference(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    const CBMUsageFrame *frame =
        usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_PY_DEFAULT_VALUE);
    if (!frame) {
        return python_default_value_climb(node);
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_PY_DEFAULT_VALUE) != 0;
    if (usage_context_checking(state)) {
        bool climbed = python_default_value_climb(node);
        usage_context_verify(ctx, state, node, "python_default_value", carried, climbed);
    }
    return carried;
}

static uint32_t usage_lexical_scope_id_for_node(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    uint32_t scope_id = active_lexical_scope_id(state);
    if (!ctx || ctx->language != CBM_LANG_PYTHON ||
        !python_default_value_reference(ctx, state, node)) {
        return scope_id;
    }
    uint32_t function_id = lexical_ancestor_of_kind(state, scope_id, true, false);
    const CBMLexicalScope *function_scope = usage_lexical_scope(state, function_id);
    /* Method bodies intentionally skip their class lookup parent, but Python
     * evaluates the method's default expressions while the class namespace is
     * executing. Use structural ownership here, not body lookup ownership. */
    return function_scope ? function_scope->parent_id : scope_id;
}

static uint32_t lexical_ancestor_of_kind(const WalkState *state, uint32_t start_id,
                                         bool want_function, bool want_block) {
    uint32_t id = start_id;
    int remaining = state ? state->lexical_scope_count : 0;
    while (id != 0 && remaining-- > 0) {
        const CBMLexicalScope *scope = usage_lexical_scope(state, id);
        if (!scope) {
            return 0;
        }
        bool function_scope = scope->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
                              scope->kind == CBM_LEXICAL_SCOPE_COMPREHENSION;
        bool block_scope = scope->kind == CBM_LEXICAL_SCOPE_BLOCK;
        if ((want_function && function_scope) || (want_block && block_scope)) {
            return id;
        }
        id = scope->parent_id;
    }
    return 0;
}

static uint32_t python_nearest_namespace(const WalkState *state, uint32_t start_id) {
    uint32_t id = start_id;
    int remaining = state ? state->lexical_scope_count : 0;
    while (id != 0 && remaining-- > 0) {
        const CBMLexicalScope *scope = usage_lexical_scope(state, id);
        if (!scope) {
            return 0;
        }
        if (scope->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
            scope->kind == CBM_LEXICAL_SCOPE_COMPREHENSION ||
            scope->kind == CBM_LEXICAL_SCOPE_CLASS || scope->kind == CBM_LEXICAL_SCOPE_MODULE) {
            return id;
        }
        id = scope->parent_id;
    }
    return 0;
}

static bool ensure_lexical_binding_capacity(WalkState *state) {
    if (!state->lexical_bindings) {
        state->lexical_bindings = state->inline_lexical_bindings;
        state->lexical_binding_capacity = INLINE_LEXICAL_BINDINGS;
        memset(state->inline_lexical_bindings, 0, sizeof(state->inline_lexical_bindings));
    }
    if (state->lexical_binding_count < state->lexical_binding_capacity) {
        return true;
    }
    if (state->lexical_binding_capacity > INT32_MAX / PAIR_LEN) {
        state->lexical_binding_tracking_failed = true;
        return false;
    }
    int new_capacity = state->lexical_binding_capacity * PAIR_LEN;
    CBMLexicalBinding *grown =
        (CBMLexicalBinding *)cbm_arena_alloc(state->arena, (size_t)new_capacity * sizeof(*grown));
    if (!grown) {
        state->lexical_binding_tracking_failed = true;
        return false;
    }
    memcpy(grown, state->lexical_bindings, (size_t)state->lexical_binding_count * sizeof(*grown));
    state->lexical_bindings = grown;
    state->lexical_binding_capacity = new_capacity;
    return true;
}

static bool lexical_ancestor_kind(TSNode node, const char *kind) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (strcmp(ts_node_type(parent), kind) == 0) {
            return true;
        }
    }
    return false;
}

/* Python `global` / `nonlocal` directive membership, carried down as
 * CBM_USAGE_CONTEXT_IN_GLOBAL / _IN_NONLOCAL. */
static bool python_directive_ancestor(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                      bool global) {
    const char *kind = global ? "global_statement" : "nonlocal_statement";
    uint32_t bit = global ? CBM_USAGE_CONTEXT_IN_GLOBAL : CBM_USAGE_CONTEXT_IN_NONLOCAL;
    const CBMUsageFrame *frame = usage_carried_frame(state, node, false, bit);
    if (!frame) {
        return lexical_ancestor_kind(node, kind);
    }
    bool carried = (frame->context & bit) != 0;
    if (usage_context_checking(state)) {
        bool climbed = lexical_ancestor_kind(node, kind);
        usage_context_verify(ctx, state, node, kind, carried, climbed);
    }
    return carried;
}

static TSNode declared_function_name_owner(TSNode node, const CBMLangSpec *spec) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (spec->function_node_types && cbm_kind_in_set(parent, spec->function_node_types)) {
            return field_contains_node(parent, "name", node) ? parent : (TSNode){0};
        }
    }
    return (TSNode){0};
}

static TSNode declared_class_name_owner(TSNode node, const CBMLangSpec *spec) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (spec->class_node_types && cbm_kind_in_set(parent, spec->class_node_types)) {
            return field_contains_node(parent, "name", node) ? parent : (TSNode){0};
        }
    }
    return (TSNode){0};
}

/* Is `node` the name its nearest function (or class) ancestor declares? The
 * walk carries CBM_USAGE_CONTEXT_FUNCTION_NAME / _CLASS_NAME; the owner node
 * itself is never needed, only whether there is one. */
static bool declares_owner_name(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                const CBMLangSpec *spec, bool function) {
    uint32_t bit = function ? CBM_USAGE_CONTEXT_FUNCTION_NAME : CBM_USAGE_CONTEXT_CLASS_NAME;
    const CBMUsageFrame *frame = usage_carried_frame(state, node, false, bit);
    if (!frame) {
        return !ts_node_is_null(function ? declared_function_name_owner(node, spec)
                                         : declared_class_name_owner(node, spec));
    }
    bool carried = (frame->context & bit) != 0;
    if (usage_context_checking(state)) {
        bool climbed = !ts_node_is_null(function ? declared_function_name_owner(node, spec)
                                                 : declared_class_name_owner(node, spec));
        usage_context_verify(ctx, state, node, function ? "function_name" : "class_name", carried,
                             climbed);
    }
    return carried;
}

static bool ensure_python_directive_capacity(WalkState *state) {
    if (!state->python_directives) {
        state->python_directives = state->inline_python_directives;
        state->python_directive_capacity = INLINE_PYTHON_DIRECTIVES;
        memset(state->inline_python_directives, 0, sizeof(state->inline_python_directives));
    }
    if (state->python_directive_count < state->python_directive_capacity) {
        return true;
    }
    if (state->python_directive_capacity > INT32_MAX / PAIR_LEN) {
        state->lexical_binding_tracking_failed = true;
        return false;
    }
    int new_capacity = state->python_directive_capacity * PAIR_LEN;
    CBMPythonDirective *grown =
        (CBMPythonDirective *)cbm_arena_alloc(state->arena, (size_t)new_capacity * sizeof(*grown));
    if (!grown) {
        state->lexical_binding_tracking_failed = true;
        return false;
    }
    memcpy(grown, state->python_directives, (size_t)state->python_directive_count * sizeof(*grown));
    state->python_directives = grown;
    state->python_directive_capacity = new_capacity;
    return true;
}

static void record_python_directive(WalkState *state, uint32_t function_scope_id, const char *name,
                                    CBMPythonDirectiveKind kind) {
    if (!function_scope_id || !name || !ensure_python_directive_capacity(state)) {
        return;
    }
    for (int i = 0; i < state->python_directive_count; i++) {
        CBMPythonDirective *directive = &state->python_directives[i];
        if (directive->function_scope_id == function_scope_id &&
            strcmp(directive->name, name) == 0) {
            directive->kind = (uint8_t)kind;
            return;
        }
    }
    CBMPythonDirective *directive = &state->python_directives[state->python_directive_count++];
    directive->function_scope_id = function_scope_id;
    directive->name = name;
    directive->kind = (uint8_t)kind;
}

static CBMPythonDirectiveKind python_directive_for(const WalkState *state,
                                                   uint32_t function_scope_id, const char *name) {
    for (int i = state ? state->python_directive_count - 1 : -1; i >= 0; i--) {
        const CBMPythonDirective *directive = &state->python_directives[i];
        if (directive->function_scope_id == function_scope_id && directive->name &&
            strcmp(directive->name, name) == 0) {
            return (CBMPythonDirectiveKind)directive->kind;
        }
    }
    return 0;
}

static uint32_t python_enclosing_function_namespace(const WalkState *state,
                                                    uint32_t inner_function_id) {
    const CBMLexicalScope *inner = usage_lexical_scope(state, inner_function_id);
    uint32_t id = inner ? inner->parent_id : 0;
    int remaining = state ? state->lexical_scope_count : 0;
    while (id != 0 && remaining-- > 0) {
        const CBMLexicalScope *scope = usage_lexical_scope(state, id);
        if (!scope) {
            return 0;
        }
        if (scope->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
            scope->kind == CBM_LEXICAL_SCOPE_COMPREHENSION) {
            return id;
        }
        id = scope->parent_id;
    }
    return 0;
}

/* Carried down as CBM_USAGE_CONTEXT_PARAMETER. */
static bool binding_is_parameter_climb(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec) {
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        const char *kind = ts_node_type(parent);
        if (kind_in_exact_set(kind, common_whole_binding_nodes) ||
            kind_in_exact_set(kind, occurrence->whole_binding_nodes)) {
            return true;
        }
        if (spec->function_node_types && cbm_kind_in_set(parent, spec->function_node_types)) {
            return field_contains_node(parent, "parameter", node) ||
                   field_contains_node(parent, "parameters", node);
        }
    }
    return false;
}

static bool binding_is_parameter(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                 const CBMLangSpec *spec) {
    const CBMUsageFrame *frame =
        usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_PARAMETER);
    if (!frame) {
        return binding_is_parameter_climb(ctx, node, spec);
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_PARAMETER) != 0;
    if (usage_context_checking(state)) {
        bool climbed = binding_is_parameter_climb(ctx, node, spec);
        usage_context_verify(ctx, state, node, "parameter", carried, climbed);
    }
    return carried;
}

/* Carried down as CBM_USAGE_CONTEXT_JS_VAR. */
static bool js_var_binding_climb(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        const char *kind = ts_node_type(parent);
        if (strcmp(kind, "variable_declaration") == 0) {
            return true;
        }
        if (strcmp(kind, "lexical_declaration") == 0) {
            return false;
        }
    }
    return false;
}

static bool js_var_binding(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    const CBMUsageFrame *frame = usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_JS_VAR);
    if (!frame) {
        return js_var_binding_climb(node);
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_JS_VAR) != 0;
    if (usage_context_checking(state)) {
        bool climbed = js_var_binding_climb(node);
        usage_context_verify(ctx, state, node, "js_var", carried, climbed);
    }
    return carried;
}

static bool import_kind_matches(TSNode node, const CBMLangSpec *spec) {
    return (spec->import_node_types && cbm_kind_in_set(node, spec->import_node_types)) ||
           (spec->import_from_types && cbm_kind_in_set(node, spec->import_from_types));
}

static TSNode nearest_import_ancestor(TSNode node, const CBMLangSpec *spec) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (import_kind_matches(parent, spec)) {
            return parent;
        }
    }
    return (TSNode){0};
}

static TSNode first_named_leaf(TSNode node) {
    while (!ts_node_is_null(node) && ts_node_named_child_count(node) > 0) {
        node = ts_node_named_child(node, 0);
    }
    return node;
}

static bool import_alias_contains(TSNode node, TSNode boundary) {
    for (TSNode parent = ts_node_parent(node);
         !ts_node_is_null(parent) && !ts_node_eq(parent, boundary);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (field_contains_node(parent, "alias", node)) {
            return true;
        }
    }
    return false;
}

static bool rust_use_list_has_direct_self(TSNode list) {
    uint32_t count = ts_node_named_child_count(list);
    for (uint32_t i = 0; i < count; i++) {
        if (strcmp(ts_node_type(ts_node_named_child(list, i)), "self") == 0) {
            return true;
        }
    }
    return false;
}

/* The rules below the import statement `boundary` once no alias field between
 * them contains node. `ancestors` walks up from node. */
static bool import_binding_below(CBMExtractCtx *ctx, TSNode node, TSNode boundary,
                                 CBMUsageAncestors ancestors) {
    switch (ctx->language) {
    case CBM_LANG_PYTHON: {
        const char *boundary_kind = ts_node_type(boundary);
        if (strcmp(boundary_kind, "future_import_statement") == 0) {
            return false;
        }
        CBMUsageAncestors scan = ancestors;
        for (TSNode parent = usage_ancestors_next(&scan, node);
             !ts_node_is_null(parent) && !ts_node_eq(parent, boundary);
             parent = usage_ancestors_next(&scan, parent)) {
            /* In an aliased import, only the alias binds. */
            if (strcmp(ts_node_type(parent), "aliased_import") == 0) {
                return false;
            }
        }
        bool from_import = strcmp(boundary_kind, "import_from_statement") == 0;
        if (from_import) {
            if (field_contains_node(boundary, "module_name", node) ||
                field_contains_node(boundary, "module", node)) {
                return false;
            }
            /* Older Python grammar variants omit the module field. Their first
             * named child is still the source module, never a local binding. */
            if (ts_node_named_child_count(boundary) > 1 &&
                node_contains(ts_node_named_child(boundary, 0), node)) {
                return false;
            }
            return strcmp(ts_node_type(node), "identifier") == 0;
        }

        TSNode entry = node;
        CBMUsageAncestors up = ancestors;
        TSNode parent = usage_ancestors_next(&up, entry);
        while (!ts_node_is_null(parent) && !ts_node_eq(parent, boundary)) {
            entry = parent;
            parent = usage_ancestors_next(&up, parent);
        }
        TSNode first = first_named_leaf(entry);
        return !ts_node_is_null(first) && ts_node_eq(first, node);
    }
    case CBM_LANG_JAVASCRIPT:
    case CBM_LANG_TYPESCRIPT:
    case CBM_LANG_TSX:
    case CBM_LANG_ARKTS: {
        if (strcmp(ts_node_type(boundary), "import_statement") != 0) {
            return false;
        }
        CBMUsageAncestors scan = ancestors;
        for (TSNode parent = usage_ancestors_next(&scan, node);
             !ts_node_is_null(parent) && !ts_node_eq(parent, boundary);
             parent = usage_ancestors_next(&scan, parent)) {
            const char *kind = ts_node_type(parent);
            if (strcmp(kind, "import_specifier") == 0) {
                TSNode alias = ts_node_child_by_field_name(parent, TS_FIELD("alias"));
                if (!ts_node_is_null(alias)) {
                    return false;
                }
                return field_contains_node(parent, "name", node) ||
                       ts_node_eq(first_named_leaf(parent), node);
            }
            if (strcmp(kind, "namespace_import") == 0) {
                return field_contains_node(parent, "name", node) ||
                       ts_node_eq(first_named_leaf(parent), node);
            }
            if (strcmp(kind, "import_clause") == 0) {
                /* A direct identifier is the default import. Named and
                 * namespace imports were handled by their inner containers. */
                return ts_node_eq(first_named_leaf(parent), node);
            }
            if (strcmp(kind, "import_require_clause") == 0) {
                /* TypeScript `import local = require("module")` and
                 * `import local = Namespace.member` put the binding first.
                 * Current grammar variants expose only the source field, so
                 * retain the first-leaf fallback as the exact role check. */
                return field_contains_node(parent, "name", node) ||
                       ts_node_eq(first_named_leaf(parent), node);
            }
        }
        return false;
    }
    case CBM_LANG_RUST: {
        TSNode boundary_alias = ts_node_child_by_field_name(boundary, TS_FIELD("alias"));
        if (!ts_node_is_null(boundary_alias) && field_contains_node(boundary, "name", node)) {
            /* `extern crate source as local` binds only local. */
            return false;
        }
        bool terminal = false;
        CBMUsageAncestors scan = ancestors;
        for (TSNode parent = usage_ancestors_next(&scan, node);
             !ts_node_is_null(parent) && !ts_node_eq(parent, boundary);
             parent = usage_ancestors_next(&scan, parent)) {
            if (field_contains_node(parent, "path", node)) {
                /* `use foo::{self}` imports the module itself under the final
                 * segment of the prefix (`foo`). An aliased `self as x` is a
                 * use_as_clause child rather than a direct self entry and is
                 * already handled by the alias rule above. */
                if (strcmp(ts_node_type(parent), "scoped_use_list") == 0 &&
                    strcmp(ts_node_type(node), "identifier") == 0) {
                    TSNode path = ts_node_child_by_field_name(parent, TS_FIELD("path"));
                    TSNode list = ts_node_child_by_field_name(parent, TS_FIELD("list"));
                    bool terminal_path = terminal || ts_node_eq(path, node);
                    if (terminal_path && !ts_node_is_null(list) &&
                        rust_use_list_has_direct_self(list)) {
                        return true;
                    }
                }
                return false;
            }
            if (field_contains_node(parent, "name", node)) {
                terminal = true;
            }
        }
        return terminal || strcmp(ts_node_type(node), "identifier") == 0;
    }
    default:
        return false;
    }
}

/* Every rule, climbing from node with ts_node_parent. */
static bool import_binding_climb(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec) {
    TSNode boundary = nearest_import_ancestor(node, spec);
    if (ts_node_is_null(boundary)) {
        return false;
    }
    /* Rust's extern-crate alias is a direct field of the import boundary,
     * unlike the nested alias containers used by Python and ES imports. */
    if (field_contains_node(boundary, "alias", node) || import_alias_contains(node, boundary)) {
        return true;
    }
    return import_binding_below(ctx, node, boundary, (CBMUsageAncestors){NULL, 0});
}

/* Import subtrees are excluded from ordinary usage emission, but their local
 * names still participate in lexical lookup. Keep this classifier narrow: it
 * identifies only the binding side, never a module path or imported source
 * name. The walk keeps the import statement and the alias rule on its frames
 * (CBM_USAGE_NEAREST_IMPORT, CBM_USAGE_CONTEXT_IMPORT_ALIAS); both climbed from
 * every import identifier to the statement, so nested Rust use lists were
 * cubic. The rules below the statement step the frames. */
static bool is_import_binding_occurrence(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                                         WalkState *state) {
    const CBMUsageFrame *frame =
        usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_IMPORT_ALIAS);
    TSNode boundary;
    uint32_t level;
    if (!frame || !usage_nearest(state, node, CBM_USAGE_NEAREST_IMPORT, &boundary, &level)) {
        return import_binding_climb(ctx, node, spec);
    }
    bool carried = !ts_node_is_null(boundary) &&
                   ((frame->context & CBM_USAGE_CONTEXT_IMPORT_ALIAS) != 0 ||
                    import_binding_below(ctx, node, boundary, usage_ancestors(state, node)));
    if (usage_context_checking(state)) {
        usage_context_verify(ctx, state, node, "import_binding", carried,
                             import_binding_climb(ctx, node, spec));
    }
    return carried;
}

static uint32_t lexical_import_scope(const WalkState *state, uint32_t start_id) {
    uint32_t id = start_id;
    int remaining = state ? state->lexical_scope_count : 0;
    while (id != 0 && remaining-- > 0) {
        const CBMLexicalScope *scope = usage_lexical_scope(state, id);
        if (!scope) {
            return 0;
        }
        if (scope->kind == CBM_LEXICAL_SCOPE_MODULE || scope->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
            scope->kind == CBM_LEXICAL_SCOPE_COMPREHENSION ||
            scope->kind == CBM_LEXICAL_SCOPE_BLOCK) {
            return id;
        }
        id = scope->parent_id;
    }
    return 0;
}

static void record_lexical_binding(CBMExtractCtx *ctx, WalkState *state, TSNode node,
                                   const CBMLangSpec *spec, const char *raw_name,
                                   bool import_binding) {
    if (!ctx || !state || !raw_name || !raw_name[0] || state->lexical_binding_tracking_failed) {
        return;
    }
    bool parameter = binding_is_parameter(ctx, state, node, spec);
    if (ctx->language == CBM_LANG_VIMSCRIPT && parameter && !strchr(raw_name, ':')) {
        raw_name = cbm_arena_sprintf(ctx->arena, "a:%s", raw_name);
        if (!raw_name) {
            state->lexical_binding_tracking_failed = true;
            return;
        }
    }
    const char *name = lexical_binding_key(ctx, state, raw_name);
    if (!name || !name[0]) {
        return;
    }

    uint32_t current_id = active_lexical_scope_id(state);
    uint32_t scope_id = 0;
    bool whole_scope = false;
    bool function_declaration = declares_owner_name(ctx, state, node, spec, true);
    bool class_declaration = declares_owner_name(ctx, state, node, spec, false);

    if (ctx->language == CBM_LANG_PYTHON && (python_directive_ancestor(ctx, state, node, true) ||
                                             python_directive_ancestor(ctx, state, node, false))) {
        uint32_t function_id = lexical_ancestor_of_kind(state, current_id, true, false);
        CBMPythonDirectiveKind directive = python_directive_ancestor(ctx, state, node, true)
                                               ? CBM_PYTHON_DIRECTIVE_GLOBAL
                                               : CBM_PYTHON_DIRECTIVE_NONLOCAL;
        record_python_directive(state, function_id, name, directive);
        return;
    }

    if (function_declaration) {
        uint32_t function_id = lexical_ancestor_of_kind(state, current_id, true, false);
        const CBMLexicalScope *function_scope = usage_lexical_scope(state, function_id);
        uint32_t parent_id = function_scope ? function_scope->parent_id : 0;
        if (ctx->language == CBM_LANG_PYTHON) {
            scope_id = python_nearest_namespace(state, parent_id);
            const CBMLexicalScope *owner = usage_lexical_scope(state, scope_id);
            if (!owner || (owner->kind != CBM_LEXICAL_SCOPE_FUNCTION &&
                           owner->kind != CBM_LEXICAL_SCOPE_COMPREHENSION)) {
                return;
            }
        } else {
            scope_id = lexical_ancestor_of_kind(state, parent_id, true, true);
        }
        /* Top-level/class callable declarations are themselves semantic
         * targets, not local-value blockers. Nested declarations still bind
         * their enclosing executable scope and must block raw-name fallback. */
        if (scope_id == 0) {
            return;
        }
        whole_scope = true;
    } else if (ctx->language == CBM_LANG_PYTHON && class_declaration) {
        uint32_t class_id = python_nearest_namespace(state, current_id);
        const CBMLexicalScope *class_scope = usage_lexical_scope(state, class_id);
        scope_id = python_nearest_namespace(state, class_scope ? class_scope->parent_id : 0);
        const CBMLexicalScope *owner = usage_lexical_scope(state, scope_id);
        if (!owner || (owner->kind != CBM_LEXICAL_SCOPE_FUNCTION &&
                       owner->kind != CBM_LEXICAL_SCOPE_COMPREHENSION)) {
            return;
        }
        whole_scope = true;
    } else if (parameter) {
        scope_id = lexical_ancestor_of_kind(state, current_id, true, false);
        whole_scope = true;
    } else if (ctx->language == CBM_LANG_PYTHON) {
        uint32_t namespace_id = python_nearest_namespace(state, current_id);
        const CBMLexicalScope *namespace_scope = usage_lexical_scope(state, namespace_id);
        uint32_t function_id =
            namespace_scope && (namespace_scope->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
                                namespace_scope->kind == CBM_LEXICAL_SCOPE_COMPREHENSION)
                ? namespace_id
                : lexical_ancestor_of_kind(state, current_id, true, false);
        CBMPythonDirectiveKind directive = python_directive_for(state, function_id, name);
        if (directive == CBM_PYTHON_DIRECTIVE_GLOBAL) {
            scope_id = state->root_lexical_scope_id;
        } else if (directive == CBM_PYTHON_DIRECTIVE_NONLOCAL) {
            scope_id = python_enclosing_function_namespace(state, function_id);
        } else {
            scope_id = namespace_id;
        }
        const CBMLexicalScope *owner = usage_lexical_scope(state, scope_id);
        if (!owner) {
            return;
        }
        whole_scope = directive == 0 && (owner->kind == CBM_LEXICAL_SCOPE_FUNCTION ||
                                         owner->kind == CBM_LEXICAL_SCOPE_COMPREHENSION);
    } else if (ctx->language == CBM_LANG_POWERSHELL) {
        scope_id = lexical_ancestor_of_kind(state, current_id, true, false);
        whole_scope = true;
    } else if (ctx->language == CBM_LANG_JAVASCRIPT || ctx->language == CBM_LANG_TYPESCRIPT ||
               ctx->language == CBM_LANG_TSX || ctx->language == CBM_LANG_ARKTS) {
        bool is_var = js_var_binding(ctx, state, node);
        scope_id = lexical_ancestor_of_kind(state, current_id, is_var, !is_var);
        if (scope_id == 0) {
            scope_id = lexical_ancestor_of_kind(state, current_id, true, false);
        }
        if (scope_id == 0) {
            scope_id = state->root_lexical_scope_id;
        }
        whole_scope = true; /* var hoisting and let/const TDZ */
    } else if (ctx->language == CBM_LANG_RUST && import_binding) {
        scope_id = lexical_import_scope(state, current_id);
        if (scope_id == 0) {
            scope_id = state->root_lexical_scope_id;
        }
        /* A Rust use/extern-crate declaration is an item whose name is in
         * scope for the complete containing block or module, independent of
         * textual declaration order. */
        whole_scope = true;
    } else {
        scope_id = lexical_ancestor_of_kind(state, current_id, true, true);
        if (scope_id == 0) {
            scope_id = state->root_lexical_scope_id;
        }
    }
    const CBMLexicalScope *scope = usage_lexical_scope(state, scope_id);
    if (!scope || !ensure_lexical_binding_capacity(state)) {
        return;
    }
    CBMLexicalBinding *binding = &state->lexical_bindings[state->lexical_binding_count++];
    binding->scope_id = scope_id;
    binding->active_start = whole_scope ? scope->start_byte : ts_node_end_byte(node);
    /* Zero means "the finalized end of this concrete scope". Split
     * signature/body languages extend the scope after parameters are seen. */
    binding->active_end = 0;
    binding->name = name;
}

static int compare_lexical_bindings(const void *left_ptr, const void *right_ptr) {
    const CBMLexicalBinding *left = (const CBMLexicalBinding *)left_ptr;
    const CBMLexicalBinding *right = (const CBMLexicalBinding *)right_ptr;
    if (left->scope_id != right->scope_id) {
        return left->scope_id < right->scope_id ? -1 : 1;
    }
    int name_order = strcmp(left->name, right->name);
    if (name_order != 0) {
        return name_order;
    }
    if (left->active_start != right->active_start) {
        return left->active_start < right->active_start ? -1 : 1;
    }
    if (left->active_end != right->active_end) {
        return left->active_end < right->active_end ? -1 : 1;
    }
    return 0;
}

static int compare_binding_key(const CBMLexicalBinding *binding, uint32_t scope_id,
                               const char *name) {
    if (binding->scope_id != scope_id) {
        return binding->scope_id < scope_id ? -1 : 1;
    }
    return strcmp(binding->name, name);
}

static int lexical_binding_lower_bound(const WalkState *state, uint32_t scope_id,
                                       const char *name) {
    int low = 0;
    int high = state->lexical_binding_count;
    while (low < high) {
        int middle = low + (high - low) / PAIR_LEN;
        if (compare_binding_key(&state->lexical_bindings[middle], scope_id, name) < 0) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    return low;
}

static bool lexical_binding_active_at(const WalkState *state, uint32_t scope_id, const char *name,
                                      uint32_t position) {
    const CBMLexicalScope *scope = usage_lexical_scope(state, scope_id);
    if (!scope) {
        return false;
    }
    int index = lexical_binding_lower_bound(state, scope_id, name);
    while (index < state->lexical_binding_count) {
        const CBMLexicalBinding *binding = &state->lexical_bindings[index++];
        if (binding->scope_id != scope_id || strcmp(binding->name, name) != 0) {
            break;
        }
        uint32_t active_end = binding->active_end ? binding->active_end : scope->end_byte;
        if (binding->active_start <= position && position < active_end) {
            return true;
        }
    }
    return false;
}

static const CBMLexicalScope *lexical_binding_scope_for_usage(const WalkState *state,
                                                              const CBMUsage *usage,
                                                              const char *name) {
    uint32_t scope_id = usage->lexical_scope_id;
    int remaining = state ? state->lexical_scope_count : 0;
    while (scope_id != 0 && remaining-- > 0) {
        const CBMLexicalScope *scope = usage_lexical_scope(state, scope_id);
        if (!scope) {
            return NULL;
        }
        if (lexical_binding_active_at(state, scope_id, name, usage->site_start_byte)) {
            return scope;
        }
        scope_id = scope->lookup_parent_id;
    }
    return NULL;
}

void cbm_finalize_lexical_usages(CBMExtractCtx *ctx, WalkState *state) {
    if (!ctx || !state) {
        return;
    }
    if (state->lexical_binding_count > 1) {
        qsort(state->lexical_bindings, (size_t)state->lexical_binding_count,
              sizeof(*state->lexical_bindings), compare_lexical_bindings);
    }
    for (int i = state->usage_start_index; i < ctx->result->usages.count; i++) {
        CBMUsage *usage = &ctx->result->usages.items[i];
        if (!usage->ref_name || !usage->ref_name[0]) {
            continue;
        }
        const char *name = lexical_binding_key(ctx, state, usage->ref_name);
        if (!name) {
            continue;
        }
        const CBMLexicalScope *binding_scope = lexical_binding_scope_for_usage(state, usage, name);
        if (!binding_scope) {
            continue;
        }
        usage->semantic_reference_blocked = true;
        usage->semantic_reference_local_shadow = binding_scope->kind != CBM_LEXICAL_SCOPE_MODULE;
    }

    /* Allocation failure must never widen textual fallback. Exact semantic
     * occurrence proof still runs first, but every unproven value fails closed
     * until the next clean extraction. */
    if (state->lexical_binding_tracking_failed) {
        for (int i = state->usage_start_index; i < ctx->result->usages.count; i++) {
            CBMUsage *usage = &ctx->result->usages.items[i];
            usage->semantic_reference_blocked = true;
            const CBMLexicalScope *scope = usage_lexical_scope(state, usage->lexical_scope_id);
            usage->semantic_reference_local_shadow =
                scope && scope->kind != CBM_LEXICAL_SCOPE_MODULE;
        }
    }
}

static char *perl_direct_coderef_name(CBMExtractCtx *ctx, TSNode node) {
    if (!ctx || ctx->language != CBM_LANG_PERL ||
        strcmp(ts_node_type(node), "refgen_expression") != 0 || !is_direct_argument_value(node)) {
        return NULL;
    }
    char *text = cbm_node_text(ctx->arena, node, ctx->source);
    const char *amp = text ? strchr(text, '&') : NULL;
    if (!amp) {
        return NULL;
    }
    const char *start = amp + 1;
    while (*start && isspace((unsigned char)*start)) {
        start++;
    }
    const char *end = start;
    while (*end && (isalnum((unsigned char)*end) || *end == '_' || *end == ':')) {
        end++;
    }
    return end > start ? cbm_arena_strndup(ctx->arena, start, (size_t)(end - start)) : NULL;
}

/* Carried down as CBM_USAGE_CONTEXT_PERL_CODEREF. */
static bool direct_perl_coderef_climb(TSNode node) {
    for (TSNode parent = ts_node_parent(node); !ts_node_is_null(parent);
         parent = ts_node_parent(parent)) {
        usage_ancestor_step_test_note();
        if (strcmp(ts_node_type(parent), "refgen_expression") == 0) {
            return is_direct_argument_value(parent);
        }
        if (is_argument_container_kind(ts_node_type(parent))) {
            return false;
        }
    }
    return false;
}

static bool inside_direct_perl_coderef(CBMExtractCtx *ctx, WalkState *state, TSNode node) {
    if (!ctx || ctx->language != CBM_LANG_PERL) {
        return false;
    }
    const CBMUsageFrame *frame =
        usage_carried_frame(state, node, false, CBM_USAGE_CONTEXT_PERL_CODEREF);
    if (!frame) {
        return direct_perl_coderef_climb(node);
    }
    bool carried = (frame->context & CBM_USAGE_CONTEXT_PERL_CODEREF) != 0;
    if (usage_context_checking(state)) {
        bool climbed = direct_perl_coderef_climb(node);
        usage_context_verify(ctx, state, node, "perl_coderef", carried, climbed);
    }
    return carried;
}

static bool emit_direct_perl_coderef_usage(CBMExtractCtx *ctx, TSNode node,
                                           const char *enclosing_func_qn,
                                           uint32_t lexical_scope_id) {
    char *name = perl_direct_coderef_name(ctx, node);
    if (!name || !name[0]) {
        return false;
    }
    CBMUsage usage = {0};
    usage.ref_name = name;
    usage.enclosing_func_qn = enclosing_func_qn;
    usage.kind = CBM_USAGE_CALL_REFERENCE;
    usage.may_be_call_reference = true;
    usage.lexical_scope_id = lexical_scope_id;
    usage.site_start_byte = ts_node_start_byte(node);
    usage.site_end_byte = ts_node_end_byte(node);
    cbm_usages_push(&ctx->result->usages, ctx->arena, usage);
    return true;
}

// Try to emit a usage for a reference node. Returns early if the node should be skipped.
static void try_emit_usage(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                           bool inside_call, bool inside_import) {
    if (emit_direct_perl_coderef_usage(ctx, node, cbm_enclosing_func_qn_cached(ctx, node), 0)) {
        return;
    }
    if (inside_direct_perl_coderef(ctx, NULL, node)) {
        return;
    }
    if (!is_reference_node(ctx, node, NULL)) {
        return;
    }
    if (is_call_argument_label(node)) {
        return;
    }
    if (inside_call || inside_import) {
        return;
    }
    if (is_binding_occurrence(ctx, node, spec, NULL) ||
        is_write_occurrence(ctx, node, spec, NULL)) {
        return;
    }
    char *name = reference_name(ctx, node);
    if (name && name[0] && !cbm_is_keyword(name, ctx->language)) {
        CBMUsage usage = {0};
        usage.ref_name = name;
        usage.enclosing_func_qn = cbm_enclosing_func_qn_cached(ctx, node);
        stamp_usage_site(ctx, &usage, node, name, NULL);
        cbm_usages_push(&ctx->result->usages, ctx->arena, usage);
    }
}

// Iterative usage walker — explicit stack.
//
// The call/import ancestry that gates usage emission is maintained as ENTER/
// EXIT counters on the walk instead of per-node ancestor re-walks: the old
// is_inside_call/is_inside_import helpers climbed every ancestor via
// ts_node_parent, and tree-sitter's ts_node_parent RE-DESCENDS from the root
// scanning siblings — O(depth x sibling-position) per node, which went
// quadratic on wide nodes (a 1,536-argument call in dotnet/runtime's JIT
// torture tests put 92% of extract time into these walks; 490 s for one
// 147 KB file). Counter semantics match the helpers exactly: strict ancestors
// only — a node is emitted BEFORE its own kind increments the counters, so a
// call node itself does not count as "inside a call".
static void walk_usages(CBMExtractCtx *ctx, TSNode root, const CBMLangSpec *spec) {
    typedef struct {
        TSNode node;
        uint32_t next_child;
        bool counts_call;
        bool counts_import;
    } UsageFrame;
    int cap = 256;
    UsageFrame *frames = (UsageFrame *)cbm_arena_alloc(ctx->arena, (size_t)cap * sizeof(*frames));
    if (!frames) {
        return;
    }
    bool has_imports = spec->import_node_types && spec->import_node_types[0];
    bool has_from_imports = spec->import_from_types && spec->import_from_types[0];
    int call_depth = 0;
    int import_depth = 0;
    int top = 0;
    frames[top++] = (UsageFrame){root, 0, false, false};
    bool entering = true;

    while (top > 0) {
        UsageFrame *f = &frames[top - 1];
        if (entering) {
            try_emit_usage(ctx, f->node, spec, call_depth > 0, import_depth > 0);
            f->counts_call = cbm_kind_in_set(f->node, spec->call_node_types);
            f->counts_import =
                (has_imports && cbm_kind_in_set(f->node, spec->import_node_types)) ||
                (has_from_imports && cbm_kind_in_set(f->node, spec->import_from_types));
            if (f->counts_call) {
                call_depth++;
            }
            if (f->counts_import) {
                import_depth++;
            }
        }
        uint32_t count = ts_node_child_count(f->node);
        if (f->next_child < count) {
            TSNode child = ts_node_child(f->node, f->next_child);
            f->next_child++;
            if (top == cap) {
                int new_cap = cap * 2;
                UsageFrame *grown =
                    (UsageFrame *)cbm_arena_alloc(ctx->arena, (size_t)new_cap * sizeof(*grown));
                if (!grown) {
                    return;
                }
                memcpy(grown, frames, (size_t)cap * sizeof(*frames));
                frames = grown;
                cap = new_cap;
            }
            frames[top++] = (UsageFrame){child, 0, false, false};
            entering = true;
        } else {
            if (f->counts_call) {
                call_depth--;
            }
            if (f->counts_import) {
                import_depth--;
            }
            top--;
            entering = false;
        }
    }
}

void cbm_extract_usages(CBMExtractCtx *ctx) {
    const CBMLangSpec *spec = cbm_lang_spec(ctx->language);
    if (!spec) {
        return;
    }

    walk_usages(ctx, ctx->root, spec);
}

/* ── Ancestor context carried by the unified walk ─────────────────────
 *
 * cbm_usage_context_enter runs for every node the walk visits. It computes the
 * node's answers (CBM_USAGE_CONTEXT_*) from its parent's frame: the parent's
 * own answers, the parent's role (resolved once, when its first child is
 * entered), and the edge between them (the field the child occupies and, for
 * the identity tests, the child itself). Each transition is one level of the
 * matching climb above, in the same rule order, so an answer is decided by the
 * same nearest ancestor that would have stopped the climb. */

/* A parent's roles in those climbs. The kind roles depend only on the node's
 * kind, so they are cached per walk by symbol; the others need the node. */
enum {
    CBM_USAGE_ROLE_RESOLVED = 1U << 0,
    CBM_USAGE_ROLE_WHOLE_BINDING = 1U << 1,   /* common/language whole_binding_nodes */
    CBM_USAGE_ROLE_DECLARING_KIND = 1U << 2,  /* field_binding_nodes, function/class/field */
    CBM_USAGE_ROLE_VARIABLE_KIND = 1U << 3,   /* variable_node_types */
    CBM_USAGE_ROLE_ASSIGNMENT_KIND = 1U << 4, /* assignment_node_types, write_nodes */
    CBM_USAGE_ROLE_ELIXIR_OPERATOR = 1U << 5, /* binds by operator text instead of kind */
    CBM_USAGE_ROLE_PLSQL_PARAMETER = 1U << 6, /* a call-argument wrapper, not a binder */
    CBM_USAGE_ROLE_LINKER_ASSIGNMENT = 1U << 7,
    CBM_USAGE_ROLE_LABELED_ARGUMENT = 1U << 8,
    CBM_USAGE_ROLE_ARGUMENT_CONTAINER = 1U << 9,
    CBM_USAGE_ROLE_FUNCTION = 1U << 10,
    CBM_USAGE_ROLE_CLASS = 1U << 11,
    CBM_USAGE_ROLE_PY_NESTED_SCOPE = 1U << 12, /* lambda or comprehension */
    CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER = 1U << 13,
    CBM_USAGE_ROLE_PY_GLOBAL = 1U << 14,
    CBM_USAGE_ROLE_PY_NONLOCAL = 1U << 15,
    CBM_USAGE_ROLE_JS_VAR_DECLARATION = 1U << 16,
    CBM_USAGE_ROLE_JS_LEXICAL_DECLARATION = 1U << 17,
    CBM_USAGE_ROLE_PERL_REFGEN = 1U << 18,
    CBM_USAGE_ROLE_IMPORT_KIND = 1U << 19, /* import_kind_matches */
    /* Per node. */
    CBM_USAGE_ROLE_DECLARED = 1U << 20,           /* standard_binding_climb's declared_container */
    CBM_USAGE_ROLE_ASSIGNMENT = 1U << 21,         /* write_climb's assignment */
    CBM_USAGE_ROLE_READS_TARGET = 1U << 22,       /* assignment_reads_target */
    CBM_USAGE_ROLE_PERL_DIRECT_REFGEN = 1U << 23, /* is_direct_argument_value */
    CBM_USAGE_ROLE_IMPORT_SCOPE = 1U << 24,       /* an import or under one: alias is a target */
    /* Where the climb for a CBM_USAGE_NEAREST_* slot stops. */
    CBM_USAGE_ROLE_NEAREST_POLICY = 1U << 25,
    CBM_USAGE_ROLE_NEAREST_POLICY_AUX = 1U << 26,
    CBM_USAGE_ROLE_NEAREST_CALL_ROLE = 1U << 27,
    CBM_USAGE_ROLE_NEAREST_IMPORT = 1U << 28,
};

static const uint32_t usage_nearest_role[CBM_USAGE_NEAREST_COUNT] = {
    [CBM_USAGE_NEAREST_POLICY] = CBM_USAGE_ROLE_NEAREST_POLICY,
    [CBM_USAGE_NEAREST_POLICY_AUX] = CBM_USAGE_ROLE_NEAREST_POLICY_AUX,
    [CBM_USAGE_NEAREST_CALL_ROLE] = CBM_USAGE_ROLE_NEAREST_CALL_ROLE,
    [CBM_USAGE_NEAREST_IMPORT] = CBM_USAGE_ROLE_NEAREST_IMPORT,
};

/* Initial frame and target-record capacities; both double as needed. */
enum { USAGE_FRAMES_INITIAL = 64, USAGE_TARGETS_INITIAL = 16 };

enum {
    CBM_USAGE_FIELD_KNOWN = 1U << 0,
    CBM_USAGE_FIELD_VALUE = 1U << 1, /* is_value_field */
    CBM_USAGE_FIELD_TYPE = 1U << 2,
    CBM_USAGE_FIELD_LABEL = 1U << 3, /* a labeled argument's name/label/key */
};

/* Field names of the CBM_USAGE_TARGET_* field slots, in slot order. The first
 * nine are binding_fields, in its order. */
static const char *const usage_target_field_names[] = {
    "name",      "pattern", "declarator", "parameter",   "parameters", "left",    "variable",
    "variables", "key",     "target",     "destination", "value",      "default", "alias",
};
_Static_assert(sizeof(usage_target_field_names) / sizeof(usage_target_field_names[0]) ==
                   CBM_USAGE_FIELD_TARGET_COUNT,
               "one field name per field target slot");

/* Kind roles decided by the kind's name alone. The climbs they mirror are only
 * asked in their own languages but do not check the language themselves, so
 * neither do these; the three language-specific rules do. */
static const struct {
    CBMLanguage language; /* CBM_LANG_COUNT: any language */
    const char *kind;
    uint32_t role;
} usage_named_kind_roles[] = {
    {CBM_LANG_COUNT, "lambda", CBM_USAGE_ROLE_PY_NESTED_SCOPE},
    {CBM_LANG_COUNT, "list_comprehension", CBM_USAGE_ROLE_PY_NESTED_SCOPE},
    {CBM_LANG_COUNT, "set_comprehension", CBM_USAGE_ROLE_PY_NESTED_SCOPE},
    {CBM_LANG_COUNT, "dictionary_comprehension", CBM_USAGE_ROLE_PY_NESTED_SCOPE},
    {CBM_LANG_COUNT, "generator_expression", CBM_USAGE_ROLE_PY_NESTED_SCOPE},
    {CBM_LANG_COUNT, "default_parameter", CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER},
    {CBM_LANG_COUNT, "typed_default_parameter", CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER},
    {CBM_LANG_COUNT, "global_statement", CBM_USAGE_ROLE_PY_GLOBAL},
    {CBM_LANG_COUNT, "nonlocal_statement", CBM_USAGE_ROLE_PY_NONLOCAL},
    {CBM_LANG_COUNT, "variable_declaration", CBM_USAGE_ROLE_JS_VAR_DECLARATION},
    {CBM_LANG_COUNT, "lexical_declaration", CBM_USAGE_ROLE_JS_LEXICAL_DECLARATION},
    {CBM_LANG_COUNT, "refgen_expression", CBM_USAGE_ROLE_PERL_REFGEN},
    {CBM_LANG_ELIXIR, "binary_operator", CBM_USAGE_ROLE_ELIXIR_OPERATOR},
    {CBM_LANG_PLSQL, "parameter", CBM_USAGE_ROLE_PLSQL_PARAMETER},
    {CBM_LANG_LINKERSCRIPT, "assignment", CBM_USAGE_ROLE_LINKER_ASSIGNMENT},
};

/* Kind roles from the language spec's kind sets and the occurrence tables. */
static uint32_t usage_spec_kind_roles(CBMExtractCtx *ctx, const CBMLangSpec *spec, TSNode node,
                                      const char *kind) {
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    bool function = spec->function_node_types && cbm_kind_in_set(node, spec->function_node_types);
    bool class_kind = spec->class_node_types && cbm_kind_in_set(node, spec->class_node_types);
    bool field = spec->field_node_types && cbm_kind_in_set(node, spec->field_node_types);
    uint32_t roles = 0;
    if (kind_in_exact_set(kind, common_whole_binding_nodes) ||
        kind_in_exact_set(kind, occurrence->whole_binding_nodes)) {
        roles |= CBM_USAGE_ROLE_WHOLE_BINDING;
    }
    if (kind_in_exact_set(kind, field_binding_nodes) || function || class_kind || field) {
        roles |= CBM_USAGE_ROLE_DECLARING_KIND;
    }
    if (spec->variable_node_types && cbm_kind_in_set(node, spec->variable_node_types)) {
        roles |= CBM_USAGE_ROLE_VARIABLE_KIND;
    }
    if ((spec->assignment_node_types && cbm_kind_in_set(node, spec->assignment_node_types)) ||
        kind_in_exact_set(kind, occurrence->write_nodes)) {
        roles |= CBM_USAGE_ROLE_ASSIGNMENT_KIND;
    }
    roles |= import_kind_matches(node, spec) ? CBM_USAGE_ROLE_IMPORT_KIND : 0U;
    roles |= function ? CBM_USAGE_ROLE_FUNCTION : 0U;
    roles |= class_kind ? CBM_USAGE_ROLE_CLASS : 0U;
    return roles;
}

static uint32_t usage_kind_roles_uncached(CBMExtractCtx *ctx, const CBMLangSpec *spec,
                                          TSNode node) {
    const char *kind = ts_node_type(node);
    uint32_t roles = CBM_USAGE_ROLE_RESOLVED | usage_spec_kind_roles(ctx, spec, node, kind);
    roles |= is_labeled_argument_kind(kind) ? CBM_USAGE_ROLE_LABELED_ARGUMENT : 0U;
    roles |= is_argument_container_kind(kind) ? CBM_USAGE_ROLE_ARGUMENT_CONTAINER : 0U;
    for (size_t i = 0; i < sizeof(usage_named_kind_roles) / sizeof(usage_named_kind_roles[0]);
         i++) {
        CBMLanguage language = usage_named_kind_roles[i].language;
        if ((language == CBM_LANG_COUNT || language == ctx->language) &&
            strcmp(kind, usage_named_kind_roles[i].kind) == 0) {
            roles |= usage_named_kind_roles[i].role;
        }
    }
    return roles;
}

/* ts_node_type is a function of ts_node_symbol (the public symbol names the
 * same kind) and cbm_kind_in_set tests the symbol, so kind roles cache by it. */
static uint32_t usage_kind_roles(CBMExtractCtx *ctx, const CBMLangSpec *spec,
                                 CBMUsageContext *context, TSNode node) {
    TSSymbol symbol = ts_node_symbol(node);
    if (symbol >= context->symbol_count) {
        return usage_kind_roles_uncached(ctx, spec, node);
    }
    if (!context->symbol_roles[symbol]) {
        context->symbol_roles[symbol] = usage_kind_roles_uncached(ctx, spec, node);
    }
    return context->symbol_roles[symbol];
}

static uint8_t usage_field_flags(CBMUsageContext *context, TSNode node, TSFieldId field_id) {
    if (field_id == 0 || field_id > context->field_count) {
        return 0;
    }
    uint8_t flags = context->field_flags[field_id];
    if (flags) {
        return flags;
    }
    const char *name = usage_field_name(node, field_id);
    flags = CBM_USAGE_FIELD_KNOWN;
    if (is_value_field(name)) {
        flags |= CBM_USAGE_FIELD_VALUE;
    }
    if (name && strcmp(name, "type") == 0) {
        flags |= CBM_USAGE_FIELD_TYPE;
    }
    if (name &&
        (strcmp(name, "name") == 0 || strcmp(name, "label") == 0 || strcmp(name, "key") == 0)) {
        flags |= CBM_USAGE_FIELD_LABEL;
    }
    context->field_flags[field_id] = flags;
    return flags;
}

/* Record the field child in `slot`: as `id` when it is a direct child of
 * `node`, else as `via`, the direct child above it. An empty target is left
 * out: it cannot contain the non-empty nodes the frames answer for. */
static void usage_resolve_field_target(CBMUsageTargets *targets, int slot, TSNode node,
                                       TSFieldId field_id) {
    TSNode target = ts_node_child_by_field_id(node, field_id);
    if (ts_node_is_null(target) || ts_node_start_byte(target) == ts_node_end_byte(target)) {
        return;
    }
    TSNode child = ts_node_child_with_descendant(node, target);
    if (child.id == target.id) {
        targets->id[slot] = target.id;
    } else {
        targets->via[slot] = child.id;
    }
}

/* Resolve the children the transitions compare with, once for this parent.
 * Records form a stack parallel to the path: a parent's record sits just above
 * its ancestors' records, and a sibling subtree reuses the slots. */
static bool usage_context_resolve_targets(CBMExtractCtx *ctx, CBMUsageContext *context,
                                          CBMUsageFrame *parent) {
    uint32_t index = parent->targets_end;
    if (index >= context->target_capacity) {
        uint32_t capacity =
            context->target_capacity ? context->target_capacity * PAIR_LEN : USAGE_TARGETS_INITIAL;
        CBMUsageTargets *grown = (CBMUsageTargets *)cbm_realloc(
            CBM_MEM_CLASS_EXTRACT, context->targets, (size_t)capacity * sizeof(*grown));
        if (!grown) {
            return false;
        }
        context->targets = grown;
        context->target_capacity = capacity;
    }
    if (!context->target_fields_resolved) {
        const TSLanguage *language = ts_node_language(parent->node);
        for (int i = 0; i < CBM_USAGE_FIELD_TARGET_COUNT; i++) {
            const char *name = usage_target_field_names[i];
            context->target_fields[i] =
                ts_language_field_id_for_name(language, name, (uint32_t)strlen(name));
        }
        context->target_fields_resolved = true;
    }
    CBMUsageTargets *targets = &context->targets[index];
    memset(targets, 0, sizeof(*targets));
    TSNode node = parent->node;
    uint32_t roles = parent->roles;
    if (roles & CBM_USAGE_ROLE_DECLARED) {
        for (int i = CBM_USAGE_TARGET_NAME; i <= CBM_USAGE_TARGET_KEY; i++) {
            usage_resolve_field_target(targets, i, node, context->target_fields[i]);
        }
    }
    if (roles & CBM_USAGE_ROLE_ASSIGNMENT) {
        for (int i = CBM_USAGE_TARGET_TARGET; i <= CBM_USAGE_TARGET_DESTINATION; i++) {
            usage_resolve_field_target(targets, i, node, context->target_fields[i]);
        }
        usage_resolve_field_target(targets, CBM_USAGE_TARGET_LEFT, node,
                                   context->target_fields[CBM_USAGE_TARGET_LEFT]);
        if (ts_node_child_count(node) > 0) {
            targets->id[CBM_USAGE_TARGET_FIRST_CHILD] = ts_node_child(node, 0).id;
        }
        if (occurrence_specs[ctx->language].first_named_child_is_write &&
            ts_node_named_child_count(node) > 0) {
            targets->id[CBM_USAGE_TARGET_FIRST_NAMED_CHILD] = ts_node_named_child(node, 0).id;
        }
    }
    if (roles & CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER) {
        for (int i = CBM_USAGE_TARGET_VALUE; i <= CBM_USAGE_TARGET_DEFAULT; i++) {
            usage_resolve_field_target(targets, i, node, context->target_fields[i]);
        }
    }
    if (roles & CBM_USAGE_ROLE_IMPORT_SCOPE) {
        usage_resolve_field_target(targets, CBM_USAGE_TARGET_ALIAS, node,
                                   context->target_fields[CBM_USAGE_TARGET_ALIAS]);
    }
    parent->targets = index;
    parent->targets_end = index + SKIP_ONE;
    return true;
}

/* The CBM_USAGE_ROLE_NEAREST_* roles of node: the slots whose climbs stop at
 * it. Text tests make some of these per node, so they are not kind roles. */
static uint32_t usage_nearest_roles(CBMExtractCtx *ctx, const CBMUsageContext *context, TSNode node,
                                    uint32_t roles) {
    const bool *kept = context->nearest_kept;
    uint32_t nearest = 0;
    if (kept[CBM_USAGE_NEAREST_POLICY] && policy_ancestor_decides(ctx, node)) {
        nearest |= CBM_USAGE_ROLE_NEAREST_POLICY;
    }
    if (kept[CBM_USAGE_NEAREST_POLICY_AUX] && policy_aux_ancestor_decides(ctx, node)) {
        nearest |= CBM_USAGE_ROLE_NEAREST_POLICY_AUX;
    }
    if (kept[CBM_USAGE_NEAREST_CALL_ROLE] &&
        cbm_call_role_ancestor_decides(ctx->language, node, ctx->source)) {
        nearest |= CBM_USAGE_ROLE_NEAREST_CALL_ROLE;
    }
    if (roles & CBM_USAGE_ROLE_IMPORT_KIND) {
        nearest |= CBM_USAGE_ROLE_NEAREST_IMPORT;
    }
    return nearest;
}

static bool usage_context_resolve_parent(CBMExtractCtx *ctx, const CBMLangSpec *spec,
                                         CBMUsageContext *context, CBMUsageFrame *parent) {
    TSNode node = parent->node;
    uint32_t roles = usage_kind_roles(ctx, spec, context, node);
    bool variable = (roles & CBM_USAGE_ROLE_VARIABLE_KIND) != 0;
    bool assignment = (roles & CBM_USAGE_ROLE_ASSIGNMENT_KIND) != 0;
    if (roles & CBM_USAGE_ROLE_ELIXIR_OPERATOR) {
        /* The operator text replaces both kind tests, as in the climbs. */
        variable = assignment = elixir_binary_operator_binds(ctx, node);
    }
    if (variable || (roles & CBM_USAGE_ROLE_DECLARING_KIND)) {
        roles |= CBM_USAGE_ROLE_DECLARED;
    }
    if (assignment) {
        roles |= CBM_USAGE_ROLE_ASSIGNMENT;
        if (assignment_reads_target(node)) {
            roles |= CBM_USAGE_ROLE_READS_TARGET;
        }
    }
    if ((roles & CBM_USAGE_ROLE_PERL_REFGEN) && is_direct_argument_value(node)) {
        roles |= CBM_USAGE_ROLE_PERL_DIRECT_REFGEN;
    }
    if ((roles & CBM_USAGE_ROLE_IMPORT_KIND) ||
        parent->nearest[CBM_USAGE_NEAREST_IMPORT] != CBM_USAGE_NO_NEAREST) {
        roles |= CBM_USAGE_ROLE_IMPORT_SCOPE;
    }
    roles |= usage_nearest_roles(ctx, context, node, roles);
    parent->roles = roles;
    if (!(roles & (CBM_USAGE_ROLE_DECLARED | CBM_USAGE_ROLE_ASSIGNMENT |
                   CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER | CBM_USAGE_ROLE_IMPORT_SCOPE))) {
        return true;
    }
    return usage_context_resolve_targets(ctx, context, parent);
}

static bool usage_slots_hold(const void *const *slots, const void *id, int first, int last) {
    for (int i = first; i <= last; i++) {
        if (slots[i] == id) {
            return true;
        }
    }
    return false;
}

/* One level of each climb, for the edge from `parent` (roles, its answers
 * `inherited`) into a child with edge-field flags `field` and node id `id`.
 * `id` is compared where the climb tests containment (see usage_carried_frame
 * for why that is the same test). */
typedef struct {
    uint32_t roles;
    uint32_t inherited;
    uint8_t field;
    const CBMUsageTargets *targets;
    const void *id;
} CBMUsageEdge;

/* The parent's answer and its unknown bit, when this level does not decide. */
static uint32_t usage_inherit(const CBMUsageEdge *edge, uint32_t answer) {
    return edge->inherited & (answer | usage_unknown(answer));
}

/* A containment test at this level: yes when the child is one of the targets
 * in [first, last], unknown when the child lies above one of them, and
 * `otherwise` when it is neither. */
static uint32_t usage_contains(const CBMUsageEdge *edge, uint32_t answer, int first, int last,
                               uint32_t otherwise) {
    if (usage_slots_hold(edge->targets->id, edge->id, first, last)) {
        return answer;
    }
    if (usage_slots_hold(edge->targets->via, edge->id, first, last)) {
        return usage_unknown(answer);
    }
    return otherwise;
}

/* standard_binding_climb */
static uint32_t usage_carry_binding(const CBMUsageEdge *edge) {
    const uint32_t answer = CBM_USAGE_CONTEXT_BINDING;
    if (edge->field & (CBM_USAGE_FIELD_VALUE | CBM_USAGE_FIELD_TYPE)) {
        return 0;
    }
    if (edge->roles & CBM_USAGE_ROLE_PLSQL_PARAMETER) {
        return usage_inherit(edge, answer); /* transparent */
    }
    if (edge->roles & CBM_USAGE_ROLE_WHOLE_BINDING) {
        return answer;
    }
    if (edge->roles & CBM_USAGE_ROLE_DECLARED) {
        return usage_contains(edge, answer, CBM_USAGE_TARGET_NAME, CBM_USAGE_TARGET_KEY,
                              usage_inherit(edge, answer));
    }
    return usage_inherit(edge, answer);
}

/* write_climb */
static uint32_t usage_carry_write(const CBMUsageEdge *edge) {
    const uint32_t answer = CBM_USAGE_CONTEXT_WRITE;
    if (edge->field & CBM_USAGE_FIELD_VALUE) {
        return 0;
    }
    if (!(edge->roles & CBM_USAGE_ROLE_ASSIGNMENT)) {
        return usage_inherit(edge, answer);
    }
    if (edge->roles & CBM_USAGE_ROLE_READS_TARGET) {
        return 0;
    }
    if (edge->roles & CBM_USAGE_ROLE_LINKER_ASSIGNMENT) {
        return usage_contains(edge, answer, CBM_USAGE_TARGET_FIRST_CHILD,
                              CBM_USAGE_TARGET_FIRST_CHILD, 0);
    }
    uint32_t named_first = usage_contains(edge, answer, CBM_USAGE_TARGET_FIRST_NAMED_CHILD,
                                          CBM_USAGE_TARGET_FIRST_NAMED_CHILD, 0);
    uint32_t target = usage_contains(edge, answer, CBM_USAGE_TARGET_TARGET,
                                     CBM_USAGE_TARGET_DESTINATION, named_first);
    return usage_contains(edge, answer, CBM_USAGE_TARGET_LEFT, CBM_USAGE_TARGET_LEFT, target);
}

/* python_default_value_climb: a lambda or comprehension stops it with no; a
 * default parameter answers yes for the child in its value or default field
 * and lets any other child keep climbing. */
static uint32_t usage_carry_python_default(const CBMUsageEdge *edge) {
    const uint32_t answer = CBM_USAGE_CONTEXT_PY_DEFAULT_VALUE;
    if (edge->roles & CBM_USAGE_ROLE_PY_NESTED_SCOPE) {
        return 0;
    }
    if (edge->roles & CBM_USAGE_ROLE_PY_DEFAULT_PARAMETER) {
        return usage_contains(edge, answer, CBM_USAGE_TARGET_VALUE, CBM_USAGE_TARGET_DEFAULT,
                              usage_inherit(edge, answer));
    }
    return usage_inherit(edge, answer);
}

/* binding_is_parameter_climb */
static uint32_t usage_carry_parameter(const CBMUsageEdge *edge) {
    const uint32_t answer = CBM_USAGE_CONTEXT_PARAMETER;
    if (edge->roles & CBM_USAGE_ROLE_WHOLE_BINDING) {
        return answer;
    }
    if (edge->roles & CBM_USAGE_ROLE_FUNCTION) {
        return usage_contains(edge, answer, CBM_USAGE_TARGET_PARAMETER, CBM_USAGE_TARGET_PARAMETERS,
                              0);
    }
    return usage_inherit(edge, answer);
}

/* declared_function_name_owner / declared_class_name_owner: the nearest
 * `owner` ancestor decides by its name field. */
static uint32_t usage_carry_owner_name(const CBMUsageEdge *edge, uint32_t owner, uint32_t answer) {
    if (edge->roles & owner) {
        return usage_contains(edge, answer, CBM_USAGE_TARGET_NAME, CBM_USAGE_TARGET_NAME, 0);
    }
    return usage_inherit(edge, answer);
}

/* A climb with no containment test that stops at the nearest `decides`
 * ancestor with `verdict`, or at the nearest `refuses` ancestor with no. */
static uint32_t usage_carry_nearest(const CBMUsageEdge *edge, uint32_t answer, uint32_t decides,
                                    bool verdict, uint32_t refuses) {
    if (edge->roles & decides) {
        return verdict ? answer : 0U;
    }
    if (edge->roles & refuses) {
        return 0;
    }
    return edge->inherited & answer;
}

/* lexical_ancestor_kind: ANY ancestor of the kind, not the nearest decider. */
static uint32_t usage_carry_any(const CBMUsageEdge *edge, uint32_t answer, uint32_t kind) {
    return (edge->roles & kind) ? answer : (edge->inherited & answer);
}

/* import_binding_climb's alias rule: an alias field at any level from the
 * nearest import statement down contains the node. An import restarts it. */
static uint32_t usage_carry_import_alias(const CBMUsageEdge *edge) {
    const uint32_t answer = CBM_USAGE_CONTEXT_IMPORT_ALIAS;
    if (!(edge->roles & CBM_USAGE_ROLE_IMPORT_SCOPE)) {
        return 0;
    }
    uint32_t above = (edge->roles & CBM_USAGE_ROLE_IMPORT_KIND) ? 0U : usage_inherit(edge, answer);
    return above | usage_contains(edge, answer, CBM_USAGE_TARGET_ALIAS, CBM_USAGE_TARGET_ALIAS, 0);
}

static uint32_t usage_context_carry(CBMUsageContext *context, const CBMUsageFrame *parent,
                                    TSFieldId field_id, TSNode child) {
    static const CBMUsageTargets no_targets = {{0}, {0}};
    CBMUsageEdge edge = {
        .roles = parent->roles,
        .inherited = parent->context,
        .field = usage_field_flags(context, child, field_id),
        .targets = parent->targets == CBM_USAGE_NO_TARGETS ? &no_targets
                                                           : &context->targets[parent->targets],
        .id = child.id,
    };
    const CBMUsageEdge *e = &edge;
    return usage_carry_binding(e) | usage_carry_write(e) | usage_carry_python_default(e) |
           usage_carry_parameter(e) |
           usage_carry_owner_name(e, CBM_USAGE_ROLE_FUNCTION, CBM_USAGE_CONTEXT_FUNCTION_NAME) |
           usage_carry_owner_name(e, CBM_USAGE_ROLE_CLASS, CBM_USAGE_CONTEXT_CLASS_NAME) |
           /* call_argument_label_climb */
           usage_carry_nearest(e, CBM_USAGE_CONTEXT_ARGUMENT_LABEL, CBM_USAGE_ROLE_LABELED_ARGUMENT,
                               (e->field & CBM_USAGE_FIELD_LABEL) != 0,
                               CBM_USAGE_ROLE_ARGUMENT_CONTAINER) |
           /* js_var_binding_climb */
           usage_carry_nearest(e, CBM_USAGE_CONTEXT_JS_VAR, CBM_USAGE_ROLE_JS_VAR_DECLARATION, true,
                               CBM_USAGE_ROLE_JS_LEXICAL_DECLARATION) |
           /* direct_perl_coderef_climb */
           usage_carry_nearest(e, CBM_USAGE_CONTEXT_PERL_CODEREF, CBM_USAGE_ROLE_PERL_REFGEN,
                               (e->roles & CBM_USAGE_ROLE_PERL_DIRECT_REFGEN) != 0,
                               CBM_USAGE_ROLE_ARGUMENT_CONTAINER) |
           usage_carry_any(e, CBM_USAGE_CONTEXT_IN_GLOBAL, CBM_USAGE_ROLE_PY_GLOBAL) |
           usage_carry_any(e, CBM_USAGE_CONTEXT_IN_NONLOCAL, CBM_USAGE_ROLE_PY_NONLOCAL) |
           usage_carry_import_alias(e);
}

void cbm_usage_context_init(CBMExtractCtx *ctx, const CBMLangSpec *spec, WalkState *state) {
    CBMUsageContext *context = &state->usage_context;
    memset(context, 0, sizeof(*context));
    CBMOccurrencePolicy policy = occurrence_specs[ctx->language].policy;
    context->nearest_kept[CBM_USAGE_NEAREST_POLICY] = policy_uses_nearest(policy);
    context->nearest_kept[CBM_USAGE_NEAREST_POLICY_AUX] =
        policy == CBM_OCCURRENCE_TLAPLUS_OPERATOR || policy == CBM_OCCURRENCE_NICKEL_LET;
    context->nearest_kept[CBM_USAGE_NEAREST_CALL_ROLE] = cbm_call_role_language(ctx->language);
    context->nearest_kept[CBM_USAGE_NEAREST_IMPORT] =
        (spec->import_node_types && spec->import_node_types[0]) ||
        (spec->import_from_types && spec->import_from_types[0]);
    const TSLanguage *language = ts_node_language(ctx->root);
    context->symbol_count = ts_language_symbol_count(language);
    context->field_count = ts_language_field_count(language);
    context->symbol_roles = (uint32_t *)cbm_calloc(
        CBM_MEM_CLASS_EXTRACT, (size_t)context->symbol_count * sizeof(*context->symbol_roles));
    context->field_flags =
        (uint8_t *)cbm_calloc(CBM_MEM_CLASS_EXTRACT, (size_t)context->field_count + SKIP_ONE);
    context->failed = !context->symbol_roles || !context->field_flags;
#ifdef CBM_ENABLE_TEST_SEAMS
    const char *check = getenv("CBM_TEST_USAGE_CONTEXT_CHECK");
    if (check && check[0] && strcmp(check, "0") != 0) {
        context->check_mode = strcmp(check, "2") == 0 ? USAGE_CHECK_ABORT : USAGE_CHECK_REPORT;
    }
    const char *climb = getenv("CBM_TEST_USAGE_CONTEXT_CLIMB");
    context->climb_only = climb && strcmp(climb, "1") == 0;
#endif
}

void cbm_usage_context_enter(CBMExtractCtx *ctx, const CBMLangSpec *spec, WalkState *state,
                             uint32_t depth, TSNode node, TSFieldId field_id) {
    CBMUsageContext *context = &state->usage_context;
    if (context->failed) {
        return;
    }
    if (depth >= context->frame_capacity) {
        uint32_t capacity =
            context->frame_capacity ? context->frame_capacity : USAGE_FRAMES_INITIAL;
        while (capacity <= depth) {
            capacity *= PAIR_LEN;
        }
        CBMUsageFrame *grown = (CBMUsageFrame *)cbm_realloc(CBM_MEM_CLASS_EXTRACT, context->frames,
                                                            (size_t)capacity * sizeof(*grown));
        if (!grown) {
            context->failed = true;
            return;
        }
        context->frames = grown;
        context->frame_capacity = capacity;
    }
    CBMUsageFrame *frame = &context->frames[depth];
    frame->node = node;
    frame->field_id = field_id;
    frame->roles = 0;
    frame->targets = CBM_USAGE_NO_TARGETS;
    context->depth = depth;
    if (depth == 0) {
        /* The root has no ancestors, so every climb from it answers no. */
        frame->targets_end = 0;
        frame->context = 0;
        for (int slot = 0; slot < CBM_USAGE_NEAREST_COUNT; slot++) {
            frame->nearest[slot] = CBM_USAGE_NO_NEAREST;
        }
        return;
    }
    CBMUsageFrame *parent = &context->frames[depth - SKIP_ONE];
    if (!(parent->roles & CBM_USAGE_ROLE_RESOLVED) &&
        !usage_context_resolve_parent(ctx, spec, context, parent)) {
        context->failed = true;
        return;
    }
    frame->targets_end = parent->targets_end;
    frame->context = usage_context_carry(context, parent, field_id, node);
    for (int slot = 0; slot < CBM_USAGE_NEAREST_COUNT; slot++) {
        frame->nearest[slot] =
            (parent->roles & usage_nearest_role[slot]) ? depth - SKIP_ONE : parent->nearest[slot];
    }
}

void cbm_usage_context_free(CBMExtractCtx *ctx, WalkState *state) {
    CBMUsageContext *context = &state->usage_context;
#ifdef CBM_ENABLE_TEST_SEAMS
    if (context->check_mode) {
        char checks[24];
        char fallbacks[24];
        char mismatches[24];
        snprintf(checks, sizeof(checks), "%llu", (unsigned long long)context->checks);
        snprintf(fallbacks, sizeof(fallbacks), "%llu", (unsigned long long)context->fallbacks);
        snprintf(mismatches, sizeof(mismatches), "%llu", (unsigned long long)context->mismatches);
        /* Quiet unless something climbed anyway or disagreed. */
        CBMLogLevel level = context->fallbacks || context->mismatches || context->failed
                                ? CBM_LOG_INFO
                                : CBM_LOG_DEBUG;
        cbm_log(level, "usage_context.summary", "path", ctx->rel_path ? ctx->rel_path : "",
                "checks", checks, "fallbacks", fallbacks, "mismatches", mismatches, "failed",
                context->failed ? "1" : "0", NULL);
    }
#else
    (void)ctx;
#endif
    cbm_free(CBM_MEM_CLASS_EXTRACT, context->frames);
    cbm_free(CBM_MEM_CLASS_EXTRACT, context->targets);
    cbm_free(CBM_MEM_CLASS_EXTRACT, context->symbol_roles);
    cbm_free(CBM_MEM_CLASS_EXTRACT, context->field_flags);
    memset(context, 0, sizeof(*context));
}

// --- Unified handler: called once per node by the cursor walk ---
// Uses WalkState flags instead of parent-chain walks for O(1) context checks.

void handle_usages(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec, WalkState *state) {
    if (emit_direct_perl_coderef_usage(ctx, node, state->enclosing_func_qn,
                                       active_lexical_scope_id(state))) {
        return;
    }
    if (inside_direct_perl_coderef(ctx, state, node)) {
        return;
    }
    bool reference_node = is_reference_node(ctx, node, state);
    const CBMOccurrenceSpec *occurrence = &occurrence_specs[ctx->language];
    bool possible_binding_leaf =
        ts_node_is_named(node) && ts_node_named_child_count(node) == 0 &&
        (state->inside_import || is_exact_language_binding(ctx, node, state) ||
         is_policy_binding(ctx, node, occurrence, state));
    if (!reference_node && !possible_binding_leaf) {
        return;
    }

    // An invocation relationship replaces only the exact AST occurrence it
    // consumes. Receivers, qualifiers, computed keys, arguments, and nested
    // bodies remain ordinary value references. Explicit callable syntax keeps
    // that exact occurrence as a typed reference instead of erasing it.
    bool exact_callee =
        (!ts_node_is_null(state->callee_expr) && ts_node_eq(node, state->callee_expr)) ||
        (!ts_node_is_null(state->callee_leaf) && ts_node_eq(node, state->callee_leaf));
    if (exact_callee) {
        if (reference_node && state->invocation_kind == CBM_INVOCATION_CALLABLE_REFERENCE) {
            char *name = reference_name(ctx, node);
            if (name && name[0] && !cbm_is_keyword(name, ctx->language)) {
                CBMUsage usage = {0};
                usage.ref_name = name;
                usage.enclosing_func_qn = state->enclosing_func_qn;
                usage.lexical_scope_id = usage_lexical_scope_id_for_node(ctx, state, node);
                /* Kotlin callable-reference syntax is only a precision
                 * candidate. The semantic pass decides whether `::name`
                 * denotes one exact callable; unresolved properties and
                 * ambiguous values must remain ordinary USAGE. */
                if (ctx->language == CBM_LANG_KOTLIN) {
                    usage.kind = CBM_USAGE_VALUE;
                    usage.may_be_call_reference = true;
                } else {
                    usage.kind = CBM_USAGE_CALL_REFERENCE;
                }
                usage.site_start_byte = ts_node_start_byte(node);
                usage.site_end_byte = ts_node_end_byte(node);
                cbm_usages_push(&ctx->result->usages, ctx->arena, usage);
            }
        }
        return;
    }
    if (is_forward_sibling_callee(ctx, state, node)) {
        return;
    }
    if (is_call_argument_label_walk(ctx, node, state)) {
        return;
    }
    // Imports do not emit ordinary usages, but their binding occurrence must
    // be recorded before the subtree is skipped.
    if (state->inside_import) {
        if (is_import_binding_occurrence(ctx, node, spec, state)) {
            char *binding_name = reference_name(ctx, node);
            if (binding_name && binding_name[0] && !cbm_is_keyword(binding_name, ctx->language)) {
                record_lexical_binding(ctx, state, node, spec, binding_name, true);
            }
        }
        return;
    }

    bool python_scope_directive =
        ctx->language == CBM_LANG_PYTHON && (python_directive_ancestor(ctx, state, node, true) ||
                                             python_directive_ancestor(ctx, state, node, false));
    if (python_scope_directive || is_binding_occurrence(ctx, node, spec, state)) {
        char *binding_name = reference_name(ctx, node);
        if (binding_name && binding_name[0] && !cbm_is_keyword(binding_name, ctx->language)) {
            record_lexical_binding(ctx, state, node, spec, binding_name, false);
        }
        return;
    }
    if (!reference_node) {
        return;
    }
    if (is_write_occurrence(ctx, node, spec, state)) {
        if (ctx->language == CBM_LANG_OBJECTSCRIPT_UDL ||
            ctx->language == CBM_LANG_OBJECTSCRIPT_ROUTINE) {
            char *binding_name = reference_name(ctx, node);
            if (binding_name && binding_name[0] && !cbm_is_keyword(binding_name, ctx->language)) {
                record_lexical_binding(ctx, state, node, spec, binding_name, false);
            }
        }
        return;
    }

    char *name = reference_name(ctx, node);
    if (name && name[0] && !cbm_is_keyword(name, ctx->language)) {
        CBMUsage usage = {0};
        usage.ref_name = name;
        usage.enclosing_func_qn = state->enclosing_func_qn;
        usage.lexical_scope_id = usage_lexical_scope_id_for_node(ctx, state, node);
        /* The member half of a selector is its own reference node
         * (field_identifier); record that shape — the name alone cannot carry
         * it, and the Go Field guard keys on it (#1962). */
        usage.is_member_access = strcmp(ts_node_type(node), "field_identifier") == 0;
        stamp_usage_site(ctx, &usage, node, name, state);
        cbm_usages_push(&ctx->result->usages, ctx->arena, usage);
    }
}
