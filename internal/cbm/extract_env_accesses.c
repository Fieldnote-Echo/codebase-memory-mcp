#include "cbm.h"
#include "arena.h" // CBMArena, cbm_arena_strndup
#include "helpers.h"
#include "lang_specs.h"
#include "extract_unified.h"
#include "foundation/constants.h"
#include "extract_node_stack.h"
#include "tree_sitter/api.h" // TSNode, ts_node_*
#include <stdint.h>          // uint32_t
#include <string.h>
#include <ctype.h>

/* Minimum length for an env var name (e.g., "DB"). */
enum { MIN_ENV_NAME_LEN = 2 };

// Unquote a string literal: "foo" -> foo, 'foo' -> foo
static const char *unquote(CBMArena *a, const char *s) {
    if (!s || !s[0]) {
        return NULL;
    }
    // Trim whitespace
    while (*s == ' ' || *s == '\t') {
        s++;
    }
    size_t len = strlen(s);
    if (len >= CBM_QUOTE_PAIR) {
        char first = s[0];
        char last = s[len - CBM_QUOTE_OFFSET];
        if ((first == '"' && last == '"') || (first == '\'' && last == '\'') ||
            (first == '`' && last == '`')) {
            return cbm_arena_strndup(a, s + CBM_QUOTE_OFFSET, len - CBM_QUOTE_PAIR);
        }
    }
    return s;
}

// Extract env key from a function call like os.Getenv("KEY").
static const char *extract_env_key_from_call(CBMExtractCtx *ctx, TSNode node,
                                             const CBMLangSpec *spec) {
    if (!spec->env_access_functions || !spec->env_access_functions[0]) {
        return NULL;
    }

    TSNode func_node = ts_node_child_by_field_name(node, TS_FIELD("function"));
    if (ts_node_is_null(func_node)) {
        return NULL;
    }
    char *callee = cbm_node_text(ctx->arena, func_node, ctx->source);
    if (!callee) {
        return NULL;
    }

    // Check if callee matches any env access function
    bool match = false;
    for (const char **ef = spec->env_access_functions; *ef; ef++) {
        if (strcmp(callee, *ef) == 0) {
            match = true;
            break;
        }
    }
    if (!match) {
        return NULL;
    }

    // Get first argument (the env key)
    TSNode args = ts_node_child_by_field_name(node, TS_FIELD("arguments"));
    if (ts_node_is_null(args)) {
        return NULL;
    }
    // Find first named child (skip parentheses)
    for (uint32_t i = 0; i < ts_node_child_count(args); i++) {
        TSNode child = ts_node_child(args, i);
        const char *ck = ts_node_type(child);
        if (strcmp(ck, "(") == 0 || strcmp(ck, ")") == 0 || strcmp(ck, ",") == 0) {
            continue;
        }
        char *arg_text = cbm_node_text(ctx->arena, child, ctx->source);
        return unquote(ctx->arena, arg_text);
    }
    return NULL;
}

/* The length of `text` (text_len bytes) read as a C string: up to its first NUL. */
static size_t env_text_c_length(const char *text, size_t text_len) {
    const char *nul = memchr(text, '\0', text_len);
    return nul ? (size_t)(nul - text) : text_len;
}

/* The length of the key after `pattern.`: all of the rest (as a C string), or 0
 * when it is empty or has a further dot or bracket. */
static size_t env_member_key_length(const char *rest, size_t rest_len) {
    size_t key_len = env_text_c_length(rest, rest_len);
    return memchr(rest, '.', key_len) || memchr(rest, '[', key_len) ? 0 : key_len;
}

// Extract env key from member access like process.env.KEY or os.environ["KEY"].
static const char *extract_env_key_from_member(CBMExtractCtx *ctx, TSNode node,
                                               const CBMLangSpec *spec) {
    if (!spec->env_access_member_patterns || !spec->env_access_member_patterns[0]) {
        return NULL;
    }

    /* The node's text is read in place, as the C string a copy of it would be
     * (up to its first NUL), and only a matched key is copied. Copying the
     * whole text first cost O(length) arena bytes for every member node, and
     * a chain a.b.c... nests one member node per link: O(n^2) in all. */
    uint32_t start = ts_node_start_byte(node);
    uint32_t end = ts_node_end_byte(node);
    const char *text = ctx->source + start;
    size_t text_len = end > start ? (size_t)(end - start) : 0;
    if (text_len == 0 || text[0] == '\0') {
        return NULL;
    }

    for (const char **pat = spec->env_access_member_patterns; *pat; pat++) {
        size_t plen = strlen(*pat);
        if (text_len <= plen || memcmp(text, *pat, plen) != 0) {
            continue;
        }
        const char *rest = text + plen + CBM_QUOTE_OFFSET;
        size_t rest_len = text_len - plen - CBM_QUOTE_OFFSET;

        // Dot access: pattern.KEY
        if (text[plen] == '.') {
            // Validate: no further dots/brackets
            size_t key_len = env_member_key_length(rest, rest_len);
            if (key_len > 0) {
                return cbm_arena_strndup(ctx->arena, rest, key_len);
            }
        }

        // Subscript: pattern["KEY"]
        if (text[plen] == '[') {
            const char *inner = rest;
            size_t ilen = env_text_c_length(inner, rest_len);
            if (ilen > 0 && inner[ilen - CBM_QUOTE_OFFSET] == ']') {
                char *bracket_content =
                    cbm_arena_strndup(ctx->arena, inner, ilen - CBM_QUOTE_OFFSET);
                return unquote(ctx->arena, bracket_content);
            }
        }
    }
    return NULL;
}

// Check if an env key name looks like an environment variable (uppercase + underscores).
static bool is_env_var_name(const char *s) {
    if (!s || strlen(s) < MIN_ENV_NAME_LEN) {
        return false;
    }
    bool has_upper = false;
    for (const char *p = s; *p; p++) {
        if (*p >= 'A' && *p <= 'Z') {
            {
                has_upper = true;
            }
        } else if (*p == '_' || (*p >= '0' && *p <= '9')) { /* ok */
        } else {
            { return false; }
        }
    }
    return has_upper;
}

// Iterative env access walker — explicit stack
static void walk_env_accesses(CBMExtractCtx *ctx, TSNode root, const CBMLangSpec *spec) {
    TSNodeStack stack;
    ts_nstack_init(&stack, ctx, 4096);
    ts_nstack_push(&stack, root);

    while (stack.count > 0) {
        TSNode node = ts_nstack_pop(&stack);
        const char *kind = ts_node_type(node);
        const char *env_key = NULL;

        if (cbm_kind_in_set(node, spec->call_node_types)) {
            env_key = extract_env_key_from_call(ctx, node, spec);
        } else if (strcmp(kind, "member_expression") == 0 || strcmp(kind, "subscript") == 0 ||
                   strcmp(kind, "attribute") == 0) {
            env_key = extract_env_key_from_member(ctx, node, spec);
        }

        if (env_key && env_key[0] && is_env_var_name(env_key)) {
            CBMEnvAccess ea;
            ea.env_key = env_key;
            ea.enclosing_func_qn = cbm_enclosing_func_qn_cached(ctx, node);
            cbm_envaccess_push(&ctx->result->env_accesses, ctx->arena, ea);
            continue; // don't push children (avoid double-counting)
        }

        ts_nstack_push_children(&stack, node);
    }
}

void cbm_extract_env_accesses(CBMExtractCtx *ctx) {
    const CBMLangSpec *spec = cbm_lang_spec(ctx->language);
    if (!spec) {
        return;
    }

    bool has_funcs = spec->env_access_functions && spec->env_access_functions[0];
    bool has_members = spec->env_access_member_patterns && spec->env_access_member_patterns[0];
    if (!has_funcs && !has_members) {
        return;
    }

    walk_env_accesses(ctx, ctx->root, spec);
}

// --- Unified handler ---

void handle_env_accesses(CBMExtractCtx *ctx, TSNode node, const CBMLangSpec *spec,
                         WalkState *state) {
    bool has_funcs = spec->env_access_functions && spec->env_access_functions[0];
    bool has_members = spec->env_access_member_patterns && spec->env_access_member_patterns[0];
    if (!has_funcs && !has_members) {
        return;
    }

    const char *kind = ts_node_type(node);
    const char *env_key = NULL;

    if (has_funcs && spec->call_node_types && cbm_kind_in_set(node, spec->call_node_types)) {
        env_key = extract_env_key_from_call(ctx, node, spec);
    } else if (has_members && (strcmp(kind, "member_expression") == 0 ||
                               strcmp(kind, "subscript") == 0 || strcmp(kind, "attribute") == 0)) {
        env_key = extract_env_key_from_member(ctx, node, spec);
    }

    if (env_key && env_key[0] && is_env_var_name(env_key)) {
        CBMEnvAccess ea;
        ea.env_key = env_key;
        ea.enclosing_func_qn = state->enclosing_func_qn;
        cbm_envaccess_push(&ctx->result->env_accesses, ctx->arena, ea);
    }
}
