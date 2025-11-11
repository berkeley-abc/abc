/**CFile****************************************************************

  FileName    [utilMiniver.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Handling counter-examples.]

  Synopsis    [Handling counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: utilMiniver.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "misc/util/abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MINIVER_LIBRARY_ONLY

#define MAXSIG  1024
#define MAXSTR  65536

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

typedef struct {
    char name[128];
    int  width;
    int  is_signed;
} decl_t;

typedef struct {
    char lhs[128];
    char rhs[4096];
} asn_t;

// Parsing/collection context (encapsulates all state)
typedef struct {
    char   modname[128];
    decl_t inputs[MAXSIG];   int ni;
    decl_t outputs[MAXSIG];  int no;
    decl_t wires[MAXSIG];    int nw;
    asn_t  assigns[MAXSIG];  int na;
    int    next_auto_in;     // next index for auto-generated input names ('a' + idx)
} mv_ctx;

// -----------------------------------------------------------------------------
// Utilities
// -----------------------------------------------------------------------------

// Remove all ASCII whitespace from 's' into 'out'.
static void strip_ws(const char *s, char *out) {
    while (*s) {
        if (!isspace((unsigned char)*s)) {
            *out++ = *s;
        }
        ++s;
    }
    *out = 0;
}

static int is_ident_start(char c) {
    return isalpha((unsigned char)c) || c == '_' || c == '$';
}

static int is_ident_char(char c) {
    return isalnum((unsigned char)c) || c == '_' || c == '$';
}

// Parse a non-negative decimal integer from 's'; store value in *v and chars consumed in *nch.
static int parse_uint(const char *s, int *v, int *nch) {
    int i = 0;
    int d = 0;
    if (!isdigit((unsigned char)s[0])) return 0;
    while (isdigit((unsigned char)s[i])) {
        d = d * 10 + (s[i] - '0');
        ++i;
    }
    *v = d;
    *nch = i;
    return 1;
}

// Check if a name is already used in any declaration.
static int name_exists(mv_ctx *ctx, const char *name) {
    for (int i = 0; i < ctx->ni; ++i) if (!strcmp(ctx->inputs[i].name, name)) return 1;
    for (int i = 0; i < ctx->no; ++i) if (!strcmp(ctx->outputs[i].name, name)) return 1;
    for (int i = 0; i < ctx->nw; ++i) if (!strcmp(ctx->wires[i].name,  name)) return 1;
    return 0;
}

// Generate next auto input name: 'a','b','c',... then 'a0','a1',... if 26 exhausted.
static void gen_auto_in_name(mv_ctx *ctx, char *out, size_t out_sz) {
    // try single letters first
    for (; ctx->next_auto_in < 26; ++ctx->next_auto_in) {
        char cand[3] = {(char)('a' + ctx->next_auto_in), 0, 0};
        if (!name_exists(ctx, cand)) { strncpy(out, cand, out_sz-1); out[out_sz-1]=0; ++ctx->next_auto_in; return; }
    }
    // fallback to aN form
    for (int n = 0;; ++n) {
        char cand[32];
        snprintf(cand, sizeof(cand), "a%d", n);
        if (!name_exists(ctx, cand)) { strncpy(out, cand, out_sz-1); out[out_sz-1]=0; return; }
    }
}

// Add (or deduplicate) declaration into an array.
static void add_decl(decl_t *arr, int *cnt, const char *name, int w, int sg) {
    for (int k = 0; k < *cnt; ++k) {
        if (!strcmp(arr[k].name, name)) return;
    }
    strncpy(arr[*cnt].name, name, sizeof(arr[*cnt].name) - 1);
    arr[*cnt].width = w;
    arr[*cnt].is_signed = sg;
    ++(*cnt);
}

// Record an assignment; returns non-zero on overflow.
static int add_asn(mv_ctx *ctx, const char *lhs, const char *rhs) {
    if (ctx->na >= MAXSIG) {
        printf("Too many assignments.\n");
        return 1;
    }
    strncpy(ctx->assigns[ctx->na].lhs, lhs, sizeof(ctx->assigns[ctx->na].lhs) - 1);
    strncpy(ctx->assigns[ctx->na].rhs, rhs, sizeof(ctx->assigns[ctx->na].rhs) - 1);
    ++ctx->na;
    return 0;
}

// Append formatted text to user-provided buffer with capacity checks.
// On insufficient capacity, print message and return 1; otherwise 0.
static int out_cat(char **p, size_t *left, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int need = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    if (need < 0 || (size_t)need >= *left) {
        printf("Output exceeds buffer capacity.\n");
        return 1;
    }
    va_start(ap, fmt);
    int wrote = vsnprintf(*p, *left, fmt, ap);
    va_end(ap);
    *p += wrote;
    *left -= (size_t)wrote;
    return 0;
}

// Emit declarations into the output buffer.
static int print_decl_to_buf(char **p, size_t *left, const char *kw, decl_t *arr, int n) {
    for (int i = 0; i < n; ++i) {
        int w  = arr[i].width;
        int sg = arr[i].is_signed;
        const char *id = arr[i].name;
        if (w == 1) {
            if (out_cat(p, left, "  %s %s%s;\n", kw, sg ? "signed " : "", id)) return 1;
        } else {
            if (out_cat(p, left, "  %s %s[%d:0] %s;\n", kw, sg ? "signed " : "", w - 1, id)) return 1;
        }
    }
    return 0;
}

static int print_decl_single(char **p, size_t *left, const char *kw, const decl_t *decl) {
    if (out_cat(p, left, "  %s ", kw)) return 1;
    if (decl->is_signed) {
        if (out_cat(p, left, "signed ")) return 1;
    }
    if (decl->width > 1) {
        if (out_cat(p, left, "[%d:0] ", decl->width - 1)) return 1;
    }
    if (out_cat(p, left, "%s;\n", decl->name)) return 1;
    return 0;
}

static int print_decl_with_assign(char **p, size_t *left, const char *kw, const decl_t *decl, const char *rhs) {
    if (out_cat(p, left, "  %s ", kw)) return 1;
    if (decl->is_signed) {
        if (out_cat(p, left, "signed ")) return 1;
    }
    if (decl->width > 1) {
        if (out_cat(p, left, "[%d:0] ", decl->width - 1)) return 1;
    }
    if (out_cat(p, left, "%s = %s;\n", decl->name, rhs)) return 1;
    return 0;
}

static int print_inputs_short(char **p, size_t *left, decl_t *arr, int n) {
    for (int i = 0; i < n; ) {
        int w  = arr[i].width;
        int sg = arr[i].is_signed;
        if (out_cat(p, left, "  input ")) return 1;
        if (sg) {
            if (out_cat(p, left, "signed ")) return 1;
        }
        if (w > 1) {
            if (out_cat(p, left, "[%d:0] ", w - 1)) return 1;
        }
        int j = i;
        while (j < n && arr[j].width == w && arr[j].is_signed == sg) {
            if (out_cat(p, left, "%s%s", j == i ? "" : ", ", arr[j].name)) return 1;
            ++j;
        }
        if (out_cat(p, left, ";\n")) return 1;
        i = j;
    }
    return 0;
}

static decl_t *find_decl_by_name(decl_t *arr, int n, const char *name) {
    for (int i = 0; i < n; ++i) {
        if (!strcmp(arr[i].name, name))
            return &arr[i];
    }
    return NULL;
}

static int has_assignment(const mv_ctx *ctx, const char *name) {
    for (int i = 0; i < ctx->na; ++i)
        if (!strcmp(ctx->assigns[i].lhs, name))
            return 1;
    return 0;
}

// Add spaces around every alphanumeric/underscore sequence for readability.
// Example: "a*b+16'b0" -> " a * b + 16 ' b0 "
static void format_rhs_readable(const char *in, char *out, size_t cap) {
    size_t o = 0;
    for (size_t i = 0; in[i]; ) {
        unsigned char c = (unsigned char)in[i];
        if (isalnum(c) || c == '_') {
            // start of a token
            if (o + 1 >= cap) { if (o) out[o-1] = 0; else if (cap) out[0] = 0; return; }
            out[o++] = ' ';
            // copy token
            size_t j = i;
            while (in[j] && (isalnum((unsigned char)in[j]) || in[j] == '_')) {
                if (o + 1 >= cap) { out[o-1] = 0; return; }
                out[o++] = in[j++];
            }
            if (o + 1 >= cap) { out[o-1] = 0; return; }
            out[o++] = ' ';
            i = j;
        } else {
            if (o + 1 >= cap) { if (o) out[o-1] = 0; else if (cap) out[0] = 0; return; }
            out[o++] = in[i++];
        }
    }
    if (o < cap) out[o] = 0; else if (cap) out[cap-1] = 0;
}

static void trim_spaces(char *s) {
    if (!s) return;
    char *start = s;
    while (*start && isspace((unsigned char)*start))
        ++start;
    char *end = start + strlen(start);
    while (end > start && isspace((unsigned char)*(end - 1)))
        --end;
    size_t len = (size_t)(end - start);
    if (start != s)
        memmove(s, start, len);
    s[len] = 0;
}

// -----------------------------------------------------------------------------
// Parsing helpers that quote offending clauses
// -----------------------------------------------------------------------------

typedef int (*emit_fn)(mv_ctx *, const char *, int, int);

static int emit_in(mv_ctx *ctx, const char *id, int w, int sg) {
    add_decl(ctx->inputs, &ctx->ni, id, w, sg);
    return 0;
}

static int emit_wi(mv_ctx *ctx, const char *id, int w, int sg) {
    add_decl(ctx->wires, &ctx->nw, id, w, sg);
    return 0;
}

// Split an identifier list like "a,b,c" and emit each item. Quotes 'clause' in diagnostics.
static int split_ids(mv_ctx *ctx, const char *clause, const char *s, emit_fn emit, int w, int sg) {
    char buf[128];
    int  j = 0;

    for (int i = 0;; ++i) {
        char c = s[i];
        if (c == ',' || c == 0) {
            if (j == 0) {
                printf("Syntax error: empty identifier in expression \"%s\".\n", clause);
                return 1;
            }
            buf[j] = 0;
            if (emit(ctx, buf, w, sg)) return 1;
            j = 0;
            if (c == 0) break;
        } else {
            if (j >= 120) {
                printf("Identifier too long in expression \"%s\".\n", clause);
                return 1;
            }
            if (!((j ? is_ident_char(c) : is_ident_start(c)))) {
                printf("Illegal identifier in expression \"%s\".\n", clause);
                return 1;
            }
            buf[j++] = c;
        }
    }
    return 0;
}

// Parse one clause (already whitespace-stripped). On error, prints a message including the clause.
static int parse_clause(mv_ctx *ctx, const char *q) {
    if (!q || !*q) return 0;

    if (q[0] == 'm') {
        if (!is_ident_start(q[1])) {
            printf("Syntax error after 'm' in expression \"%s\".\n", q);
            return 1;
        }
        int i = 1;
        while (q[i] && is_ident_char(q[i])) ++i;
        if (q[i]) {
            printf("Garbage after module name in expression \"%s\".\n", q);
            return 1;
        }
        size_t n = (size_t)(i - 1);
        if (n >= sizeof(ctx->modname)) n = sizeof(ctx->modname) - 1;
        strncpy(ctx->modname, q + 1, n);
        ctx->modname[n] = 0;
        return 0;
    }

    if (q[0] != 'i' && q[0] != 'o' && q[0] != 'w') {
        printf("Unknown clause start in expression \"%s\".\n", q);
        return 1;
    }

    int kind = q[0];
    int i    = 1;
    int sg   = 0;
    int w    = 0;
    int nconsumed = 0;

    if (q[i] == 's') {
        sg = 1;
        ++i;
    }
    if (!parse_uint(q + i, &w, &nconsumed)) {
        printf("Width expected in expression \"%s\".\n", q);
        return 1;
    }
    i += nconsumed;
    if (w <= 0) {
        printf("Non-positive width in expression \"%s\".\n", q);
        return 1;
    }

    const char *eq = strchr(q + i, '=');

    if (kind == 'i') {
        // Support unnamed inputs: 'i4' -> auto-generate one input named a,b,c,...
        if (!q[i]) {
            char auto_name[32];
            gen_auto_in_name(ctx, auto_name, sizeof(auto_name));
            add_decl(ctx->inputs, &ctx->ni, auto_name, w, sg);
            return 0;
        }
        if (eq) {
            printf("Unexpected '=' in input clause in expression \"%s\".\n", q);
            return 1;
        }
        return split_ids(ctx, q, q + i, emit_in, w, sg);
    }

    if (kind == 'w' && !eq) {
        if (!q[i]) {
            printf("Identifiers expected for wires in expression \"%s\".\n", q);
            return 1;
        }
        return split_ids(ctx, q, q + i, emit_wi, w, sg);
    }

    if (!eq) {
        printf("Assignment expected in expression \"%s\".\n", q);
        return 1;
    }

    // Parse the LHS name for 'o' or 'w'. For 'o', allow omitted name (defaults to "o").
    char lhs[128];
    int  lj = 0;
    for (int k = i; k < (int)(eq - q); ++k) {
        char c = q[k];
        if (!lj && kind == 'o' && !is_ident_start(c)) {
            lhs[0] = 'o';
            lhs[1] = 0;
            goto lhs_done;
        }
        if (!(lj ? is_ident_char(c) : is_ident_start(c))) {
            printf("Illegal LHS identifier in expression \"%s\".\n", q);
            return 1;
        }
        if (lj >= 120) {
            printf("Identifier too long in expression \"%s\".\n", q);
            return 1;
        }
        lhs[lj++] = c;
    }
    if (lj == 0) {
        if (kind == 'o') {
            lhs[0] = 'o';
            lhs[1] = 0;
        } else {
            printf("Wire assignment needs a name in expression \"%s\".\n", q);
            return 1;
        }
    } else {
        lhs[lj] = 0;
    }
lhs_done:;
    const char *rhs = eq + 1;
    if (!*rhs) {
        printf("Empty RHS expression in expression \"%s\".\n", q);
        return 1;
    }

    if (kind == 'o') add_decl(ctx->outputs, &ctx->no, lhs, w, sg);
    if (kind == 'w') add_decl(ctx->wires,   &ctx->nw, lhs, w, sg);
    return add_asn(ctx, lhs, rhs);
}

// -----------------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------------

// Translate a raw mini-Verilog string 'input' into standard Verilog.
// The function strips whitespace internally, parses, and writes into 'out' (cap bytes).
// Returns 0 on success, 1 on error. Errors are printed (no exit()).
int miniver_translate(const char *input, char *out, size_t cap, int fShort) {
    if (!input || !out || cap == 0) {
        printf("Invalid arguments.\n");
        return 1;
    }

    // Step 1: strip whitespace (per spec).
    char flat[MAXSTR];
    strip_ws(input, flat);
    if (!*flat) {
        printf("Empty input.\n");
        return 1;
    }

    // Step 2: parse clauses into a context.
    mv_ctx *ctx = (mv_ctx*)calloc(1, sizeof(mv_ctx));
    if (!ctx) {
        printf("Out of memory.\n");
        return 1;
    }
    strncpy(ctx->modname, "top", sizeof(ctx->modname) - 1);
    ctx->next_auto_in = 0;

    // Make a modifiable copy to split on semicolons.
    char *buf = (char*)malloc(strlen(flat) + 1);
    if (!buf) {
        printf("Out of memory.\n");
        free(ctx);
        return 1;
    }
    strcpy(buf, flat);

    char *s = buf;
    while (*s) {
        char *semi = strchr(s, ';');
        if (semi) *semi = 0;
        if (parse_clause(ctx, s)) {
            free(buf);
            free(ctx);
            return 1;
        }
        if (!semi) break;
        s = semi + 1;
    }
    free(buf);

    if (!*ctx->modname) {
        printf("Module name missing.\n");
        free(ctx);
        return 1;
    }
    if (ctx->no == 0) {
        printf("At least one output with assignment is required.\n");
        free(ctx);
        return 1;
    }

    // Step 3: emit Verilog into caller buffer.
    char *p = out;
    size_t left = cap;

    if (out_cat(&p, &left, "module %s (", ctx->modname)) {
        free(ctx); return 1;
    }
    for (int i = 0; i < ctx->ni; ++i) {
        if (out_cat(&p, &left, "%s%s", i ? ", " : "", ctx->inputs[i].name)) {
            free(ctx); return 1;
        }
    }
    for (int i = 0; i < ctx->no; ++i) {
        if (out_cat(&p, &left, "%s%s", (ctx->ni || i) ? ", " : "", ctx->outputs[i].name)) {
            free(ctx); return 1;
        }
    }
    if (out_cat(&p, &left, ");\n")) {
        free(ctx); return 1;
    }

    if (!fShort) {
        if (print_decl_to_buf(&p, &left, "input",  ctx->inputs,  ctx->ni)) { free(ctx); return 1; }
        if (print_decl_to_buf(&p, &left, "output", ctx->outputs, ctx->no))  { free(ctx); return 1; }
        if (print_decl_to_buf(&p, &left, "wire",   ctx->wires,   ctx->nw))  { free(ctx); return 1; }

        for (int i = 0; i < ctx->na; ++i) {
            char rhs_sp[8192];
            format_rhs_readable(ctx->assigns[i].rhs, rhs_sp, sizeof(rhs_sp));
            if (out_cat(&p, &left, "  assign %s = %s;\n", ctx->assigns[i].lhs, rhs_sp)) {
                free(ctx); return 1;
            }
        }
    } else {
        if (print_inputs_short(&p, &left, ctx->inputs, ctx->ni)) { free(ctx); return 1; }
        for (int i = 0; i < ctx->nw; ++i) {
            if (has_assignment(ctx, ctx->wires[i].name))
                continue;
            if (print_decl_single(&p, &left, "wire", &ctx->wires[i])) {
                free(ctx); return 1;
            }
        }
        for (int i = 0; i < ctx->na; ++i) {
            char rhs_sp[8192];
            format_rhs_readable(ctx->assigns[i].rhs, rhs_sp, sizeof(rhs_sp));
            trim_spaces(rhs_sp);
            const char *kw = "wire";
            decl_t *decl = find_decl_by_name(ctx->outputs, ctx->no, ctx->assigns[i].lhs);
            if (decl) {
                kw = "output";
            } else {
                decl = find_decl_by_name(ctx->wires, ctx->nw, ctx->assigns[i].lhs);
            }
            if (decl) {
                if (print_decl_with_assign(&p, &left, kw, decl, rhs_sp)) {
                    free(ctx); return 1;
                }
            } else {
                if (out_cat(&p, &left, "  assign %s = %s;\n", ctx->assigns[i].lhs, rhs_sp)) {
                    free(ctx); return 1;
                }
            }
        }
    }
    if (out_cat(&p, &left, "endmodule\n")) {
        free(ctx); return 1;
    }

    *p = 0;
    free(ctx);
    return 0;
}

// -----------------------------------------------------------------------------
// Optional CLI wrapper (define MINIVER_LIBRARY_ONLY to omit main)
// -----------------------------------------------------------------------------
#ifndef MINIVER_LIBRARY_ONLY
int main(int argc, char **argv) {
    char in[MAXSTR] = {0};

    if (argc >= 2) {
        size_t L = strlen(argv[1]);
        if (L >= MAXSTR - 1) {
            printf("Input too long.\n");
            return 1;
        }
        strcpy(in, argv[1]);
    } else {
        size_t off = 0;
        int c = 0;
        while ((c = fgetc(stdin)) != EOF) {
            if (off >= MAXSTR - 1) {
                printf("Input too long.\n");
                return 1;
            }
            in[off++] = (char)c;
        }
        in[off] = 0;
    }

    char out[10240];
    int rc = miniver_translate(in, out, sizeof(out), 0);
    if (!rc) {
        printf("%s", out);
    }
    return rc;
}
#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
