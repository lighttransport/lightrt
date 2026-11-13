/*
 * lean_vectors.c - replay Lean-generated MaterialX node evaluation vectors.
 *
 * tests/generated/mtlx-eval.inc is produced by the Lean 4 model of the
 * MaterialX standard nodes in the materialx-conformance repository
 * (`lake exe mtlxspec-gen`); each row is a nodegraph body, a node name and
 * the exact rational value the specification gives that node's output. The
 * body goes through the real parse -> doc -> eval path and the float result
 * is compared with the rational within a small tolerance.
 *
 * Usage: lean_vectors [-v] [--xfail FILE]
 *   --xfail FILE lists vector ids that are known to differ (one id per line,
 *   `#` comments). A listed id that passes is an error, so the list can only
 *   shrink.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mtlx_doc.h"
#include "mtlx_eval.h"
#include "vecmath.h"

static int g_total = 0, g_fail = 0, g_xfail = 0, g_xpass = 0, g_verbose = 0, g_no_expected = 0;
static int g_xfail_ids[1024];
static int g_nxfail = 0;

static int is_xfail(int id) {
    for (int i = 0; i < g_nxfail; i++) if (g_xfail_ids[i] == id) return 1;
    return 0;
}

static double rat(const char *s, const char **end) {
    char *e;
    double n = strtod(s, &e), d = 1.0;
    if (*e == '/') d = strtod(e + 1, &e);
    *end = e;
    return n / d;
}

static int parse_payload(const char *s, double *out, int cap) {
    int n = 0;
    while (*s && n < cap) {
        const char *e;
        out[n++] = rat(s, &e);
        s = (*e == ',') ? e + 1 : e;
        if (e == s && *s) break;
    }
    return n;
}

static double g_tol = 1e-5;

static int close_enough(double got, double want) {
    double tol = g_tol * fmax(1.0, fabs(want));
    return fabs(got - want) <= tol;
}

static void check_eval(int id, const char *body, const char *node, int defined,
                       const char *kind, const char *payload) {
    g_total++;
    char *buf = malloc(strlen(body) + 256);
    sprintf(buf, "<?xml version=\"1.0\"?>\n<materialx version=\"1.39\">\n"
                 "<nodegraph name=\"t\">\n%s\n</nodegraph>\n</materialx>\n", body);
    MtlxDoc *d = mtlx_load_string(buf);
    free(buf);
    char why[256] = "";
    int ok = 0;
    MtlxValue r;
    memset(&r, 0, sizeof(r));
    if (!d) {
        snprintf(why, sizeof(why), "document did not load");
    } else {
        int nid = mtlx_find_node(d, 0, node);
        if (nid < 0) {
            snprintf(why, sizeof(why), "node not found");
        } else {
            ShadeContext ctx;
            memset(&ctx, 0, sizeof(ctx));
            ctx.doc = d;
            ctx.Ns = v3_make(0, 1, 0); ctx.Ng = ctx.Ns;
            ctx.dpdu = v3_make(1, 0, 0); ctx.dpdv = v3_make(0, 0, 1);
            size_t n = (size_t)(d->nnode > 0 ? d->nnode : 1);
            ctx.memo = malloc(sizeof(MtlxValue) * n);
            ctx.memo_done = malloc(n);
            r = mtlx_eval_node_test(&ctx, nid);
            free(ctx.memo); free(ctx.memo_done);
            double want[16];
            int nw = parse_payload(payload, want, 16);
            if (!defined) {
                ++g_no_expected;
                ok = 1; /* parsed successfully; no expected value to compare */
            } else if (!strcmp(kind, "num") || !strcmp(kind, "int") || !strcmp(kind, "bool")) {
                double w = !strcmp(kind, "bool") ? (!strcmp(payload, "true") ? 1.0 : 0.0) : want[0];
                ok = close_enough(r.v[0], w);
                if (!ok) snprintf(why, sizeof(why), "got %.7g want %.7g", r.v[0], w);
            } else if (!strcmp(kind, "agg")) {
                ok = 1;
                for (int i = 0; i < nw; i++) {
                    /* matrices: both the vectors and MtlxValue hold the
                     * sixteen (nine) numbers in value-string order */
                    if (!close_enough(r.v[i], want[i])) {
                        ok = 0;
                        snprintf(why, sizeof(why), "channel %d: got %.7g want %.7g", i, r.v[i], want[i]);
                        break;
                    }
                }
            } else {
                snprintf(why, sizeof(why), "unsupported kind %s", kind);
            }
        }
        mtlx_free(d);
    }
    if (is_xfail(id)) {
        if (ok) { g_xpass++; printf("XPASS %d (listed as a known difference but agrees)\n", id); }
        else { g_xfail++; if (g_verbose) printf("xfail %d: %s\n", id, why); }
        return;
    }
    if (!ok) {
        g_fail++;
        printf("FAIL %d: %s\n     %s\n", id, why, body);
    } else if (g_verbose) {
        printf("ok   %d\n", id);
    }
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-v")) g_verbose = 1;
        else if (!strcmp(argv[i], "--xfail") && i + 1 < argc) {
            FILE *f = fopen(argv[++i], "r");
            if (!f) { fprintf(stderr, "cannot open %s\n", argv[i]); return 2; }
            char line[256];
            while (fgets(line, sizeof(line), f)) {
                char *p = line;
                while (*p == ' ') p++;
                if (*p >= '0' && *p <= '9' && g_nxfail < 1024) g_xfail_ids[g_nxfail++] = atoi(p);
            }
            fclose(f);
        }
    }
#define MTLX_EVAL(id, body, node, defined, kind, payload) \
    check_eval(id, body, node, defined, kind, payload);
#include "generated/mtlx-eval.inc"
#undef MTLX_EVAL
    /* Nodes defined over the reals: the payload is a binary64 evaluation of
     * the formula; binary32 library functions get a wider tolerance. Ids are
     * offset so the xfail list can name them. */
    g_tol = 1e-4;
#define MTLX_EVAL_APPROX(id, body, node, payload) \
    check_eval(100000 + id, body, node, 1, strchr(payload, ',') ? "agg" : "num", payload);
#include "generated/mtlx-eval-approx.inc"
#undef MTLX_EVAL_APPROX
    printf("lean_vectors: %d vectors, %d without expected values, %d failures, %d known differences, %d unexpected passes\n",
           g_total, g_no_expected, g_fail, g_xfail, g_xpass);
    return (g_fail || g_xpass) ? 1 : 0;
}
