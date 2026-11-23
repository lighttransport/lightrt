/* EXT-001 prototype: certified-weight GGX sampling kernel.
 * See materialx-conformance/issues/spec-extension/EXT-001-certified-energy-bsdf.md
 * and doc/validation/joint-weight-envelope-2026-11-23.md there.
 */
#include "certified_bsdf.h"
#include "cert_surrogate_table.h"
#include <math.h>
#include <stdio.h>
#include <string.h>

/* Piece lookup by name.  Production should cache these indices once per shader
 * instance; the prototype keeps the named lookup for clarity and regeneration
 * robustness. */
static const cert_surrogate_piece *piece(const char *name) {
    for (int i = 0; i < CERT_SURROGATE_COUNT; ++i)
        if (strcmp(cert_surrogate_pieces[i].name, name) == 0)
            return &cert_surrogate_pieces[i];
    return 0;
}

float cert_smith_lambda(float x) {
    if (!(x > 0.0f)) return 0.0f;
    if (x <= 1.0f) return cert_surrogate_eval(piece("lambda_0_1"), x);
    if (x <= 4.0f) return cert_surrogate_eval(piece("lambda_1_4"), x);
    /* Large-x asymptotic: Lambda = x/2 - 1/2 + r(1/x)/x. */
    float t = 1.0f / x;
    float r = cert_surrogate_eval(piece("lambda_tail_r"), t);
    return 0.5f * x - 0.5f + r / x;
}

float cert_fresnel_reflectance(float c, float eta) {
    const int entering = eta <= 1.0f;
    const char *tag = entering
        ? (fabsf(eta - 0.6666667f) < fabsf(eta - 0.625f) ? "enter15" : "enter16")
        : (fabsf(eta - 1.5f) < fabsf(eta - 1.6f) ? "exit15" : "exit16");
    if (entering) {
        char name[32];
        if (c < 0.3f) snprintf(name, sizeof name, "fres_%s_a", tag);
        else if (c < 0.6f) snprintf(name, sizeof name, "fres_%s_b", tag);
        else snprintf(name, sizeof name, "fres_%s_c", tag);
        return cert_surrogate_eval(piece(name), c);
    }
    /* Exiting: TIR is exact; the critical band uses the q=sqrt(c-c_crit) spline
     * for 1-F so no sqrt(1-eta^2(1-c^2)) cancellation is ever evaluated. */
    float inv_eta2 = 1.0f / (eta * eta);
    float ccrit = sqrtf(fmaxf(0.0f, 1.0f - inv_eta2));
    if (c <= ccrit) return 1.0f;
    if (c < ccrit + 0.05f) {
        float q = sqrtf(c - ccrit);
        char name[32];
        snprintf(name, sizeof name, "delta_%s", tag);
        float one_minus_f = cert_surrogate_eval(piece(name), q);
        return 1.0f - one_minus_f;
    }
    char name[32];
    snprintf(name, sizeof name, c < 0.9f ? "fres_%s_a" : "fres_%s_b", tag);
    return cert_surrogate_eval(piece(name), c);
}

void cert_composed_weights(float x_v, float x_l, float c, float eta,
                           float *w_r, float *w_t) {
    float lv = cert_smith_lambda(x_v);
    float ll = cert_smith_lambda(x_l);
    float ratio = (1.0f + lv) / (1.0f + lv + ll);
    float f = cert_fresnel_reflectance(c, eta);
    *w_r = f * ratio;
    *w_t = (1.0f - f) * ratio;
}
