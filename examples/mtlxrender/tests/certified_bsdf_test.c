/* EXT-001 prototype test: composed sampling weights against exact vectors.
 * Generated vectors come from materialx-conformance/scripts/lobe-error/gen_cert_vectors.py.
 * Budget: max absolute error of W_R and W_T <= 2e-3 (the ~1.05e-3 ledger plus
 * composition slack); the measured error should be well below it.
 */
#include <math.h>
#include <stdio.h>
#include "certified_bsdf.h"
#include "generated/certified-weight-vectors.inc"

static int max_err_printed = 0;

#define CHECK(MUV, MUL, A, ETA, C, WR, WT)                                      \
  {                                                                              \
    double muv = (MUV), mul = (MUL), a = (A), eta = (ETA), c = (C);              \
    float xv = (float)(a * sqrt(1.0 - muv * muv) / muv);                         \
    float xl = (float)(a * sqrt(1.0 - mul * mul) / mul);                         \
    float wr, wt;                                                                \
    cert_composed_weights(xv, xl, (float)c, (float)eta, &wr, &wt);               \
    double er = fabs((double)wr - (WR)), et = fabs((double)wt - (WT));           \
    if (er > worst_r) { worst_r = er; worst_r_row = __LINE__; }                   \
    if (et > worst_t) { worst_t = et; worst_t_row = __LINE__; }                   \
    if (!isfinite(wr) || !isfinite(wt) || er > 2e-3 || et > 2e-3) {              \
      if (max_err_printed++ < 8)                                                 \
        printf("FAIL row %d: mu=%g/%g a=%g eta=%g c=%.9g wr=%.9g/%.9g wt=%.9g/%.9g\n", \
               __LINE__, muv, mul, a, eta, c, wr, (WR), wt, (WT));               \
      failures++;                                                                 \
    }                                                                             \
    ++n;                                                                          \
  }

int main(void) {
    double worst_r = 0.0, worst_t = 0.0;
    int worst_r_row = 0, worst_t_row = 0;
    int failures = 0;
    long n = 0;
    CERT_WEIGHT_VECTORS(CHECK)
    printf("certified-weight prototype: %ld vectors, max |dWR|=%.3e (row %d), "
           "max |dWT|=%.3e (row %d): %s\n",
           n, worst_r, worst_r_row, worst_t, worst_t_row,
           failures ? "FAIL" : "ok");
    return failures ? 1 : 0;
}
