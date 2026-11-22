/*
 * test_lrt_sqrtf.c — bit-exactness of lrt_sqrtf against IEEE-754 sqrtf.
 *
 * Build:  make test_lrt_sqrtf && ./test_lrt_sqrtf
 * (or)    cc -O2 -msse2 -I. tests/test_lrt_sqrtf.c -lm -o /tmp/test_lrt_sqrtf
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include "lrt_sqrtf.h"

static uint32_t bits(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }
static float frombits(uint32_t u) { float x; memcpy(&x, &u, 4); return x; }
static int is_nan_bits(uint32_t u) { return ((u & 0x7f800000u) == 0x7f800000u) && ((u & 0x7fffffu) != 0); }

/* libm reference; kept in its own translation-unit-local wrapper so the
 * compiler cannot constant-fold and conflate it with lrt_sqrtf. */
static float libm_sqrtf(float x) { volatile float v = x; return sqrtf(v); }

int main(void) {
    static const uint32_t special[] = {
        0x00000000u, /* +0 */
        0x80000000u, /* -0 */
        0x00000001u, /* smallest subnormal */
        0x007fffffu, /* largest subnormal */
        0x00800000u, /* smallest normal */
        0x3f800000u, /* 1 */
        0x40000000u, /* 2 */
        0x7f7fffffu, /* largest finite */
        0x7f800000u, /* +inf */
        0xff800000u, /* -inf */
        0x7fc00000u, /* quiet NaN */
        0x7f800001u, /* signalling NaN */
        0xbf800000u, /* -1 */
        0xc0400000u, /* -2 */
    };
    size_t i;
    uint64_t n = 0, bad = 0, nan_cases = 0;
    for (i = 0; i < sizeof(special) / sizeof(special[0]); ++i) {
        float x = frombits(special[i]);
        float a = lrt_sqrtf(x), b = libm_sqrtf(x);
        uint32_t ua = bits(a), ub = bits(b);
        ++n;
        if (is_nan_bits(ua) || is_nan_bits(ub)) {
            ++nan_cases;
            if (is_nan_bits(ua) != is_nan_bits(ub)) { ++bad; printf("NaN mismatch in=%08x got=%08x ref=%08x\n", special[i], ua, ub); }
        } else if (ua != ub) {
            ++bad; printf("mismatch in=%08x got=%08x ref=%08x\n", special[i], ua, ub);
        }
    }
    /* Sweep every exponent and a set of mantissas, both signs. */
    uint32_t e, m;
    static const uint32_t mants[] = { 0u, 1u, 2u, 0x123456u, 0x400000u, 0x7fffffu };
    for (e = 0; e < 255; ++e) {
        for (i = 0; i < sizeof(mants) / sizeof(mants[0]); ++i) {
            uint32_t s;
            for (s = 0; s < 2; ++s) {
                uint32_t in = (s << 31) | (e << 23) | (mants[i] & 0x7fffffu);
                float x = frombits(in);
                float a = lrt_sqrtf(x), b = libm_sqrtf(x);
                uint32_t ua = bits(a), ub = bits(b);
                ++n;
                if (is_nan_bits(ua) || is_nan_bits(ub)) {
                    ++nan_cases;
                    if (is_nan_bits(ua) != is_nan_bits(ub)) { ++bad; if (bad < 10) printf("NaN mismatch in=%08x got=%08x ref=%08x\n", in, ua, ub); }
                } else if (ua != ub) {
                    ++bad; if (bad < 10) printf("mismatch in=%08x got=%08x ref=%08x\n", in, ua, ub);
                }
            }
        }
    }
    /* Deterministic pseudo-random sweep. */
    uint32_t rng = 0x12345678u;
    for (i = 0; i < 200000; ++i) {
        rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
        float x = frombits(rng);
        float a = lrt_sqrtf(x), b = libm_sqrtf(x);
        uint32_t ua = bits(a), ub = bits(b);
        ++n;
        if (is_nan_bits(ua) || is_nan_bits(ub)) {
            ++nan_cases;
            if (is_nan_bits(ua) != is_nan_bits(ub)) { ++bad; if (bad < 10) printf("NaN mismatch in=%08x got=%08x ref=%08x\n", rng, ua, ub); }
        } else if (ua != ub) {
            ++bad; if (bad < 10) printf("mismatch in=%08x got=%08x ref=%08x\n", rng, ua, ub);
        }
    }
    printf("lrt_sqrtf impl=%s cases=%llu nan_cases=%llu mismatches=%llu : %s\n",
           LRT_SQRTF_IMPL, (unsigned long long)n, (unsigned long long)nan_cases,
           (unsigned long long)bad, bad ? "FAIL" : "PASS");
    (void)m;
    return bad ? 1 : 0;
}
