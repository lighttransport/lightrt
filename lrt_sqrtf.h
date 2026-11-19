/*
 * lrt_sqrtf.h — portable scalar `sqrtf` built from the target ISA's
 * correctly-rounded square-root instruction (no libm call).
 *
 * Rationale
 * ---------
 * LightRT's C11 kernel needs `sqrtf` in a handful of scalar intersectors.
 * Calling the platform libm makes the result depend on the C runtime; here
 * every supported target instead issues the ISA's IEEE-754 square-root
 * instruction, which is *specified* to be correctly rounded (round-to-nearest,
 * ties-to-even) for binary32.  Consequently all targets agree bit-for-bit with
 * each other and with the formal binary32 model in
 * `formal/LightRT/FP/Binary32.lean` (`sqrtBits`).
 *
 * Targets
 * -------
 *   x86-64 SSE / SSE2 / AVX / AVX2 : SQRTSS (_mm_sqrt_ss)
 *   ARM64 NEON                     : FSQRT (vsqrtq_f32, lane 0)
 *   fallback (other targets)       : libm sqrtf (also IEEE correctly rounded)
 *
 * No FTZ/DAZ is assumed (the rest of the kernel assumes the same default
 * MXCSR/FPCR), so subnormal inputs and outputs follow IEEE-754.  Negative
 * finite inputs produce the default NaN with the invalid flag, exactly like
 * C `sqrtf`; sqrt(-0) = -0 and sqrt(+inf) = +inf.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRT_SQRTF_H
#define LRT_SQRTF_H

#include <math.h>

#if defined(__SSE__) || defined(__SSE2__) || defined(__AVX__) || defined(__AVX2__)
#include <xmmintrin.h>
/* SQRTSS: SSE1 scalar sqrt, correctly rounded; AVX/AVX2 encode the same
 * instruction (VEX-encoded vsqrtss) and produce identical bits. */
static inline float lrt_sqrtf(float x) {
    return _mm_cvtss_f32(_mm_sqrt_ss(_mm_set_ss(x)));
}
#define LRT_SQRTF_IMPL "sqrtss"
#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
#include <arm_neon.h>
/* FSQRT on lane 0: ARMv8 NEON scalar-path sqrt, correctly rounded. */
static inline float lrt_sqrtf(float x) {
    return vgetq_lane_f32(vsqrtq_f32(vdupq_n_f32(x)), 0);
}
#define LRT_SQRTF_IMPL "vsqrt.f32"
#else
static inline float lrt_sqrtf(float x) { return sqrtf(x); }
#define LRT_SQRTF_IMPL "libm"
#endif

#endif /* LRT_SQRTF_H */
