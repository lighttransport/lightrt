/*
 * timing.h — monotonic-clock helpers for the C benchmark harness.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef LRTBENCH_TIMING_H
#define LRTBENCH_TIMING_H

#include <stdint.h>
#include <time.h>

static inline uint64_t bench_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static inline double bench_ns_to_ms(uint64_t ns) { return (double)ns / 1.0e6; }
static inline double bench_ns_to_s(uint64_t ns) { return (double)ns / 1.0e9; }

#endif /* LRTBENCH_TIMING_H */
