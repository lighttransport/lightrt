// SPDX-License-Identifier: MIT
// Copyright 2025 - Present, Light Transport Entertainment Inc.
// lightrt_hipew - see lightrt_hipew.h.
#include "lightrt_hipew.h"

#include <dlfcn.h>
#include <stdlib.h>

#define LRT_HIPEW_DEF(name) lrt_pfn_##name lrt_hipew_##name = NULL;
LRT_HIPEW_FUNCS(LRT_HIPEW_DEF)
LRT_HIPEW_RTC_FUNCS(LRT_HIPEW_DEF)
#undef LRT_HIPEW_DEF

static void *lrt_hipew_open(const char *env, const char *const *names) {
    const char *p = getenv(env);
    if (p && p[0]) {
        void *h = dlopen(p, RTLD_NOW | RTLD_LOCAL);
        if (h) return h;
    }
    for (int i = 0; names[i]; i++) {
        void *h = dlopen(names[i], RTLD_NOW | RTLD_LOCAL);
        if (h) return h;
    }
    return NULL;
}

int hipewInit(uint32_t flags) {
    static void *lib_hip = NULL, *lib_rtc = NULL;
    if (flags & HIPEW_INIT_HIP) {
        static const char *const names[] = {"libamdhip64.so", "libamdhip64.so.7",
                                            "libamdhip64.so.6", "/opt/rocm/lib/libamdhip64.so", NULL};
        if (!lib_hip) lib_hip = lrt_hipew_open("LRT_HIP_LIB", names);
        if (!lib_hip) return HIPEW_ERROR_OPEN_FAILED;
#define LRT_HIPEW_LOAD(name)                                                   \
        lrt_hipew_##name = (lrt_pfn_##name)dlsym(lib_hip, #name);              \
        if (!lrt_hipew_##name) return HIPEW_ERROR_OPEN_FAILED;
        LRT_HIPEW_FUNCS(LRT_HIPEW_LOAD)
#undef LRT_HIPEW_LOAD
    }
    if (flags & HIPEW_INIT_HIPRTC) {
        static const char *const names[] = {"libhiprtc.so", "libhiprtc.so.7",
                                            "libhiprtc.so.6", "/opt/rocm/lib/libhiprtc.so", NULL};
        if (!lib_rtc) lib_rtc = lrt_hipew_open("LRT_HIPRTC_LIB", names);
        if (!lib_rtc) return HIPEW_ERROR_OPEN_FAILED;
#define LRT_HIPEW_LOAD(name)                                                   \
        lrt_hipew_##name = (lrt_pfn_##name)dlsym(lib_rtc, #name);              \
        if (!lrt_hipew_##name) return HIPEW_ERROR_OPEN_FAILED;
        LRT_HIPEW_RTC_FUNCS(LRT_HIPEW_LOAD)
#undef LRT_HIPEW_LOAD
    }
    return HIPEW_SUCCESS;
}
