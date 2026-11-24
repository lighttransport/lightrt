// SPDX-License-Identifier: MIT
// Copyright 2025 - Present, Light Transport Entertainment Inc.
// lightrt_hipew - see lightrt_hipew.h.
#include "lightrt_hipew.h"

#include <dirent.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LRT_HIPEW_DEF(name) lrt_pfn_##name lrt_hipew_##name = NULL;
LRT_HIPEW_FUNCS(LRT_HIPEW_DEF)
LRT_HIPEW_RTC_FUNCS(LRT_HIPEW_DEF)
#undef LRT_HIPEW_DEF

/* ROCm may be installed as versioned roots, e.g. /opt/rocm/core-10.1/lib
 * (Ubuntu's rocm metapackage); /opt/rocm/lib is often the legacy layout or
 * absent. Parse "core-10.1" as 10.1 so the newest root wins, not the
 * lexicographically largest ("core-7.14" < "core-10.1" as text). */
static void lrt_hipew_ver(const char *s, int v[3]) {
    v[0] = v[1] = v[2] = 0;
    int i = 0;
    while (*s && i < 3) {
        while (*s && (*s < '0' || *s > '9')) s++;
        if (!*s) break;
        v[i++] = atoi(s);
        while (*s >= '0' && *s <= '9') s++;
        if (*s == '.') s++;
    }
}

static void *lrt_hipew_try_dir(const char *dir, const char *const *names) {
    for (int i = 0; names[i]; i++) {
        if (names[i][0] == '/') continue; /* absolute entry tried already */
        char path[1024];
        snprintf(path, sizeof path, "%s/%s", dir, names[i]);
        void *h = dlopen(path, RTLD_NOW | RTLD_LOCAL);
        if (h) return h;
    }
    return NULL;
}

/* Newest /opt/rocm/<root>/lib that provides one of `names`. */
static void *lrt_hipew_open_rocm(const char *const *names) {
    const char *base = "/opt/rocm";
    void *h = lrt_hipew_try_dir("/opt/rocm/lib", names);
    if (h) return h;
    DIR *d = opendir(base);
    if (!d) return NULL;
    char dirs[64][512];
    int vers[64][3];
    int nd = 0;
    struct dirent *e;
    while ((e = readdir(d)) && nd < 64) {
        if (e->d_name[0] == '.') continue;
        lrt_hipew_ver(e->d_name, vers[nd]);
        snprintf(dirs[nd], sizeof dirs[nd], "%s/%s/lib", base, e->d_name);
        nd++;
    }
    closedir(d);
    /* Insertion sort: newest version first. */
    for (int i = 1; i < nd; i++) {
        char d0[512];
        int v0[3];
        snprintf(d0, sizeof d0, "%s", dirs[i]);
        v0[0] = vers[i][0]; v0[1] = vers[i][1]; v0[2] = vers[i][2];
        int j = i - 1;
        while (j >= 0 && (vers[j][0] < v0[0] ||
               (vers[j][0] == v0[0] && (vers[j][1] < v0[1] ||
                (vers[j][1] == v0[1] && vers[j][2] < v0[2]))))) {
            snprintf(dirs[j + 1], sizeof dirs[j + 1], "%s", dirs[j]);
            vers[j + 1][0] = vers[j][0]; vers[j + 1][1] = vers[j][1]; vers[j + 1][2] = vers[j][2];
            j--;
        }
        snprintf(dirs[j + 1], sizeof dirs[j + 1], "%s", d0);
        vers[j + 1][0] = v0[0]; vers[j + 1][1] = v0[1]; vers[j + 1][2] = v0[2];
    }
    for (int i = 0; i < nd; i++) {
        h = lrt_hipew_try_dir(dirs[i], names);
        if (h) return h;
    }
    return NULL;
}

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
    return lrt_hipew_open_rocm(names);
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
