// SPDX-License-Identifier: MIT
// Copyright 2025 - Present, Light Transport Entertainment Inc.
//
// lightrt_hipew - minimal HIP + hiprtc runtime loader for lightrt_c_hip.c
// (the hiprtc Path-A trace). Like lightrt_vkew: no ROCm SDK headers, no
// link-time -lamdhip64 / -lhiprtc; libamdhip64 and libhiprtc are dlopen'd at
// runtime and only the ~20 entry points lightrt_c_hip.c uses are declared.
// The types and enum values mirror the ROCm ABI (hip_runtime_api.h, hiprtc.h).
#ifndef LIGHTRT_HIPEW_H
#define LIGHTRT_HIPEW_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef int hipError_t;            /* hipSuccess == 0 */
typedef int hipDevice_t;
typedef struct ihipModule_t *hipModule_t;
typedef struct ihipModuleSymbol_t *hipFunction_t;
typedef struct ihipStream_t *hipStream_t;
typedef void *hipDeviceptr_t;
typedef int hiprtcResult;          /* HIPRTC_SUCCESS == 0 */
typedef struct _hiprtcProgram *hiprtcProgram;

#define hipSuccess 0
#define HIPRTC_SUCCESS 0

typedef hipError_t (*lrt_pfn_hipInit)(unsigned int);
typedef hipError_t (*lrt_pfn_hipGetDeviceCount)(int *);
typedef hipError_t (*lrt_pfn_hipSetDevice)(int);
typedef hipError_t (*lrt_pfn_hipDeviceGet)(hipDevice_t *, int);
typedef hipError_t (*lrt_pfn_hipDeviceGetName)(char *, int, hipDevice_t);
typedef hipError_t (*lrt_pfn_hipDeviceSynchronize)(void);
typedef hipError_t (*lrt_pfn_hipMalloc)(void **, size_t);
typedef hipError_t (*lrt_pfn_hipFree)(void *);
typedef hipError_t (*lrt_pfn_hipMemcpyHtoD)(hipDeviceptr_t, void *, size_t);
typedef hipError_t (*lrt_pfn_hipMemcpyDtoH)(void *, hipDeviceptr_t, size_t);
typedef hipError_t (*lrt_pfn_hipModuleLoadData)(hipModule_t *, const void *);
typedef hipError_t (*lrt_pfn_hipModuleUnload)(hipModule_t);
typedef hipError_t (*lrt_pfn_hipModuleGetFunction)(hipFunction_t *, hipModule_t, const char *);
typedef hipError_t (*lrt_pfn_hipModuleLaunchKernel)(hipFunction_t, unsigned int, unsigned int,
                                                     unsigned int, unsigned int, unsigned int,
                                                     unsigned int, unsigned int, hipStream_t,
                                                     void **, void **);
typedef hiprtcResult (*lrt_pfn_hiprtcCreateProgram)(hiprtcProgram *, const char *, const char *,
                                                    int, const char **, const char **);
typedef hiprtcResult (*lrt_pfn_hiprtcCompileProgram)(hiprtcProgram, int, const char **);
typedef hiprtcResult (*lrt_pfn_hiprtcDestroyProgram)(hiprtcProgram *);
typedef hiprtcResult (*lrt_pfn_hiprtcGetProgramLogSize)(hiprtcProgram, size_t *);
typedef hiprtcResult (*lrt_pfn_hiprtcGetProgramLog)(hiprtcProgram, char *);
typedef hiprtcResult (*lrt_pfn_hiprtcGetCodeSize)(hiprtcProgram, size_t *);
typedef hiprtcResult (*lrt_pfn_hiprtcGetCode)(hiprtcProgram, char *);

#define LRT_HIPEW_FUNCS(X)                                                     \
    X(hipInit) X(hipGetDeviceCount) X(hipSetDevice) X(hipDeviceGet)            \
    X(hipDeviceGetName) X(hipDeviceSynchronize) X(hipMalloc) X(hipFree)        \
    X(hipMemcpyHtoD) X(hipMemcpyDtoH) X(hipModuleLoadData) X(hipModuleUnload)  \
    X(hipModuleGetFunction) X(hipModuleLaunchKernel)
#define LRT_HIPEW_RTC_FUNCS(X)                                                 \
    X(hiprtcCreateProgram) X(hiprtcCompileProgram) X(hiprtcDestroyProgram)     \
    X(hiprtcGetProgramLogSize) X(hiprtcGetProgramLog) X(hiprtcGetCodeSize)     \
    X(hiprtcGetCode)

#define LRT_HIPEW_DECL(name) extern lrt_pfn_##name lrt_hipew_##name;
LRT_HIPEW_FUNCS(LRT_HIPEW_DECL)
LRT_HIPEW_RTC_FUNCS(LRT_HIPEW_DECL)
#undef LRT_HIPEW_DECL

/* Call sites use the plain HIP names. */
#define hipInit lrt_hipew_hipInit
#define hipGetDeviceCount lrt_hipew_hipGetDeviceCount
#define hipSetDevice lrt_hipew_hipSetDevice
#define hipDeviceGet lrt_hipew_hipDeviceGet
#define hipDeviceGetName lrt_hipew_hipDeviceGetName
#define hipDeviceSynchronize lrt_hipew_hipDeviceSynchronize
#define hipMalloc lrt_hipew_hipMalloc
#define hipFree lrt_hipew_hipFree
#define hipMemcpyHtoD lrt_hipew_hipMemcpyHtoD
#define hipMemcpyDtoH lrt_hipew_hipMemcpyDtoH
#define hipModuleLoadData lrt_hipew_hipModuleLoadData
#define hipModuleUnload lrt_hipew_hipModuleUnload
#define hipModuleGetFunction lrt_hipew_hipModuleGetFunction
#define hipModuleLaunchKernel lrt_hipew_hipModuleLaunchKernel
#define hiprtcCreateProgram lrt_hipew_hiprtcCreateProgram
#define hiprtcCompileProgram lrt_hipew_hiprtcCompileProgram
#define hiprtcDestroyProgram lrt_hipew_hiprtcDestroyProgram
#define hiprtcGetProgramLogSize lrt_hipew_hiprtcGetProgramLogSize
#define hiprtcGetProgramLog lrt_hipew_hiprtcGetProgramLog
#define hiprtcGetCodeSize lrt_hipew_hiprtcGetCodeSize
#define hiprtcGetCode lrt_hipew_hiprtcGetCode

#define HIPEW_INIT_HIP 1u
#define HIPEW_INIT_HIPRTC 2u
#define HIPEW_SUCCESS 0
#define HIPEW_ERROR_OPEN_FAILED (-1)
#define HIPEW_ERROR_ATEXIT_FAILED (-2)

/* Load the requested libraries (idempotent). Returns HIPEW_SUCCESS or < 0.
 * LRT_HIP_LIB / LRT_HIPRTC_LIB override the library paths. */
int hipewInit(uint32_t flags);

#ifdef __cplusplus
}
#endif
#endif /* LIGHTRT_HIPEW_H */
