#include "pathtrace.h"
#include <math.h>
#include <stdio.h>

int main(void) {
    if (mtlx_pixel_offset(0.0f,0) != 0.0f || mtlx_pixel_offset(1.0f,0) != 1.0f ||
        mtlx_pixel_offset(0.0f,1) != -0.5f || mtlx_pixel_offset(0.5f,1) != 0.5f ||
        mtlx_pixel_offset(1.0f,1) != 1.5f) return 1;
    double mean=0.0, variance=0.0;
    const int n=100000;
    for (int i=0;i<n;++i) {
        float u=(i+0.5f)/n, x=mtlx_pixel_offset(u,1);
        if (fabsf(x+mtlx_pixel_offset(1.0f-u,1)-1.0f)>1e-5f) return 1;
        mean+=x; variance+=(x-0.5f)*(x-0.5f);
    }
    if (fabs(mean/n-0.5)>1e-5 || fabs(variance/n-1.0/6.0)>1e-5) return 1;
    puts("PASS: box and tent pixel filter distributions");
    return 0;
}
