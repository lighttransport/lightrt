/*
 * framebuffer.h - HDR accumulation buffer + EXR / PNG output.
 */
#ifndef MTLXRENDER_FRAMEBUFFER_H_
#define MTLXRENDER_FRAMEBUFFER_H_

#include "vecmath.h"
#include "color.h"

typedef struct {
    int   w, h;
    v3   *accum;     /* sum of radiance per pixel */
    int  *nsamp;     /* samples per pixel */
} Framebuffer;

void fb_init(Framebuffer *fb, int w, int h);
void fb_free(Framebuffer *fb);
static inline void fb_add(Framebuffer *fb, int x, int y, v3 c) {
    int i = y * fb->w + x;
    if (v3_is_finite(c)) { fb->accum[i] = v3_add(fb->accum[i], c); fb->nsamp[i]++; }
    else { fb->nsamp[i]++; } /* count the sample, drop the NaN */
}

/* Write linear HDR RGB as float EXR. Returns 0 on success. */
int fb_write_exr(const Framebuffer *fb, const char *path);

/* Write a tonemapped 8-bit sRGB PNG preview. Returns 0 on success. */
int fb_write_png(const Framebuffer *fb, const char *path, tonemap_kind tm, float exposure);

/* Write a plain linear->sRGB 8-bit PNG with an exposure scale (NO ACES tonemap).
 * Matches MaterialXView's framebuffer encoding for the verify harness. */
int fb_write_png_srgb(const Framebuffer *fb, const char *path, float exposure);

#endif /* MTLXRENDER_FRAMEBUFFER_H_ */
