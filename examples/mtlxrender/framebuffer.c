#include "framebuffer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "exr.h"
#include "stb_image_write.h"

void fb_init(Framebuffer *fb, int w, int h) {
    fb->w = w; fb->h = h;
    fb->accum = (v3 *)calloc((size_t)w * h, sizeof(v3));
    fb->nsamp = (int *)calloc((size_t)w * h, sizeof(int));
}

void fb_free(Framebuffer *fb) {
    if (!fb) return;
    free(fb->accum); free(fb->nsamp);
    fb->accum = NULL; fb->nsamp = NULL;
}

static v3 fb_resolve(const Framebuffer *fb, int i) {
    int n = fb->nsamp[i];
    return n > 0 ? v3_scale(fb->accum[i], 1.0f / n) : v3_splat(0.0f);
}

int fb_write_exr(const Framebuffer *fb, const char *path) {
    int W = fb->w, H = fb->h;
    size_t npx = (size_t)W * H;
    /* planar channels, sorted by name: B, G, R */
    float *B = (float *)malloc(npx * sizeof(float));
    float *G = (float *)malloc(npx * sizeof(float));
    float *R = (float *)malloc(npx * sizeof(float));
    for (size_t i = 0; i < npx; i++) {
        v3 c = fb_resolve(fb, (int)i);
        R[i] = c.x; G[i] = c.y; B[i] = c.z;
    }

    exr_channel channels[3];
    memset(channels, 0, sizeof(channels));
    const char *names[3] = {"B", "G", "R"};
    for (int c = 0; c < 3; c++) {
        snprintf(channels[c].name, sizeof(channels[c].name), "%s", names[c]);
        channels[c].pixel_type = EXR_PIXEL_FLOAT;
        channels[c].x_sampling = 1;
        channels[c].y_sampling = 1;
        channels[c].p_linear = 1;
    }
    void *images[3] = {B, G, R};

    exr_header hdr;
    memset(&hdr, 0, sizeof(hdr));
    hdr.part_type = 0; /* scanline */
    hdr.compression = EXR_COMPRESSION_NONE;
    hdr.line_order = 0;
    hdr.data_window.min_x = 0; hdr.data_window.min_y = 0;
    hdr.data_window.max_x = W - 1; hdr.data_window.max_y = H - 1;
    hdr.display_window = hdr.data_window;
    hdr.pixel_aspect_ratio = 1.0f;
    hdr.screen_window_width = 1.0f;
    hdr.num_channels = 3;
    hdr.channels = channels;

    exr_part part;
    memset(&part, 0, sizeof(part));
    part.header = hdr;
    part.width = W; part.height = H;
    part.images = images;

    exr_image img;
    memset(&img, 0, sizeof(img));
    img.num_parts = 1;
    img.parts = &part;

    exr_result r = exr_save_to_file(path, &img, EXR_COMPRESSION_NONE);
    free(B); free(G); free(R);
    if (!EXR_OK(r)) { fprintf(stderr, "exr: save failed: %s\n", exr_result_string(r)); return 1; }
    fprintf(stderr, "wrote %s (%dx%d float EXR)\n", path, W, H);
    return 0;
}

int fb_write_png(const Framebuffer *fb, const char *path, tonemap_kind tm, float exposure) {
    int W = fb->w, H = fb->h;
    unsigned char *rgb = (unsigned char *)malloc((size_t)W * H * 3);
    for (int i = 0; i < W * H; i++) {
        v3 hdr = fb_resolve(fb, i);
        v3 m = tonemap(hdr, tm, exposure);
        v3 s = linear_to_srgb3(m);
        rgb[i * 3 + 0] = (unsigned char)(clampf(s.x, 0, 1) * 255.0f + 0.5f);
        rgb[i * 3 + 1] = (unsigned char)(clampf(s.y, 0, 1) * 255.0f + 0.5f);
        rgb[i * 3 + 2] = (unsigned char)(clampf(s.z, 0, 1) * 255.0f + 0.5f);
    }
    int ok = stbi_write_png(path, W, H, 3, rgb, W * 3);
    free(rgb);
    if (!ok) { fprintf(stderr, "png: write failed for %s\n", path); return 1; }
    fprintf(stderr, "wrote %s (%dx%d sRGB PNG)\n", path, W, H);
    return 0;
}

/* Plain linear->sRGB encode with an exposure scale, NO filmic/ACES tonemap.
 * This matches MaterialXView's gamma-encoded framebuffer capture, so the two
 * PNGs are directly comparable in the same (sRGB) space by the verify harness. */
int fb_write_png_srgb(const Framebuffer *fb, const char *path, float exposure) {
    int W = fb->w, H = fb->h;
    unsigned char *rgb = (unsigned char *)malloc((size_t)W * H * 3);
    for (int i = 0; i < W * H; i++) {
        v3 hdr = v3_scale(fb_resolve(fb, i), exposure);
        v3 s = linear_to_srgb3(hdr); /* sRGB OETF clamps internally below */
        rgb[i * 3 + 0] = (unsigned char)(clampf(s.x, 0, 1) * 255.0f + 0.5f);
        rgb[i * 3 + 1] = (unsigned char)(clampf(s.y, 0, 1) * 255.0f + 0.5f);
        rgb[i * 3 + 2] = (unsigned char)(clampf(s.z, 0, 1) * 255.0f + 0.5f);
    }
    int ok = stbi_write_png(path, W, H, 3, rgb, W * 3);
    free(rgb);
    if (!ok) { fprintf(stderr, "png: write failed for %s\n", path); return 1; }
    fprintf(stderr, "wrote %s (%dx%d plain-sRGB PNG)\n", path, W, H);
    return 0;
}
