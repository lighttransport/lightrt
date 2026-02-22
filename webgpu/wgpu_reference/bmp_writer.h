/* bmp_writer.h — Minimal single-header BMP writer (RGBA input) */
#ifndef BMP_WRITER_H
#define BMP_WRITER_H

#include <stdint.h>
#include <stdio.h>

static int write_bmp(const char *filename, uint32_t w, uint32_t h,
                     const uint8_t *rgba) {
    uint32_t row_bytes = (w * 3 + 3) & ~3u; /* 4-byte aligned rows */
    uint32_t pixel_size = row_bytes * h;
    uint32_t file_size = 54 + pixel_size;

    uint8_t hdr[54] = {0};
    /* BM signature */
    hdr[0] = 'B'; hdr[1] = 'M';
    /* File size */
    hdr[2] = (uint8_t)file_size; hdr[3] = (uint8_t)(file_size >> 8);
    hdr[4] = (uint8_t)(file_size >> 16); hdr[5] = (uint8_t)(file_size >> 24);
    /* Pixel data offset */
    hdr[10] = 54;
    /* DIB header size */
    hdr[14] = 40;
    /* Width */
    hdr[18] = (uint8_t)w; hdr[19] = (uint8_t)(w >> 8);
    hdr[20] = (uint8_t)(w >> 16); hdr[21] = (uint8_t)(w >> 24);
    /* Height */
    hdr[22] = (uint8_t)h; hdr[23] = (uint8_t)(h >> 8);
    hdr[24] = (uint8_t)(h >> 16); hdr[25] = (uint8_t)(h >> 24);
    /* Planes */
    hdr[26] = 1;
    /* Bits per pixel */
    hdr[28] = 24;
    /* Pixel data size */
    hdr[34] = (uint8_t)pixel_size; hdr[35] = (uint8_t)(pixel_size >> 8);
    hdr[36] = (uint8_t)(pixel_size >> 16); hdr[37] = (uint8_t)(pixel_size >> 24);

    FILE *f = fopen(filename, "wb");
    if (!f) return 0;
    fwrite(hdr, 1, 54, f);

    /* Write rows bottom-up, converting RGBA to BGR */
    uint8_t pad[3] = {0, 0, 0};
    uint32_t pad_bytes = row_bytes - w * 3;
    for (uint32_t y = 0; y < h; y++) {
        const uint8_t *row = rgba + (h - 1 - y) * w * 4;
        for (uint32_t x = 0; x < w; x++) {
            uint8_t bgr[3] = {row[x * 4 + 2], row[x * 4 + 1], row[x * 4 + 0]};
            fwrite(bgr, 1, 3, f);
        }
        if (pad_bytes > 0) fwrite(pad, 1, pad_bytes, f);
    }

    fclose(f);
    return 1;
}

#endif /* BMP_WRITER_H */
