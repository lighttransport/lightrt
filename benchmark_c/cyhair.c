/*
 * cyhair.c — CyHair (.hair) binary loader. See cyhair.h.
 *
 * Header layout (128 bytes, little-endian) and array order match Cem Yuksel's
 * cyHairFile reference. Arrays appear in the file in this fixed order, each
 * gated by a bit in `arrays`: segments (u16/strand), points (f32x3/point),
 * thickness (f32/point), transparency (f32/point), colors (f32x3/point). We
 * only consume up to the thickness array (everything we need precedes it).
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include "cyhair.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CY_BIT_SEGMENTS 1u
#define CY_BIT_POINTS 2u
#define CY_BIT_THICKNESS 4u
/* transparency (8) and colors (16) exist in the stream but are unused here. */

typedef struct {
    char signature[4];
    uint32_t hair_count;
    uint32_t point_count;
    uint32_t arrays;
    uint32_t d_segments;
    float d_thickness;
    float d_transparency;
    float d_color[3];
    char info[88];
} cy_header;
_Static_assert(sizeof(cy_header) == 128, "CyHair header must be 128 bytes");

void cyhair_free(cyhair_t *h) {
    if (!h) return;
    free(h->points);
    free(h->radius);
    free(h->strand_first);
    free(h->strand_count);
    memset(h, 0, sizeof(*h));
}

int cyhair_load(const char *path, float radius_scale, cyhair_t *out) {
    if (!path || !out) return -1;
    memset(out, 0, sizeof(*out));
    if (!(radius_scale > 0.0f)) radius_scale = 1.0f;

    FILE *f = fopen(path, "rb");
    if (!f) return -1;

    cy_header h;
    if (fread(&h, 1, sizeof(h), f) != sizeof(h)) {
        fclose(f);
        return -2;
    }
    if (memcmp(h.signature, "HAIR", 4) != 0) {
        fclose(f);
        return -3;
    }

    const size_t nstrands = h.hair_count;
    const size_t npoints = h.point_count;
    if (nstrands == 0 || npoints == 0) {
        fclose(f);
        return -4;
    }
    if (!(h.arrays & CY_BIT_POINTS)) {
        fclose(f);
        return -5;
    }

    int rc = -10;
    uint16_t *segs16 = NULL;
    float *pts = NULL, *thick = NULL, *rad = NULL;
    uint32_t *sfirst = NULL, *scount = NULL;

    /* segments array (u16 per strand) */
    if (h.arrays & CY_BIT_SEGMENTS) {
        segs16 = (uint16_t *)malloc(nstrands * sizeof(uint16_t));
        if (!segs16) goto done;
        if (fread(segs16, sizeof(uint16_t), nstrands, f) != nstrands) {
            rc = -2;
            goto done;
        }
    }

    /* points array (float3 per point) */
    pts = (float *)malloc(npoints * 3 * sizeof(float));
    if (!pts) goto done;
    if (fread(pts, sizeof(float), npoints * 3, f) != npoints * 3) {
        rc = -2;
        goto done;
    }

    /* thickness array (float per point), else the header default */
    if (h.arrays & CY_BIT_THICKNESS) {
        thick = (float *)malloc(npoints * sizeof(float));
        if (!thick) goto done;
        if (fread(thick, sizeof(float), npoints, f) != npoints) {
            rc = -2;
            goto done;
        }
    }

    /* per-strand offsets (points per strand = segments + 1) */
    sfirst = (uint32_t *)malloc(nstrands * sizeof(uint32_t));
    scount = (uint32_t *)malloc(nstrands * sizeof(uint32_t));
    if (!sfirst || !scount) goto done;
    {
        size_t acc = 0, nseg = 0;
        for (size_t i = 0; i < nstrands; i++) {
            uint32_t seg = segs16 ? (uint32_t)segs16[i] : h.d_segments;
            uint32_t cnt = seg + 1u;
            sfirst[i] = (uint32_t)acc;
            scount[i] = cnt;
            acc += cnt;
            nseg += seg;
        }
        if (acc != npoints) { /* malformed: strand sizes do not tile the points */
            rc = -6;
            goto done;
        }
        out->nsegments = nseg;
    }

    /* per-point radius from thickness (treated as diameter) */
    rad = (float *)malloc(npoints * sizeof(float));
    if (!rad) goto done;
    for (size_t i = 0; i < npoints; i++) {
        float th = thick ? thick[i] : h.d_thickness;
        rad[i] = 0.5f * th * radius_scale;
    }

    /* bounding box over all points */
    {
        float lo[3] = {1e30f, 1e30f, 1e30f};
        float hi[3] = {-1e30f, -1e30f, -1e30f};
        for (size_t i = 0; i < npoints; i++) {
            for (int a = 0; a < 3; a++) {
                float v = pts[i * 3 + a];
                if (v < lo[a]) lo[a] = v;
                if (v > hi[a]) hi[a] = v;
            }
        }
        for (int a = 0; a < 3; a++) {
            out->bbox_min[a] = lo[a];
            out->bbox_max[a] = hi[a];
        }
    }

    out->points = pts;
    out->radius = rad;
    out->strand_first = sfirst;
    out->strand_count = scount;
    out->nstrands = nstrands;
    out->npoints = npoints;
    pts = rad = NULL; /* ownership transferred to *out */
    sfirst = scount = NULL;
    rc = 0;

done:
    fclose(f);
    free(segs16);
    free(thick);
    free(pts);
    free(rad);
    free(sfirst);
    free(scount);
    return rc;
}
