/*
 * bsdf.h - OpenPBR-style layered BSDF (metallic-roughness core + dielectric
 * specular + smooth glass transmission + subsurface-as-tinted-diffuse).
 *
 * All directions are world-space; wo points from the surface toward the viewer.
 * The shading normal N is oriented to the wo side by the caller helpers.
 */
#ifndef MTLXRENDER_BSDF_H_
#define MTLXRENDER_BSDF_H_

#include "mtlx_eval.h"
#include "vecmath.h"

typedef struct {
    v3    wi;          /* sampled incident direction (world) */
    v3    throughput;  /* f * |cos| / pdf */
    float pdf;
    int   specular;    /* delta lobe: skip NEE/MIS for this bounce */
    int   transmission;/* glass refraction lobe (ray enters/exits medium) */
    int   crossed;     /* transmission actually refracted across the interface
                          (vs reflected/TIR); toggles the caller's medium state */
    int   subsurface;  /* diffuse lobe flagged as subsurface entry */
} BsdfSample;

/* Importance-sample the BSDF. Returns 0 if no valid sample. */
int bsdf_sample(const OpenPBRParams *p, v3 N, v3 wo, pcg32 *rng, BsdfSample *out);

/* Beer-Lambert volume absorption coefficient (per channel) for a transmissive
 * medium: transmission_color is the color seen after transmission_depth units,
 * so sigma_a = -ln(transmission_color)/transmission_depth. Returns 0 (no
 * absorption) when transmission_depth <= 0. */
v3 transmission_sigma_a(const OpenPBRParams *p);

/* Evaluate the non-delta BSDF (diffuse + rough specular) for NEE/MIS.
 * Returns f (rgb); *pdf_out gets the mixture pdf for sampling wi. */
v3 bsdf_eval(const OpenPBRParams *p, v3 N, v3 wo, v3 wi, float *pdf_out);

#endif /* MTLXRENDER_BSDF_H_ */
