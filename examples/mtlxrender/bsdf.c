#include "bsdf.h"

#include <math.h>

/* ---- microfacet helpers ----------------------------------------------- */

static v3 fresnel_schlick(float cos_t, v3 f0) {
    float m = clampf(1.0f - cos_t, 0.0f, 1.0f);
    float m5 = m * m * m * m * m;
    return v3_add(f0, v3_scale(v3_sub(v3_splat(1.0f), f0), m5));
}

/* scalar dielectric Fresnel (unpolarized). cosi >= 0, eta = ni/nt. */
static float fresnel_dielectric(float cosi, float eta) {
    float sint2 = eta * eta * (1.0f - cosi * cosi);
    if (sint2 >= 1.0f) return 1.0f; /* TIR */
    float cost = sqrtf(1.0f - sint2);
    float rs = (eta * cosi - cost) / (eta * cosi + cost);
    float rp = (cosi - eta * cost) / (cosi + eta * cost);
    return 0.5f * (rs * rs + rp * rp);
}

static float ggx_D(float NdotH, float a) {
    if (NdotH <= 0.0f) return 0.0f;
    float a2 = a * a;
    float d = NdotH * NdotH * (a2 - 1.0f) + 1.0f;
    return a2 / (MTLX_PI * d * d);
}

static float ggx_G1(float NdotX, float a) {
    if (NdotX <= 0.0f) return 0.0f;
    float a2 = a * a;
    float t = NdotX * NdotX;
    return 2.0f * NdotX / (NdotX + sqrtf(a2 + (1.0f - a2) * t));
}

static float ggx_G(float NdotV, float NdotL, float a) {
    return ggx_G1(NdotV, a) * ggx_G1(NdotL, a);
}

/* ---- layer-weight extraction ------------------------------------------ */
typedef struct {
    v3    diff_color;  /* effective diffuse albedo (incl. subsurface tint) */
    v3    F0;          /* specular reflectance at normal incidence */
    float alpha;       /* GGX roughness^2 */
    float glass_w;     /* glass selection weight */
    float ior;
    /* normalized lobe selection probabilities */
    float pd, ps, pg;
} Layers;

static Layers extract(const OpenPBRParams *p) {
    Layers L;
    float metal = p->metalness;
    float trans = p->transmission;
    v3 base = v3_scale(p->base_color, p->base_weight);

    v3 diff = v3_scale(base, (1.0f - metal) * (1.0f - trans));
    /* subsurface: tint the diffuse albedo toward subsurface_color */
    if (p->subsurface > 0.0f)
        diff = v3_lerp(diff, v3_scale(p->subsurface_color, (1.0f - metal) * (1.0f - trans)), p->subsurface);
    L.diff_color = diff;

    float f0d = (p->specular_ior - 1.0f) / (p->specular_ior + 1.0f);
    f0d = f0d * f0d * p->specular_weight;
    v3 f0_dielectric = v3_mul(v3_splat(f0d), p->specular_color);
    L.F0 = v3_lerp(f0_dielectric, base, metal);
    L.ior = p->specular_ior;

    float rough = clampf(p->specular_roughness, 0.02f, 1.0f);
    L.alpha = rough * rough;

    L.glass_w = (1.0f - metal) * trans;

    float lumD = luminance(L.diff_color);
    float lumS = luminance(L.F0) + 0.04f;
    float tot = lumD + lumS + L.glass_w + 1e-4f;
    L.pd = lumD / tot;
    L.ps = lumS / tot;
    L.pg = L.glass_w / tot;
    return L;
}

/* orient N to the same hemisphere as wo (two-sided shading). */
static v3 face_forward(v3 N, v3 wo) { return v3_dot(N, wo) < 0.0f ? v3_neg(N) : N; }

int bsdf_sample(const OpenPBRParams *p, v3 Ns, v3 wo, pcg32 *rng, BsdfSample *out) {
    v3 N = face_forward(v3_normalize(Ns), wo);
    Layers L = extract(p);
    v3 T, B;
    onb(N, &T, &B);

    float u = pcg32_f(rng);
    float u1 = pcg32_f(rng), u2 = pcg32_f(rng);

    /* ---- glass (smooth dielectric) ---- */
    if (u < L.pg) {
        float entering = v3_dot(wo, N) > 0.0f ? 1.0f : -1.0f;
        (void)entering;
        float eta = 1.0f / L.ior; /* outside->inside */
        float cosi = clampf(v3_dot(N, wo), 0.0f, 1.0f);
        float F = fresnel_dielectric(cosi, eta);
        v3 wi;
        if (pcg32_f(rng) < F) {
            wi = v3_sub(v3_scale(N, 2.0f * v3_dot(N, wo)), wo); /* reflect */
        } else {
            /* refract */
            float sint2 = eta * eta * (1.0f - cosi * cosi);
            float cost = sqrtf(maxf(0.0f, 1.0f - sint2));
            wi = v3_sub(v3_scale(N, eta * cosi - cost), v3_scale(wo, eta));
            wi = v3_normalize(wi);
        }
        out->wi = wi;
        out->throughput = v3_scale(p->transmission_color, 1.0f); /* energy-preserving (F handled by branch) */
        out->pdf = 1.0f;
        out->specular = 1;
        out->transmission = 1;
        out->subsurface = 0;
        return 1;
    }

    /* ---- glossy specular (GGX) ---- */
    if (u < L.pg + L.ps) {
        v3 h_local = sample_ggx_h(L.alpha, u1, u2);
        v3 H = v3_normalize(to_world(h_local, T, B, N));
        v3 wi = v3_sub(v3_scale(H, 2.0f * v3_dot(wo, H)), wo);
        float NdotL = v3_dot(N, wi);
        float NdotV = v3_dot(N, wo);
        if (NdotL <= 0.0f || NdotV <= 0.0f) return 0;
        float NdotH = v3_dot(N, H);
        float VdotH = v3_dot(wo, H);
        float D = ggx_D(NdotH, L.alpha);
        float G = ggx_G(NdotV, NdotL, L.alpha);
        v3 F = fresnel_schlick(VdotH, L.F0);
        v3 spec = v3_scale(F, D * G / (4.0f * NdotV * NdotL));
        float pdf_spec = D * NdotH / (4.0f * VdotH);
        /* diffuse also contributes to the same wi (mixture pdf) */
        float pdf_diff = NdotL * MTLX_INV_PI;
        v3 diff = v3_scale(L.diff_color, MTLX_INV_PI);
        v3 f = v3_add(spec, diff);
        float pdf = L.ps * pdf_spec + L.pd * pdf_diff;
        if (pdf <= 0.0f) return 0;
        out->wi = wi;
        out->throughput = v3_scale(f, NdotL / pdf);
        out->pdf = pdf;
        out->specular = 0;
        out->transmission = 0;
        out->subsurface = 0;
        return 1;
    }

    /* ---- diffuse / subsurface entry ---- */
    {
        v3 d_local = sample_cosine_hemisphere(u1, u2);
        v3 wi = to_world(d_local, T, B, N);
        float NdotL = v3_dot(N, wi);
        if (NdotL <= 0.0f) return 0;
        float NdotV = maxf(v3_dot(N, wo), 1e-4f);
        v3 diff = v3_scale(L.diff_color, MTLX_INV_PI);
        float pdf_diff = NdotL * MTLX_INV_PI;
        /* specular contribution to this wi for the mixture pdf */
        v3 H = v3_normalize(v3_add(wo, wi));
        float NdotH = v3_dot(N, H), VdotH = v3_dot(wo, H);
        float D = ggx_D(NdotH, L.alpha);
        float G = ggx_G(NdotV, NdotL, L.alpha);
        v3 F = fresnel_schlick(VdotH, L.F0);
        v3 spec = v3_scale(F, D * G / (4.0f * NdotV * NdotL));
        float pdf_spec = D * NdotH / (4.0f * VdotH);
        v3 f = v3_add(diff, spec);
        float pdf = L.pd * pdf_diff + L.ps * pdf_spec;
        if (pdf <= 0.0f) return 0;
        out->wi = wi;
        out->throughput = v3_scale(f, NdotL / pdf);
        out->pdf = pdf;
        out->specular = 0;
        out->transmission = 0;
        out->subsurface = (p->subsurface > 0.5f) ? 1 : 0;
        return 1;
    }
}

v3 bsdf_eval(const OpenPBRParams *p, v3 Ns, v3 wo, v3 wi, float *pdf_out) {
    v3 N = face_forward(v3_normalize(Ns), wo);
    Layers L = extract(p);
    float NdotL = v3_dot(N, wi);
    float NdotV = v3_dot(N, wo);
    if (NdotL <= 0.0f || NdotV <= 0.0f) { *pdf_out = 0.0f; return v3_splat(0.0f); }

    v3 diff = v3_scale(L.diff_color, MTLX_INV_PI);
    float pdf_diff = NdotL * MTLX_INV_PI;

    v3 H = v3_normalize(v3_add(wo, wi));
    float NdotH = v3_dot(N, H), VdotH = v3_dot(wo, H);
    float D = ggx_D(NdotH, L.alpha);
    float G = ggx_G(NdotV, NdotL, L.alpha);
    v3 F = fresnel_schlick(VdotH, L.F0);
    v3 spec = v3_scale(F, D * G / (4.0f * NdotV * NdotL));
    float pdf_spec = D * NdotH / (4.0f * VdotH);

    *pdf_out = L.pd * pdf_diff + L.ps * pdf_spec;
    return v3_add(diff, spec);
}
