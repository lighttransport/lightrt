#include "bsdf.h"

#include <math.h>

/* ---- microfacet helpers ----------------------------------------------- */

static v3 fresnel_schlick(float cos_t, v3 f0) {
    float m = clampf(1.0f - cos_t, 0.0f, 1.0f);
    float m5 = m * m * m * m * m;
    return v3_add(f0, v3_scale(v3_sub(v3_splat(1.0f), f0), m5));
}
static float fresnel_schlick_s(float cos_t, float f0) {
    float m = clampf(1.0f - cos_t, 0.0f, 1.0f);
    float m5 = m * m * m * m * m;
    return f0 + (1.0f - f0) * m5;
}
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
static float ggx_G(float NdotV, float NdotL, float a) { return ggx_G1(NdotV, a) * ggx_G1(NdotL, a); }

/* "Charlie" sheen NDF (Estevez & Kulla 2017) + Neubelt visibility. */
static float charlie_D(float NdotH, float r) {
    r = clampf(r, 0.05f, 1.0f);
    float inv = 1.0f / r;
    float sin2 = maxf(0.0f, 1.0f - NdotH * NdotH);
    return (2.0f + inv) * powf(sin2, inv * 0.5f) * (1.0f / (2.0f * MTLX_PI));
}
static float sheen_V(float NdotV, float NdotL) {
    return 1.0f / (4.0f * (NdotL + NdotV - NdotL * NdotV) + 1e-4f);
}

/* ---- layered material ------------------------------------------------- */
typedef struct {
    v3    diff_color;  /* effective diffuse albedo (incl. subsurface tint) */
    v3    F0;          /* specular reflectance at normal incidence */
    float alpha;       /* GGX roughness^2 */
    v3    sheen_color; float sheen_alpha, sheen_w;
    float coat_alpha, coat_w, coat_f0;
    float glass_w, ior;
    /* normalized lobe selection probabilities (glass is delta) */
    float pd, ps, pc, pg;
} Layers;

static Layers extract(const OpenPBRParams *p) {
    Layers L;
    float metal = p->metalness, trans = p->transmission;
    v3 base = v3_scale(p->base_color, p->base_weight);

    v3 diff = v3_scale(base, (1.0f - metal) * (1.0f - trans));
    if (p->subsurface > 0.0f)
        diff = v3_lerp(diff, v3_scale(p->subsurface_color, (1.0f - metal) * (1.0f - trans)), p->subsurface);
    L.diff_color = diff;

    float f0d = (p->specular_ior - 1.0f) / (p->specular_ior + 1.0f);
    f0d = f0d * f0d * p->specular_weight;
    L.F0 = v3_lerp(v3_mul(v3_splat(f0d), p->specular_color), base, metal);
    L.ior = p->specular_ior;
    L.alpha = clampf(p->specular_roughness, 0.02f, 1.0f); L.alpha *= L.alpha;

    L.sheen_w = p->sheen_weight;
    L.sheen_color = p->sheen_color;
    L.sheen_alpha = clampf(p->sheen_roughness, 0.05f, 1.0f);

    L.coat_w = clampf(p->coat_weight, 0.0f, 1.0f);
    L.coat_alpha = clampf(p->coat_roughness, 0.02f, 1.0f); L.coat_alpha *= L.coat_alpha;
    float c = (p->coat_ior - 1.0f) / (p->coat_ior + 1.0f);
    L.coat_f0 = c * c;

    L.glass_w = (1.0f - metal) * trans;

    float lumD = luminance(L.diff_color) + 0.5f * L.sheen_w * luminance(L.sheen_color);
    float lumS = luminance(L.F0) + 0.04f;
    float wc = L.coat_w * 0.5f;
    float tot = lumD + lumS + wc + L.glass_w + 1e-4f;
    L.pd = lumD / tot; L.ps = lumS / tot; L.pc = wc / tot; L.pg = L.glass_w / tot;
    return L;
}

static v3 face_forward(v3 N, v3 wo) { return v3_dot(N, wo) < 0.0f ? v3_neg(N) : N; }

/* Unified reflection-lobe evaluation (diffuse + spec + sheen + coat). Fills the
 * mixture pdf for the sampled wi. Returns f (rgb). Excludes the glass lobe. */
static v3 eval_reflection(const Layers *L, v3 N, v3 wo, v3 wi, float *pdf) {
    float NdotL = v3_dot(N, wi), NdotV = v3_dot(N, wo);
    if (NdotL <= 0.0f || NdotV <= 0.0f) { *pdf = 0.0f; return v3_splat(0.0f); }
    v3 H = v3_normalize(v3_add(wo, wi));
    float NdotH = v3_dot(N, H), VdotH = v3_dot(wo, H);

    /* coat attenuates the layers beneath it */
    float coat_fr = L->coat_w * fresnel_schlick_s(NdotV, L->coat_f0);
    float base_atten = 1.0f - coat_fr;

    v3 diff = v3_scale(L->diff_color, MTLX_INV_PI * base_atten);

    float D = ggx_D(NdotH, L->alpha), G = ggx_G(NdotV, NdotL, L->alpha);
    v3 F = fresnel_schlick(VdotH, L->F0);
    v3 spec = v3_scale(F, D * G / (4.0f * NdotV * NdotL) * base_atten);

    v3 sheen = v3_splat(0.0f);
    if (L->sheen_w > 0.0f)
        sheen = v3_scale(L->sheen_color, L->sheen_w * charlie_D(NdotH, L->sheen_alpha) * sheen_V(NdotV, NdotL) * base_atten);

    v3 coat = v3_splat(0.0f);
    if (L->coat_w > 0.0f) {
        float Dc = ggx_D(NdotH, L->coat_alpha), Gc = ggx_G(NdotV, NdotL, L->coat_alpha);
        float Fc = L->coat_w * fresnel_schlick_s(VdotH, L->coat_f0);
        coat = v3_splat(Fc * Dc * Gc / (4.0f * NdotV * NdotL));
    }

    float pdf_diff = NdotL * MTLX_INV_PI;
    float pdf_spec = ggx_D(NdotH, L->alpha) * NdotH / (4.0f * VdotH + 1e-6f);
    float pdf_coat = ggx_D(NdotH, L->coat_alpha) * NdotH / (4.0f * VdotH + 1e-6f);
    *pdf = L->pd * pdf_diff + L->ps * pdf_spec + L->pc * pdf_coat;

    return v3_add(v3_add(diff, spec), v3_add(sheen, coat));
}

int bsdf_sample(const OpenPBRParams *p, v3 Ns, v3 wo, pcg32 *rng, BsdfSample *out) {
    v3 N = face_forward(v3_normalize(Ns), wo);
    Layers L = extract(p);
    v3 T, B; onb(N, &T, &B);
    float u = pcg32_f(rng), u1 = pcg32_f(rng), u2 = pcg32_f(rng);

    /* glass (dielectric; microfacet-roughened when alpha is significant) */
    if (u < L.pg) {
        /* sample a microfacet normal m (= N for smooth glass) and reflect/
         * refract about it, giving frosted glass for rough surfaces. */
        v3 m = (L.alpha > 1e-3f) ? v3_normalize(to_world(sample_ggx_h(L.alpha, u1, u2), T, B, N)) : N;
        if (v3_dot(m, wo) < 0.0f) m = v3_neg(m);
        float eta = 1.0f / L.ior;
        float cosi = clampf(v3_dot(m, wo), 0.0f, 1.0f);
        float Fr = fresnel_dielectric(cosi, eta);
        v3 wi;
        if (pcg32_f(rng) < Fr) {
            wi = v3_sub(v3_scale(m, 2.0f * v3_dot(m, wo)), wo);
            if (v3_dot(wi, N) <= 0.0f) return 0; /* reflected below surface: reject */
        } else {
            float sint2 = eta * eta * (1.0f - cosi * cosi);
            float cost = sqrtf(maxf(0.0f, 1.0f - sint2));
            wi = v3_normalize(v3_sub(v3_scale(m, eta * cosi - cost), v3_scale(wo, eta)));
        }
        out->wi = wi; out->throughput = p->transmission_color; out->pdf = 1.0f;
        out->specular = 1; out->transmission = 1; out->subsurface = 0;
        return 1;
    }

    /* choose a reflection lobe to generate a direction */
    v3 wi;
    if (u < L.pg + L.pc) {              /* coat GGX */
        v3 H = v3_normalize(to_world(sample_ggx_h(L.coat_alpha, u1, u2), T, B, N));
        wi = v3_sub(v3_scale(H, 2.0f * v3_dot(wo, H)), wo);
    } else if (u < L.pg + L.pc + L.ps) { /* base spec GGX */
        v3 H = v3_normalize(to_world(sample_ggx_h(L.alpha, u1, u2), T, B, N));
        wi = v3_sub(v3_scale(H, 2.0f * v3_dot(wo, H)), wo);
    } else {                             /* diffuse / sheen (cosine) */
        wi = to_world(sample_cosine_hemisphere(u1, u2), T, B, N);
    }
    if (v3_dot(N, wi) <= 0.0f) return 0;

    float pdf;
    v3 f = eval_reflection(&L, N, wo, wi, &pdf);
    if (pdf <= 0.0f) return 0;
    out->wi = wi;
    out->throughput = v3_scale(f, v3_dot(N, wi) / pdf);
    out->pdf = pdf;
    out->specular = 0; out->transmission = 0;
    out->subsurface = (p->subsurface > 0.5f) ? 1 : 0;
    return 1;
}

v3 bsdf_eval(const OpenPBRParams *p, v3 Ns, v3 wo, v3 wi, float *pdf_out) {
    v3 N = face_forward(v3_normalize(Ns), wo);
    Layers L = extract(p);
    return eval_reflection(&L, N, wo, wi, pdf_out);
}
