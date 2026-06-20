#include "pathtrace.h"
#include "bsdf.h"
#include "mtlx_eval.h"

#include <math.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

#define TILE 16

/* Per-hit shading geometry pulled from the flat side tables. */
typedef struct {
    v3  P;       /* world hit point */
    v3  Ns;      /* interpolated shading normal */
    v3  Ng;      /* geometric normal */
    v3  dpdu;    /* UV tangent */
    float uv[2];
    int surface_node;
} HitInfo;

static v3 ray_point(const lrt_ray *r, float t) {
    return v3_make(r->org[0] + r->dir[0] * t, r->org[1] + r->dir[1] * t, r->org[2] + r->dir[2] * t);
}

static void fill_hit(const Scene *s, const MaterialBinding *bind, const lrt_ray *ray,
                     const lrt_hit *hit, HitInfo *hi) {
    uint32_t pid = hit->prim_id;
    float u = hit->u, v = hit->v, w = 1.0f - u - v;

    const float *N = &s->tri_n[pid * 9];
    v3 n0 = v3_make(N[0], N[1], N[2]), n1 = v3_make(N[3], N[4], N[5]), n2 = v3_make(N[6], N[7], N[8]);
    hi->Ns = v3_normalize(v3_add(v3_add(v3_scale(n0, w), v3_scale(n1, u)), v3_scale(n2, v)));

    const float *UV = &s->tri_uv[pid * 6];
    hi->uv[0] = w * UV[0] + u * UV[2] + v * UV[4];
    hi->uv[1] = w * UV[1] + u * UV[3] + v * UV[5];

    const float *P = &s->verts[pid * 9];
    v3 p0 = v3_make(P[0], P[1], P[2]), p1 = v3_make(P[3], P[4], P[5]), p2 = v3_make(P[6], P[7], P[8]);
    v3 e1 = v3_sub(p1, p0), e2 = v3_sub(p2, p0);
    hi->Ng = v3_normalize(v3_cross(e1, e2));
    hi->P = ray_point(ray, hit->t);

    /* UV tangent (Lengyel) for normal mapping */
    float du1 = UV[2] - UV[0], dv1 = UV[3] - UV[1];
    float du2 = UV[4] - UV[0], dv2 = UV[5] - UV[1];
    float det = du1 * dv2 - dv1 * du2;
    if (fabsf(det) > 1e-12f) {
        float inv = 1.0f / det;
        hi->dpdu = v3_scale(v3_sub(v3_scale(e1, dv2), v3_scale(e2, dv1)), inv);
    } else {
        v3 t, b; onb(hi->Ns, &t, &b); hi->dpdu = t;
    }

    int geom = s->tri_geom[pid];
    hi->surface_node = (geom >= 0 && geom < bind->ngeom) ? bind->geom_to_surface[geom] : -1;
}

static lrt_ray make_ray(v3 org, v3 dir, v3 ng, float tmax) {
    lrt_ray r;
    float s = (v3_dot(dir, ng) < 0.0f) ? -1.0f : 1.0f;
    v3 o = v3_add(org, v3_scale(ng, s * 1e-4f));
    r.org[0] = o.x; r.org[1] = o.y; r.org[2] = o.z;
    r.dir[0] = dir.x; r.dir[1] = dir.y; r.dir[2] = dir.z;
    r.tmin = 1e-4f; r.tmax = tmax;
    return r;
}

static float mis_power(float a, float b) { float a2 = a * a; return a2 / (a2 + b * b); }

/* Optional random-walk subsurface scattering. Returns 1 if the walk exited the
 * medium (P/N updated, throughput scaled by albedo per scatter); 0 if absorbed. */
static int sss_walk(const Scene *s, v3 *P, v3 N, const OpenPBRParams *p, pcg32 *rng,
                    v3 *throughput) {
    v3 mfp = v3_scale(p->subsurface_radius, p->subsurface_scale);
    float mfp_avg = maxf((mfp.x + mfp.y + mfp.z) / 3.0f, 1e-5f);
    float sigma_t = 1.0f / mfp_avg;
    v3 albedo = p->subsurface_color;
    v3 cur = *P;
    v3 dir = v3_neg(v3_normalize(N)); /* enter the surface */
    for (int step = 0; step < 256; step++) {
        float dist = -logf(1.0f - pcg32_f(rng)) / sigma_t;
        lrt_ray r = make_ray(cur, dir, v3_neg(dir), dist);
        lrt_hit h;
        if (lrt_tri_intersect1(s->bvh, &r, &h)) {
            float tsurf = h.t;
            if (dist < tsurf) {
                cur = ray_point(&r, dist);
                dir = sample_uniform_sphere(pcg32_f(rng), pcg32_f(rng));
                *throughput = v3_mul(*throughput, albedo);
            } else {
                *P = ray_point(&r, tsurf);
                return 1; /* exited */
            }
        } else {
            *P = cur; return 1; /* no boundary found; treat as exit */
        }
    }
    return 1; /* step cap: exit where we are (approx) */
}

static v3 trace_path(const Scene *s, const MtlxDoc *doc, const MaterialBinding *bind,
                     TextureCache *tex, const Env *env, const SunLight *sun, lrt_ray ray,
                     int max_bounces, int sss_walk_enabled, int hide_env_bg, pcg32 *rng,
                     MtlxValue *memo, char *memo_done) {
    v3 radiance = v3_splat(0.0f);
    v3 throughput = v3_splat(1.0f);
    int specular_bounce = 1;
    float prev_pdf = 0.0f;
    int in_medium = 0;            /* inside a transmissive volume (after refraction) */
    v3 medium_sigma = v3_splat(0.0f); /* Beer-Lambert absorption coeff of that volume */

    ShadeContext ctx;
    ctx.doc = doc; ctx.tex = tex; ctx.memo = memo; ctx.memo_done = memo_done;

    for (int depth = 0; depth < max_bounces; depth++) {
        lrt_hit hit;
        v3 dir = v3_make(ray.dir[0], ray.dir[1], ray.dir[2]);
        if (!lrt_tri_intersect1(s->bvh, &ray, &hit)) {
            /* Hide the env in the background (primary miss) but keep it as a
             * light for indirect rays -- matches MaterialXView's black bg. */
            if (!(depth == 0 && hide_env_bg)) {
                v3 Le = env_eval(env, dir);
                float w = 1.0f;
                if (!specular_bounce) { float pe = env_pdf(env, dir); w = mis_power(prev_pdf, pe); }
                radiance = v3_add(radiance, v3_mul(throughput, v3_scale(Le, w)));
            }
            break;
        }

        /* Beer-Lambert: attenuate over the path length just traversed inside a
         * transmissive medium (the segment from the entry refraction to here). */
        if (in_medium) {
            throughput = v3_mul(throughput, v3_make(expf(-medium_sigma.x * hit.t),
                                                    expf(-medium_sigma.y * hit.t),
                                                    expf(-medium_sigma.z * hit.t)));
        }

        HitInfo hi;
        fill_hit(s, bind, &ray, &hit, &hi);
        v3 wo = v3_neg(dir);

        ctx.uv[0] = hi.uv[0]; ctx.uv[1] = hi.uv[1];
        ctx.P = hi.P;
        ctx.Ns = hi.Ns; ctx.Ng = hi.Ng; ctx.dpdu = hi.dpdu; ctx.dpdv = v3_cross(hi.Ns, hi.dpdu);
        OpenPBRParams params;
        mtlx_eval_surface(&ctx, hi.surface_node, &params);

        if (params.emission > 0.0f)
            radiance = v3_add(radiance, v3_mul(throughput, v3_scale(params.emission_color, params.emission)));

        v3 Nsh = params.normal;

        /* ---- NEE against the environment ---- */
        {
            v3 wi_l; float pdf_l;
            v3 L = env_sample(env, pcg32_f(rng), pcg32_f(rng), &wi_l, &pdf_l);
            if (pdf_l > 0.0f && luminance(L) > 0.0f) {
                float pdf_b;
                v3 f = bsdf_eval(&params, Nsh, wo, wi_l, &pdf_b);
                float ndl = fabsf(v3_dot(v3_normalize(Nsh), wi_l));
                if (pdf_b > 0.0f && (f.x + f.y + f.z) > 0.0f) {
                    lrt_ray sr = make_ray(hi.P, wi_l, hi.Ng, 1e30f);
                    if (!lrt_tri_occluded1(s->bvh, &sr)) {
                        float w = mis_power(pdf_l, pdf_b);
                        radiance = v3_add(radiance, v3_mul(v3_mul(throughput, f),
                                                           v3_scale(L, ndl * w / pdf_l)));
                    }
                }
            }
        }

        /* ---- NEE for the directional sun (delta light, no MIS) ---- */
        if (sun && sun->enabled) {
            v3 wi_s = sun->dir;
            float pdf_b;
            v3 f = bsdf_eval(&params, Nsh, wo, wi_s, &pdf_b);
            float ndl = fabsf(v3_dot(v3_normalize(Nsh), wi_s));
            if ((f.x + f.y + f.z) > 0.0f && ndl > 0.0f) {
                lrt_ray sr = make_ray(hi.P, wi_s, hi.Ng, 1e30f);
                if (!lrt_tri_occluded1(s->bvh, &sr))
                    radiance = v3_add(radiance, v3_mul(v3_mul(throughput, f),
                                                       v3_scale(sun->radiance, ndl)));
            }
        }

        /* ---- BSDF sampling ---- */
        BsdfSample bs;
        if (!bsdf_sample(&params, Nsh, wo, rng, &bs)) break;
        if (bs.pdf <= 0.0f) break;

        if (bs.subsurface && sss_walk_enabled) {
            if (!sss_walk(s, &hi.P, Nsh, &params, rng, &throughput)) break;
            specular_bounce = 1; /* re-enter from a fresh diffuse exit */
        }

        throughput = v3_mul(throughput, bs.throughput);
        specular_bounce = bs.specular;
        prev_pdf = bs.pdf;

        if (!v3_is_finite(throughput)) break;

        /* Russian roulette */
        if (depth >= 3) {
            float q = clampf(v3_maxc(throughput), 0.02f, 0.95f);
            if (pcg32_f(rng) >= q) break;
            throughput = v3_scale(throughput, 1.0f / q);
        }

        /* A refraction crosses the interface: toggle in/out of the medium and,
         * on entry, capture that material's absorption coefficient. */
        if (bs.crossed) {
            if (!in_medium) { in_medium = 1; medium_sigma = transmission_sigma_a(&params); }
            else            { in_medium = 0; }
        }

        ray = make_ray(hi.P, bs.wi, hi.Ng, 1e30f);
    }
    return radiance;
}

/* ---- threading -------------------------------------------------------- */
typedef struct {
    const Scene *s; const MtlxDoc *doc; const MaterialBinding *bind;
    TextureCache *tex; const Env *env; const Camera *cam;
    const RenderConfig *cfg; Framebuffer *fb;
    int tiles_x, tiles_y, ntiles;
    atomic_int next_tile;
    atomic_int done_tiles;
} Job;

static void *worker(void *arg) {
    Job *j = (Job *)arg;
    int W = j->cfg->width, H = j->cfg->height;
    int nnode = j->doc->nnode;
    MtlxValue *memo = (MtlxValue *)malloc(sizeof(MtlxValue) * (size_t)(nnode > 0 ? nnode : 1));
    char *memo_done = (char *)malloc((size_t)(nnode > 0 ? nnode : 1));

    for (;;) {
        int tile = atomic_fetch_add(&j->next_tile, 1);
        if (tile >= j->ntiles) break;
        int tx = (tile % j->tiles_x) * TILE;
        int ty = (tile / j->tiles_x) * TILE;
        int x1 = tx + TILE < W ? tx + TILE : W;
        int y1 = ty + TILE < H ? ty + TILE : H;
        for (int y = ty; y < y1; y++) {
            for (int x = tx; x < x1; x++) {
                pcg32 rng;
                pcg32_seed(&rng, ((uint64_t)j->cfg->seed << 32) ^ ((uint64_t)y * W + x), 0x9e3779b9u);
                v3 sum = v3_splat(0.0f);
                for (int sp = 0; sp < j->cfg->spp; sp++) {
                    float px = (x + pcg32_f(&rng)) / W;
                    float py = (y + pcg32_f(&rng)) / H;
                    lrt_ray r = camera_ray(j->cam, px, py);
                    v3 L = trace_path(j->s, j->doc, j->bind, j->tex, j->env, &j->cfg->sun, r,
                                      j->cfg->max_bounces, j->cfg->sss_walk,
                                      j->cfg->hide_env_bg, &rng, memo, memo_done);
                    if (v3_is_finite(L)) sum = v3_add(sum, L);
                }
                int i = y * W + x;
                j->fb->accum[i] = sum;
                j->fb->nsamp[i] = j->cfg->spp;
            }
        }
        int d = atomic_fetch_add(&j->done_tiles, 1) + 1;
        if ((d % 16) == 0 || d == j->ntiles)
            fprintf(stderr, "\rrendering: %d/%d tiles", d, j->ntiles);
    }
    free(memo); free(memo_done);
    return NULL;
}

void render(const Scene *scene, const MtlxDoc *doc, const MaterialBinding *bind,
            TextureCache *tex, const Env *env, const Camera *cam,
            const RenderConfig *cfg, Framebuffer *fb) {
    Job j;
    memset(&j, 0, sizeof(j));
    j.s = scene; j.doc = doc; j.bind = bind; j.tex = tex; j.env = env; j.cam = cam;
    j.cfg = cfg; j.fb = fb;
    j.tiles_x = (cfg->width + TILE - 1) / TILE;
    j.tiles_y = (cfg->height + TILE - 1) / TILE;
    j.ntiles = j.tiles_x * j.tiles_y;
    atomic_init(&j.next_tile, 0);
    atomic_init(&j.done_tiles, 0);

    int nt = cfg->nthreads > 0 ? cfg->nthreads : 1;
    pthread_t *threads = (pthread_t *)malloc(sizeof(pthread_t) * nt);
    for (int t = 0; t < nt; t++) pthread_create(&threads[t], NULL, worker, &j);
    for (int t = 0; t < nt; t++) pthread_join(threads[t], NULL);
    fprintf(stderr, "\n");
}
