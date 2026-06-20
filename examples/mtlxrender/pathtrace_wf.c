#include "pathtrace_wf.h"
#include "bsdf.h"
#include "mtlx_eval.h"

#include <math.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

/* ---- per-hit geometry (mirrors pathtrace.c's fill_hit) ------------------- */
typedef struct {
    v3 P, Ns, Ng, dpdu;
    float uv[2];
    int surface_node;
} HitInfo;

static v3 ray_point(const lrt_ray *r, float t) {
    return v3_make(r->org[0] + r->dir[0] * t, r->org[1] + r->dir[1] * t,
                   r->org[2] + r->dir[2] * t);
}

static void fill_hit(const Scene *s, const MaterialBinding *bind,
                     const lrt_ray *ray, const lrt_hit *hit, HitInfo *hi) {
    uint32_t pid = hit->prim_id;
    float u = hit->u, v = hit->v, w = 1.0f - u - v;

    const float *N = &s->tri_n[pid * 9];
    v3 n0 = v3_make(N[0], N[1], N[2]), n1 = v3_make(N[3], N[4], N[5]),
       n2 = v3_make(N[6], N[7], N[8]);
    hi->Ns = v3_normalize(v3_add(v3_add(v3_scale(n0, w), v3_scale(n1, u)),
                                 v3_scale(n2, v)));

    const float *UV = &s->tri_uv[pid * 6];
    hi->uv[0] = w * UV[0] + u * UV[2] + v * UV[4];
    hi->uv[1] = w * UV[1] + u * UV[3] + v * UV[5];

    const float *P = &s->verts[pid * 9];
    v3 p0 = v3_make(P[0], P[1], P[2]), p1 = v3_make(P[3], P[4], P[5]),
       p2 = v3_make(P[6], P[7], P[8]);
    v3 e1 = v3_sub(p1, p0), e2 = v3_sub(p2, p0);
    hi->Ng = v3_normalize(v3_cross(e1, e2));
    hi->P = ray_point(ray, hit->t);

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
    hi->surface_node =
        (geom >= 0 && geom < bind->ngeom) ? bind->geom_to_surface[geom] : -1;
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

/* ---- per-pixel path state ------------------------------------------------ */
typedef struct {
    lrt_ray ray;
    v3 thr, rad;
    pcg32 rng;
    float prev_pdf;
    uint8_t alive, spec;
} Path;

/* shadow-ray slot (two per shaded hit: env NEE + sun NEE) */
typedef struct { lrt_ray ray; v3 contrib; int owner; uint8_t valid; } Shadow;

/* ---- parallel shading of one bounce ------------------------------------- */
typedef struct {
    const Scene *s; const MtlxDoc *doc; const MaterialBinding *bind;
    TextureCache *tex; const Env *env; const SunLight *sun;
    Path *path; const int *active; const lrt_hit *hits; int M;
    Shadow *shadow; /* sized 2*M; slots [2k],[2k+1] for active k */
    int depth;          /* current bounce (0 = primary) */
    int hide_env_bg;    /* primary-ray miss returns black, not the env */
    atomic_int next;
} ShadeJob;

static void shade_range(ShadeJob *j, int k0, int k1, MtlxValue *memo, char *memo_done) {
    ShadeContext ctx;
    ctx.doc = j->doc; ctx.tex = j->tex; ctx.memo = memo; ctx.memo_done = memo_done;

    for (int k = k0; k < k1; k++) {
        int i = j->active[k];
        Path *p = &j->path[i];
        const lrt_hit *hit = &j->hits[k];
        j->shadow[2 * k].valid = j->shadow[2 * k + 1].valid = 0;
        v3 dir = v3_make(p->ray.dir[0], p->ray.dir[1], p->ray.dir[2]);

        if (hit->prim_id == LRT_TRI_NO_HIT) {
            /* Hide the env in the background (primary miss) but keep it lighting
             * indirect rays -- matches MaterialXView's black bg. */
            if (!(j->depth == 0 && j->hide_env_bg)) {
                v3 Le = env_eval(j->env, dir);
                float w = 1.0f;
                if (!p->spec) { float pe = env_pdf(j->env, dir); w = mis_power(p->prev_pdf, pe); }
                p->rad = v3_add(p->rad, v3_mul(p->thr, v3_scale(Le, w)));
            }
            p->alive = 0;
            continue;
        }

        HitInfo hi;
        fill_hit(j->s, j->bind, &p->ray, hit, &hi);
        v3 wo = v3_neg(dir);
        ctx.uv[0] = hi.uv[0]; ctx.uv[1] = hi.uv[1];
        ctx.P = hi.P; ctx.Ns = hi.Ns; ctx.Ng = hi.Ng;
        ctx.dpdu = hi.dpdu; ctx.dpdv = v3_cross(hi.Ns, hi.dpdu);
        OpenPBRParams params;
        mtlx_eval_surface(&ctx, hi.surface_node, &params);

        if (params.emission > 0.0f)
            p->rad = v3_add(p->rad, v3_mul(p->thr, v3_scale(params.emission_color, params.emission)));

        v3 Nsh = params.normal;

        /* env NEE -> shadow slot 2k (MIS) */
        {
            v3 wi_l; float pdf_l;
            v3 L = env_sample(j->env, pcg32_f(&p->rng), pcg32_f(&p->rng), &wi_l, &pdf_l);
            if (pdf_l > 0.0f && luminance(L) > 0.0f) {
                float pdf_b;
                v3 f = bsdf_eval(&params, Nsh, wo, wi_l, &pdf_b);
                float ndl = fabsf(v3_dot(v3_normalize(Nsh), wi_l));
                if (pdf_b > 0.0f && (f.x + f.y + f.z) > 0.0f) {
                    float w = mis_power(pdf_l, pdf_b);
                    j->shadow[2 * k].ray = make_ray(hi.P, wi_l, hi.Ng, 1e30f);
                    j->shadow[2 * k].contrib =
                        v3_mul(v3_mul(p->thr, f), v3_scale(L, ndl * w / pdf_l));
                    j->shadow[2 * k].owner = i;
                    j->shadow[2 * k].valid = 1;
                }
            }
        }
        /* sun NEE -> shadow slot 2k+1 (delta light, no MIS) */
        if (j->sun && j->sun->enabled) {
            v3 wi_s = j->sun->dir;
            float pdf_b;
            v3 f = bsdf_eval(&params, Nsh, wo, wi_s, &pdf_b);
            float ndl = fabsf(v3_dot(v3_normalize(Nsh), wi_s));
            if ((f.x + f.y + f.z) > 0.0f && ndl > 0.0f) {
                j->shadow[2 * k + 1].ray = make_ray(hi.P, wi_s, hi.Ng, 1e30f);
                j->shadow[2 * k + 1].contrib =
                    v3_mul(v3_mul(p->thr, f), v3_scale(j->sun->radiance, ndl));
                j->shadow[2 * k + 1].owner = i;
                j->shadow[2 * k + 1].valid = 1;
            }
        }

        /* BSDF sampling -> next bounce */
        BsdfSample bs;
        if (!bsdf_sample(&params, Nsh, wo, &p->rng, &bs) || bs.pdf <= 0.0f) {
            p->alive = 0; continue;
        }
        p->thr = v3_mul(p->thr, bs.throughput);
        p->spec = (uint8_t)bs.specular;
        p->prev_pdf = bs.pdf;
        if (!v3_is_finite(p->thr)) { p->alive = 0; continue; }

        /* Russian roulette is applied to survivors after the bounce (apply_rr). */
        p->ray = make_ray(hi.P, bs.wi, hi.Ng, 1e30f);
    }
}

typedef struct { ShadeJob *job; int nnode; } Worker;

static void *shade_worker(void *arg) {
    Worker *wk = (Worker *)arg;
    ShadeJob *j = wk->job;
    int nn = wk->nnode > 0 ? wk->nnode : 1;
    MtlxValue *memo = (MtlxValue *)malloc(sizeof(MtlxValue) * (size_t)nn);
    char *memo_done = (char *)malloc((size_t)nn);
    const int GRAIN = 256;
    for (;;) {
        int k0 = atomic_fetch_add(&j->next, GRAIN);
        if (k0 >= j->M) break;
        int k1 = k0 + GRAIN < j->M ? k0 + GRAIN : j->M;
        shade_range(j, k0, k1, memo, memo_done);
    }
    free(memo); free(memo_done);
    return NULL;
}

/* Russian roulette is applied to the surviving paths between bounces. */
static void apply_rr(Path *path, const int *active, int M, int depth) {
    if (depth < 3) return;
    for (int k = 0; k < M; k++) {
        Path *p = &path[active[k]];
        if (!p->alive) continue;
        float q = clampf(v3_maxc(p->thr), 0.02f, 0.95f);
        if (pcg32_f(&p->rng) >= q) { p->alive = 0; }
        else p->thr = v3_scale(p->thr, 1.0f / q);
    }
}

void render_wavefront(const Scene *scene, const MtlxDoc *doc,
                      const MaterialBinding *bind, TextureCache *tex,
                      const Env *env, const Camera *cam, const RenderConfig *cfg,
                      Framebuffer *fb, RayTracer *rt) {
    int W = cfg->width, H = cfg->height;
    size_t N = (size_t)W * H;
    int nt = cfg->nthreads > 0 ? cfg->nthreads : 1;

    Path *path = (Path *)malloc(N * sizeof(Path));
    int *active = (int *)malloc(N * sizeof(int));
    lrt_ray *rbatch = (lrt_ray *)malloc(N * sizeof(lrt_ray));
    lrt_hit *hbatch = (lrt_hit *)malloc(N * sizeof(lrt_hit));
    Shadow *shadow = (Shadow *)malloc(2 * N * sizeof(Shadow));
    lrt_ray *sbatch = (lrt_ray *)malloc(2 * N * sizeof(lrt_ray));
    int *sslot = (int *)malloc(2 * N * sizeof(int));
    uint8_t *socc = (uint8_t *)malloc(2 * N * sizeof(uint8_t));
    pthread_t *threads = (pthread_t *)malloc((size_t)nt * sizeof(pthread_t));
    Worker *workers = (Worker *)malloc((size_t)nt * sizeof(Worker));
    if (!path || !active || !rbatch || !hbatch || !shadow || !sbatch ||
        !sslot || !socc || !threads || !workers) {
        fprintf(stderr, "wavefront: out of memory\n");
        goto cleanup;
    }

    /* seed one RNG stream per pixel (continues across sample passes) */
    for (size_t i = 0; i < N; i++)
        pcg32_seed(&path[i].rng, ((uint64_t)cfg->seed << 32) ^ (uint64_t)i, 0x9e3779b9u);

    for (int sp = 0; sp < cfg->spp; sp++) {
        for (int y = 0; y < H; y++) {
            for (int x = 0; x < W; x++) {
                size_t i = (size_t)y * W + x;
                Path *p = &path[i];
                float px = (x + pcg32_f(&p->rng)) / W;
                float py = (y + pcg32_f(&p->rng)) / H;
                p->ray = camera_ray(cam, px, py);
                p->thr = v3_splat(1.0f);
                p->rad = v3_splat(0.0f);
                p->prev_pdf = 0.0f;
                p->alive = 1; p->spec = 1;
            }
        }

        for (int depth = 0; depth < cfg->max_bounces; depth++) {
            int M = 0;
            for (size_t i = 0; i < N; i++)
                if (path[i].alive) active[M++] = (int)i;
            if (M == 0) break;

            for (int k = 0; k < M; k++) rbatch[k] = path[active[k]].ray;
            rt_closest(rt, rbatch, hbatch, (uint32_t)M);

            ShadeJob job;
            job.s = scene; job.doc = doc; job.bind = bind; job.tex = tex;
            job.env = env; job.sun = &cfg->sun;
            job.path = path; job.active = active; job.hits = hbatch; job.M = M;
            job.shadow = shadow;
            job.depth = depth; job.hide_env_bg = cfg->hide_env_bg;
            atomic_init(&job.next, 0);
            for (int t = 0; t < nt; t++) {
                workers[t].job = &job; workers[t].nnode = doc->nnode;
                pthread_create(&threads[t], NULL, shade_worker, &workers[t]);
            }
            for (int t = 0; t < nt; t++) pthread_join(threads[t], NULL);

            /* compact valid shadow rays, batch-occlude, accumulate direct light */
            int ns = 0;
            for (int k = 0; k < 2 * M; k++) {
                if (shadow[k].valid) { sbatch[ns] = shadow[k].ray; sslot[ns] = k; ns++; }
            }
            if (ns > 0) {
                rt_occluded(rt, sbatch, socc, (uint32_t)ns);
                for (int c = 0; c < ns; c++) {
                    if (!socc[c]) {
                        Shadow *sh = &shadow[sslot[c]];
                        path[sh->owner].rad = v3_add(path[sh->owner].rad, sh->contrib);
                    }
                }
            }

            apply_rr(path, active, M, depth);
        }

        for (size_t i = 0; i < N; i++)
            if (v3_is_finite(path[i].rad))
                fb->accum[i] = v3_add(fb->accum[i], path[i].rad);

        fprintf(stderr, "\rwavefront: %d/%d spp", sp + 1, cfg->spp);
    }
    fprintf(stderr, "\n");
    for (size_t i = 0; i < N; i++) fb->nsamp[i] = cfg->spp;

cleanup:
    free(path); free(active); free(rbatch); free(hbatch); free(shadow);
    free(sbatch); free(sslot); free(socc); free(threads); free(workers);
}
