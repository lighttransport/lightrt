/* Differential-testing driver, C side: runs the *real* scalar LightRT kernels
 * (lightrt_c_tri.c is #included so its static functions are visible) on the
 * vectors of tools/cdiff.py and prints results in the format of CDiff.lean.
 * Build with -ffp-contract=off (no FMA contraction) so the C is bit-exact
 * with the MiniC binary32 semantics. */
#include "lightrt_c_tri.c"
#include <stdio.h>
#include <string.h>

static float f(unsigned x) { float r; memcpy(&r, &x, 4); return r; }
static unsigned b(float x) { unsigned r; memcpy(&r, &x, 4); return r; }

int main(void) {
    char kind[16];
    while (scanf("%15s", kind) == 1) {
        if (strcmp(kind, "slab") == 0 || strcmp(kind, "slabr") == 0) {
            unsigned w[15];
            for (int k = 0; k < 15; k++) if (scanf("%x", &w[k]) != 1) return 1;
            lrt_ray ray;
            float in[8];
            for (int k = 0; k < 8; k++) in[k] = f(w[k]);
            memcpy(&ray, in, sizeof ray);
            tri_ray_ctx rc;
            memset(&rc, 0, sizeof rc);
            tri_ray_setup(&ray, &rc);
            unsigned words[16]; /* 13 legacy words; + sinv[3] in the default build */
            int nw = 13;
#ifdef LRT_TRI_SLAB_ROBUST
            nw = 16;
            memcpy(words, &rc, 52);
            memcpy(words + 13, rc.sinv, 12);
#else
            memcpy(words, &rc, 52);
#endif
            for (int k = 0; k < nw; k++) printf("%08x ", words[k]);
            float lo[3] = {f(w[8]), f(w[9]), f(w[10])}, hi[3] = {f(w[11]), f(w[12]), f(w[13])};
            float tnear = 0.0f;
            int r = tri_slab_scalar(&lo[0], &lo[1], &lo[2], &hi[0], &hi[1], &hi[2], 0, &rc,
                                    f(w[14]), &tnear);
            printf("%d %08x\n", r, b(tnear));
        } else if (strcmp(kind, "mt") == 0) {
            unsigned w[17];
            for (int k = 0; k < 17; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float v[15];
            for (int k = 0; k < 15; k++) v[k] = f(w[k]);
            float t = 0, u = 0, vv = 0;
            int r = tri_mt_one(&v[0], &v[3], &v[6], &v[9], &v[12], f(w[15]), f(w[16]), &t, &u, &vv);
            if (r == 1) printf("1 %08x %08x %08x\n", b(t), b(u), b(vv));
            else printf("%d\n", r);
        } else if (strcmp(kind, "woop") == 0) {
            unsigned w[17];
            for (int k = 0; k < 17; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float v[15];
            for (int k = 0; k < 15; k++) v[k] = f(w[k]);
            float t = 0, u = 0, vv = 0;
            int r = tri_woop_one(&v[0], &v[3], &v[6], &v[9], &v[12], f(w[15]), f(w[16]), &t, &u, &vv);
            if (r == 1) printf("1 %08x %08x %08x\n", b(t), b(u), b(vv));
            else printf("%d\n", r);
        } else {
            printf("BADLINE\n");
        }
        fflush(stdout);
    }
    return 0;
}
