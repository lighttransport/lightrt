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
        } else if (strcmp(kind, "sph") == 0) {
            /* sqrt path: scalar ray/sphere distance (tri_sphere_dist_f). */
            unsigned w[10];
            for (int k = 0; k < 10; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float in[10];
            for (int k = 0; k < 10; k++) in[k] = f(w[k]);
            printf("%08x\n", b(tri_sphere_dist_f(in, in + 3, in + 6, in[9])));
        } else if (strcmp(kind, "sdfs") == 0) {
            unsigned w[4];
            for (int k = 0; k < 4; k++) if (scanf("%x", &w[k]) != 1) return 1;
            printf("%08x\n", b(tri_sdf_sphere_core(f(w[0]), f(w[1]), f(w[2]), f(w[3]))));
        } else if (strcmp(kind, "sdfb") == 0) {
            unsigned w[6];
            for (int k = 0; k < 6; k++) if (scanf("%x", &w[k]) != 1) return 1;
            printf("%08x\n", b(tri_sdf_box_core(f(w[0]), f(w[1]), f(w[2]),
                                               f(w[3]), f(w[4]), f(w[5]))));
        } else if (strcmp(kind, "sdft") == 0) {
            unsigned w[5];
            for (int k = 0; k < 5; k++) if (scanf("%x", &w[k]) != 1) return 1;
            printf("%08x\n", b(tri_sdf_torus_core(f(w[0]), f(w[1]), f(w[2]),
                                                  f(w[3]), f(w[4]))));
        } else if (strcmp(kind, "bilin") == 0) {
            unsigned w[18];
            for (int k = 0; k < 18; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float in[18], oa, ob, oc;
            for (int k = 0; k < 18; k++) in[k] = f(w[k]);
            tri_bilin_quad_core(in, in + 3, in + 6, in + 9, in + 12, in + 15,
                                &oa, &ob, &oc);
            printf("%08x %08x %08x\n", b(oa), b(ob), b(oc));
        } else if (strcmp(kind, "rlcy") == 0) {
            unsigned w[9];
            for (int k = 0; k < 9; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float in[9];
            for (int k = 0; k < 9; k++) in[k] = f(w[k]);
            printf("%08x\n", b(tri_rlc_plane_y_core(in, in + 3, in + 6)));
        } else if (strcmp(kind, "rlcc") == 0) {
            unsigned w[11];
            for (int k = 0; k < 11; k++) if (scanf("%x", &w[k]) != 1) return 1;
            float in[11];
            for (int k = 0; k < 11; k++) in[k] = f(w[k]);
            printf("%d\n", tri_rlc_cone_test_core(in, in[3], in + 4, in[7], in + 8));
        } else if (strcmp(kind, "detp") == 0) {
            unsigned w[7];
            for (int k = 0; k < 7; k++) if (scanf("%x", &w[k]) != 1) return 1;
            printf("%d\n", tri_isect_det_parallel(f(w[0]), f(w[1]), f(w[2]),
                                                  f(w[3]), f(w[4]), f(w[5]), f(w[6])));
        } else {
            printf("BADLINE\n");
        }
        fflush(stdout);
    }
    return 0;
}
