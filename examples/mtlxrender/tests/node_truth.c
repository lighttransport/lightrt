/*
 * node_truth.c - per-node numeric GROUND-TRUTH tests for the MaterialX
 * interpreter.
 *
 * Each case feeds inputs through the real parse -> doc -> eval path and asserts
 * the output equals a value computed INDEPENDENTLY from the MaterialX node's
 * spec definition (basic math / the documented formula), not from our own
 * implementation. This validates node correctness, not self-consistency.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mtlx_doc.h"
#include "mtlx_eval.h"
#include "vecmath.h"

static int g_total = 0, g_fail = 0;

static MtlxValue mv_from(v3 c) { MtlxValue v; memset(&v, 0, sizeof(v)); v.type = MV_COLOR3; v.v[0]=c.x; v.v[1]=c.y; v.v[2]=c.z; return v; }

typedef struct { float uv[2]; v3 P, Ns; } Geo;

/* Evaluate node `name` inside a one-graph snippet; return its value. */
static MtlxValue ev(const char *inner, const char *name, Geo g) {
    char buf[8192];
    snprintf(buf, sizeof(buf),
             "<?xml version=\"1.0\"?>\n<materialx version=\"1.39\">\n"
             "<nodegraph name=\"t\">\n%s\n</nodegraph>\n</materialx>\n", inner);
    MtlxDoc *d = mtlx_load_string(buf);
    if (!d) { fprintf(stderr, "parse failed for %s\n", name); MtlxValue z; memset(&z,0,sizeof(z)); return z; }
    int id = mtlx_find_node(d, 0, name);
    ShadeContext ctx; memset(&ctx, 0, sizeof(ctx));
    ctx.doc = d; ctx.tex = NULL;
    ctx.uv[0] = g.uv[0]; ctx.uv[1] = g.uv[1];
    ctx.P = g.P; ctx.Ns = g.Ns; ctx.Ng = g.Ns;
    ctx.dpdu = v3_make(1, 0, 0); ctx.dpdv = v3_make(0, 0, 1);
    ctx.memo = malloc(sizeof(MtlxValue) * (size_t)(d->nnode > 0 ? d->nnode : 1));
    ctx.memo_done = malloc((size_t)(d->nnode > 0 ? d->nnode : 1));
    MtlxValue r = (id >= 0) ? mtlx_eval_node_test(&ctx, id) : (MtlxValue){0};
    free(ctx.memo); free(ctx.memo_done); mtlx_free(d);
    return r;
}

static Geo geo0(void) { Geo g = { {0.25f, 0.75f}, {1, 2, 3}, {0, 1, 0} }; return g; }

/* Evaluate a top-level surface shader node into OpenPBR params. */
static OpenPBRParams eval_surf(const char *shader_xml, const char *name) {
    char buf[8192];
    snprintf(buf, sizeof(buf),
             "<?xml version=\"1.0\"?>\n<materialx version=\"1.39\">\n%s\n</materialx>\n", shader_xml);
    MtlxDoc *d = mtlx_load_string(buf);
    OpenPBRParams p; openpbr_defaults(&p);
    if (d) {
        int id = mtlx_find_node(d, -1, name);
        ShadeContext ctx; memset(&ctx, 0, sizeof(ctx));
        ctx.doc = d; ctx.Ns = v3_make(0, 1, 0); ctx.Ng = ctx.Ns;
        ctx.dpdu = v3_make(1, 0, 0); ctx.dpdv = v3_make(0, 0, 1);
        ctx.memo = malloc(sizeof(MtlxValue) * (size_t)(d->nnode > 0 ? d->nnode : 1));
        ctx.memo_done = malloc((size_t)(d->nnode > 0 ? d->nnode : 1));
        mtlx_eval_surface(&ctx, id, &p);
        free(ctx.memo); free(ctx.memo_done); mtlx_free(d);
    }
    return p;
}

static void chk1(const char *name, float got, float exp) {
    g_total++;
    if (fabsf(got - exp) > 1e-3f) { printf("  FAIL %-22s got %.5f  exp %.5f\n", name, got, exp); g_fail++; }
    else printf("  ok   %-22s = %.5f\n", name, got);
}
static void chk3(const char *name, MtlxValue v, float x, float y, float z) {
    g_total++;
    if (fabsf(v.v[0]-x) > 1e-3f || fabsf(v.v[1]-y) > 1e-3f || fabsf(v.v[2]-z) > 1e-3f) {
        printf("  FAIL %-22s got (%.4f %.4f %.4f) exp (%.4f %.4f %.4f)\n", name, v.v[0],v.v[1],v.v[2], x,y,z);
        g_fail++;
    } else printf("  ok   %-22s = (%.4f %.4f %.4f)\n", name, v.v[0], v.v[1], v.v[2]);
}

/* helper: a single float-output node with two float inputs */
#define BIN(cat, a, b) \
    "<" cat " name=\"n\" type=\"float\"><input name=\"in1\" type=\"float\" value=\"" a \
    "\"/><input name=\"in2\" type=\"float\" value=\"" b "\"/></" cat ">"
#define UN(cat, a) \
    "<" cat " name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"" a "\"/></" cat ">"

int main(void) {
    Geo g = geo0();
    printf("MaterialX node ground-truth tests\n");

    /* ---- math: binary (definition = the operation) ---- */
    chk1("add",        ev(BIN("add","2","3"), "n", g).v[0], 5.0f);
    chk1("subtract",   ev(BIN("subtract","5","2"), "n", g).v[0], 3.0f);
    chk1("multiply",   ev(BIN("multiply","4","2.5"), "n", g).v[0], 10.0f);
    chk1("divide",     ev(BIN("divide","6","3"), "n", g).v[0], 2.0f);
    chk1("modulo",     ev(BIN("modulo","5","3"), "n", g).v[0], 2.0f);
    chk1("power",      ev(BIN("power","2","3"), "n", g).v[0], 8.0f);
    chk1("min",        ev(BIN("min","3","5"), "n", g).v[0], 3.0f);
    chk1("max",        ev(BIN("max","3","5"), "n", g).v[0], 5.0f);
    chk1("atan2",      ev(BIN("atan2","1","1"), "n", g).v[0], (float)(M_PI/4));

    /* ---- math: unary ---- */
    chk1("sin",        ev(UN("sin","0"), "n", g).v[0], 0.0f);
    chk1("cos",        ev(UN("cos","0"), "n", g).v[0], 1.0f);
    chk1("tan",        ev(UN("tan","0"), "n", g).v[0], 0.0f);
    chk1("asin",       ev(UN("asin","1"), "n", g).v[0], (float)(M_PI/2));
    chk1("acos",       ev(UN("acos","1"), "n", g).v[0], 0.0f);
    chk1("sqrt",       ev(UN("sqrt","9"), "n", g).v[0], 3.0f);
    chk1("ln",         ev(UN("ln","1"), "n", g).v[0], 0.0f);
    chk1("exp",        ev(UN("exp","0"), "n", g).v[0], 1.0f);
    chk1("abs",        ev(UN("absval","-4"), "n", g).v[0], 4.0f);
    chk1("floor",      ev(UN("floor","2.7"), "n", g).v[0], 2.0f);
    chk1("ceil",       ev(UN("ceil","2.1"), "n", g).v[0], 3.0f);
    chk1("round",      ev(UN("round","2.4"), "n", g).v[0], 2.0f);
    chk1("sign",       ev(UN("sign","-3"), "n", g).v[0], -1.0f);

    /* ---- vector math ---- */
    chk1("dotproduct",
         ev("<dotproduct name=\"n\" type=\"float\"><input name=\"in1\" type=\"vector3\" value=\"1,2,3\"/>"
            "<input name=\"in2\" type=\"vector3\" value=\"4,5,6\"/></dotproduct>", "n", g).v[0], 32.0f);
    chk3("crossproduct",
         ev("<crossproduct name=\"n\" type=\"vector3\"><input name=\"in1\" type=\"vector3\" value=\"1,0,0\"/>"
            "<input name=\"in2\" type=\"vector3\" value=\"0,1,0\"/></crossproduct>", "n", g), 0, 0, 1);
    chk1("magnitude",
         ev("<magnitude name=\"n\" type=\"float\"><input name=\"in\" type=\"vector3\" value=\"3,4,0\"/></magnitude>", "n", g).v[0], 5.0f);
    chk3("normalize",
         ev("<normalize name=\"n\" type=\"vector3\"><input name=\"in\" type=\"vector3\" value=\"0,3,0\"/></normalize>", "n", g), 0, 1, 0);

    /* ---- compositing / adjust ---- */
    chk1("mix", ev("<mix name=\"n\" type=\"float\"><input name=\"fg\" type=\"float\" value=\"10\"/>"
                   "<input name=\"bg\" type=\"float\" value=\"2\"/><input name=\"mix\" type=\"float\" value=\"0.25\"/></mix>",
                   "n", g).v[0], 4.0f); /* 2*0.75 + 10*0.25 */
    chk1("clamp_hi", ev("<clamp name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"1.5\"/>"
                        "<input name=\"low\" type=\"float\" value=\"0\"/><input name=\"high\" type=\"float\" value=\"1\"/></clamp>", "n", g).v[0], 1.0f);
    chk1("clamp_lo", ev("<clamp name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"-0.5\"/>"
                        "<input name=\"low\" type=\"float\" value=\"0\"/><input name=\"high\" type=\"float\" value=\"1\"/></clamp>", "n", g).v[0], 0.0f);
    chk1("smoothstep", ev("<smoothstep name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.5\"/>"
                          "<input name=\"low\" type=\"float\" value=\"0\"/><input name=\"high\" type=\"float\" value=\"1\"/></smoothstep>", "n", g).v[0], 0.5f);
    chk1("remap", ev("<remap name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.5\"/>"
                     "<input name=\"inlow\" type=\"float\" value=\"0\"/><input name=\"inhigh\" type=\"float\" value=\"1\"/>"
                     "<input name=\"outlow\" type=\"float\" value=\"10\"/><input name=\"outhigh\" type=\"float\" value=\"20\"/></remap>", "n", g).v[0], 15.0f);
    chk1("range", ev("<range name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.5\"/>"
                     "<input name=\"inhigh\" type=\"float\" value=\"1\"/><input name=\"outhigh\" type=\"float\" value=\"10\"/></range>", "n", g).v[0], 5.0f);
    chk1("contrast", ev("<contrast name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.75\"/>"
                        "<input name=\"amount\" type=\"float\" value=\"2\"/><input name=\"pivot\" type=\"float\" value=\"0.5\"/></contrast>", "n", g).v[0], 1.0f);
    chk1("invert", ev("<invert name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.3\"/></invert>", "n", g).v[0], 0.7f);
    chk1("luminance_white",
         ev("<luminance name=\"n\" type=\"color3\"><input name=\"in\" type=\"color3\" value=\"1,1,1\"/></luminance>", "n", g).v[0], 1.0f);
    chk1("luminance_red",
         ev("<luminance name=\"n\" type=\"color3\"><input name=\"in\" type=\"color3\" value=\"1,0,0\"/></luminance>", "n", g).v[0], 0.2126f);

    /* ---- color spaces (Rec.709 HSV) ---- */
    chk3("rgbtohsv_red",
         ev("<rgbtohsv name=\"n\" type=\"color3\"><input name=\"in\" type=\"color3\" value=\"1,0,0\"/></rgbtohsv>", "n", g), 0, 1, 1);
    chk3("hsvtorgb_red",
         ev("<hsvtorgb name=\"n\" type=\"color3\"><input name=\"in\" type=\"color3\" value=\"0,1,1\"/></hsvtorgb>", "n", g), 1, 0, 0);

    /* ---- channel ---- */
    chk3("combine3",
         ev("<combine3 name=\"n\" type=\"vector3\"><input name=\"in1\" type=\"float\" value=\"1\"/>"
            "<input name=\"in2\" type=\"float\" value=\"2\"/><input name=\"in3\" type=\"float\" value=\"3\"/></combine3>", "n", g), 1, 2, 3);
    chk1("extract_index2",
         ev("<extract name=\"n\" type=\"float\"><input name=\"in\" type=\"color3\" value=\"9,8,7\"/>"
            "<input name=\"index\" type=\"integer\" value=\"2\"/></extract>", "n", g).v[0], 7.0f);
    chk1("separate3.outg",
         ev("<separate3 name=\"s\" type=\"vector3\"><input name=\"in\" type=\"vector3\" value=\"0.1,0.2,0.3\"/></separate3>"
            "<multiply name=\"n\" type=\"float\"><input name=\"in1\" type=\"float\" nodename=\"s\" output=\"outg\"/>"
            "<input name=\"in2\" type=\"float\" value=\"1\"/></multiply>", "n", g).v[0], 0.2f);

    /* ---- geometric (return shading-context values) ---- */
    chk3("position", ev("<position name=\"n\" type=\"vector3\"/>", "n", g), 1, 2, 3);
    chk3("normal",   ev("<normal name=\"n\" type=\"vector3\"/>", "n", g), 0, 1, 0);
    chk3("tangent",  ev("<tangent name=\"n\" type=\"vector3\"/>", "n", g), 1, 0, 0);
    { MtlxValue tc = ev("<texcoord name=\"n\" type=\"vector2\"/>", "n", g);
      chk1("texcoord.u", tc.v[0], 0.25f); chk1("texcoord.v", tc.v[1], 0.75f); }

    /* ---- conditional / utility ---- */
    chk1("ifgreater_t", ev("<ifgreater name=\"n\" type=\"float\"><input name=\"value1\" type=\"float\" value=\"3\"/>"
                           "<input name=\"value2\" type=\"float\" value=\"2\"/><input name=\"in1\" type=\"float\" value=\"10\"/>"
                           "<input name=\"in2\" type=\"float\" value=\"20\"/></ifgreater>", "n", g).v[0], 10.0f);
    chk1("ifgreater_f", ev("<ifgreater name=\"n\" type=\"float\"><input name=\"value1\" type=\"float\" value=\"1\"/>"
                           "<input name=\"value2\" type=\"float\" value=\"2\"/><input name=\"in1\" type=\"float\" value=\"10\"/>"
                           "<input name=\"in2\" type=\"float\" value=\"20\"/></ifgreater>", "n", g).v[0], 20.0f);
    chk1("ifequal", ev("<ifequal name=\"n\" type=\"float\"><input name=\"value1\" type=\"float\" value=\"5\"/>"
                       "<input name=\"value2\" type=\"float\" value=\"5\"/><input name=\"in1\" type=\"float\" value=\"1\"/>"
                       "<input name=\"in2\" type=\"float\" value=\"0\"/></ifequal>", "n", g).v[0], 1.0f);
    chk1("switch_which2", ev("<switch name=\"n\" type=\"float\"><input name=\"in1\" type=\"float\" value=\"10\"/>"
                             "<input name=\"in2\" type=\"float\" value=\"20\"/><input name=\"in3\" type=\"float\" value=\"30\"/>"
                             "<input name=\"which\" type=\"integer\" value=\"2\"/></switch>", "n", g).v[0], 30.0f);
    chk1("dot", ev("<dot name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"7\"/></dot>", "n", g).v[0], 7.0f);
    chk1("oneminus", ev("<oneminus name=\"n\" type=\"float\"><input name=\"in\" type=\"float\" value=\"0.3\"/></oneminus>", "n", g).v[0], 0.7f);
    chk3("rotate2d_90", ev("<rotate2d name=\"n\" type=\"vector2\"><input name=\"in\" type=\"vector2\" value=\"1,0\"/>"
                           "<input name=\"amount\" type=\"float\" value=\"90\"/></rotate2d>", "n", g), 0, 1, 0);
    chk1("ramp4_br", ev("<ramp4 name=\"n\" type=\"float\"><input name=\"valuetl\" type=\"float\" value=\"1\"/>"
                        "<input name=\"valuetr\" type=\"float\" value=\"2\"/><input name=\"valuebl\" type=\"float\" value=\"3\"/>"
                        "<input name=\"valuebr\" type=\"float\" value=\"4\"/><input name=\"texcoord\" type=\"vector2\" value=\"1,1\"/></ramp4>", "n", g).v[0], 4.0f);

    /* ---- more adjust / channel ---- */
    chk1("saturate_gray", ev("<saturate name=\"n\" type=\"color3\"><input name=\"in\" type=\"color3\" value=\"1,0,0\"/>"
                             "<input name=\"amount\" type=\"float\" value=\"0\"/></saturate>", "n", g).v[0], 0.2126f);
    chk3("combine2_pad", ev("<combine2 name=\"n\" type=\"vector2\"><input name=\"in1\" type=\"float\" value=\"0.5\"/>"
                            "<input name=\"in2\" type=\"float\" value=\"0.25\"/></combine2>", "n", g), 0.5f, 0.25f, 0.0f);
    chk3("convert_f_to_c3", ev("<convert name=\"n\" type=\"color3\"><input name=\"in\" type=\"float\" value=\"0.4\"/></convert>", "n", g), 0.4f, 0.4f, 0.4f);

    /* ---- surface shader -> OpenPBR parameter mapping ground truth ---- */
    { OpenPBRParams p = eval_surf(
        "<standard_surface name=\"s\" type=\"surfaceshader\">"
        "<input name=\"base_color\" type=\"color3\" value=\"0.2,0.4,0.6\"/>"
        "<input name=\"metalness\" type=\"float\" value=\"0.7\"/>"
        "<input name=\"specular_roughness\" type=\"float\" value=\"0.25\"/></standard_surface>", "s");
      chk3("std_surface.base_color", mv_from(p.base_color), 0.2f, 0.4f, 0.6f);
      chk1("std_surface.metalness", p.metalness, 0.7f);
      chk1("std_surface.roughness", p.specular_roughness, 0.25f); }
    { OpenPBRParams p = eval_surf(
        "<gltf_pbr name=\"s\" type=\"surfaceshader\">"
        "<input name=\"base_color\" type=\"color3\" value=\"0.1,0.5,0.9\"/>"
        "<input name=\"metallic\" type=\"float\" value=\"0.3\"/></gltf_pbr>", "s");
      chk3("gltf_pbr.base_color", mv_from(p.base_color), 0.1f, 0.5f, 0.9f);
      chk1("gltf_pbr.metalness", p.metalness, 0.3f); }
    { OpenPBRParams p = eval_surf(
        "<UsdPreviewSurface name=\"s\" type=\"surfaceshader\">"
        "<input name=\"diffuseColor\" type=\"color3\" value=\"0.8,0.2,0.1\"/>"
        "<input name=\"metallic\" type=\"float\" value=\"0.0\"/></UsdPreviewSurface>", "s");
      chk3("usd.diffuse->base", mv_from(p.base_color), 0.8f, 0.2f, 0.1f); }
    { OpenPBRParams p = eval_surf(
        "<disney_principled name=\"s\" type=\"surfaceshader\">"
        "<input name=\"baseColor\" type=\"color3\" value=\"0.3,0.6,0.3\"/>"
        "<input name=\"subsurface\" type=\"float\" value=\"0.5\"/></disney_principled>", "s");
      chk3("disney.base_color", mv_from(p.base_color), 0.3f, 0.6f, 0.3f);
      chk1("disney.subsurface", p.subsurface, 0.5f); }

    /* ---- procedural invariants (implementation-defined values; check spec
     *      properties instead of exact numbers) ---- */
    { MtlxValue a = ev("<noise3d name=\"n\" type=\"float\"><input name=\"position\" type=\"vector3\" value=\"1.5,2.5,3.5\"/></noise3d>", "n", g);
      MtlxValue b = ev("<noise3d name=\"n\" type=\"float\"><input name=\"position\" type=\"vector3\" value=\"1.5,2.5,3.5\"/></noise3d>", "n", g);
      g_total++; if (a.v[0] != b.v[0] || a.v[0] < -1.01f || a.v[0] > 1.01f) { printf("  FAIL noise3d (determinism/range) %.4f\n", a.v[0]); g_fail++; }
      else printf("  ok   noise3d (det,[-1,1])    = %.5f\n", a.v[0]); }
    { MtlxValue c = ev("<cellnoise3d name=\"n\" type=\"float\"><input name=\"position\" type=\"vector3\" value=\"0.5,0.5,0.5\"/></cellnoise3d>", "n", g);
      g_total++; if (c.v[0] < 0.0f || c.v[0] > 1.0f) { printf("  FAIL cellnoise3d range %.4f\n", c.v[0]); g_fail++; }
      else printf("  ok   cellnoise3d ([0,1])     = %.5f\n", c.v[0]); }

    printf("----\nnode ground-truth: %d/%d passed, %d failed\n", g_total - g_fail, g_total, g_fail);
    return g_fail == 0 ? 0 : 1;
}
