#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mtlx_eval.h"
#include "mtlx_doc.h"
#include "color.h"
#include "texture.h"

static int near(float actual, float expected, float tolerance) {
  return isfinite(actual) && fabsf(actual - expected) <= tolerance;
}

static int fail(const char *what, const float sample[4]) {
  fprintf(stderr, "FAIL: %s: (%.6f, %.6f, %.6f, %.6f)\n", what,
          sample[0], sample[1], sample[2], sample[3]);
  return 1;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: texture-sampling <fixture.ppm>\n");
    return 2;
  }
  char path[1024];
  snprintf(path, sizeof(path), "%s", argv[1]);
  char *slash = strrchr(path, '/');
  char *backslash = strrchr(path, '\\');
  if (!slash || (backslash && backslash > slash)) slash = backslash;
  const char *base_dir = ".";
  const char *filename = path;
  if (slash) {
    *slash = '\0';
    base_dir = path[0] ? path : "/";
    filename = slash + 1;
  }

  FILE *image = fopen(argv[1], "wb");
  if (!image) {
    perror("cannot create texture fixture");
    return 1;
  }
  static const unsigned char pixels[12] = {
      128, 128, 128,  0, 255, 0,
      0,   0,   255,  255, 255, 255,
  };
  const int wrote = fprintf(image, "P6\n2 2\n255\n") > 0 &&
                    fwrite(pixels, 1, sizeof(pixels), image) == sizeof(pixels);
  const int closed = fclose(image) == 0;
  if (!wrote || !closed) {
    fprintf(stderr, "cannot write texture fixture\n");
    remove(argv[1]);
    return 1;
  }

  TextureCache *cache = texcache_create(base_dir);
  if (!cache) {
    remove(argv[1]);
    return 1;
  }
  const int linear_id = texcache_get(cache, filename, 0);
  const int srgb_id = texcache_get(cache, filename, 1);
  if (linear_id < 0 || srgb_id < 0) {
    texcache_free(cache);
    remove(argv[1]);
    return 1;
  }

  float sample[4];
  if (!near(srgb_to_linear_f(10.0f / 255.0f), 0.00303527f, 2e-8f) ||
      !near(srgb_to_linear_f(11.0f / 255.0f), 0.00334654f, 2e-8f)) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: sRGB linear/power transfer branches\n");
    return 1;
  }
  if (!near(linear_to_srgb_f(0.001f), 0.01292f, 1e-7f) ||
      !near(linear_to_srgb_f(0.5f), 0.735357f, 2e-6f) ||
      !near(linear_to_srgb_f(-0.25f), 0.0f, 1e-7f) ||
      !near(linear_to_srgb_f(1.25f), 1.0f, 1e-7f)) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: linear-to-sRGB branches and input clamp\n");
    return 1;
  }
  texcache_sample_nearest_address(cache, linear_id, 0.25f, 0.75f,
                                  "clamp", "clamp", sample);
  if (!near(sample[0], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[1], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[2], 128.0f / 255.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("nearest texel-center sample", sample);
  }
  texcache_sample_nearest_address(cache, linear_id, 0.25f, 0.25f,
                                  "clamp", "clamp", sample);
  if (!near(sample[0], 0.0f, 1e-6f) || !near(sample[1], 0.0f, 1e-6f) ||
      !near(sample[2], 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("lower-left UV row orientation", sample);
  }

  texcache_sample_address(cache, linear_id, 0.5f, 0.5f,
                          "clamp", "clamp", sample);
  if (!near(sample[0], 0.37549f, 2e-5f) ||
      !near(sample[1], 0.62549f, 2e-5f) ||
      !near(sample[2], 0.62549f, 2e-5f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("bilinear center sample", sample);
  }

  if (!texcache_build_mips(cache, linear_id) ||
      !texcache_build_mips(cache, srgb_id)) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: building linear and sRGB mip chains\n");
    return 1;
  }
  if (!near(texcache_lod_from_grad(cache, linear_id, 0.25f, 0.0f,
                                   0.0f, 0.25f), 0.0f, 1e-6f) ||
      !near(texcache_lod_from_grad(cache, linear_id, 1.0f, 0.0f,
                                   0.0f, 1.0f), 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: derivative-to-mip LOD selection\n");
    return 1;
  }
  texcache_sample_trilinear(cache, linear_id, 0.5f, 0.5f, 1.0f,
                            "clamp", "clamp", sample);
  if (!near(sample[0], 0.37549f, 2e-5f) ||
      !near(sample[1], 0.62549f, 2e-5f) ||
      !near(sample[2], 0.62549f, 2e-5f) || !near(sample[3], 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("linear-space 2x2 mip average", sample);
  }
  texcache_sample_trilinear(cache, srgb_id, 0.5f, 0.5f, 1.0f,
                            "clamp", "clamp", sample);
  if (!near(sample[0], 0.303965f, 2e-5f) ||
      !near(sample[1], 0.553965f, 2e-5f) ||
      !near(sample[2], 0.553965f, 2e-5f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("sRGB-decoded mip generation", sample);
  }
  texcache_sample_trilinear(cache, linear_id, 0.5f, 0.5f, -2.0f,
                            "clamp", "clamp", sample);
  if (!near(sample[0], 0.37549f, 2e-5f) ||
      !near(sample[1], 0.62549f, 2e-5f) ||
      !near(sample[2], 0.62549f, 2e-5f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("negative mip LOD clamps to base level", sample);
  }

  texcache_sample_address_filter(cache, linear_id, 0.375f, 0.75f,
                                 "clamp", "clamp", "cubic", sample);
  if (!near(sample[0], 0.39998f, 2e-4f) ||
      !near(sample[1], 0.60313f, 2e-4f) ||
      !near(sample[2], 0.39998f, 2e-4f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("Catmull-Rom cubic reconstruction", sample);
  }

  texcache_sample_address_grad_filter(cache, linear_id, 0.5f, 0.75f,
                                      0.25f, 0.0f, 0.0f, 0.0f,
                                      "clamp", "clamp", "closest", sample);
  if (!near(sample[0], 0.0f, 1e-6f) || !near(sample[1], 1.0f, 1e-6f) ||
      !near(sample[2], 0.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("sub-texel derivative uses point filter", sample);
  }
  texcache_sample_address_grad_filter(cache, linear_id, 0.5f, 0.75f,
                                      1.0f, 0.0f, 0.0f, 0.0f,
                                      "clamp", "clamp", "closest", sample);
  if (!near(sample[0], 64.0f / 255.0f, 1e-6f) ||
      !near(sample[1], 191.5f / 255.0f, 1e-6f) ||
      !near(sample[2], 64.0f / 255.0f, 1e-6f) ||
      !near(sample[3], 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("wide derivative uses 4x4 footprint integration", sample);
  }

  texcache_sample_nearest_address(cache, linear_id, -0.25f, 0.75f,
                                  "periodic", "clamp", sample);
  if (!near(sample[0], 0.0f, 1e-6f) || !near(sample[1], 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("periodic address mode", sample);
  }
  texcache_sample_nearest_address(cache, linear_id, -0.25f, 0.75f,
                                  "clamp", "clamp", sample);
  if (!near(sample[0], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[1], 128.0f / 255.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("clamp address mode", sample);
  }
  texcache_sample_nearest_address(cache, linear_id, -0.25f, 0.75f,
                                  "mirror", "clamp", sample);
  if (!near(sample[0], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[1], 128.0f / 255.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("mirror address mode", sample);
  }
  texcache_sample_address(cache, linear_id, 0.0f, 0.75f,
                          "constant", "constant", sample);
  if (!near(sample[0], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[1], 128.0f / 255.0f, 1e-6f) ||
      !near(sample[2], 128.0f / 255.0f, 1e-6f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("constant address edge sample", sample);
  }

  texcache_sample_nearest_address(cache, srgb_id, 0.25f, 0.75f,
                                  "clamp", "clamp", sample);
  if (!near(sample[0], 0.21586f, 1e-4f) ||
      !near(sample[1], 0.21586f, 1e-4f) ||
      !near(sample[2], 0.21586f, 1e-4f)) {
    texcache_free(cache);
    remove(argv[1]);
    return fail("sRGB decode", sample);
  }

  char xml[16384];
  snprintf(xml, sizeof(xml),
      "<materialx version=\"1.39\">"
      "<image name=\"sample\" type=\"color3\">"
      "<input name=\"file\" type=\"filename\" value=\"%s\"/>"
      "<input name=\"default\" type=\"color3\" value=\"0.1, 0.2, 0.3\"/>"
      "<input name=\"uaddressmode\" type=\"string\" value=\"constant\"/>"
      "<input name=\"vaddressmode\" type=\"string\" value=\"clamp\"/>"
      "<input name=\"filtertype\" type=\"string\" value=\"cubic\"/>"
      "</image>"
      "<image name=\"literal_uv\" type=\"color3\">"
      "<input name=\"file\" type=\"filename\" value=\"%s\"/>"
      "<input name=\"texcoord\" type=\"vector2\" value=\"0.75,0.25\"/>"
      "<input name=\"filtertype\" type=\"string\" value=\"closest\"/>"
      "</image>"
      "<tiledimage name=\"tiled\" type=\"color3\">"
      "<input name=\"file\" type=\"filename\" value=\"%s\"/>"
      "<input name=\"default\" type=\"color3\" value=\"0.1, 0.2, 0.3\"/>"
      "<input name=\"uvtiling\" type=\"vector2\" value=\"2, 2\"/>"
      "<input name=\"uvoffset\" type=\"vector2\" value=\"0.5, 0\"/>"
      "<input name=\"realworldimagesize\" type=\"vector2\" value=\"2, 2\"/>"
      "<input name=\"realworldtilesize\" type=\"vector2\" value=\"1, 1\"/>"
      "<input name=\"filtertype\" type=\"string\" value=\"closest\"/>"
      "</tiledimage>"
      "<tiledimage name=\"tiled_zero\" type=\"color3\">"
      "<input name=\"file\" type=\"filename\" value=\"%s\"/>"
      "<input name=\"default\" type=\"color3\" value=\"0.1, 0.2, 0.3\"/>"
      "<input name=\"realworldimagesize\" type=\"vector2\" value=\"0, 2\"/>"
      "</tiledimage>"
      "<transformmatrix name=\"acescg_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.705050992658, -0.130256417507, -0.024003356805, -0.621792120657, 1.140804736575, -0.128968976065, -0.083258872001, -0.010548319068, 1.15297233287\"/>"
      "</transformmatrix>"
      "<transformmatrix name=\"linear_adobergb_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.39835574e+00, -2.50233861e-16, 2.77555756e-17, -3.98355744e-01, 1.00000000e+00, -4.29289893e-02, 0.00000000e+00, 0.00000000e+00, 1.04292899e+00\"/>"
      "</transformmatrix>"
      "<max name=\"ap1_nonnegative\" type=\"color3\">"
      "<input name=\"in1\" type=\"color3\" value=\"-0.25, 0.5, 0.75\"/>"
      "<input name=\"in2\" type=\"float\" value=\"0\"/>"
      "</max>"
      "<power name=\"ap1_gamma\" type=\"color3\">"
      "<input name=\"in1\" type=\"color3\" nodename=\"ap1_nonnegative\"/>"
      "<input name=\"in2\" type=\"float\" value=\"2.2\"/>"
      "</power>"
      "<transformmatrix name=\"g22_ap1_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" nodename=\"ap1_gamma\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.705050992658, -0.130256417507, -0.024003356805, -0.621792120657, 1.140804736575, -0.128968976065, -0.083258872001, -0.010548319068, 1.15297233287\"/>"
      "</transformmatrix>"
      "<divide name=\"adobe_gamma\" type=\"float\">"
      "<input name=\"in1\" type=\"float\" value=\"563\"/>"
      "<input name=\"in2\" type=\"float\" value=\"256\"/>"
      "</divide>"
      "<max name=\"adobe_nonnegative\" type=\"color3\">"
      "<input name=\"in1\" type=\"color3\" value=\"-0.25, 0.5, 0.75\"/>"
      "<input name=\"in2\" type=\"float\" value=\"0\"/>"
      "</max>"
      "<power name=\"adobe_encoded_gamma\" type=\"color3\">"
      "<input name=\"in1\" type=\"color3\" nodename=\"adobe_nonnegative\"/>"
      "<input name=\"in2\" type=\"float\" nodename=\"adobe_gamma\"/>"
      "</power>"
      "<transformmatrix name=\"adobergb_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" nodename=\"adobe_encoded_gamma\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.39835574e+00, -2.50233861e-16, 2.77555756e-17, -3.98355744e-01, 1.00000000e+00, -4.29289893e-02, 0.00000000e+00, 0.00000000e+00, 1.04292899e+00\"/>"
      "</transformmatrix>"
      "<transformmatrix name=\"linear_displayp3_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.224940176281, -0.04205695470969, -0.01963755459033, -0.2249401762806, 1.042056954710, -0.07863604555063, 0., 0., 1.098273600141\"/>"
      "</transformmatrix>"
      "<transformmatrix name=\"linear_ap0_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"2.521686186744, -0.276479914230, -0.015378064966, -1.134130988240, 1.372719087668, -0.152975335867, -0.387555198504, -0.096239173438, 1.16835340083\"/>"
      "</transformmatrix>"
      "<transformmatrix name=\"linear_rec2020_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"1.660491002108, -0.124550474522, -0.018150763355, -0.587641138788, 1.132899897126, -0.100578898008, -0.072849863320, -0.008349422604, 1.11872966136\"/>"
      "</transformmatrix>"
      "<transformmatrix name=\"linear_xyzd65_to_rec709\" type=\"vector3\">"
      "<input name=\"in\" type=\"vector3\" value=\"0.25, 0.5, 0.75\"/>"
      "<input name=\"mat\" type=\"matrix33\" value=\"3.240969941905, -0.969243636281, 0.055630079697, -1.53738317757, 1.875967501508, -0.203976958889, -0.498610760293, 0.041555057407, 1.056971514243\"/>"
      "</transformmatrix></materialx>", filename, filename, filename, filename);
  MtlxDoc *doc = mtlx_load_string(xml);
  if (!doc) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: could not load constant-address MaterialX fixture\n");
    return 1;
  }
  const int node = mtlx_find_node(doc, -1, "sample");
  const int literal_node = mtlx_find_node(doc, -1, "literal_uv");
  const int tiled_node = mtlx_find_node(doc, -1, "tiled");
  const int tiled_zero_node = mtlx_find_node(doc, -1, "tiled_zero");
  const int aces_matrix_node = mtlx_find_node(doc, -1, "acescg_to_rec709");
  const int adobe_matrix_node = mtlx_find_node(doc, -1, "linear_adobergb_to_rec709");
  const int g22_ap1_node = mtlx_find_node(doc, -1, "g22_ap1_to_rec709");
  const int adobergb_node = mtlx_find_node(doc, -1, "adobergb_to_rec709");
  const int displayp3_matrix_node =
      mtlx_find_node(doc, -1, "linear_displayp3_to_rec709");
  const int ap0_matrix_node = mtlx_find_node(doc, -1, "linear_ap0_to_rec709");
  const int rec2020_matrix_node =
      mtlx_find_node(doc, -1, "linear_rec2020_to_rec709");
  const int xyz_matrix_node = mtlx_find_node(doc, -1, "linear_xyzd65_to_rec709");
  MtlxValue *memo = (MtlxValue *)calloc((size_t)doc->nnode, sizeof(MtlxValue));
  char *memo_done = (char *)calloc((size_t)doc->nnode, sizeof(char));
  if (node < 0 || literal_node < 0 || tiled_node < 0 || tiled_zero_node < 0 ||
      aces_matrix_node < 0 || adobe_matrix_node < 0 ||
      g22_ap1_node < 0 || adobergb_node < 0 ||
      displayp3_matrix_node < 0 || ap0_matrix_node < 0 ||
      rec2020_matrix_node < 0 || xyz_matrix_node < 0 || !memo || !memo_done) {
    free(memo);
    free(memo_done);
    mtlx_free(doc);
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: invalid constant-address MaterialX fixture state\n");
    return 1;
  }
  ShadeContext context;
  memset(&context, 0, sizeof(context));
  context.doc = doc;
  context.tex = cache;
  context.uv[0] = -0.25f;
  context.uv[1] = 0.75f;
  context.memo = memo;
  context.memo_done = memo_done;
  context.has_uv_derivatives = 1;
  context.uv_dx[0] = 1.0f;
  const MtlxValue literal_uv = mtlx_eval_node_test(&context, literal_node);
  const int literal_uv_ok = literal_uv.type == MV_COLOR3 &&
      near(literal_uv.v[0], 1.0f, 1e-6f) && near(literal_uv.v[1], 1.0f, 1e-6f) &&
      near(literal_uv.v[2], 1.0f, 1e-6f);
  context.has_uv_derivatives = 0;
  context.uv_dx[0] = 0.0f;
  const MtlxValue aces_matrix =
      mtlx_eval_node_test(&context, aces_matrix_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue adobe_matrix =
      mtlx_eval_node_test(&context, adobe_matrix_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue g22_ap1 =
      mtlx_eval_node_test(&context, g22_ap1_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue adobergb =
      mtlx_eval_node_test(&context, adobergb_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue displayp3_matrix =
      mtlx_eval_node_test(&context, displayp3_matrix_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue ap0_matrix = mtlx_eval_node_test(&context, ap0_matrix_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue rec2020_matrix =
      mtlx_eval_node_test(&context, rec2020_matrix_node);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue xyz_matrix = mtlx_eval_node_test(&context, xyz_matrix_node);
  int matrix_ok =
      aces_matrix.type == MV_VEC3 &&
      near(aces_matrix.v[0], 0.052922534f, 2e-6f) &&
      near(aces_matrix.v[1], 0.529927025f, 2e-6f) &&
      near(aces_matrix.v[2], 0.794243922f, 2e-6f) &&
      adobe_matrix.type == MV_VEC3 &&
      near(adobe_matrix.v[0], 0.150411063f, 2e-6f) &&
      near(adobe_matrix.v[1], 0.5f, 2e-6f) &&
      near(adobe_matrix.v[2], 0.760732248f, 2e-6f) &&
      g22_ap1.type == MV_VEC3 &&
      near(g22_ap1.v[0], -0.179539930f, 3e-6f) &&
      near(g22_ap1.v[1], 0.242680375f, 3e-6f) &&
      near(g22_ap1.v[2], 0.584216560f, 3e-6f) &&
      adobergb.type == MV_VEC3 &&
      near(adobergb.v[0], -0.086744165f, 3e-6f) &&
      near(adobergb.v[1], 0.217755528f, 3e-6f) &&
      near(adobergb.v[2], 0.544623099f, 3e-6f);
  const MtlxValue matrix_values[] = {
      displayp3_matrix, ap0_matrix, rec2020_matrix, xyz_matrix};
  const float expected_matrix_values[][3] = {
      {0.193764956f, 0.510514239f, 0.779477789f},
      {-0.227310346f, 0.545060185f, 0.795932866f},
      {0.066664784f, 0.529050263f, 0.784220106f},
      {-0.332407174f, 0.726839135f, 0.704647676f}};
  for (size_t conversion = 0; conversion < 4; ++conversion) {
    matrix_ok = matrix_ok && matrix_values[conversion].type == MV_VEC3;
    for (size_t channel = 0; channel < 3; ++channel) {
      matrix_ok = matrix_ok &&
          near(matrix_values[conversion].v[channel],
               expected_matrix_values[conversion][channel], 3e-6f);
    }
  }
  if (!matrix_ok) {
    fprintf(stderr, "FAIL: cmlib color-space conversion result\\n");
    free(memo);
    free(memo_done);
    mtlx_free(doc);
    texcache_free(cache);
    remove(argv[1]);
    return 1;
  }
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue fallback = mtlx_eval_node_test(&context, node);
  const int fallback_ok = fallback.type == MV_COLOR3 &&
      near(fallback.v[0], 0.1f, 1e-6f) &&
      near(fallback.v[1], 0.2f, 1e-6f) &&
      near(fallback.v[2], 0.3f, 1e-6f);
  context.uv[0] = 0.375f;
  context.uv[1] = 0.75f;
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue cubic_image = mtlx_eval_node_test(&context, node);
  const int cubic_image_ok = cubic_image.type == MV_COLOR3 &&
      near(cubic_image.v[0], 0.39998f, 2e-4f) &&
      near(cubic_image.v[1], 0.60313f, 2e-4f) &&
      near(cubic_image.v[2], 0.39998f, 2e-4f);
  context.uv[0] = 0.5f;
  context.uv[1] = 0.75f;
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue tiled_sample = mtlx_eval_node_test(&context, tiled_node);
  const int tiled_sample_ok = tiled_sample.type == MV_COLOR3 &&
      near(tiled_sample.v[0], 128.0f / 255.0f, 1e-6f) &&
      near(tiled_sample.v[1], 128.0f / 255.0f, 1e-6f) &&
      near(tiled_sample.v[2], 128.0f / 255.0f, 1e-6f);
  memset(memo_done, 0, (size_t)doc->nnode * sizeof(char));
  const MtlxValue tiled_zero = mtlx_eval_node_test(&context, tiled_zero_node);
  const int tiled_zero_ok = tiled_zero.type == MV_COLOR3 &&
      near(tiled_zero.v[0], 0.1f, 1e-6f) &&
      near(tiled_zero.v[1], 0.2f, 1e-6f) &&
      near(tiled_zero.v[2], 0.3f, 1e-6f);
  free(memo);
  free(memo_done);
  mtlx_free(doc);
  if (!literal_uv_ok || !fallback_ok || !cubic_image_ok || !tiled_sample_ok || !tiled_zero_ok) {
    texcache_free(cache);
    remove(argv[1]);
    fprintf(stderr, "FAIL: MaterialX texture filter, tiledimage transform, or constant default behavior\n");
    return 1;
  }

  char odd_path[1032], odd_filename[1032];
  snprintf(odd_path, sizeof(odd_path), "%s.odd.ppm", argv[1]);
  snprintf(odd_filename, sizeof(odd_filename), "%s.odd.ppm", filename);
  FILE *odd_image = fopen(odd_path, "wb");
  static const unsigned char odd_pixels[9] = {
      255, 0, 0,  0, 255, 0,  0, 0, 255,
  };
  const int odd_wrote = odd_image &&
      fprintf(odd_image, "P6\n3 1\n255\n") > 0 &&
      fwrite(odd_pixels, 1, sizeof(odd_pixels), odd_image) == sizeof(odd_pixels);
  const int odd_closed = odd_image ? fclose(odd_image) == 0 : 0;
  const int odd_id = odd_wrote && odd_closed
      ? texcache_get(cache, odd_filename, 0) : -1;
  if (odd_id < 0 || !texcache_build_mips(cache, odd_id)) {
    texcache_free(cache);
    remove(odd_path);
    remove(argv[1]);
    fprintf(stderr, "FAIL: building round-up mips for odd image dimensions\n");
    return 1;
  }
  texcache_sample_trilinear(cache, odd_id, 0.75f, 0.5f, 1.0f,
                            "clamp", "clamp", sample);
  if (!near(sample[0], 0.0f, 1e-6f) ||
      !near(sample[1], 0.0f, 1e-6f) || !near(sample[2], 1.0f, 1e-6f)) {
    texcache_free(cache);
    remove(odd_path);
    remove(argv[1]);
    return fail("round-up mip retains the unmatched edge texel", sample);
  }
  texcache_sample_trilinear(cache, odd_id, 0.5f, 0.5f, 2.0f,
                            "clamp", "clamp", sample);
  if (!near(sample[0], 0.25f, 1e-6f) ||
      !near(sample[1], 0.25f, 1e-6f) ||
      !near(sample[2], 0.5f, 1e-6f)) {
    texcache_free(cache);
    remove(odd_path);
    remove(argv[1]);
    return fail("odd-edge mip pyramid terminal average", sample);
  }

  texcache_free(cache);
  remove(odd_path);
  remove(argv[1]);
  puts("PASS: nearest/bilinear/cubic, derivative footprint, mip generation/LOD, color matrices and gamma, UV orientation, addressing, and sRGB sampling");
  return 0;
}
