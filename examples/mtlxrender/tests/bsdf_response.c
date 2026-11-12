/* Pointwise regression for LightRT's isolated isotropic dielectric GGX lobe.
 * Expected values are generated from the corresponding Lean implementation
 * model. This checks native evaluator consistency, not complete MaterialX
 * OpenPBR parity (the renderer uses separable Smith visibility). */
#include "bsdf.h"

#include <math.h>
#include <stdio.h>
#include <string.h>

typedef struct {
  int id;
  float roughness;
  float ior;
  float weight;
  v3 color;
  v3 wo;
  v3 wi;
  v3 expected;
} BsdfResponseVector;

#define MTLX_BSDF_RESPONSE(id_, roughness_, ior_, weight_, cr_, cg_, cb_, \
                           vox_, voy_, voz_, lix_, liy_, liz_, er_, eg_, eb_) \
  { id_, roughness_, ior_, weight_, { cr_, cg_, cb_ }, \
    { vox_, voy_, voz_ }, { lix_, liy_, liz_ }, { er_, eg_, eb_ } },
static const BsdfResponseVector vectors[] = {
#include "generated/bsdf-response.inc"
};
#undef MTLX_BSDF_RESPONSE

static int close3(v3 actual, v3 expected, float tolerance) {
  return fabsf(actual.x - expected.x) <= tolerance &&
         fabsf(actual.y - expected.y) <= tolerance &&
         fabsf(actual.z - expected.z) <= tolerance;
}

int main(void) {
  const v3 normal = v3_make(0.0f, 0.0f, 1.0f);
  const float tolerance = 2.0e-5f;
  for (size_t i = 0; i < sizeof(vectors) / sizeof(vectors[0]); ++i) {
    const BsdfResponseVector *v = &vectors[i];
    OpenPBRParams p;
    memset(&p, 0, sizeof(p));
    p.base_weight = 0.0f;
    p.specular_weight = v->weight;
    p.specular_color = v->color;
    p.specular_roughness = v->roughness;
    p.specular_ior = v->ior;
    p.transmission_color = v3_splat(1.0f);
    p.coat_ior = 1.5f;
    p.normal = normal;
    p.opacity = 1.0f;

    v3 diffuse, specular;
    float pdf = 0.0f;
    (void)bsdf_eval_lobes(&p, normal, v->wo, v->wi,
                          &diffuse, &specular, &pdf);
    if (!close3(specular, v->expected, tolerance) ||
        !close3(diffuse, v3_splat(0.0f), tolerance)) {
      fprintf(stderr,
              "FAIL: response vector %d expected=(%.8f,%.8f,%.8f) "
              "actual=(%.8f,%.8f,%.8f)\n",
              v->id, v->expected.x, v->expected.y, v->expected.z,
              specular.x, specular.y, specular.z);
      return 1;
    }
    printf("PASS: response vector %d specular=(%.7f,%.7f,%.7f)\n",
           v->id, specular.x, specular.y, specular.z);
  }
  printf("PASS: %zu Lean-generated LightRT GGX response vectors\n",
         sizeof(vectors) / sizeof(vectors[0]));
  return 0;
}
