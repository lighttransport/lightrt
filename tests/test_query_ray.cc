#include "lightrt.hh"

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <vector>

int main() {
  std::vector<lightrt::AABB> boxes;
  boxes.emplace_back(lightrt::Vec3(1.0f, -1.0f, -1.0f),
                     lightrt::Vec3(2.0f, 1.0f, 1.0f));
  boxes.emplace_back(lightrt::Vec3(4.0f, -1.0f, -1.0f),
                     lightrt::Vec3(5.0f, 1.0f, 1.0f));
  boxes.emplace_back(lightrt::Vec3(1.0f, 3.0f, -1.0f),
                     lightrt::Vec3(2.0f, 4.0f, 1.0f));

  lightrt::BVH bvh;
  if (!bvh.build(boxes)) {
    std::fprintf(stderr, "failed to build test BVH\n");
    return 1;
  }

  const lightrt::Ray ray(lightrt::Vec3(0.0f, 0.0f, 0.0f),
                         lightrt::Vec3(1.0f, 0.0f, 0.0f));
  std::vector<uint32_t> hits;
  bvh.queryRay(ray, 10.0f, hits);
  std::sort(hits.begin(), hits.end());
  if (hits != std::vector<uint32_t>({0, 1})) {
    std::fprintf(stderr, "queryRay did not return both intersected boxes\n");
    return 1;
  }

  bvh.queryRay(ray, 3.0f, hits);
  if (hits != std::vector<uint32_t>({0})) {
    std::fprintf(stderr, "queryRay did not honor max_t\n");
    return 1;
  }

  lightrt::GaussianSplat splat;
  splat.position = lightrt::Vec3(2.0f, 0.0f, 0.0f);
  splat.scale = lightrt::Vec3(0.5f, 0.25f, 0.25f);
  splat.opacity = 0.75f;
  float splat_t = 100.0f;
  float density = 0.0f;
  if (!splat.intersect(ray, splat_t, density) ||
      std::abs(splat_t - 2.0f) > 1.0e-4f ||
      std::abs(density - 0.75f) > 1.0e-4f) {
    std::fprintf(stderr, "Gaussian peak-density intersection failed\n");
    return 1;
  }
  lightrt::Vec3 dc = splat.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  if (std::abs(dc.x - 0.5f) > 1.0e-5f ||
      std::abs(dc.y - 0.5f) > 1.0e-5f ||
      std::abs(dc.z - 0.5f) > 1.0e-5f) {
    std::fprintf(stderr, "Gaussian SH DC evaluation failed\n");
    return 1;
  }

  splat.sh_coeffs[0] = 0.6f;
  splat.sh_coeffs[1] = -0.3f;
  splat.sh_coeffs[2] = 0.15f;
  lightrt::QuantizedGaussianSplat quantized;
  quantized.quantize(splat, lightrt::Vec3(0.0f, -1.0f, -1.0f),
                     lightrt::Vec3(4.0f, 1.0f, 1.0f), 0.01f, 1.0f);
  const lightrt::GaussianSplat restored = quantized.dequantize(
      lightrt::Vec3(0.0f, -1.0f, -1.0f),
      lightrt::Vec3(4.0f, 1.0f, 1.0f), 0.01f, 1.0f);
  const lightrt::Vec3 original_color =
      splat.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  const lightrt::Vec3 restored_color =
      restored.getColor(lightrt::Vec3(0.0f, 0.0f, 1.0f));
  if (std::abs(original_color.x - restored_color.x) > 1.0f / 255.0f ||
      std::abs(original_color.y - restored_color.y) > 1.0f / 255.0f ||
      std::abs(original_color.z - restored_color.z) > 1.0f / 255.0f) {
    std::fprintf(stderr, "Quantized Gaussian DC round-trip failed\n");
    return 1;
  }

  std::puts("queryRay and Gaussian primitive tests passed");
  return 0;
}
