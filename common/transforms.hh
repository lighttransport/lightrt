// Transform utilities for 3x4 matrices
// Extracted from cli/scene.hh for shared use
#pragma once

#include "lightrt.hh"
#include <cmath>
#include <cstring>

namespace lightrt_common {

inline void matrix4dTo3x4(const double m[4][4], float out[12]) {
  for (int r = 0; r < 3; r++)
    for (int c = 0; c < 4; c++)
      out[r * 4 + c] = static_cast<float>(m[r][c]);
}

inline bool invert3x4(const float m[12], float inv[12]) {
  float a00 = m[0], a01 = m[1], a02 = m[2];
  float a10 = m[4], a11 = m[5], a12 = m[6];
  float a20 = m[8], a21 = m[9], a22 = m[10];

  float det = a00 * (a11 * a22 - a12 * a21)
            - a01 * (a10 * a22 - a12 * a20)
            + a02 * (a10 * a21 - a11 * a20);

  if (std::fabs(det) < 1e-12f) return false;

  float inv_det = 1.0f / det;

  float i00 = (a11 * a22 - a12 * a21) * inv_det;
  float i01 = (a02 * a21 - a01 * a22) * inv_det;
  float i02 = (a01 * a12 - a02 * a11) * inv_det;
  float i10 = (a12 * a20 - a10 * a22) * inv_det;
  float i11 = (a00 * a22 - a02 * a20) * inv_det;
  float i12 = (a02 * a10 - a00 * a12) * inv_det;
  float i20 = (a10 * a21 - a11 * a20) * inv_det;
  float i21 = (a01 * a20 - a00 * a21) * inv_det;
  float i22 = (a00 * a11 - a01 * a10) * inv_det;

  inv[0] = i00; inv[1] = i01; inv[2] = i02;
  inv[4] = i10; inv[5] = i11; inv[6] = i12;
  inv[8] = i20; inv[9] = i21; inv[10] = i22;

  float tx = m[3], ty = m[7], tz = m[11];
  inv[3]  = -(i00 * tx + i01 * ty + i02 * tz);
  inv[7]  = -(i10 * tx + i11 * ty + i12 * tz);
  inv[11] = -(i20 * tx + i21 * ty + i22 * tz);

  return true;
}

inline void lerp3x4(const float a[12], const float b[12], float t, float out[12]) {
  for (int i = 0; i < 12; i++)
    out[i] = a[i] + (b[i] - a[i]) * t;
}

inline lightrt::Vec3 transformPoint(const float m[12], const lightrt::Vec3& p) {
  return lightrt::Vec3(
    m[0] * p.x + m[1] * p.y + m[2]  * p.z + m[3],
    m[4] * p.x + m[5] * p.y + m[6]  * p.z + m[7],
    m[8] * p.x + m[9] * p.y + m[10] * p.z + m[11]);
}

inline lightrt::Vec3 transformDir(const float m[12], const lightrt::Vec3& d) {
  return lightrt::Vec3(
    m[0] * d.x + m[1] * d.y + m[2]  * d.z,
    m[4] * d.x + m[5] * d.y + m[6]  * d.z,
    m[8] * d.x + m[9] * d.y + m[10] * d.z);
}

// Transform normal by inverse-transpose of 3x3 part of inv_m
// (inv_m is already the inverse, so transpose of inv_m's 3x3 = inverse-transpose of original)
inline lightrt::Vec3 transformNormal(const float inv_m[12], const lightrt::Vec3& n) {
  // Transpose of 3x3 part of inv_m
  return lightrt::Vec3(
    inv_m[0] * n.x + inv_m[4] * n.y + inv_m[8]  * n.z,
    inv_m[1] * n.x + inv_m[5] * n.y + inv_m[9]  * n.z,
    inv_m[2] * n.x + inv_m[6] * n.y + inv_m[10] * n.z);
}

inline lightrt::AABB transformAABB(const lightrt::AABB& box, const float m[12]) {
  lightrt::AABB result;
  for (int i = 0; i < 8; i++) {
    lightrt::Vec3 corner(
      (i & 1) ? box.max.x : box.min.x,
      (i & 2) ? box.max.y : box.min.y,
      (i & 4) ? box.max.z : box.min.z);
    result.expand(transformPoint(m, corner));
  }
  return result;
}

} // namespace lightrt_common
