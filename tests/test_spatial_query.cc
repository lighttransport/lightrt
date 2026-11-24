#include "lightrt.hh"
#include <algorithm>
#include <cmath>
#include <iostream>
#include <initializer_list>
#include <vector>

using namespace lightrt;

static bool hasExactly(std::vector<uint32_t> results,
                       std::initializer_list<uint32_t> expected) {
  std::sort(results.begin(), results.end());
  return results == std::vector<uint32_t>(expected);
}

int main() {
  std::cout << "Testing spatial query methods...\n\n";
  bool all_pass = true;

  // Create a simple scene with triangles in known locations
  std::vector<Triangle> triangles;

  // Triangle 1: at origin (0, 0, 0)
  triangles.emplace_back(
    Vec3(0.0f, 0.0f, 0.0f),
    Vec3(1.0f, 0.0f, 0.0f),
    Vec3(0.0f, 1.0f, 0.0f)
  );

  // Triangle 2: at (5, 0, 0)
  triangles.emplace_back(
    Vec3(5.0f, 0.0f, 0.0f),
    Vec3(6.0f, 0.0f, 0.0f),
    Vec3(5.0f, 1.0f, 0.0f)
  );

  // Triangle 3: at (0, 5, 0)
  triangles.emplace_back(
    Vec3(0.0f, 5.0f, 0.0f),
    Vec3(1.0f, 5.0f, 0.0f),
    Vec3(0.0f, 6.0f, 0.0f)
  );

  // Triangle 4: at (10, 10, 0)
  triangles.emplace_back(
    Vec3(10.0f, 10.0f, 0.0f),
    Vec3(11.0f, 10.0f, 0.0f),
    Vec3(10.0f, 11.0f, 0.0f)
  );

  // Build BVH
  TriangleBVH bvh;
  if (!bvh.build(triangles)) {
    std::cerr << "Failed to build triangle BVH\n";
    return 1;
  }
  std::cout << "Built BVH with " << triangles.size() << " triangles\n\n";

  // Test 1: Query AABB at origin - should find triangle 0
  {
    AABB query(Vec3(-1.0f, -1.0f, -1.0f), Vec3(2.0f, 2.0f, 1.0f));
    std::vector<uint32_t> results;
    bvh.queryAABB(query, results);

    std::cout << "Test 1: Query AABB at origin\n";
    std::cout << "  Expected: triangle 0\n";
    std::cout << "  Found " << results.size() << " triangles: ";
    for (auto idx : results) {
      std::cout << idx << " ";
    }
    std::cout << "\n";

    bool pass = (results.size() == 1 && results[0] == 0);
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 2: Query AABB covering triangles 0 and 1
  {
    AABB query(Vec3(-1.0f, -1.0f, -1.0f), Vec3(7.0f, 2.0f, 1.0f));
    std::vector<uint32_t> results;
    bvh.queryAABB(query, results);

    std::cout << "Test 2: Query AABB covering triangles 0 and 1\n";
    std::cout << "  Expected: triangles 0, 1\n";
    std::cout << "  Found " << results.size() << " triangles: ";
    for (auto idx : results) {
      std::cout << idx << " ";
    }
    std::cout << "\n";

    bool pass = hasExactly(results, {0, 1});
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 3: Query sphere at origin with radius 2 - should find triangle 0
  {
    Vec3 center(0.5f, 0.5f, 0.0f);
    float radius = 2.0f;
    std::vector<uint32_t> results;
    bvh.querySphere(center, radius, results);

    std::cout << "Test 3: Query sphere at origin with radius 2\n";
    std::cout << "  Expected: triangle 0\n";
    std::cout << "  Found " << results.size() << " triangles: ";
    for (auto idx : results) {
      std::cout << idx << " ";
    }
    std::cout << "\n";

    bool pass = hasExactly(results, {0});
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 4: Query sphere with large radius - should find all triangles
  {
    Vec3 center(5.0f, 5.0f, 0.0f);
    float radius = 10.0f;
    std::vector<uint32_t> results;
    bvh.querySphere(center, radius, results);

    std::cout << "Test 4: Query sphere at (5,5,0) with radius 10\n";
    std::cout << "  Expected: all 4 triangles\n";
    std::cout << "  Found " << results.size() << " triangles: ";
    for (auto idx : results) {
      std::cout << idx << " ";
    }
    std::cout << "\n";

    bool pass = hasExactly(results, {0, 1, 2, 3});
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 5: Query AABB with no intersection
  {
    AABB query(Vec3(100.0f, 100.0f, 100.0f), Vec3(200.0f, 200.0f, 200.0f));
    std::vector<uint32_t> results;
    bvh.queryAABB(query, results);

    std::cout << "Test 5: Query AABB with no intersection\n";
    std::cout << "  Expected: 0 triangles\n";
    std::cout << "  Found " << results.size() << " triangles\n";

    bool pass = (results.size() == 0);
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 6: Query sphere with small radius - should find only nearby triangle
  {
    Vec3 center(10.5f, 10.5f, 0.0f);
    float radius = 1.5f;
    std::vector<uint32_t> results;
    bvh.querySphere(center, radius, results);

    std::cout << "Test 6: Query sphere at (10.5,10.5,0) with radius 1.5\n";
    std::cout << "  Expected: triangle 3\n";
    std::cout << "  Found " << results.size() << " triangles: ";
    for (auto idx : results) {
      std::cout << idx << " ";
    }
    std::cout << "\n";

    bool pass = (results.size() == 1 && results[0] == 3);
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 7: KNN with k=1 should return the nearest primitive and distance.
  {
    std::vector<KNNResult> results;
    bvh.queryKNN(Vec3(0.5f, 0.5f, 1.0f), 1, results);

    std::cout << "Test 7: KNN query with k=1\n";
    std::cout << "  Expected: triangle 0 at distance squared 1\n";
    bool pass = results.size() == 1 && results[0].prim_id == 0 &&
                std::abs(results[0].distance_sq - 1.0f) < 1.0e-6f;
    all_pass = all_pass && pass;
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 8: Empty BVHs must clear caller-provided output vectors.
  {
    BVH empty_bvh;
    std::vector<uint32_t> results = {42};
    empty_bvh.queryAABB(
        AABB(Vec3(-1.0f, -1.0f, -1.0f), Vec3(1.0f, 1.0f, 1.0f)), results);
    bool pass = results.empty();
    all_pass = all_pass && pass;
    std::cout << "Test 8: Empty BVH clears query results\n";
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  // Test 9: Identity clip-space frustum should retain only the origin tile.
  {
    const float identity[16] = {
        1.0f, 0.0f, 0.0f, 0.0f,
        0.0f, 1.0f, 0.0f, 0.0f,
        0.0f, 0.0f, 1.0f, 0.0f,
        0.0f, 0.0f, 0.0f, 1.0f};
    const Frustum frustum = Frustum::fromMatrix(identity);
    std::vector<uint32_t> results;
    bvh.queryFrustum(frustum, results);
    bool pass = hasExactly(results, {0});
    all_pass = all_pass && pass;
    std::cout << "Test 9: Identity frustum query\n";
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  std::cout << "Spatial query tests completed!\n";
  return all_pass ? 0 : 1;
}
