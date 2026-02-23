#include "lightrt.hh"
#include <iostream>
#include <vector>

using namespace lightrt;

int main() {
  std::cout << "Testing spatial query methods...\n\n";

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
  bvh.build(triangles);
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

    bool pass = (results.size() == 2);
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

    bool pass = (results.size() >= 1);
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

    bool pass = (results.size() == 4);
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
    std::cout << "  Result: " << (pass ? "PASS" : "FAIL") << "\n\n";
  }

  std::cout << "Spatial query tests completed!\n";
  return 0;
}
