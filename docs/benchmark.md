# LightRT C11 Triangle BVH — Performance Report

Measured 2026-06 on an AMD Ryzen Threadripper 1950X (Zen 1, 16 cores / 32
threads, SSE4.2/AVX2/FMA, quad-channel DDR4), gcc 13.3, `-O3`, transparent
huge pages enabled. Harness: [`benchmark_c/`](../benchmark_c/README.md) —
procedural mandelbulb scene (marching cubes), identical deterministic ray
sets for every backend, median of repeated runs, all backends verified to
≥ 99.9 % per-ray agreement against an fp64 brute-force oracle.

Backends: `c11-*` is this library (`lightrt_c_tri.h`, pure C11);
[Embree 4.3.3](https://github.com/RenderKit/embree) (`rtcIntersect1`/
`rtcOccluded1`), [tinybvh](https://github.com/jbikker/tinybvh) (`BVH8_CPU`),
and [madmann91/bvh v2](https://github.com/madmann91/bvh) (Quality::High).

## Single-thread ray throughput

![single thread, 128k triangles](img/st_128k.svg)

`c11-bvh4` matches or beats Embree on primary rays (octant-ordered traversal)
and leads every non-Embree library on incoherent rays. Embree keeps its
single-thread leads on incoherent (its kernels hide latency per ray) and
shadow rays (any-hit kernel design; tree quality, push ordering, leaf size
and spatial splits were all measured and ruled out).

## Multi-threaded ray throughput

![16 threads, 710k triangles](img/mt_710k.svg)

At 710k triangles and 16 threads, `c11-bvh4` leads incoherent rays
(1.1–1.3× Embree) and `c11-bvh8` leads shadow rays. The 8-way per-thread ray
pipelining stacks with thread-level parallelism.

## Build throughput

![build throughput](img/build.svg)

The default builder is a binned SAH (single-pass 3-axis binning, block-based
cost) with a deterministic parallel mode (subtree tasks on disjoint arena
slices — bit-identical trees at any thread count). `LRT_TRI_BUILD_FAST` is a
Morton/LBVH path (radix-sorted keys, highest-differing-bit splits) that
matches Embree's TBB build throughput while costing ~10–15 % traversal.
`LRT_TRI_BUILD_HQ` adds SBVH spatial splits (not shown: ~0.2 Mtris/s, only
worthwhile for overlapping geometry).

## How the single-thread incoherent gap was closed

![optimization progression](img/progression.svg)

The big steps, in order:

1. **fp32 wide BVH + SIMD kernels** (vs the fp64 per-primitive-callback
   baseline): BVH4/BVH8 SoA nodes, 4/8-wide Möller-Trumbore leaf blocks with
   pre-swizzled edges — ~2.8×.
2. **Block-based SAH + large leaves** (cost counts SIMD blocks, leaf cap 60)
   and multi-line prefetch.
3. **Transparent huge pages**: the launch environment had per-process THP
   disabled (`THP_enabled: 0`), silently defeating `madvise(MADV_HUGEPAGE)`
   for every backend; a 35 MB BVH walked through 4 KB pages thrashes the
   dTLB. The benchmark clears `PR_SET_THP_DISABLE` and the library
   2 MB-aligns + madvises all arenas ≥ 2 MB.
4. **8-way interleaved ray traversal** (`LRT_TRI_BATCH_INCOHERENT`): eight
   rays in flight per thread, one node visit each per turn, so one ray's
   cache miss overlaps the others' compute — +60 %, past Embree. Coherent
   batches (`LRT_TRI_BATCH_COHERENT`) keep the plain per-ray kernel, which
   instead uses a per-octant child-order table baked into the nodes
   (+20 % on primary rays).

Variants measured and rejected along the way (kept out of the code): octant
ordering in the incoherent pipeline (exact tnear sorting wins when
latency-bound), any push ordering or eager-leaf processing in any-hit
kernels, quantized 128-byte BVH8 nodes as a default (+8 % only when
latency-bound; the decode ALU becomes the bottleneck once pipelining hides
the latency).

## Hair-like geometry: the primitive, not the build algorithm

![hair scene](img/hair.svg)

The adversarial `thinspan` scene (hair-thin triangles spanning the cube
diagonally) collapses every triangle BVH by ~3 orders of magnitude:
axis-aligned boxes around diagonal slivers are mostly empty space that no
partitioning removes. Spatial splits (ours, or Embree's
`RTC_BUILD_QUALITY_HIGH` at 10× build cost) recover at most ~2.8× and only
for full-length hairs. The capsule primitive
(`lrt_curve_scene_build`: segment + radius, subdivided at build time into
sub-segments ~16 radii long so the boxes hug the hair) is **15× the best
triangle BVH and 43× Embree's** on the same geometry — at the cost of a
~3.9 s build and 143 MB for 100k hairs.

## Reproducing

```bash
benchmark_c/scripts/download_libs.sh           # Embree SDK + pinned clones
cmake -S benchmark_c -B build_bench_c -DCMAKE_BUILD_TYPE=Release
cmake --build build_bench_c -j
benchmark_c/scripts/run_all.sh                 # full matrix -> CSV + tables
./build_bench_c/bench_c --help                 # single configurations
```

Numbers in this document are medians from the runs recorded in
`benchmark_c/results/` and the commit messages of the optimization series
(`91b87e2..0d2ad81`); run-to-run variance on a loaded machine is ±10 %, so
same-run ratios are what matter.
