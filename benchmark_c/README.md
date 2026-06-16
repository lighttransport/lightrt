# benchmark_c — C11 ray tracing benchmark (lightrt vs Embree)

Standalone C11 benchmark harness for LightRT's C APIs, using a procedural
mandelbulb (marching cubes over the power-8 mandelbulb distance estimator —
the same generator as the X11 viewer's benchmark mode) and comparing against
a pinned Embree 4 prebuilt binary.

## Backends

| name        | what it measures                                                       |
|-------------|------------------------------------------------------------------------|
| `c11-cb`    | existing `lightrt_c.h` callback API (fp64 Möller-Trumbore callback) — the pre-optimization baseline |
| `c11-bvh4`  | new `lightrt_c_tri.h` fp32 triangle API, 4-wide BVH (SSE4 kernels), binned SAH build |
| `c11-bvh8`  | new `lightrt_c_tri.h` fp32 triangle API, 8-wide BVH (AVX2 kernels), binned SAH build |
| `c11-lbvh4` | same BVH4 kernels, LBVH fast build (`LRT_TRI_BUILD_FAST`: Morton sort + bit splits) |
| `c11-lbvh8` | same BVH8 kernels, LBVH fast build                                     |
| `c11-bvh8q` | 8-wide with 8-bit quantized child bounds (128B nodes vs 256B)          |
| `embree`    | Embree 4 `rtcIntersect1`/`rtcOccluded1` per ray (optional)             |
| `tinybvh`   | jbikker/tinybvh `BVH8_CPU` (8-wide AVX2 layout) (optional)             |
| `mm-bvh`    | madmann91/bvh v2, `DefaultBuilder` Quality::High + `PrecomputedTri` (optional) |

## Quick start

```bash
# optional: fetch ALL comparison libraries (Embree 4.3.3 SDK + pinned clones
# of madmann91/bvh and jbikker/tinybvh) into third_party/
benchmark_c/scripts/download_libs.sh
# (or just the Embree SDK: benchmark_c/scripts/download_embree.sh)

cmake -S benchmark_c -B build_bench_c -DCMAKE_BUILD_TYPE=Release
cmake --build build_bench_c -j

# single config
./build_bench_c/bench_c --fineness 128 --backend all --threads 16 --csv out.csv

# verify fp32 backends against the fp64 callback oracle
./build_bench_c/bench_c --fineness 64 --nrays 500000 --backend all --verify

# full matrix (fineness x workloads x backends x threads) + comparison table
benchmark_c/scripts/run_all.sh
python3 benchmark_c/compare.py benchmark_c/results/bench_*.csv
```

## Workloads

All ray sets are deterministic from `--seed` and identical across backends:

- `primary` — coherent pinhole-camera rays at (2.5,2.5,2.5) looking at the
  origin, emitted in Morton pixel order.
- `incoherent` — random sphere-origin rays toward the center with spread; a
  direct port of the viewer benchmark's ray generator.
- `shadow` — occlusion (any-hit) rays from primary-hit surface points toward a
  point light at (4,6,4). Derived once from the first backend's primary hits,
  then shared by every backend.

Multithreaded runs split the ray array into static per-thread chunks
(pthreads). The reported Mrays/s is the median of `--repeat` timed runs after
one warm-up pass.

## CSV columns

`backend,scene,ntris,build_ms,build_mtris_s,mem_mb,workload,threads,mrays_s,hit_frac`

`hit_frac` must agree across backends within 0.1% — `compare.py` warns
otherwise. `--verify` additionally cross-checks per-ray hits of the fp32
backends against the fp64 `c11-cb` oracle (≥ 99.9% agreement, t within 1e-3
relative).

## Results (AMD Threadripper 1950X, Zen 1, gcc 13.3, Embree 4.3.3)

Full matrix: `results/bench_20260611_180720.csv` (fineness {64,128,192,256} ×
workloads × backends × threads {1,16,32}, 2M rays, median of 3). `hit_frac`
agreed across all backends in every cell. Representative slice — mandelbulb at
fineness 192 (347,460 triangles):

| workload   | threads | c11-cb | c11-bvh4 | c11-bvh8 | embree | best vs embree |
|------------|--------:|-------:|---------:|---------:|-------:|---------------:|
| primary    |       1 |   6.18 |    16.87 |    16.64 |  18.49 | 0.91× |
| incoherent |       1 |   0.61 |     1.75 |     1.78 |   2.01 | 0.89× |
| shadow     |       1 |   0.97 |     3.10 |     3.59 |   4.48 | 0.80× |
| primary    |      16 |  16.92 |    50.32 |    53.29 |  72.42 | 0.74× |
| incoherent |      16 |   5.89 |    24.98 |    24.10 |  19.64 | **1.27×** |
| shadow     |      16 |   8.62 |    37.07 |    46.22 |  53.70 | 0.86× |

(Mrays/s. `c11-cb` is the pre-optimization fp64 callback baseline.)

Across the whole matrix the new triangle backends run at 0.62–1.27× of Embree
(typically 0.7–0.9×) and 2.7–5× the `c11-cb` baseline. On the larger scenes'
multithreaded incoherent workload `c11-bvh4` beats Embree (1.27× at 347k tris
/ 16T, 1.22× at 710k / 32T). On this Zen 1 part BVH4 and BVH8 are within a few
percent of each other (256-bit ops execute as 2×128), which is why
`LRT_TRI_LAYOUT_AUTO` picks BVH4.

BVH build (SAH): ~1.4 Mtris/s serial, ~3.3–3.9 Mtris/s at 16 threads vs
Embree's ~13–17 Mtris/s (TBB). The LBVH fast path (`LRT_TRI_BUILD_FAST`,
Morton sort + highest-differing-bit splits) builds at ~6.5–7.3 Mtris/s serial
and ~7.8–9.3 Mtris/s multithreaded — e.g. at 710k tris / 16 threads:
`c11-lbvh4` 91 ms vs `c11-bvh4` 196 ms vs Embree 44 ms. Its tree quality costs
~10–15% traversal throughput vs the SAH build (SAH cost +8.5% on the
mandelbulb), e.g. 14.0 vs 16.9 Mrays/s incoherent at 710k/16T (Embree: 16.0).
Builds are deterministic — bit-identical trees at any thread count for both
quality modes.

Quantized nodes (`c11-bvh8q`, 128-byte nodes with 8-bit child bounds): +8%
single-thread incoherent vs `c11-bvh8` (the memory-latency-bound case it
targets), neutral on multithreaded incoherent, ~10% slower on shadow rays
where the decode ALU shows. Leaf blocks dominate the footprint, which bounds
the win; an option rather than the default.

### Transparent huge pages

Some launch environments disable THP per process (`THP_enabled: 0` in
`/proc/self/status`), which silently defeats both lightrt's `MADV_HUGEPAGE`
arenas and Embree's huge-page allocator: a multi-MB BVH walked by incoherent
rays then thrashes the dTLB through 4KB pages. `bench_c` clears
`PR_SET_THP_DISABLE` at startup so every backend gets huge pages (system THP
policy `madvise` is enough); the lightrt allocator 2MB-aligns and madvises
all arenas ≥ 2MB. Worth ~+5-8% on large-scene traversal for every backend.

### Cross-library comparison (same rays, hit fractions identical, THP on)

Mandelbulb, fineness 128 (127,752 tris), single thread, Mrays/s:

| backend   | primary | incoherent | shadow | build (ms) |
|-----------|--------:|-----------:|-------:|-----------:|
| embree    |   19.69 |       3.48 |   5.43 |       50.4 |
| tinybvh   |   18.61 |       2.49 |   4.56 |       52.8 |
| c11-bvh4  |   18.13 |       2.86 |   3.93 |       75.3 |
| c11-bvh8q |   15.76 |   **2.92** |   3.92 |       62.7 |
| c11-lbvh4 |   15.80 |       2.40 |   3.50 |   **16.9** |
| mm-bvh    |   14.39 |       1.21 |   1.90 |      107.9 |

Fineness 256 (710,536 tris), 16 threads:

| backend   | incoherent |    shadow | build (ms) | build Mtris/s |
|-----------|-----------:|----------:|-----------:|--------------:|
| c11-bvh4  |  **17.78** |     43.37 |      178.3 |          3.99 |
| c11-bvh8  |      17.15 | **47.35** |      172.8 |          4.11 |
| embree    |      15.90 |     44.60 |       82.0 |          8.66 |
| c11-lbvh4 |      14.62 |     34.92 |   **80.3** |      **8.85** |
| tinybvh   |      13.32 |     41.82 |      515.8 |          1.38 |
| mm-bvh    |       9.00 |     16.60 |      298.8 |          2.38 |

At 710k tris / 16 threads, `c11-bvh4` leads incoherent rays (1.12x Embree) and
`c11-bvh8` leads shadow rays (1.06x Embree); the LBVH fast build matches
Embree's TBB build throughput.

### Interleaved (software-pipelined) batch traversal

`lrt_tri_intersect1N/occluded1N` take a `lrt_tri_batch_hint`. With
`LRT_TRI_BATCH_INCOHERENT` the library keeps `TRI_PIPE_WIDTH` (8, measured
optimum on Zen 1) rays in flight per thread — on all SIMD layouts (BVH4/SSE,
BVH8 and BVH8Q/AVX2) — advancing each by one node/leaf visit per turn, so one
ray's cache miss overlaps the others' compute. Results are bit-identical to
single-ray calls (enforced by tests). Effect at 710k tris: single-thread
incoherent 1.41 → 2.25 Mrays/s on BVH4 (+60%, 1.33x Embree, where Embree was
previously 1.12x ahead), 1.43 → 1.92 on BVH8 (+34%), 1.51 → 1.82 on BVH8Q
(+21%; with the latency hidden, the quantized decode ALU becomes the cost and
plain BVH4 is the best layout); 16-thread incoherent 17.8 → 20-22 (1.1-1.3x
Embree, same-run). Coherent batches (primary rays, surface-to-light shadow
rays) run the plain per-ray kernel — pipelining costs ~20% there because the
working set is already cache-resident; the benchmark passes the matching hint
per workload.

### Octant-ordered coherent traversal

BVH4 nodes store a per-octant child permutation (8 octants x 4 slots x 2
bits, packed into previously padding bytes) computed at collapse from child
centers. The coherent closest-hit kernel iterates it instead of insertion-
sorting child tnear values per node: primary rays gained ~20% (22.6 vs
Embree's 20.5 Mrays/s at 128k tris, parity at 710k). Three variants were
measured and rejected: octant order in the *incoherent* pipeline loses to
exact tnear sorting (the sort hides behind cache misses and tighter order
saves node visits), and for any-hit both ordered pushes and eager-leaf
processing lose to plain unordered pushes.

### Spatial splits (`c11-sbvh4`, `LRT_TRI_BUILD_HQ`)

`LRT_TRI_BUILD_HQ` is an SBVH build (Stich et al. 2009): binned object SAH
plus alpha-gated spatial splits over 32 bins, with straddling references
duplicated into both children under plane-clipped bounds (extended-range
allocation, object-split fallback when a range's slack runs out). It is
correct and verified, and helps overlapping geometry (the co-planar test
scene improves), but on the mandelbulb it is a no-op: marching-cubes
triangles are tiny and uniform, so fewer than 1% of references get split
(memory 6.67 vs 6.62 MB) and shadow/primary throughput is unchanged. This
*rules out* tree quality as the cause of the remaining single-thread
shadow/any-hit gap (~0.75x Embree) on this scene; what remains is Embree's
any-hit kernel itself (profiling on our side shows no hotspot — work is
evenly spread across node tests and leaf loads).

### Synthetic adversarial scene: `--scene thinspan`

Long thin diagonal triangles (`--ntris`, `--span` = length as a fraction of
the cube diagonal, `0.002` thick). Every backend collapses on it — at span
1.0 (corner-to-corner hairs, 100k tris) throughput drops three orders of
magnitude below the mandelbulb for everyone — which is the point: thin
diagonal slivers give every axis-aligned box enormous empty volume no
partitioning can remove.

Findings (100k tris, primary rays, single thread):
- span 1.0: `c11-sbvh4` 0.016 Mrays/s vs `c11-bvh4` 0.011 (+45%) vs Embree
  and tinybvh both 0.006 — spatial splits help (+77% duplicated refs) and
  our SBVH leads the field 2.7x over Embree here.
- span <= 0.5: spatial splits stop firing — the per-node SAH comparison
  correctly concludes that chopping a *diagonal* sliver's box on one axis
  barely shrinks it while doubling references. Embree agrees: its own
  spatial-split builder (`LRTBENCH_EMBREE_QUALITY=high`, 10x build time)
  gains nothing on this scene either.
- The real fix for hair-like geometry is a different primitive — measured
  below.

### Capsule (curve) primitive: `c11-hair`

`lrt_curve_scene_build` treats each hair as a capsule (segment + radius),
subdivided at build time into short sub-segments (length ~16 radii, capped at
32 pieces) whose AABBs hug the hair; hits report the original segment id and
its [0,1] parameter. The `c11-hair` backend reinterprets thinspan's sliver
triangles as capsules. On span-1.0 hairs (100k):

| backend   | primary | incoherent | vs best triangle BVH |
|-----------|--------:|-----------:|---------------------:|
| c11-hair  |   0.259 |      0.128 | **15-16x** |
| c11-sbvh4 |   0.017 |      0.008 | 1x |
| embree    |   0.006 |      0.006 | 0.4-0.7x |

The right primitive beats any triangle-BVH strategy by an order of magnitude
(43x Embree on primary rays). The trade is build cost: 3.2M sub-segments
take ~3.9 s and 143 MB. `c11-hair` is excluded from `--backend all` because
its geometry (and hence hit fractions) intentionally differs from the
triangle representation on generic scenes.

### Ray-space transform slab test

On FMA-capable builds the per-ray setup precomputes `org*invd` (clamped
finite so `bound*invd` overflow cannot produce inf−inf NaNs), turning every
slab plane into a single `fmsub` instead of subtract+multiply — 6 fewer ops
per node test. Measured effect on Zen 1: within noise to +3% (the slab is
not the bottleneck); kept since it is strictly fewer operations.

## Notes

- The mandelbulb DE is NaN at the grid point exactly at the origin
  (`acosf(0/0)`); the generator drops the few affected triangles, so triangle
  counts are slightly below the viewer's displayed count (which includes the
  NaN triangles its own BVH build then rejects).
- Embree is pinned (version + sha256) in `scripts/download_embree.sh`; the
  build refuses to silently pick up a system Embree.
- `c11-cb` scenes keep per-query scratch and are not thread-safe; the backend
  builds one scene per worker thread (reported build time is for one build).
