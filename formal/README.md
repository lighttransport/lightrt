# LightRT formal verification (Lean 4 + Mathlib)

This directory contains Lean 4 specifications of ray-tracing primitives over ℝ³: slab ray/AABB, Möller–Trumbore, Woop watertight, and BVH. It also contains a floating-point rounding model and robustness theorems, plus a **C → Lean bridge** that ties the specifications to the real `lightrt_c_tri.c`.

- `tools/c2lean.py` translates the scalar kernels into the MiniC deep embedding (`LightRT/C/Gen.lean`).
- MiniC runs IEEE binary32 bit-exactly (`LightRT/FP/Binary32.lean`).
- `tools/cdiff.py` checks that compiled C, MiniC and the Lean reference agree.

The plan, status, `sorry` count, review checklist and milestones are in [PLAN.md](PLAN.md).

```sh
make formal                                   # from the repo root: everything below
cd formal && lake exe cache get && lake build # specs + proofs (~1 min incremental)
python3 tools/c2lean.py --check               # Gen.lean matches lightrt_c_tri.c
python3 tools/cdiff.py --n 20000              # C == MiniC == Lean reference, bit-exact
python3 tools/cdiff.py --search-miss --n 200000   # slab false-miss search (+ inflated fix)
sh tools/count_sorry.sh; python3 tools/check_axioms.py
```

Requirements:
- elan, with the toolchain pinned in `lean-toolchain`
- `clang`, used for the AST, the layout probe, and cdiff with ASan/UBSan
- Python 3

MiniC, the logic files and `c2lean.py` were ported from tinygltf's `formal/` (MIT).
