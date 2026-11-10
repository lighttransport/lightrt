import Lake
open Lake DSL

package «lightrt» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «LightRT» where
  srcDir := "."
  globs := #[.andSubmodules `LightRT]

/-- Differential-testing driver (see tools/cdiff.py). -/
lean_exe «cdiff» where
  root := `CDiff

/-- BVH validator over C-built trees (see tools/bvhdump.c). -/
lean_exe «checkbvh» where
  root := `CheckBVH
