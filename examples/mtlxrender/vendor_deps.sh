#!/usr/bin/env bash
#
# vendor_deps.sh - fetch the third-party libraries mtlxrender needs into deps/
# (which is git-ignored). Prefers local clones under $HOME/work, falling back to
# fetching from GitHub. Run once before building:
#
#     ./vendor_deps.sh && make
#
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
DEPS="$HERE/deps"
TINYEXR_DST="$DEPS/tinyexr"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

mkdir -p "$DEPS" "$TINYEXR_DST/include" "$TINYEXR_DST/src" \
         "$TINYEXR_DST/tocio/include" "$TINYEXR_DST/tocio/src"

# ---- tinygltf v3 (pure-C loader, branch v3_c) -----------------------------
GLTF_SRC="${TINYGLTF_DIR:-$HOME/work/tinygltf}"
if [ ! -d "$GLTF_SRC/.git" ]; then
    echo "cloning tinygltf..."
    git clone --quiet https://github.com/syoyo/tinygltf "$TMP/tinygltf"
    GLTF_SRC="$TMP/tinygltf"
fi
git -C "$GLTF_SRC" fetch --quiet origin v3_c 2>/dev/null || true
for f in tiny_gltf_v3.c tiny_gltf_v3.h tinygltf_json_c.h stb_image.h stb_image_write.h; do
    git -C "$GLTF_SRC" show origin/v3_c:"$f" > "$DEPS/$f"
done
echo "vendored tinygltf v3_c -> deps/"

# ---- tinyexr v3 (pure-C EXR + tinycolorio) --------------------------------
EXR_SRC="${TINYEXR_DIR:-$HOME/work/tinyexr}"
if [ ! -d "$EXR_SRC/include" ]; then
    echo "cloning tinyexr..."
    git clone --quiet https://github.com/syoyo/tinyexr "$TMP/tinyexr"
    EXR_SRC="$TMP/tinyexr"
fi
cp "$EXR_SRC"/include/exr.h "$TINYEXR_DST/include/"
cp "$EXR_SRC"/src/*.c "$EXR_SRC"/src/*.h "$EXR_SRC"/src/*.inc "$TINYEXR_DST/src/" 2>/dev/null || true
cp "$EXR_SRC"/sandbox/tocio/include/*.h "$TINYEXR_DST/tocio/include/" 2>/dev/null || true
cp "$EXR_SRC"/sandbox/tocio/src/*.c "$TINYEXR_DST/tocio/src/" 2>/dev/null || true

# Drop GPU/ZSTD translation units (we build CPU-only, -DEXR_NO_ZSTD).
rm -f "$TINYEXR_DST"/src/exr_gpu_cuda.c \
      "$TINYEXR_DST"/src/exr_vk_vulkan.c \
      "$TINYEXR_DST"/src/exr_zstd.c \
      "$TINYEXR_DST"/src/*.cuh.inc \
      "$TINYEXR_DST"/src/exr_vk_shaders.spv.inc
echo "vendored tinyexr v3 -> deps/tinyexr/"

echo "done. Now run: make    (or cmake -S . -B build && cmake --build build -j)"
