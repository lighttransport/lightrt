#!/bin/bash
# Setup external dependencies for LightRT CLI

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DEPS_DIR="$ROOT_DIR/deps"

mkdir -p "$DEPS_DIR"

# TinyUSDZ
TINYUSDZ_DIR="$DEPS_DIR/tinyusdz"
if [ -d "$TINYUSDZ_DIR" ]; then
  echo "tinyusdz already cloned at $TINYUSDZ_DIR"
else
  echo "Cloning tinyusdz (mtlx-nodegraph branch)..."
  git clone --branch mtlx-nodegraph --depth 1 \
    https://github.com/syoyo/tinyusdz.git "$TINYUSDZ_DIR"
fi

echo "Dependencies ready."
