#!/bin/bash
# Setup external dependencies for LightRT CLI

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DEPS_DIR="$ROOT_DIR/deps"
DEP_DIR="$ROOT_DIR/dep"

mkdir -p "$DEPS_DIR"
mkdir -p "$DEP_DIR"

# TinyUSDZ
TINYUSDZ_DIR="$DEPS_DIR/tinyusdz"
if [ -d "$TINYUSDZ_DIR" ]; then
  echo "tinyusdz already cloned at $TINYUSDZ_DIR"
else
  echo "Cloning tinyusdz (lightusd branch)..."
  git clone --branch lightusd --depth 1 \
    https://github.com/syoyo/tinyusdz.git "$TINYUSDZ_DIR"
fi

# LightUSD-C (standalone repo)
LIGHTUSD_C_DIR="$DEP_DIR/lightusd_c"
if [ -d "$LIGHTUSD_C_DIR" ]; then
  echo "lightusd-c already cloned at $LIGHTUSD_C_DIR"
else
  echo "Cloning lightusd-c..."
  if [ -d "$HOME/work/lightusd_c/.git" ]; then
    git clone "$HOME/work/lightusd_c" "$LIGHTUSD_C_DIR"
  elif [ -d "$HOME/work/lightusd-c/.git" ]; then
    git clone "$HOME/work/lightusd-c" "$LIGHTUSD_C_DIR"
  else
    git clone --depth 1 \
      https://github.com/lighttransport/lightusd-c "$LIGHTUSD_C_DIR"
  fi
fi

# lightusd-c currently includes yyjson from an ordinary reference checkout.
# Keep this reproducible without creating a git submodule in either project.
LIGHTUSD_TINYUSDZ_DIR="$LIGHTUSD_C_DIR/ref/tinyusdz"
if [ ! -f "$LIGHTUSD_TINYUSDZ_DIR/src/external/yyjson.c" ]; then
  echo "Cloning lightusd-c's tinyusdz reference checkout..."
  git clone "$TINYUSDZ_DIR" "$LIGHTUSD_TINYUSDZ_DIR"
fi

echo "Dependencies ready."
