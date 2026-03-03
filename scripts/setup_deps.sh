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
  echo "Cloning tinyusdz (lightusd branch)..."
  git clone --branch lightusd --depth 1 \
    https://github.com/syoyo/tinyusdz.git "$TINYUSDZ_DIR"
fi

# LightUSD-C (standalone repo)
LIGHTUSD_C_DIR="$DEPS_DIR/lightusd-c"
if [ -d "$LIGHTUSD_C_DIR" ]; then
  echo "lightusd-c already cloned at $LIGHTUSD_C_DIR"
else
  echo "Cloning lightusd-c..."
  git clone --depth 1 \
    https://github.com/lighttransport/lightusd-c "$LIGHTUSD_C_DIR"
fi

echo "Dependencies ready."
