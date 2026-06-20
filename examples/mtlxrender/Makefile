# Makefile for mtlxrender (standalone). From this directory: `make`.
# Everything is C11; links lightrt_c_tri.c, tinygltf v3, tinyexr v3 directly.

CC      ?= cc
CSTD     = -std=c11
WARN     = -Wall -Wextra
OPT     ?= -O3
DEFS     = -D_POSIX_C_SOURCE=200809L -DTINYGLTF3_ENABLE_FS -DEXR_NO_ZSTD -DEXR_USE_THREADS

LIGHTRT  = ../..
DEPS     = deps
TINYEXR  = $(DEPS)/tinyexr

INCLUDES = -I. -I$(LIGHTRT) -I$(DEPS) -I$(TINYEXR)/include

UNAME_M := $(shell uname -m)
ifneq (,$(filter x86_64 amd64,$(UNAME_M)))
  SIMD = -msse4.1 -mavx2 -mfma
else
  SIMD =
endif

# Separate object dirs for CPU vs VK builds so toggling VK never links stale,
# differently-compiled objects (the .o files don't track -DMTLX_HAVE_VK).
BUILD = build$(if $(VK),-vk,)

# our first-party sources (full warnings). raytracer_vk.c is empty unless
# MTLX_HAVE_VK is defined, so it is always listed.
APP_SRC = main.c pathtrace.c pathtrace_wf.c raytracer.c raytracer_vk.c \
          bsdf.c env.c framebuffer.c color.c \
          gltf_load.c mesh_build.c obj_load.c mtlx_xml.c mtlx_doc.c mtlx_eval.c \
          material_bind.c texture.c
# third-party sources (compiled quietly with -w)
TP_SRC  = third_party_impl.c \
          $(LIGHTRT)/lightrt_c_tri.c \
          $(DEPS)/tiny_gltf_v3.c \
          $(wildcard $(TINYEXR)/src/*.c)

LDFLAGS = -lm -lpthread

# VK=1 enables the Vulkan GPU-traced backend (runtime dlopen of libvulkan).
ifdef VK
  DEFS    += -DMTLX_HAVE_VK
  TP_SRC  += $(LIGHTRT)/lightrt_vkew.c $(LIGHTRT)/lightrt_c_vk.c
  LDFLAGS += -ldl
endif

APP_OBJ = $(addprefix $(BUILD)/,$(notdir $(APP_SRC:.c=.o)))
TP_OBJ  = $(addprefix $(BUILD)/tp_,$(notdir $(TP_SRC:.c=.o)))

CFLAGS  = $(CSTD) $(OPT) $(SIMD) $(DEFS) $(INCLUDES)

mtlxrender: $(APP_OBJ) $(TP_OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

# Per-node numeric ground-truth tests (reuses the app object files).
TEST_DEPS = $(BUILD)/node_truth.o $(BUILD)/mtlx_doc.o $(BUILD)/mtlx_xml.o \
            $(BUILD)/mtlx_eval.o $(BUILD)/texture.o $(BUILD)/color.o \
            $(BUILD)/tp_third_party_impl.o
$(BUILD)/node_truth.o: tests/node_truth.c | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -c $< -o $@
node_truth: $(TEST_DEPS)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
test: node_truth
	./node_truth

# MaterialX -> GPU shading bridge (bakes per-material OpenPBR params and shades
# one sphere per material on the GPU via the Vulkan backend). Needs the vk
# sources from the repo root + libdl for the runtime Vulkan loader.
MTLXVK_OBJ = $(BUILD)/mtlxvk.o $(BUILD)/mtlx_doc.o $(BUILD)/mtlx_xml.o \
             $(BUILD)/mtlx_eval.o $(BUILD)/texture.o $(BUILD)/color.o \
             $(BUILD)/tp_third_party_impl.o $(BUILD)/tp_lightrt_c_tri.o \
             $(BUILD)/tp_lightrt_vkew.o $(BUILD)/tp_lightrt_c_vk.o
mtlxvk: $(MTLXVK_OBJ)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS) -ldl

# Full verification: node ground-truth + golden render regression.
check: node_truth mtlxrender
	./node_truth
	./golden.sh check

$(BUILD)/%.o: %.c | $(BUILD)
	$(CC) $(CFLAGS) $(WARN) -c $< -o $@

# pattern rules for the (few) third-party sources in various dirs
$(BUILD)/tp_%.o: %.c | $(BUILD)
	$(CC) $(CFLAGS) -w -c $< -o $@
$(BUILD)/tp_%.o: $(LIGHTRT)/%.c | $(BUILD)
	$(CC) $(CFLAGS) -w -c $< -o $@
$(BUILD)/tp_%.o: $(DEPS)/%.c | $(BUILD)
	$(CC) $(CFLAGS) -w -c $< -o $@
$(BUILD)/tp_%.o: $(TINYEXR)/src/%.c | $(BUILD)
	$(CC) $(CFLAGS) -w -c $< -o $@

$(BUILD):
	mkdir -p $(BUILD)

clean:
	rm -rf build build-vk mtlxrender node_truth mtlxvk

.PHONY: clean test check
