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

BUILD = build

# our first-party sources (full warnings)
APP_SRC = main.c pathtrace.c bsdf.c env.c framebuffer.c color.c \
          gltf_load.c mtlx_xml.c mtlx_doc.c mtlx_eval.c material_bind.c texture.c
# third-party sources (compiled quietly with -w)
TP_SRC  = third_party_impl.c \
          $(LIGHTRT)/lightrt_c_tri.c \
          $(DEPS)/tiny_gltf_v3.c \
          $(wildcard $(TINYEXR)/src/*.c)

APP_OBJ = $(addprefix $(BUILD)/,$(notdir $(APP_SRC:.c=.o)))
TP_OBJ  = $(addprefix $(BUILD)/tp_,$(notdir $(TP_SRC:.c=.o)))

CFLAGS  = $(CSTD) $(OPT) $(SIMD) $(DEFS) $(INCLUDES)
LDFLAGS = -lm -lpthread

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
	rm -rf $(BUILD) mtlxrender node_truth

.PHONY: clean test check
