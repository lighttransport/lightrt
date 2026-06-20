# Standalone Makefile for the Vulkan analytic-shading demo.
# Runtime dlopen of libvulkan — no Vulkan SDK headers, no -lvulkan.
#   make            -> ./vk_shade
#   make run        -> build + run (writes vk_shade_{cpu,gpu}.ppm)

CC      ?= cc
CSTD     = -std=c11
WARN     = -Wall -Wextra
OPT     ?= -O2
LIGHTRT  = ../..
INCLUDES = -I. -I$(LIGHTRT)
CFLAGS   = $(CSTD) $(OPT) $(WARN) $(INCLUDES)
LDFLAGS  = -lm -ldl

SRC = vk_shade.c $(LIGHTRT)/lightrt_vkew.c $(LIGHTRT)/lightrt_c_vk.c \
      $(LIGHTRT)/lightrt_c_tri.c

vk_shade: $(SRC)
	$(CC) $(CFLAGS) -o $@ $(SRC) $(LDFLAGS)

run: vk_shade
	./vk_shade

clean:
	rm -f vk_shade vk_shade_cpu.ppm vk_shade_gpu.ppm

.PHONY: run clean
