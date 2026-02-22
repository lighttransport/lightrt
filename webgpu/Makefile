CXX ?= g++
AR ?= ar

CXXFLAGS = -std=c++17 -Wall -Wextra -O3 -fno-rtti -fno-exceptions

# SIMD flags (x86-64)
ARCH := $(shell $(CXX) -dumpmachine 2>/dev/null)
ifneq (,$(findstring x86_64,$(ARCH)))
  CXXFLAGS += -msse2
  ifndef NO_AVX
    CXXFLAGS += -mavx
  endif
  ifndef NO_AVX2
    CXXFLAGS += -mavx2 -mfma
  endif
  ifndef NO_F16C
    CXXFLAGS += -mf16c
  endif
endif

# ARM64
ifneq (,$(findstring aarch64,$(ARCH)))
  CXXFLAGS += -march=armv8-a
  ifndef NO_SVE
    CXXFLAGS += -march=armv8-a+sve
  endif
endif

ifeq ($(DEBUG),1)
  CXXFLAGS := $(filter-out -O3,$(CXXFLAGS)) -O0 -g -DDEBUG
endif

LIGHTRT_LIB = ../liblightrt.a
INCLUDES = -I..

TARGET = webgpu_example

.PHONY: all clean run

all: $(TARGET)

# Build parent library if needed
$(LIGHTRT_LIB):
	$(MAKE) -C .. liblightrt.a

webgpu_lightrt.o: webgpu_lightrt.cc webgpu_lightrt.hh ../lightrt.hh
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

webgpu_example.o: webgpu_example.cc webgpu_lightrt.hh
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

$(TARGET): webgpu_example.o webgpu_lightrt.o $(LIGHTRT_LIB)
	$(CXX) $(CXXFLAGS) $^ -lpthread -o $@

run: $(TARGET)
	./$(TARGET)

clean:
	rm -f *.o $(TARGET) triangle.bmp
