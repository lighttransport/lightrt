# Meson build file for LightRT library
# To be used with meson/ninja build system

project('lightrt',
    version: '1.0.0'
)

# Compiler flags
add_project_arguments('-Wall -Wextra -O3',
  native: true,
  language: 'c++'
)

# Library target
static_lib = static_library('lightrt',
  sources: ['lightrt.cc', 'lightrt_c.cc'],
  install: true
)

# Example executable
lightrt_example = executable('lightrt_example',
  sources: ['example.cc'],
  static_lib
)

# Benchmark executable
lightrt_benchmark = executable('lightrt_benchmark',
  sources: ['benchmark/benchmark.cc'],
  static_lib
)

# Installation
install()