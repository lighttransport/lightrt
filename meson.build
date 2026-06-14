# Meson build file for LightRT library
# To be used with meson/ninja build system

project('lightrt',
    ['cpp', 'c'],
    version: '1.0.0',
    default_options: ['c_std=c11']
)

# Compiler flags (meson uses 'cpp' as the C++ language id; pass args as a list)
add_project_arguments(['-Wall', '-Wextra', '-O3'],
  native: true,
  language: 'cpp'
)

# C binding implementation. lightrt_c.c is standalone pure C11 and does not
# depend on the C++ BVH wrapper.
c_binding_src = 'lightrt_c.c'

# Library target
static_lib = static_library('lightrt',
  sources: ['lightrt.cc', c_binding_src],
  install: true
)

# Example executable
lightrt_example = executable('lightrt_example',
  sources: ['example.cc'],
  link_with: static_lib
)

# Benchmark executable
lightrt_benchmark = executable('lightrt_benchmark',
  sources: ['benchmark/benchmark.cc'],
  link_with: static_lib
)

# Pure-C11 binding self-test (compiles lightrt_c.c directly; no C++ dependency).
m_dep = meson.get_compiler('c').find_library('m', required: false)
lightrt_c_test = executable('lightrt_c_test',
  sources: ['lightrt_c.c', 'tests/test_lightrt_c.c'],
  dependencies: m_dep,
  build_by_default: false
)
test('lightrt_c_test', lightrt_c_test)

# Installation (the static library is installed via install: true above)
install_headers('lightrt.hh', 'lightrt_c.h')
