#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "wgsl_clair_adapter.hh"

#ifdef SOFTRT_ENABLE_CLAIR
#include "wgsl-ast.hh"
#include "wgsl-jit-compiler.hh"
#endif

namespace {

std::string readTextFile(const std::string& path) {
  std::ifstream ifs(path);
  if (!ifs) {
    return {};
  }
  std::ostringstream oss;
  oss << ifs.rdbuf();
  return oss.str();
}

#ifdef SOFTRT_ENABLE_CLAIR
clair::wgsl::TargetBackend parseBackend(const std::string& s) {
  if (s == "SPIRV") return clair::wgsl::TargetBackend::SPIRV;
  if (s == "CPU") return clair::wgsl::TargetBackend::CPU;
  if (s == "CPU_JIT") return clair::wgsl::TargetBackend::CPU_JIT;
  if (s == "PTX") return clair::wgsl::TargetBackend::PTX;
  return clair::wgsl::TargetBackend::SPIRV;
}

clair::wgsl::ShaderStage detectStage(const std::string& source,
                                     const std::string& explicit_stage) {
  if (explicit_stage == "compute") return clair::wgsl::ShaderStage::COMPUTE;
  if (explicit_stage == "vertex") return clair::wgsl::ShaderStage::VERTEX;
  if (explicit_stage == "fragment") return clair::wgsl::ShaderStage::FRAGMENT;

  if (source.find("@compute") != std::string::npos) {
    return clair::wgsl::ShaderStage::COMPUTE;
  }
  if (source.find("@vertex") != std::string::npos) {
    return clair::wgsl::ShaderStage::VERTEX;
  }
  if (source.find("@fragment") != std::string::npos) {
    return clair::wgsl::ShaderStage::FRAGMENT;
  }
  return clair::wgsl::ShaderStage::COMPUTE;
}
#endif

}  // namespace

int main(int argc, char** argv) {
  std::string input_path;
  std::string entry = "main";
  std::string backend = "SPIRV";
  std::string stage = "auto";
  int opt = 0;

  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--input" && i + 1 < argc) {
      input_path = argv[++i];
    } else if (arg == "--entry" && i + 1 < argc) {
      entry = argv[++i];
    } else if (arg == "--backend" && i + 1 < argc) {
      backend = argv[++i];
    } else if (arg == "--stage" && i + 1 < argc) {
      stage = argv[++i];
    } else if (arg == "--opt" && i + 1 < argc) {
      opt = std::atoi(argv[++i]);
      if (opt < 0) opt = 0;
      if (opt > 3) opt = 3;
    } else if (arg == "-h" || arg == "--help") {
      std::cout
          << "Usage: webgpu_wgsl_compile_file --input <shader.wgsl> "
             "[--entry main] [--backend SPIRV|CPU|CPU_JIT|PTX] "
             "[--stage auto|compute|vertex|fragment] [--opt 0..3]\n";
      return 0;
    } else {
      std::cerr << "Unknown argument: " << arg << "\n";
      return 2;
    }
  }

  if (input_path.empty()) {
    std::cerr << "--input is required\n";
    return 2;
  }

  const std::string source = readTextFile(input_path);
  if (source.empty()) {
    std::cerr << "Failed to read input: " << input_path << "\n";
    return 2;
  }

#ifndef SOFTRT_ENABLE_CLAIR
  std::cerr << "SOFTRT_ENABLE_CLAIR is disabled\n";
  return 3;
#else
  clair::wgsl::WGSLJITCompiler compiler;
  compiler.setCacheDirectory("/tmp/clair-wgsl-cache");
  compiler.setTargetBackend(parseBackend(backend));
  compiler.setOptimizationLevel(opt);

  const std::string normalized_wgsl = softrt::normalizeWGSLForClair(source);
  auto compile_result =
      compiler.compileShader(normalized_wgsl, entry,
                            detectStage(normalized_wgsl, stage));
  if (!compile_result) {
    std::cerr << "Compile failed: " << compile_result.error() << "\n";
    return 1;
  }

  std::cout << "OK: " << input_path << "\n";
  return 0;
#endif
}
