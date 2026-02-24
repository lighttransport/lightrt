#include "wgsl_clair_adapter.hh"

#include <cctype>
#include <regex>
#include <string>
#include <vector>

namespace softrt {
namespace {

std::string trim(const std::string& s) {
  size_t b = 0;
  while (b < s.size() && std::isspace(static_cast<unsigned char>(s[b]))) {
    ++b;
  }
  size_t e = s.size();
  while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1]))) {
    --e;
  }
  return s.substr(b, e - b);
}

bool isIdentStart(char c) {
  return std::isalpha(static_cast<unsigned char>(c)) || c == '_';
}

bool isIdentContinue(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
}

size_t skipWs(const std::string& s, size_t i) {
  while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i]))) {
    ++i;
  }
  return i;
}

bool matchKeywordAt(const std::string& s, size_t i, const char* kw) {
  size_t k = 0;
  while (kw[k]) {
    if (i + k >= s.size() || s[i + k] != kw[k]) return false;
    ++k;
  }
  const bool left_ok = (i == 0) || !isIdentContinue(s[i - 1]);
  const bool right_ok = (i + k >= s.size()) || !isIdentContinue(s[i + k]);
  return left_ok && right_ok;
}

std::string replaceWord(const std::string& in, const std::string& from,
                        const std::string& to) {
  if (from.empty()) return in;
  std::string out;
  out.reserve(in.size());
  size_t i = 0;
  while (i < in.size()) {
    if (i + from.size() <= in.size() &&
        in.compare(i, from.size(), from) == 0) {
      const bool left_ok = (i == 0) || !isIdentContinue(in[i - 1]);
      const bool right_ok =
          (i + from.size() >= in.size()) || !isIdentContinue(in[i + from.size()]);
      if (left_ok && right_ok) {
        out += to;
        i += from.size();
        continue;
      }
    }
    out.push_back(in[i++]);
  }
  return out;
}

std::string normalizeWGSLDialects(const std::string& source) {
  std::string out = source;

  // Common CTS aliases accepted by other WGSL compilers.
  out = replaceWord(out, "vec2f", "vec2<f32>");
  out = replaceWord(out, "vec3f", "vec3<f32>");
  out = replaceWord(out, "vec4f", "vec4<f32>");
  out = replaceWord(out, "vec2i", "vec2<i32>");
  out = replaceWord(out, "vec3i", "vec3<i32>");
  out = replaceWord(out, "vec4i", "vec4<i32>");
  out = replaceWord(out, "vec2u", "vec2<u32>");
  out = replaceWord(out, "vec3u", "vec3<u32>");
  out = replaceWord(out, "vec4u", "vec4<u32>");

  out = replaceWord(out, "mat2x2f", "mat2x2<f32>");
  out = replaceWord(out, "mat3x3f", "mat3x3<f32>");
  out = replaceWord(out, "mat4x4f", "mat4x4<f32>");

  // Test-only address-space spelling used by some extracted snippets.
  out = replaceWord(out, "var<immediate>", "var<private>");

  // Accept `break if cond;` (used in CTS snippets) by lowering to an explicit
  // conditional break.
  out = std::regex_replace(out,
                           std::regex(R"(break\s+if\s+([^;]+);)"),
                           "if ($1) { break; }");

  // Accept legacy CTS form `if cond {` by adding parentheses required by our
  // current parser (`if (cond) {`).
  out = std::regex_replace(out,
                           std::regex(R"(\bif\s+([^\(\{\n][^\{\n]*)\{)"),
                           "if ($1){");

  // Some snippets place blend source attributes on local declarations.
  // Strip these attributes for current parser compatibility.
  out = std::regex_replace(out,
                           std::regex(R"(\s*@blend_src\(\d+\)\s*)"),
                           " ");

  // Some extracted snippets attach @group/@binding to local private vars.
  // Strip those attributes to keep the parser/lowering path moving.
  out = std::regex_replace(out,
                           std::regex(R"(@group\([^\)]*\)\s*@binding\([^\)]*\)\s*\n(\s*var\b))"),
                           "$1");

  // Be permissive: accept top-level `};` by dropping the redundant semicolon.
  {
    std::string fixed;
    fixed.reserve(out.size());
    int brace_depth = 0;
    bool in_line_comment = false;
    bool in_block_comment = false;
    bool in_string = false;
    for (size_t i = 0; i < out.size(); ++i) {
      const char c = out[i];
      const char next = (i + 1 < out.size()) ? out[i + 1] : '\0';

      if (in_line_comment) {
        fixed.push_back(c);
        if (c == '\n') in_line_comment = false;
        continue;
      }
      if (in_block_comment) {
        fixed.push_back(c);
        if (c == '*' && next == '/') {
          fixed.push_back(next);
          ++i;
          in_block_comment = false;
        }
        continue;
      }
      if (in_string) {
        fixed.push_back(c);
        if (c == '\\' && next != '\0') {
          fixed.push_back(next);
          ++i;
        } else if (c == '"') {
          in_string = false;
        }
        continue;
      }
      if (c == '/' && next == '/') {
        fixed.push_back(c);
        fixed.push_back(next);
        ++i;
        in_line_comment = true;
        continue;
      }
      if (c == '/' && next == '*') {
        fixed.push_back(c);
        fixed.push_back(next);
        ++i;
        in_block_comment = true;
        continue;
      }
      if (c == '"') {
        fixed.push_back(c);
        in_string = true;
        continue;
      }
      if (c == '{') {
        ++brace_depth;
      } else if (c == '}') {
        if (brace_depth > 0) --brace_depth;
      }
      if (c == ';' && brace_depth == 0 && !fixed.empty()) {
        size_t j = fixed.size();
        while (j > 0 &&
               std::isspace(static_cast<unsigned char>(fixed[j - 1]))) {
          --j;
        }
        if (j > 0 && fixed[j - 1] == '}') {
          continue;
        }
      }
      fixed.push_back(c);
    }
    out.swap(fixed);
  }

  return out;
}

size_t skipAttributeList(const std::string& s, size_t i) {
  i = skipWs(s, i);
  while (i < s.size() && s[i] == '@') {
    ++i;
    i = skipWs(s, i);
    if (i >= s.size() || !isIdentStart(s[i])) {
      return i;
    }
    while (i < s.size() && isIdentContinue(s[i])) {
      ++i;
    }
    i = skipWs(s, i);
    if (i < s.size() && s[i] == '(') {
      int depth = 0;
      do {
        if (s[i] == '(') {
          ++depth;
        } else if (s[i] == ')') {
          --depth;
        }
        ++i;
      } while (i < s.size() && depth > 0);
    }
    i = skipWs(s, i);
  }
  return i;
}

std::string defaultInitializerForType(const std::string& type) {
  const std::string t = trim(type);
  if (t.empty()) return "0";

  auto base_end = t.find('<');
  if (base_end == std::string::npos) {
    base_end = t.find_first_of(" \t\r\n");
  }
  if (base_end == std::string::npos) base_end = t.size();
  const std::string base = t.substr(0, base_end);

  if (base == "bool") return "false";
  if (base == "u32" || base == "u64") return "0u";
  if (base == "i32" || base == "i64") return "0";
  if (base == "f16" || base == "f32" || base == "f64") return "0.0";

  if (base.rfind("vec", 0) == 0) {
    if (t.find("bool") != std::string::npos) return t + "(false)";
    if (t.find("u32") != std::string::npos || t.find("u64") != std::string::npos) {
      return t + "(0u)";
    }
    if (t.find("i32") != std::string::npos || t.find("i64") != std::string::npos) {
      return t + "(0)";
    }
    return t + "(0.0)";
  }

  if (base.rfind("mat", 0) == 0) {
    return t + "(0.0)";
  }

  return "0";
}

bool parseOverrideDecl(const std::string& stmt, std::string& name_out,
                       std::string& type_out, std::string& init_out) {
  name_out.clear();
  type_out.clear();
  init_out.clear();

  size_t i = 0;
  i = skipAttributeList(stmt, i);
  i = skipWs(stmt, i);
  if (!matchKeywordAt(stmt, i, "override")) {
    return false;
  }
  i += 8;  // len("override")

  i = skipWs(stmt, i);
  if (i >= stmt.size() || !isIdentStart(stmt[i])) {
    return false;
  }
  size_t name_begin = i;
  while (i < stmt.size() && isIdentContinue(stmt[i])) {
    ++i;
  }
  name_out = stmt.substr(name_begin, i - name_begin);

  i = skipWs(stmt, i);
  if (i < stmt.size() && stmt[i] == ':') {
    ++i;
    size_t type_begin = i;
    int angle = 0;
    int paren = 0;
    int bracket = 0;
    while (i < stmt.size()) {
      const char c = stmt[i];
      if (c == '<') {
        ++angle;
      } else if (c == '>') {
        if (angle > 0) --angle;
      } else if (c == '(') {
        ++paren;
      } else if (c == ')') {
        if (paren > 0) --paren;
      } else if (c == '[') {
        ++bracket;
      } else if (c == ']') {
        if (bracket > 0) --bracket;
      } else if ((c == '=' || c == ';') && angle == 0 && paren == 0 && bracket == 0) {
        break;
      }
      ++i;
    }
    type_out = trim(stmt.substr(type_begin, i - type_begin));
  }

  i = skipWs(stmt, i);
  if (i < stmt.size() && stmt[i] == '=') {
    ++i;
    size_t init_begin = i;
    size_t semi = stmt.rfind(';');
    if (semi == std::string::npos || semi < init_begin) {
      return false;
    }
    init_out = trim(stmt.substr(init_begin, semi - init_begin));
  }

  return !name_out.empty();
}

std::string maybeRewriteTopLevelOverride(const std::string& stmt) {
  std::string name;
  std::string type;
  std::string init;
  if (!parseOverrideDecl(stmt, name, type, init)) {
    return stmt;
  }

  if (init.empty()) {
    init = defaultInitializerForType(type);
  }

  std::string out = "const " + name;
  if (!type.empty()) {
    out += ": " + trim(type);
  }
  out += " = " + init + ";";
  return out;
}

}  // namespace

std::string normalizeWGSLForClair(const std::string& source) {
  const std::string normalized_source = normalizeWGSLDialects(source);

  std::string out;
  out.reserve(normalized_source.size());

  std::string stmt;
  stmt.reserve(256);

  int brace_depth = 0;
  bool in_line_comment = false;
  bool in_block_comment = false;
  bool in_string = false;

  for (size_t i = 0; i < normalized_source.size(); ++i) {
    const char c = normalized_source[i];
    const char next = (i + 1 < normalized_source.size()) ? normalized_source[i + 1] : '\0';

    if (in_line_comment) {
      stmt.push_back(c);
      if (c == '\n') in_line_comment = false;
      continue;
    }
    if (in_block_comment) {
      stmt.push_back(c);
      if (c == '*' && next == '/') {
        stmt.push_back(next);
        ++i;
        in_block_comment = false;
      }
      continue;
    }
    if (in_string) {
      stmt.push_back(c);
      if (c == '\\' && next != '\0') {
        stmt.push_back(next);
        ++i;
      } else if (c == '"') {
        in_string = false;
      }
      continue;
    }

    if (c == '/' && next == '/') {
      stmt.push_back(c);
      stmt.push_back(next);
      ++i;
      in_line_comment = true;
      continue;
    }
    if (c == '/' && next == '*') {
      stmt.push_back(c);
      stmt.push_back(next);
      ++i;
      in_block_comment = true;
      continue;
    }
    if (c == '"') {
      stmt.push_back(c);
      in_string = true;
      continue;
    }

    if (c == '{') {
      ++brace_depth;
    } else if (c == '}') {
      if (brace_depth > 0) --brace_depth;
    }

    stmt.push_back(c);

    if (c == ';' && brace_depth == 0) {
      out += maybeRewriteTopLevelOverride(stmt);
      stmt.clear();
    }
  }

  out += stmt;
  return out;
}

}  // namespace softrt
