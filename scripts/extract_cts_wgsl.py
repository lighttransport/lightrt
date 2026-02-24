#!/usr/bin/env python3
import argparse
import hashlib
import json
import os
import pathlib
import re
from typing import List, Tuple


WGSL_STAGE_PAT = re.compile(r"@(?:compute|vertex|fragment)\b")
WGSL_FN_PAT = re.compile(r"\bfn\s+[A-Za-z_]\w*\s*\(")
INTERP_SENTINEL = "__CTS_TEMPLATE_EXPR__"
WGSL_ENTRY_PAT = re.compile(
    r"@(?P<stage>compute|vertex|fragment)\b(?:[\s\r\n]+@[^\r\n]+)*[\s\r\n]+fn\s+(?P<name>[A-Za-z_]\w*)\s*\(",
    re.MULTILINE,
)


def has_balanced_delimiters(s: str) -> bool:
    brace = 0
    paren = 0
    angle = 0
    i = 0
    n = len(s)
    in_line_comment = False
    in_block_comment = False
    in_string = False
    while i < n:
        c = s[i]
        nxt = s[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if c == "\n":
                in_line_comment = False
            i += 1
            continue
        if in_block_comment:
            if c == "*" and nxt == "/":
                in_block_comment = False
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue

        if c == "/" and nxt == "/":
            in_line_comment = True
            i += 2
            continue
        if c == "/" and nxt == "*":
            in_block_comment = True
            i += 2
            continue
        if c == '"':
            in_string = True
            i += 1
            continue

        if c == "{":
            brace += 1
        elif c == "}":
            brace -= 1
            if brace < 0:
                return False
        elif c == "(":
            paren += 1
        elif c == ")":
            paren -= 1
            if paren < 0:
                return False
        elif c == "<":
            # Heuristic: only track obvious generic/type contexts.
            prev = s[i - 1] if i > 0 else ""
            if prev.isalnum() or prev in "_>)]":
                angle += 1
        elif c == ">":
            if angle > 0:
                angle -= 1

        i += 1

    return brace == 0 and paren == 0 and not in_block_comment and not in_string


def extract_template_literals(text: str) -> List[str]:
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] != "`":
            i += 1
            continue
        i += 1
        buf = []
        while i < n:
            c = text[i]
            if c == "\\":
                if i + 1 < n:
                    buf.append(text[i : i + 2])
                    i += 2
                else:
                    i += 1
                continue
            if c == "`":
                i += 1
                break
            if c == "$" and i + 1 < n and text[i + 1] == "{":
                i += 2
                depth = 1
                while i < n and depth > 0:
                    c2 = text[i]
                    if c2 == "\\":
                        i += 2
                        continue
                    if c2 == "{":
                        depth += 1
                    elif c2 == "}":
                        depth -= 1
                    i += 1
                buf.append(INTERP_SENTINEL)
                continue
            buf.append(c)
            i += 1
        out.append("".join(buf))
    return out


def looks_like_wgsl(s: str) -> bool:
    if INTERP_SENTINEL in s:
        return False
    if s.lstrip().startswith("*"):
        return False
    if "[[" in s:
        return False
    if not WGSL_STAGE_PAT.search(s):
        return False
    if not WGSL_FN_PAT.search(s):
        return False
    if s.lstrip().startswith("}"):
        return False
    if not has_balanced_delimiters(s):
        return False
    if not detect_entries(s):
        return False
    return True


def guess_stage(s: str) -> str:
    if "@compute" in s:
        return "compute"
    if "@vertex" in s:
        return "vertex"
    if "@fragment" in s:
        return "fragment"
    return "unknown"


def detect_entries(s: str) -> List[Tuple[str, str]]:
    entries: List[Tuple[str, str]] = []
    for m in WGSL_ENTRY_PAT.finditer(s):
        stage = m.group("stage")
        name = m.group("name")
        entries.append((stage, name))
    return entries


def iter_ts_files(cts_root: pathlib.Path) -> List[pathlib.Path]:
    include_roots = [
        cts_root / "src" / "webgpu",
        cts_root / "src" / "unittests",
        cts_root / "src",
    ]
    files = []
    seen = set()
    for root in include_roots:
        if not root.exists():
            continue
        for p in root.rglob("*.ts"):
            rp = p.resolve()
            if rp in seen:
                continue
            seen.add(rp)
            files.append(p)
    return files


def main() -> int:
    ap = argparse.ArgumentParser(description="Extract WGSL snippets from WebGPU CTS sources")
    ap.add_argument("--cts-root", required=True, help="Path to webgpu-cts checkout")
    ap.add_argument("--out-dir", required=True, help="Output directory")
    ap.add_argument("--limit", type=int, default=0, help="Maximum snippets to extract (0 = no limit)")
    args = ap.parse_args()

    cts_root = pathlib.Path(args.cts_root)
    out_dir = pathlib.Path(args.out_dir)
    shader_dir = out_dir / "shaders"
    shader_dir.mkdir(parents=True, exist_ok=True)

    files = iter_ts_files(cts_root)
    manifest = []
    count = 0

    for path in files:
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        literals = extract_template_literals(text)
        for idx, lit in enumerate(literals):
            lit2 = lit.strip()
            if not looks_like_wgsl(lit2):
                continue

            h = hashlib.sha256(lit2.encode("utf-8")).hexdigest()[:16]
            out_name = f"{path.stem}_{idx}_{h}.wgsl"
            out_path = shader_dir / out_name
            out_path.write_text(lit2 + "\n", encoding="utf-8")

            manifest.append(
                {
                    "source_file": str(path.relative_to(cts_root)),
                    "shader_file": str(out_path),
                    "stage": guess_stage(lit2),
                    "entries": [{"stage": st, "name": fn} for st, fn in detect_entries(lit2)],
                }
            )
            count += 1
            if args.limit > 0 and count >= args.limit:
                break
        if args.limit > 0 and count >= args.limit:
            break

    out_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = out_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print(f"Extracted {len(manifest)} WGSL snippets")
    print(f"Manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
