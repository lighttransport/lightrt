#!/usr/bin/env python3
"""CI gate: `#print axioms` for every theorem in LightRT/.

* A theorem whose axioms include `sorryAx` is reported as OPEN (allowed).
* Every other theorem may depend only on the allowlist below.
* `native_decide` / `bv_decide` (which add `Lean.ofReduceBool` / trust the
  compiler) are forbidden under LightRT/Robust and LightRT/C/Proofs.
"""
import os
import re
import subprocess
import sys

FORMAL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
CORE_DIRS = ("LightRT/Robust", "LightRT/C/Proofs")


def theorems():
    out = []
    for dp, _, fs in os.walk(os.path.join(FORMAL, "LightRT")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dp, f)
            mod = os.path.relpath(path, FORMAL)[:-5].replace("/", ".")
            ns, ends = [], []
            for line in open(path):
                m = re.match(r"\s*namespace\s+(\S+)", line)
                if m:
                    ns.append(m.group(1))
                m = re.match(r"\s*end\s+(\S+)\s*$", line)
                if m and ns and ns[-1] == m.group(1):
                    ns.pop()
                # private theorems have mangled names and are covered by their callers
                m = re.match(r"(?:@\[[^\]]*\]\s*)?theorem\s+([^\s(:{\[]+)", line)
                if m:
                    out.append((mod, ".".join(ns + [m.group(1)]), path))
    return out


def main():
    bad = 0
    for d in CORE_DIRS:
        for dp, _, fs in os.walk(os.path.join(FORMAL, d)):
            for f in fs:
                if f.endswith(".lean"):
                    txt = open(os.path.join(dp, f)).read()
                    for kw in ("native_decide", "bv_decide"):
                        if re.search(r"(?<![`\w])" + kw + r"(?![`\w])", re.sub(r"--.*", "", txt)):
                            print(f"FORBIDDEN {kw} in {os.path.join(d, f)}")
                            bad += 1
    ths = theorems()
    mods = sorted({m for m, _, _ in ths})
    src = "\n".join(f"import {m}" for m in mods) + "\n"
    src += "\n".join(f"#print axioms {n}" for _, n, _ in ths) + "\n"
    tmp = os.path.join(FORMAL, ".lake", "AxiomCheck.lean")
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    open(tmp, "w").write(src)
    res = subprocess.run(["lake", "env", "lean", tmp], cwd=FORMAL, capture_output=True, text=True)
    text = res.stdout + res.stderr
    blocks = re.split(r"(?m)^(?='\S+' (?:depends|does))", text)
    seen, closed, open_ = {}, [], []
    for b in blocks:
        m = re.match(r"'(.+?)' (depends on axioms: \[(.*?)\]|does not depend on any axioms)", b, re.S)
        if m:
            axs = {a.strip() for a in (m.group(3) or "").replace("\n", " ").split(",") if a.strip()}
            seen[m.group(1)] = axs
    for _, n, _ in ths:
        if n not in seen:
            print(f"ERROR no axiom report for {n}")
            bad += 1
            continue
        axs = seen[n]
        if "sorryAx" in axs:
            open_.append(n)
        elif axs - ALLOW:
            print(f"DISALLOWED axioms in {n}: {sorted(axs - ALLOW)}")
            bad += 1
        else:
            closed.append(n)
    print(f"{len(closed)} theorems closed (axioms ⊆ {sorted(ALLOW)}), {len(open_)} open (sorry)")
    for n in closed:
        print(f"  closed: {n}")
    if res.returncode != 0 and not seen:
        print(text[-2000:])
        bad += 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
