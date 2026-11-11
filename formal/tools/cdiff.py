#!/usr/bin/env python3
"""Differential testing: compiled C (tools/cdiff_c.c, the real lightrt_c_tri.c
kernels) vs. the MiniC semantics of the c2lean-translated C (CDiff.lean,
binary32 RNE in Lean). Results must agree bit-for-bit (all NaNs are treated as
equal: IEEE leaves the NaN payload unspecified).

Usage:
    python3 formal/tools/cdiff.py --n 10000 [--seed S]
    python3 formal/tools/cdiff.py --search-miss --n 200000
        searches for rays that geometrically hit a box (decided exactly with
        rationals) but that `tri_slab_scalar` rejects: witnesses for
        `tri_slab_scalar_false_miss_exists` in LightRT/Robust/Slab.lean.
"""
import argparse
import os
import random
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
FORMAL = os.path.dirname(HERE)
ROOT = os.path.dirname(FORMAL)
CC = os.environ.get("CC", "clang")


def bits(x):
    return struct.unpack("<I", struct.pack("<f", fl(x)))[0]


def fl(x):
    """Round a Python float to binary32 (overflow → ±inf, as RNE does)."""
    try:
        return struct.unpack("<f", struct.pack("<f", x))[0]
    except OverflowError:
        return float("inf") if x > 0 else float("-inf")


def ffrom(b):
    return struct.unpack("<f", struct.pack("<I", b))[0]


SPECIAL = [0.0, -0.0, 1.0, -1.0, 1e-20, -1e-20, 1e-38, 1e-45, float("inf"), float("-inf"),
           3.4028234663852886e38, 0.5, 2.0, 1e18, 1e-18]


def rnd(r, special_p=0.1):
    if r.random() < special_p:
        return r.choice(SPECIAL + [float("nan")] * (1 if r.random() < 0.1 else 0) or [0.0])
    e = r.choice([0, 0, 0, 1, 3, 10, 30])
    return fl(r.uniform(-1, 1) * 10.0 ** r.uniform(-e, e))


def vec_slab(r):
    o = [rnd(r) for _ in range(3)]
    d = [rnd(r) for _ in range(3)]
    tmin = abs(rnd(r, 0.05)) if r.random() < 0.8 else 0.0
    tmax = r.choice([float("inf"), abs(rnd(r, 0.05)) + tmin])
    lo = [rnd(r) for _ in range(3)]
    hi = [x + abs(rnd(r, 0.05)) for x in lo]
    tbest = r.choice([float("inf"), tmax, abs(rnd(r))])
    vals = o + [tmin] + d + [tmax] + lo + [fl(x) for x in hi] + [tbest]
    return "slab " + " ".join(f"{bits(fl(v)):08x}" for v in vals)


def vec_slabr(r):
    """Default-build robust slab; half the vectors put the ray parallel to and
    exactly ON a face plane (d = +-0, o = lo or hi), the `sinv = +inf` case."""
    w = vec_slab(r).split()[1:]
    if r.random() < 0.5:
        k = r.randrange(3)
        w[4 + k] = r.choice(["00000000", "80000000"])
        w[k] = w[8 + k] if r.random() < 0.5 else w[11 + k]
    return "slabr " + " ".join(w)


def vec_mt(r):
    vals = [rnd(r) for _ in range(15)]
    vals += [abs(rnd(r, 0.05)) if r.random() < 0.8 else 0.0, r.choice([float("inf"), abs(rnd(r))])]
    return "mt " + " ".join(f"{bits(fl(v)):08x}" for v in vals)


def vec_woop(r):
    return "woop" + vec_mt(r)[2:]


def vec_degenerate(r):
    """MT with v1 = v0 or v2 = v0 (zero edge), Woop with any two vertices equal:
    both must MISS (Robust/Degenerate.lean). Copies are numerically equal; a
    zero component may flip sign (+0 vs -0 still gives a zero edge)."""
    kind = r.choice(["mt", "woop"])
    w = vec_mt(r).split()[1:]
    pairs = [(6, 9), (6, 12)] + ([(9, 12)] if kind == "woop" else [])
    src, dst = r.choice(pairs)
    for k in range(3):
        x = w[src + k]
        if x in ("00000000", "80000000") and r.random() < 0.5:
            x = "80000000" if x == "00000000" else "00000000"
        w[dst + k] = x
    return "deg" + kind + " " + " ".join(w)


def norm(line):
    out = []
    for w in line.split():
        if len(w) == 8:
            v = int(w, 16)
            if (v >> 23) & 0xFF == 0xFF and v & 0x7FFFFF:
                w = "nan"
        out.append(w)
    return " ".join(out)


LEGACY = ["-DLRT_TRI_NO_SLAB_ROBUST", "-DLRT_TRI_NO_LEAF_BOX_EXACT"]


def build_c(tmp, flags=LEGACY, name="cdiff_c"):
    """`slab`/`mt`/`woop` lines go to the legacy build (model `Gen`); `slabr`
    lines to the default build (robust slab, model `GenRobust`)."""
    exe = os.path.join(tmp, name)
    subprocess.check_call([CC, "-std=c11", "-O0", "-ffp-contract=off", "-w", *flags,
                           "-fsanitize=address,undefined", "-fno-sanitize-recover=undefined",
                           f"-I{ROOT}", "-o", exe, os.path.join(HERE, "cdiff_c.c"),
                           "-lm", "-lpthread"])
    return exe


def run(cmd, inp, cwd=None):
    return subprocess.run(cmd, input=inp, capture_output=True, text=True, check=True,
                          cwd=cwd).stdout.splitlines()


def lean_exe():
    subprocess.check_call(["lake", "build", "cdiff"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    return [os.path.join(FORMAL, ".lake", "build", "bin", "cdiff")]


def exact_hit(o, d, tmin, tmax, lo, hi):
    """Exact (rational) ray-segment/box intersection on finite float inputs."""
    a, b = Fraction(tmin), (None if tmax == float("inf") else Fraction(tmax))
    for i in range(3):
        oi, di, l, h = Fraction(o[i]), Fraction(d[i]), Fraction(lo[i]), Fraction(hi[i])
        if di == 0:
            if not (l <= oi <= h):
                return False
            continue
        t0, t1 = (l - oi) / di, (h - oi) / di
        if t0 > t1:
            t0, t1 = t1, t0
        a = max(a, t0)
        b = t1 if b is None else min(b, t1)
    return b is None or a <= b


def vec_grazing(r):
    """Rays aimed at a box corner/edge, where the slab test is most fragile."""
    o = [fl(r.uniform(-1, 1) * 10.0 ** r.uniform(0, 4)) for _ in range(3)]
    d = [fl(r.uniform(-1, 1) * 10.0 ** r.uniform(-3, 1)) or 1.0 for _ in range(3)]
    t = r.uniform(0.5, 1000)
    p = [o[i] + t * d[i] for i in range(3)]
    size = [fl(abs(r.uniform(0, 1)) * 10.0 ** r.uniform(-6, 2)) for _ in range(3)]
    lo, hi = [], []
    for i in range(3):
        if r.random() < 0.5:
            lo.append(fl(p[i])); hi.append(fl(p[i] + size[i]))
        else:
            hi.append(fl(p[i])); lo.append(fl(p[i] - size[i]))
    return o, d, 0.0, float("inf"), lo, hi


def search_miss(args, cexe, lexe):
    r = random.Random(args.seed)
    cases, lines = [], []
    for _ in range(args.n):
        o, d, tmin, tmax, lo, hi = vec_grazing(r)
        if not exact_hit(o, d, tmin, tmax, lo, hi):
            continue
        vals = o + [tmin] + d + [tmax] + lo + hi + [float("inf")]
        cases.append((o, d, tmin, tmax, lo, hi))
        lines.append("slab " + " ".join(f"{bits(v):08x}" for v in vals))
    inp = "\n".join(lines) + "\n"
    cout = run([cexe], inp)
    lout = run(lexe, inp)
    misses = 0
    for case, line, c, l in zip(cases, lines, cout, lout):
        if norm(c) != norm(l):
            print("MISMATCH C vs MiniC:", line, "|", c, "|", l)
            return 1
        if c.split()[13] == "0":
            misses += 1
            if misses <= 3:
                print("FALSE MISS witness (C and MiniC agree):", line)
    print(f"{len(cases)} exact-hit grazing rays, {misses} false misses by tri_slab_scalar")
    # Inflated far bound (Stage 3): K = ceil_f32(1 + 2γ₃) = 1+8u and ceil_f32(1 + 2γ₄) = 1+10u.
    for name, kbits in (("1+2γ3", 0x3f800004), ("1+2γ4", 0x3f800005)):
        kin = "\n".join(l.replace("slab ", "slabk ", 1) + f" {kbits:08x}" for l in lines) + "\n"
        kout = run(lexe, kin)
        left = sum(1 for k in kout if k.strip() == "0")
        print(f"  inflated K={name}: {left} false misses remain")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--search-miss", action="store_true")
    args = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        cexe = build_c(tmp)
        rexe = build_c(tmp, [], "cdiff_c_default")
        lexe = lean_exe()
        if args.search_miss:
            return search_miss(args, cexe, lexe)
        r = random.Random(args.seed)
        gens = [vec_slab, vec_mt, vec_woop, vec_slabr, vec_degenerate]
        tagged = [gens[k % 5](r) for k in range(args.n)]
        deg = [l.startswith("deg") for l in tagged]
        lines = [l[3:] if d else l for l, d in zip(tagged, deg)]
        inp = "\n".join(lines) + "\n"
        rob = [l.startswith("slabr ") for l in lines]
        leg_out = iter(run([cexe], "\n".join(l for l, x in zip(lines, rob) if not x) + "\n"))
        rob_out = iter(run([rexe], "\n".join(l for l, x in zip(lines, rob) if x) + "\n"))
        cout = [next(rob_out) if x else next(leg_out) for x in rob]
        lout = run(lexe, inp)
        if len(cout) != len(lines) or len(lout) != len(lines):
            print(f"output length mismatch: C={len(cout)} MiniC={len(lout)} n={len(lines)}")
            return 1
        bad = 0
        for line, c, l in zip(lines, cout, lout):
            if norm(c) != norm(l):
                bad += 1
                if bad <= 5:
                    print("MISMATCH\n  in:   ", line, "\n  C:    ", c, "\n  MiniC:", l)
        degbad = 0
        for line, c, d in zip(lines, cout, deg):
            if d and norm(c) != "0":
                degbad += 1
                if degbad <= 5:
                    print("DEGENERATE HIT\n  in:", line, "\n  C: ", c)
        bad += degbad
        hits = sum(1 for c, d in zip(cout, deg) if c.startswith("1 ") and not d)
        print(f"{len(lines)} vectors ({sum(rob)} default-build robust slab, {sum(deg)} degenerate: "
              f"{sum(deg) - degbad} miss as proved), {bad} mismatches, {hits} MT/Woop hits")
        return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
