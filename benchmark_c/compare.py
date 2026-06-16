#!/usr/bin/env python3
"""Pretty-print bench_c CSV results, with speedups against a reference backend.

Usage:
  compare.py results.csv                  # tables grouped by scene/workload/threads
  compare.py results.csv --ref embree     # speedup column vs embree (default)
  compare.py new.csv --baseline old.csv   # regression diff between two runs

Stdlib only. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import csv
import sys
from collections import OrderedDict


def read_rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def fmt_table(rows, header):
    widths = [len(h) for h in header]
    for r in rows:
        for i, c in enumerate(r):
            widths[i] = max(widths[i], len(str(c)))
    lines = []
    sep = "  "
    lines.append(sep.join(h.ljust(widths[i]) for i, h in enumerate(header)))
    lines.append(sep.join("-" * widths[i] for i in range(len(header))))
    for r in rows:
        lines.append(sep.join(str(c).ljust(widths[i]) for i, c in enumerate(r)))
    return "\n".join(lines)


def group_key(row):
    return (row["scene"], row["ntris"], row["workload"], row["threads"])


def print_run(rows, ref_backend):
    groups = OrderedDict()
    for r in rows:
        groups.setdefault(group_key(r), []).append(r)

    for (scene, ntris, workload, threads), grp in groups.items():
        ref = next((g for g in grp if g["backend"] == ref_backend), None)
        ref_mrays = float(ref["mrays_s"]) if ref else None
        print(f"\n== {scene} ({int(ntris):,} tris)  workload={workload}  "
              f"threads={threads} ==")
        out = []
        for g in sorted(grp, key=lambda x: -float(x["mrays_s"])):
            speed = ""
            if ref_mrays and ref_mrays > 0:
                speed = f"{float(g['mrays_s']) / ref_mrays:.2f}x"
            out.append([
                g["backend"],
                f"{float(g['mrays_s']):.2f}",
                speed,
                f"{float(g['build_ms']):.1f}",
                f"{float(g['build_mtris_s']):.2f}",
                f"{float(g['mem_mb']):.2f}",
                f"{float(g['hit_frac']):.4f}",
            ])
        print(fmt_table(out, ["backend", "Mrays/s", f"vs {ref_backend}",
                              "build ms", "Mtris/s", "mem MB", "hit"]))

        hit_fracs = [float(g["hit_frac"]) for g in grp]
        if hit_fracs and (max(hit_fracs) - min(hit_fracs)) > 0.001:
            print("WARNING: hit_frac spread > 0.1% across backends "
                  f"({min(hit_fracs):.4f} .. {max(hit_fracs):.4f})")


def print_diff(rows, baseline_rows):
    def key(r):
        return (r["backend"], r["scene"], r["ntris"], r["workload"], r["threads"])

    base = {key(r): r for r in baseline_rows}
    out = []
    for r in rows:
        b = base.get(key(r))
        if not b:
            continue
        new = float(r["mrays_s"])
        old = float(b["mrays_s"])
        delta = (new / old - 1.0) * 100.0 if old > 0 else 0.0
        out.append([
            r["backend"], r["workload"], r["threads"], r["ntris"],
            f"{old:.2f}", f"{new:.2f}", f"{delta:+.1f}%",
        ])
    print(fmt_table(out, ["backend", "workload", "thr", "ntris",
                          "old Mrays/s", "new Mrays/s", "delta"]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv")
    ap.add_argument("--ref", default="embree",
                    help="reference backend for the speedup column")
    ap.add_argument("--baseline", help="older CSV to diff against")
    args = ap.parse_args()

    rows = read_rows(args.csv)
    if not rows:
        print("no rows", file=sys.stderr)
        return 1

    if args.baseline:
        print_diff(rows, read_rows(args.baseline))
    else:
        ref = args.ref
        if not any(r["backend"] == ref for r in rows):
            fallback = rows[0]["backend"]
            print(f"note: reference backend '{ref}' absent; using '{fallback}'")
            ref = fallback
        print_run(rows, ref)
    return 0


if __name__ == "__main__":
    sys.exit(main())
