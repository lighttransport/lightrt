#!/usr/bin/env python3
"""BVH validation: dump C-built BVHs (tools/bvhdump.c) and check them in Lean (CheckBVH).

Built with -DLRT_TRI_LEAF_BOX_EXACT every tree must pass `checkWF` (the hypothesis
of `Check.checked_run_root` / `Flat.run_approx`), and the Lean mirror of the
traversal loop (verified Ref.raySetup / Ref.slab) must reproduce the C scalar
traversal bit for bit. Differences from brute force are reported, not failed:
1-ulp tnear culling (run_approx) and the parallel-ray false miss
(slab_parallel_false_miss) are known, proved behaviours of the default kernel.
"""
import argparse, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
FORMAL = os.path.join(ROOT, "formal")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rays", type=int, default=200)
    ap.add_argument("--seeds", type=int, default=3)
    a = ap.parse_args()
    tmp = tempfile.mkdtemp()
    exe = {}
    for name, flags in (("plain", []), ("exact", ["-DLRT_TRI_LEAF_BOX_EXACT"])):
        exe[name] = os.path.join(tmp, "bvhdump_" + name)
        subprocess.check_call(["cc", "-O1", "-ffp-contract=off", "-msse4.1", "-mavx2", "-mfma",
                               "-w", "-I" + ROOT, *flags, "-o", exe[name],
                               os.path.join(HERE, "bvhdump.c"), "-lm", "-lpthread"])
    subprocess.check_call(["lake", "build", "checkbvh"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    chk = os.path.join(FORMAL, ".lake", "build", "bin", "checkbvh")
    # (ntris, quality, layout, scene): LBVH/SAH x BVH4/BVH8 x soup/heightfield
    cfgs = [(400, 0, 4, 0), (500, 1, 4, 0), (1000, 1, 4, 1), (800, 0, 8, 1), (800, 1, 8, 0)]
    bad = 0
    tot = {"rays": 0, "brute": 0, "miss": 0, "wf_plain_fail": 0, "trees": 0}
    for seed in range(1, a.seeds + 1):
        for (n, q, w, g) in cfgs:
            for name in ("plain", "exact"):
                dump = subprocess.run([exe[name], str(seed), str(n), str(a.rays), str(q), str(w), str(g)],
                                      check=True, capture_output=True).stdout
                out = subprocess.run([chk], input=dump, check=True, capture_output=True).stdout.decode()
                m = dict(re.findall(r"([\w/\-\(\)=]+?)=(\w+)", out.replace("\n", " ")))
                wf = "checkWF=true" in out
                rays = int(re.search(r"rays=(\d+)", out).group(1))
                same = int(re.search(r"lean==C-scalar\(t,prim\)=(\d+)", out).group(1))
                brute = int(re.search(r"t==brute=(\d+)", out).group(1))
                miss = int(re.search(r"hit/miss-vs-brute=(\d+)", out).group(1))
                if same != rays:
                    print(f"FAIL seed={seed} cfg={(n,q,w,g)} {name}: Lean mirror != C on {rays-same} rays")
                    bad += 1
                if name == "exact":
                    tot["trees"] += 1; tot["rays"] += rays
                    tot["brute"] += rays - brute; tot["miss"] += miss
                    if not wf:
                        print(f"FAIL seed={seed} cfg={(n,q,w,g)}: checkWF false with LRT_TRI_LEAF_BOX_EXACT")
                        bad += 1
                elif not wf:
                    tot["wf_plain_fail"] += 1
    print(f"{tot['trees']} C-built BVHs x {a.rays} rays: Lean traversal == C scalar on all; "
          f"checkWF true on all with LRT_TRI_LEAF_BOX_EXACT (false on {tot['wf_plain_fail']} without); "
          f"{tot['brute']} rays differ from brute force ({tot['miss']} hit/miss, rest <= few-ulp t)")
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
