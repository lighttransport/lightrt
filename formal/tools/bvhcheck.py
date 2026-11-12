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
    ap.add_argument("--only-patho", action="store_true", help="run only the pathological scenes")
    a = ap.parse_args()
    tmp = tempfile.mkdtemp()
    exe = {}
    variants = (("plain", ["-DLRT_TRI_NO_SLAB_ROBUST", "-DLRT_TRI_NO_LEAF_BOX_EXACT", "-DLRT_TRI_NO_BITEXACT"]),
                ("exact", ["-DLRT_TRI_NO_SLAB_ROBUST", "-DLRT_TRI_LEAF_BOX_EXACT", "-DLRT_TRI_NO_BITEXACT"]),
                ("robust", ["-DLRT_TRI_LEAF_BOX_EXACT", "-DLRT_TRI_SLAB_ROBUST", "-DLRT_TRI_BITEXACT"]),
                ("exactn", ["-DLRT_TRI_LEAF_BOX_EXACT", "-DLRT_TRI_SLAB_ROBUST", "-DLRT_TRI_BITEXACT",
                            "-DLRT_TRI_EXACT_NEAREST"]))
    for name, flags in variants:
        exe[name] = os.path.join(tmp, "bvhdump_" + name)
        subprocess.check_call(["cc", "-O1", "-ffp-contract=off", "-msse4.1", "-mavx2", "-mfma",
                               "-w", "-I" + ROOT, *flags, "-o", exe[name],
                               os.path.join(HERE, "bvhdump.c"), "-lm", "-lpthread"])
    subprocess.check_call(["lake", "build", "checkbvh"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    chk = os.path.join(FORMAL, ".lake", "build", "bin", "checkbvh")
    # (ntris, quality, layout, scene): LBVH/SAH x BVH4/BVH8 x soup/heightfield
    cfgs = [(400, 0, 4, 0), (500, 1, 4, 0), (1000, 1, 4, 1), (800, 0, 8, 1), (800, 1, 8, 0)]
    hq = [(600, 2, 4, 1), (600, 2, 4, 0)]
    # pathological scenes: all vertices identical (2), coplanar overlap (3)
    patho = [(2000, 1, 4, 2), (2000, 1, 8, 2), (500, 1, 4, 3), (500, 0, 8, 3)]
    cfgs = patho if a.only_patho else cfgs + patho
    if a.only_patho:
        hq = []  # SBVH: clipped boxes, coverage (run_cover) not WF
    bad = 0
    tot = {"rays": 0, "brute": 0, "miss": 0, "wf_plain_fail": 0, "trees": 0,
           "rob_miss": 0, "rob_brute": 0, "rob_simd": 0, "hq": 0}
    for seed in range(1, a.seeds + 1):
        for (n, q, w, g) in cfgs + hq:
            for name in ("plain", "exact", "robust", "exactn"):
                if (n, q, w, g) in hq and name not in ("plain", "robust"):
                    continue
                dump = subprocess.run([exe[name], str(seed), str(n), str(a.rays), str(q), str(w), str(g)],
                                      check=True, capture_output=True).stdout
                out = subprocess.run([chk], input=dump, check=True, capture_output=True).stdout.decode()
                m = dict(re.findall(r"([\w/\-\(\)=]+?)=(\w+)", out.replace("\n", " ")))
                wf = "checkWF=true" in out
                rays = int(re.search(r"rays=(\d+)", out).group(1))
                same = int(re.search(r"lean==C-scalar\(t,prim\)=(\d+)", out).group(1))
                brute = int(re.search(r"t==brute=(\d+)", out).group(1))
                miss = int(re.search(r" hit/miss-vs-brute=(\d+)", out).group(1))
                smiss = int(re.search(r"dispatched-hit/miss-vs-brute=(\d+)", out).group(1))
                if same != rays:
                    print(f"FAIL seed={seed} cfg={(n,q,w,g)} {name}: Lean mirror != C on {rays-same} rays")
                    bad += 1
                full = int(re.search(r"\(t,prim\)==C-dispatched=(\d+)", out).group(1))
                aC, aD, aB, unc = map(int, re.search(
                    r"anyhit lean==C-scalar=(\d+) lean==C-dispatched=(\d+) lean==brute=(\d+) uncovered-hits=(\d+)", out).groups())
                if aC != rays:
                    print(f"FAIL seed={seed} cfg={(n,q,w,g)} {name}: any-hit Lean runAny != C scalar on {rays-aC} rays")
                    bad += 1
                need = int(re.search(r"stack need=(\d+)", out).group(1))
                tot["need"] = max(tot.get("need", 0), need)
                if need > 1024:
                    print(f"FAIL seed={seed} cfg={(n,q,w,g)} {name}: stack need {need} > TRI_STACK_SIZE")
                    bad += 1
                key = ("hq_" + name) if (n, q, w, g) in hq else name
                st = tot.setdefault("any_" + key, [0, 0, 0, 0])
                st[0] += rays; st[1] += rays - aD; st[2] += rays - aB; st[3] += unc
                if name in ("robust", "exactn") and (aB != rays or aD != rays or unc):
                    print(f"FAIL seed={seed} cfg={(n,q,w,g)} {name}: any-hit vs brute {rays-aB}, "
                          f"vs SIMD {rays-aD}, uncovered hits {unc}")
                    bad += 1
                if (n, q, w, g) in hq:
                    tot["hq"] += 1
                    continue
                if name == "exactn":
                    tot["exn"] = tot.get("exn", 0) + 1
                    if brute != rays or full != rays or not wf:
                        print(f"FAIL seed={seed} cfg={(n,q,w,g)}: exact-nearest != brute on {rays-brute} rays "
                              f"(SIMD!=scalar {rays-full}, wf={wf})")
                        bad += 1
                    continue
                if name == "robust":
                    tot["rob_miss"] += miss; tot["rob_brute"] += rays - brute
                    if full != rays:
                        print(f"FAIL seed={seed} cfg={(n,q,w,g)}: SIMD != scalar on {rays-full} rays under LRT_TRI_BITEXACT")
                        bad += 1
                    if not wf:
                        print(f"FAIL seed={seed} cfg={(n,q,w,g)}: checkWF false (robust)"); bad += 1
                if name == "exact":
                    tot["trees"] += 1; tot["rays"] += rays
                    tot["brute"] += rays - brute; tot["miss"] += miss; tot["smiss"] = tot.get("smiss", 0) + smiss
                    if not wf:
                        print(f"FAIL seed={seed} cfg={(n,q,w,g)}: checkWF false with LRT_TRI_LEAF_BOX_EXACT")
                        bad += 1
                elif not wf:
                    tot["wf_plain_fail"] += 1
    print(f"{tot['trees']} C-built BVHs x {a.rays} rays: Lean traversal == C scalar on all; "
          f"checkWF true on all with LRT_TRI_LEAF_BOX_EXACT (false on {tot['wf_plain_fail']} without); "
          f"{tot['brute']} rays differ from brute force ({tot['miss']} hit/miss, rest <= few-ulp t; SIMD path {tot.get('smiss', 0)} hit/miss); "
          f"robust+bitexact: SIMD == scalar (t,prim) on all, {tot['rob_brute']} differ from brute ({tot['rob_miss']} hit/miss); "
          f"{tot['hq']} SBVH trees: Lean traversal == C scalar; "
          f"exact-nearest: t == brute force (and SIMD == scalar) on all rays of {tot.get('exn', 0)} trees")
    print(f"stack: max need over all trees {tot.get('need', 0)} <= TRI_STACK_SIZE 1024 (runAnyB_root hypothesis)")
    for k in ("plain", "exact", "robust", "exactn", "hq_plain", "hq_robust"):
        if "any_" + k in tot:
            r_, d_, b_, u_ = tot["any_" + k]
            print(f"any-hit [{k}]: {r_} rays, Lean runAny == C scalar on all; != SIMD {d_}, != brute {b_}, "
                  f"hits without a covering box path {u_}")
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
