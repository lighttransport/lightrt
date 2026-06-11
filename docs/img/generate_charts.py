import os

PALETTE = {"c11": "#2f7ed8", "c11b": "#6aa5e6", "c11c": "#a3c6ef",
           "embree": "#d84b2f", "tinybvh": "#39a05a", "mm-bvh": "#8e6cc0",
           "cb": "#9aa0a6", "hair": "#e0a800"}

def bar_chart(path, title, ylabel, groups, series, log=False, width=860, height=420):
    """groups: list of group labels. series: list of (name, color, [values or None])."""
    import math
    L, R, T, B = 70, 20, 48, 64
    pw, ph = width - L - R, height - T - B
    vals = [v for _, _, vs in series for v in vs if v is not None]
    vmax = max(vals)
    if log:
        vmin = min(v for v in vals if v > 0)
        lo = math.floor(math.log10(vmin)); hi = math.ceil(math.log10(vmax))
        def ybar(v): return ph * (math.log10(v) - lo) / (hi - lo)
        ticks = [10 ** e for e in range(lo, hi + 1)]
    else:
        lo = 0
        def ybar(v): return ph * v / (vmax * 1.08)
        step = 10 ** math.floor(math.log10(vmax)) 
        if vmax / step > 6: step *= 2
        if vmax / step < 3: step /= 2
        ticks, t = [], 0
        while t <= vmax * 1.08:
            ticks.append(t); t += step
    s = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
         f'font-family="sans-serif" font-size="12">',
         f'<rect width="{width}" height="{height}" fill="white"/>',
         f'<text x="{width/2}" y="22" text-anchor="middle" font-size="15" font-weight="bold">{title}</text>']
    for t in ticks:
        y = T + ph - ybar(t) if (not log or t > 0) else T + ph
        if log and t <= 0: continue
        lab = f"{t:g}"
        s.append(f'<line x1="{L}" y1="{y:.1f}" x2="{width-R}" y2="{y:.1f}" stroke="#e3e3e3"/>')
        s.append(f'<text x="{L-6}" y="{y+4:.1f}" text-anchor="end" fill="#555">{lab}</text>')
    s.append(f'<text x="16" y="{T+ph/2}" text-anchor="middle" fill="#333" '
             f'transform="rotate(-90 16 {T+ph/2})">{ylabel}</text>')
    ng, ns = len(groups), len(series)
    gw = pw / ng
    bw = gw * 0.8 / ns
    for gi, g in enumerate(groups):
        gx = L + gi * gw
        s.append(f'<text x="{gx+gw/2:.1f}" y="{T+ph+18}" text-anchor="middle" fill="#333">{g}</text>')
        for si, (name, color, vs) in enumerate(series):
            v = vs[gi]
            if v is None: continue
            h = ybar(v)
            x = gx + gw * 0.1 + si * bw
            y = T + ph - h
            s.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{bw*0.92:.1f}" height="{h:.1f}" fill="{color}"/>')
            lab = f"{v:g}"
            s.append(f'<text x="{x+bw*0.46:.1f}" y="{y-4:.1f}" text-anchor="middle" '
                     f'font-size="10" fill="#333">{lab}</text>')
    lx = L
    for name, color, _ in series:
        s.append(f'<rect x="{lx}" y="{height-26}" width="12" height="12" fill="{color}"/>')
        s.append(f'<text x="{lx+16}" y="{height-16}" fill="#333">{name}</text>')
        lx += 16 + 7 * len(name) + 26
    s.append('</svg>')
    open(path, 'w').write('\n'.join(s))
    print(path)

D = "docs/img"

# 1. Single-thread, 128k tris (latest verified run)
bar_chart(f"{D}/st_128k.svg",
    "Mandelbulb 127,752 tris — single thread (Mrays/s, higher is better)",
    "Mrays/s",
    ["primary", "incoherent", "shadow"],
    [("c11-bvh4", PALETTE["c11"],     [22.6, 2.93, 4.14]),
     ("c11-bvh8q", PALETTE["c11c"],   [15.8, 2.92, 3.92]),
     ("embree", PALETTE["embree"],    [20.5, 3.48, 5.43]),
     ("tinybvh", PALETTE["tinybvh"],  [18.6, 2.49, 4.56]),
     ("mm-bvh", PALETTE["mm-bvh"],    [14.4, 1.21, 1.90])])

# 2. 16 threads, 710k tris
bar_chart(f"{D}/mt_710k.svg",
    "Mandelbulb 710,536 tris — 16 threads (Mrays/s)",
    "Mrays/s",
    ["incoherent", "shadow"],
    [("c11-bvh4", PALETTE["c11"],    [22.3, 43.4]),
     ("c11-bvh8", PALETTE["c11b"],   [20.5, 47.4]),
     ("embree", PALETTE["embree"],   [16.0, 44.6]),
     ("tinybvh", PALETTE["tinybvh"], [13.3, 41.8]),
     ("mm-bvh", PALETTE["mm-bvh"],   [9.0, 16.6])])

# 3. Build throughput
bar_chart(f"{D}/build.svg",
    "BVH build throughput, 710k tris (Mtris/s)",
    "Mtris/s",
    ["serial", "16 threads"],
    [("c11 SAH", PALETTE["c11"],    [1.4, 3.9]),
     ("c11 LBVH", PALETTE["c11b"],  [7.3, 8.85]),
     ("embree (TBB)", PALETTE["embree"], [2.3, 8.66]),
     ("tinybvh BVH8_CPU", PALETTE["tinybvh"], [2.4, 1.38]),
     ("mm-bvh HQ", PALETTE["mm-bvh"], [1.2, 2.38])])

# 4. Optimization progression, ST incoherent @710k
bar_chart(f"{D}/progression.svg",
    "Optimization progression — 710k tris, single-thread incoherent (Mrays/s)",
    "Mrays/s",
    ["fp64 callback\n(baseline)", "wide BVH\n+SIMD", "+block SAH\n+leaf60", "+huge pages", "+8-way ray\npipelining"],
    [("c11", PALETTE["c11"], [0.46, 1.30, 1.34, 1.41, 2.25]),
     ("embree (ref)", PALETTE["embree"], [None, None, None, None, 1.69])])

# 5. Hair scene (log scale)
bar_chart(f"{D}/hair.svg",
    "Hair scene: 100k corner-to-corner thin hairs — primary rays (Mrays/s, log scale)",
    "Mrays/s (log)",
    ["triangle BVH\n(embree/tinybvh)", "object SAH\n(c11-bvh4)", "spatial splits\n(c11-sbvh4)", "capsule primitive\n(c11-hair)"],
    [("throughput", PALETTE["hair"], [0.006, 0.011, 0.017, 0.259])],
    log=True)
