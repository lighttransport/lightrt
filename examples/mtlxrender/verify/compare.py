#!/usr/bin/env python3
"""compare.py - quantitative image agreement for the MaterialX verify harness.

Compares a candidate render (lightrt mtlxrender) against one or more reference
renders (ASF MaterialX GLSL / OSL). Both are plain-sRGB PNGs of the SAME mesh /
camera / env, so the only differences are the shading + integrator.

Because two different renderers never agree on absolute brightness (different
exposure conventions, tonemap-free vs not, sample budgets), we:
  1. Build a foreground mask (pixels that differ from the black background in
     either image) so the background doesn't dominate the metric.
  2. Solve a single least-squares scalar exposure `s` minimizing
     |s*candidate - reference| over the foreground (in linear light), apply it.
  3. Report RMSE (full frame) and masked-RMSE (foreground only), both in sRGB
     [0,1], plus the fitted exposure. masked-RMSE is the headline number.
A side-by-side + 5x-amplified difference contact sheet is written for eyeballing.

Usage:
  compare.py --candidate cand.png --ref ref.png [--ref ref2.png ...] \
             --labels lightrt,ASF-GLSL[,ASF-OSL] --out-sheet sheet.png [--json]
Exit code is always 0 (this is a measurement tool, not a gate); the harness
decides pass/fail from the numbers.
"""
import argparse
import json
import sys

import numpy as np

try:
    import imageio.v2 as imageio
except Exception:  # pragma: no cover
    import imageio


def load_srgb(path):
    """Load an 8-bit (or float) PNG as float sRGB in [0,1], RGB only."""
    img = imageio.imread(path)
    img = np.asarray(img, dtype=np.float64)
    if img.ndim == 2:
        img = np.stack([img] * 3, axis=-1)
    if img.shape[-1] == 4:
        img = img[..., :3]
    if img.max() > 1.0:
        img /= 255.0
    return img


def srgb_to_linear(c):
    a = 0.055
    return np.where(c <= 0.04045, c / 12.92, ((c + a) / (1 + a)) ** 2.4)


def linear_to_srgb(c):
    a = 0.055
    c = np.clip(c, 0.0, 1.0)
    return np.where(c <= 0.0031308, c * 12.92, (1 + a) * np.power(c, 1 / 2.4) - a)


def foreground_mask(a, b, thresh=0.02):
    """Pixels that are non-background (differ from black) in either image."""
    la = a.mean(axis=-1)
    lb = b.mean(axis=-1)
    return (la > thresh) | (lb > thresh)


def disk_mask(h, w, frac):
    """Analytic centered disk of radius `frac * min(h,w)`. Both renderers center
    the sphere at the image center with a geometrically-known projected radius,
    so this isolates exactly the sphere pixels regardless of background or dark
    (unlit) shading -- more robust than a luminance threshold."""
    cy, cx = (h - 1) / 2.0, (w - 1) / 2.0
    r = frac * min(h, w)
    ys, xs = np.ogrid[0:h, 0:w]
    return ((ys - cy) ** 2 + (xs - cx) ** 2) <= r * r


def fit_exposure(cand_lin, ref_lin, mask):
    """Least-squares scalar s minimizing |s*cand - ref| over masked pixels."""
    c = cand_lin[mask].reshape(-1)
    r = ref_lin[mask].reshape(-1)
    denom = float(np.dot(c, c))
    if denom < 1e-12:
        return 1.0
    s = float(np.dot(c, r) / denom)
    return max(1e-4, min(1e4, s))


def rmse(a, b, mask=None):
    d = (a - b) ** 2
    if mask is not None:
        m = np.broadcast_to(mask[..., None], d.shape)
        d = d[m]
    return float(np.sqrt(d.mean())) if d.size else float("nan")


def resize_nn(img, h, w):
    """Nearest-neighbor resize to (h,w) -- only used to reconcile a resolution
    mismatch between candidate and reference (the harness renders them equal, so
    this is a safety net, not the normal path)."""
    if img.shape[0] == h and img.shape[1] == w:
        return img
    yi = (np.arange(h) * (img.shape[0] / h)).astype(int).clip(0, img.shape[0] - 1)
    xi = (np.arange(w) * (img.shape[1] / w)).astype(int).clip(0, img.shape[1] - 1)
    return img[yi][:, xi]


def compare_one(cand, ref, disk_frac=None):
    """Return (metrics dict, exposure-matched candidate in sRGB) for a ref."""
    h = min(cand.shape[0], ref.shape[0])
    w = min(cand.shape[1], ref.shape[1])
    c = resize_nn(cand, h, w)
    r = resize_nn(ref, h, w)
    mask = disk_mask(h, w, disk_frac) if disk_frac else foreground_mask(c, r)
    c_lin = srgb_to_linear(c)
    r_lin = srgb_to_linear(r)
    s = fit_exposure(c_lin, r_lin, mask) if mask.any() else 1.0
    c_adj = linear_to_srgb(c_lin * s)
    metrics = {
        "exposure": s,
        "rmse": rmse(c_adj, r),
        "masked_rmse": rmse(c_adj, r, mask),
        "fg_frac": float(mask.mean()),
    }
    return metrics, c_adj, r, mask


def make_sheet(path, tiles, labels):
    """Horizontal contact sheet: candidate | ref | 5x|diff| per reference."""
    try:
        from PIL import Image, ImageDraw  # optional, nicer labels
        have_pil = True
    except Exception:
        have_pil = False
    pad = 4
    h = max(t.shape[0] for t in tiles)
    w = sum(t.shape[1] for t in tiles) + pad * (len(tiles) - 1)
    sheet = np.ones((h, w, 3), dtype=np.float64)
    x = 0
    for t in tiles:
        sheet[: t.shape[0], x : x + t.shape[1]] = t
        x += t.shape[1] + pad
    out = (np.clip(sheet, 0, 1) * 255 + 0.5).astype(np.uint8)
    if have_pil:
        im = Image.fromarray(out)
        d = ImageDraw.Draw(im)
        xx = 0
        for t, lab in zip(tiles, labels):
            d.text((xx + 4, 4), lab, fill=(255, 80, 80))
            xx += t.shape[1] + pad
        im.save(path)
    else:
        imageio.imwrite(path, out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidate", required=True)
    ap.add_argument("--ref", action="append", required=True)
    ap.add_argument("--labels", default="")
    ap.add_argument("--out-sheet", default=None)
    ap.add_argument("--disk-frac", type=float, default=None,
                    help="mask to a centered disk of this radius (fraction of "
                         "min(h,w)); isolates the sphere robustly. If omitted, a "
                         "luminance foreground mask is used.")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    labels = args.labels.split(",") if args.labels else (
        ["candidate"] + [f"ref{i}" for i in range(len(args.ref))]
    )
    cand = load_srgb(args.candidate)

    results = {}
    sheet_tiles = [cand]
    sheet_labels = [labels[0] if labels else "candidate"]
    for i, refpath in enumerate(args.ref):
        ref = load_srgb(refpath)
        m, c_adj, r_crop, mask = compare_one(cand, ref, args.disk_frac)
        rlabel = labels[i + 1] if len(labels) > i + 1 else f"ref{i}"
        results[rlabel] = m
        diff = np.clip(np.abs(c_adj - r_crop) * 5.0, 0, 1)
        sheet_tiles.extend([r_crop, diff])
        sheet_labels.extend([rlabel, f"5x|{labels[0]}-{rlabel}|"])

    if args.out_sheet:
        make_sheet(args.out_sheet, sheet_tiles, sheet_labels)

    if args.json:
        print(json.dumps(results))
    else:
        for rlabel, m in results.items():
            print("%-12s exposure=%.3f  rmse=%.4f  masked_rmse=%.4f  fg=%.1f%%"
                  % (rlabel, m["exposure"], m["rmse"], m["masked_rmse"],
                     100 * m["fg_frac"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
