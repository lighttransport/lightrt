#!/usr/bin/env python3
import argparse
import json
from pathlib import Path


def read_rgba(path: Path, width: int, height: int) -> bytes:
    data = path.read_bytes()
    expected = width * height * 4
    if len(data) != expected:
        raise ValueError(
            f"{path}: expected {expected} bytes for {width}x{height} RGBA, got {len(data)}"
        )
    return data


def write_diff_ppm(path: Path, width: int, height: int, diff: bytes) -> None:
    # Visualize absolute RGB diff directly.
    with path.open("wb") as f:
        f.write(f"P6\n{width} {height}\n255\n".encode("ascii"))
        for i in range(0, len(diff), 4):
            f.write(diff[i : i + 3])


def main() -> int:
    ap = argparse.ArgumentParser(description="Pixel-wise RGBA comparison")
    ap.add_argument("--a", required=True, help="Reference RGBA file")
    ap.add_argument("--b", required=True, help="Candidate RGBA file")
    ap.add_argument("--width", type=int, required=True)
    ap.add_argument("--height", type=int, required=True)
    ap.add_argument(
        "--pixel-threshold",
        type=int,
        default=2,
        help="Per-channel abs diff threshold for marking a mismatched pixel",
    )
    ap.add_argument(
        "--max-mismatch-ratio",
        type=float,
        default=0.02,
        help="Allowed mismatch ratio (0..1)",
    )
    ap.add_argument(
        "--max-mean-abs-error",
        type=float,
        default=1.0,
        help="Allowed mean absolute error over all RGBA channels",
    )
    ap.add_argument("--summary-json", default="", help="Optional JSON summary output")
    ap.add_argument("--diff-ppm", default="", help="Optional PPM diff visualization")
    args = ap.parse_args()

    a_path = Path(args.a)
    b_path = Path(args.b)
    width = args.width
    height = args.height
    if width <= 0 or height <= 0:
        raise SystemExit("width and height must be > 0")

    a = read_rgba(a_path, width, height)
    b = read_rgba(b_path, width, height)

    num_pixels = width * height
    total_channels = num_pixels * 4

    mismatched = 0
    sum_abs = 0
    max_abs = 0
    diff_bytes = bytearray(len(a))

    for px in range(num_pixels):
        base = px * 4
        dr = abs(a[base + 0] - b[base + 0])
        dg = abs(a[base + 1] - b[base + 1])
        db = abs(a[base + 2] - b[base + 2])
        da = abs(a[base + 3] - b[base + 3])
        diff_bytes[base + 0] = dr
        diff_bytes[base + 1] = dg
        diff_bytes[base + 2] = db
        diff_bytes[base + 3] = da

        local_max = max(dr, dg, db, da)
        if local_max > args.pixel_threshold:
            mismatched += 1

        sum_abs += dr + dg + db + da
        if local_max > max_abs:
            max_abs = local_max

    mismatch_ratio = mismatched / float(num_pixels)
    mean_abs_error = sum_abs / float(total_channels)

    summary = {
        "a": str(a_path),
        "b": str(b_path),
        "width": width,
        "height": height,
        "pixel_threshold": args.pixel_threshold,
        "max_mismatch_ratio": args.max_mismatch_ratio,
        "max_mean_abs_error": args.max_mean_abs_error,
        "mismatched_pixels": mismatched,
        "num_pixels": num_pixels,
        "mismatch_ratio": mismatch_ratio,
        "mean_abs_error": mean_abs_error,
        "max_abs_error": max_abs,
    }

    if args.summary_json:
        Path(args.summary_json).write_text(json.dumps(summary, indent=2) + "\n")

    if args.diff_ppm:
        write_diff_ppm(Path(args.diff_ppm), width, height, bytes(diff_bytes))

    print(json.dumps(summary, indent=2))

    ok = (
        mismatch_ratio <= args.max_mismatch_ratio
        and mean_abs_error <= args.max_mean_abs_error
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

