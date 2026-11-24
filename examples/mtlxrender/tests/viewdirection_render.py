#!/usr/bin/env python3
"""Exercise viewdirection through both standalone CPU path tracers."""
import os
import pathlib
import struct
import subprocess
import sys
import tempfile
import zlib

OBJ = """v -2 -2 0
v 2 -2 0
v 2 2 0
v -2 2 0
vn 0 0 1
f 1//1 2//1 3//1
f 1//1 3//1 4//1
"""
MTLX = """<materialx version="1.39">
<viewdirection name="v" type="vector3"/>
<surface_unlit name="s" type="surfaceshader"><input name="emission" type="float" value="1"/><input name="emission_color" type="color3" nodename="v"/></surface_unlit>
<surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s"/></surfacematerial>
</materialx>"""

def center_rgb(path):
    data = path.read_bytes()
    if data[:8] != b"\x89PNG\r\n\x1a\n":
        raise ValueError("invalid PNG")
    pos, packed = 8, bytearray()
    while pos < len(data):
        size = struct.unpack_from(">I", data, pos)[0]
        tag, chunk = data[pos+4:pos+8], data[pos+8:pos+8+size]
        pos += size + 12
        if tag == b"IHDR":
            w, h, bits, color, comp, filt, interlace = struct.unpack(">IIBBBBB", chunk)
            if (bits, color, comp, filt, interlace) != (8, 2, 0, 0, 0):
                raise ValueError("unexpected PNG format")
        elif tag == b"IDAT":
            packed.extend(chunk)
        elif tag == b"IEND":
            break
    raw = zlib.decompress(packed)
    stride, previous = w * 3, bytearray(w * 3)
    for row_index in range(h):
        offset = row_index * (stride + 1)
        mode, row = raw[offset], bytearray(raw[offset+1:offset+1+stride])
        for i in range(stride):
            left = row[i-3] if i >= 3 else 0
            up = previous[i]
            upper_left = previous[i-3] if i >= 3 else 0
            if mode == 0: predictor = 0
            elif mode == 1: predictor = left
            elif mode == 2: predictor = up
            elif mode == 3: predictor = (left + up) // 2
            elif mode == 4:
                p = left + up - upper_left
                distances = (abs(p-left), abs(p-up), abs(p-upper_left))
                predictor = (left, up, upper_left)[distances.index(min(distances))]
            else: raise ValueError("invalid PNG filter")
            row[i] = (row[i] + predictor) & 255
        if row_index == h // 2:
            return tuple(row[(w//2)*3:(w//2)*3+3])
        previous = row
    raise ValueError("missing center row")

def main():
    binary = pathlib.Path(os.environ.get("MTLXRENDER_BINARY",
        pathlib.Path(__file__).resolve().parent.parent / "mtlxrender"))
    with tempfile.TemporaryDirectory(prefix="mtlx-view-") as tmp:
        root = pathlib.Path(tmp)
        (root / "plane.obj").write_text(OBJ)
        (root / "view.mtlx").write_text(MTLX)
        for backend in (sys.argv[1:] or ("cpu", "cpu-wavefront")):
            for camera, min_red in (("0,0,5", 0), ("5,0,5", 100)):
                subprocess.run([str(binary), "--obj", str(root / "plane.obj"),
                    "--mtlx", str(root / "view.mtlx"), "--w", "16", "--h", "16",
                    "--spp", "1", "--bounces", "1", "--threads", "1",
                    "--cam-eye", camera, "--cam-target", "0,0,0", "--hide-env",
                    "--backend", backend, "--out", str(root / "frame.exr"),
                    "--srgb", str(root / "frame.png")], check=True,
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                red, _, blue = center_rgb(root / "frame.png")
                if blue < 160 or red < min_red:
                    raise AssertionError(f"{backend} view {camera}: RGB={red},_,{blue}")
    print("PASS: viewdirection drives both CPU integrators")

if __name__ == "__main__":
    main()
