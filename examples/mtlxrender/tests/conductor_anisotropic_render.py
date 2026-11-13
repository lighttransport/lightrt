#!/usr/bin/env python3
"""Render a directional light against rotated anisotropic conductor tangents."""
import os
from pathlib import Path
import subprocess
import tempfile
from viewdirection_render import OBJ, center_rgb


def material(tangent):
    return f'''<materialx version="1.39">
<conductor_bsdf name="c" type="BSDF">
  <input name="roughness" type="vector2" value="0.1,0.6"/>
  <input name="tangent" type="vector3" value="{tangent}"/>
</conductor_bsdf>
<surface name="s" type="surfaceshader"><input name="bsdf" type="BSDF" nodename="c"/></surface>
<surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s"/></surfacematerial>
</materialx>'''


def main():
    binary = Path(os.environ.get("MTLXRENDER_BINARY", Path(__file__).resolve().parent.parent / "mtlxrender"))
    with tempfile.TemporaryDirectory(prefix="mtlx-anisotropy-") as tmp:
        root = Path(tmp)
        (root / "plane.obj").write_text(OBJ)
        for backend in ("cpu", "cpu-wavefront"):
            values = []
            for tangent in ("1,0,0", "0,1,0"):
                (root / "material.mtlx").write_text(material(tangent))
                subprocess.run([str(binary), "--obj", str(root / "plane.obj"),
                    "--mtlx", str(root / "material.mtlx"), "--w", "16", "--h", "16",
                    "--spp", "1", "--bounces", "1", "--threads", "1",
                    "--cam-eye", "0,0,5", "--cam-target", "0,0,0", "--hide-env",
                    "--env-intensity", "0", "--sun", "--sun-az", "45", "--sun-el", "0",
                    "--sun-intensity", "2", "--backend", backend,
                    "--out", str(root / "frame.exr"), "--srgb", str(root / "frame.png")],
                    check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                values.append(center_rgb(root / "frame.png"))
            if values[1][0] - values[0][0] < 40:
                raise AssertionError(f"{backend}: tangent rotation did not change response: {values}")
    print("PASS: tangent rotation changes anisotropic conductor render on both CPU integrators")


if __name__ == "__main__":
    main()
