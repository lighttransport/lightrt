from pathlib import Path
from setuptools import Extension, setup

ROOT = Path(__file__).resolve().parents[2]

setup(
    packages=["lightrt_c"],
    ext_modules=[
        Extension(
            "lightrt_c._lightrt_c",
            sources=[
                "src/lightrt_c_py.c",
                str(ROOT / "lightrt_c.c"),
            ],
            include_dirs=[str(ROOT)],
            extra_compile_args=["-std=c11", "-O3"],
        )
    ],
)

