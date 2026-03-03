# LightRT CLI Renderer

## Overview

The LightRT CLI renderer provides command-line interface for rendering USD scenes using the LightRT BVH library.

## Usage

### Basic Rendering

```bash
# Basic render with default options
lightrt_cli input.usd -o output.png -w 800 -h 600

# With timecode and camera selection
lightrt_cli input.usd -t 1.5 --camera cam_001
```

### AOV Rendering

```bash
# Render all passes
lightrt_cli input.usd --aov beauty,geom_normal,shading_normal,depth

# Just depth pass
lightrt_cli input.usd --aov depth

# Geometry and shading normals
lightrt_cli input.usd --aov geom_normal,shading_normal
```

### Command Line Options

| Option | Description |
|--------|-------------|
| `-o <file>` | Output file (default: output.png) |
| `-w <width>` | Image width (default: 800) |
| `-h <height>` | Image height (default: 600) |
| `-t <timecode>` | Timecode for rendering |
| `--camera <name>` | Camera name or index |
| `--mblur-samples <N>` | Motion blur samples |
| `--spp <N>` | Samples per pixel |
| `--envmap <file>` | Environment map file |
| `--aov <outputs>` | AOV output specification |

## AOV Render Options

| Output | Description |
|--------|-------------|
| `beauty` | Standard color output (final render) |
| `geom_normal` | Geometry normals (pre-transformation) |
| `shading_normal` | Normals after transformation (curved surfaces) |
| `vertex_color` | Vertex `displayColor` from USD |
| `vertex_opacity` | Vertex `displayOpacity` from USD |
| `depth` | Distance to hit point |
| `material_id` | Per-triangle material identifier |

## Examples

### Render with AOV Outputs

```bash
# Beauty + depth
lightrt_cli scene.usd --aov beauty,depth

# All passes
lightrt_cli scene.usd --aov beauty,geom_normal,shading_normal,vertex_color,vertex_opacity,depth,material_id
```

### Render with Time Range

```bash
# Time range with step
lightrt_cli scene.usd --time-range 0 10 1
```

### Render with Camera Selection

```bash
# By name
lightrt_cli scene.usd --camera cam_001

# By index
lightrt_cli scene.usd --camera 0
```

## Building

```bash
# Build with CMake
mkdir build && cd build
cmake ..
make

# Or use Makefile
make
```

## Output Files

When using AOV rendering, separate output files are created:
- `beauty.png` - Standard beauty render
- `depth.png` - Depth values
- `geom_normal.png` - Geometry normals
- etc.

Or use `--aov-output-file` to specify custom output filename.

## Troubleshooting

### Camera Issues

If camera transforms are incorrect, ensure you're using the same row-major convention as the USD file.

### Lighting Issues

For SphereLight, verify that area light sampling is enabled (`--mblur-samples > 1`).

### Geometry Issues

For Z-up/Y-up scenes, ensure the default camera up vector is set correctly based on scene coordinate system.

## Documentation

- [AOV Rendering](./AOV_RENDERING.md) - AOV rendering documentation
- [Advanced Features](./ADVANCED_FEATURES.md) - SBVH, AutoTuner, MMapBVH
- [Spatial Queries](./SPATIAL_QUERIES.md) - Spatial queries test integration
- [Collision Detection](./COLLISION_DETECTION.md) - Collision detection examples
- [Heatmap Writer](./HEATMAP_WRITER.md) - Heatmap writer usage

