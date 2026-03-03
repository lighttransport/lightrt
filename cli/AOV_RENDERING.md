# AOV Rendering Support

## Overview

AOV (Arbitrary Output Variable) rendering extends the LightRT CLI renderer with multiple render passes beyond the standard beauty output. This allows for specialized rendering tasks like:

- **Beauty** - Standard color output (final render)
- **Geom Normal** - Geometry normals (pre-transformation)
- **Shading Normal** - Normals after transformation (for curved surfaces)
- **Vertex Color** - Vertex `displayColor` from USD
- **Vertex Opacity** - Vertex `displayOpacity` from USD
- **Depth** - Distance to hit point
- **Material ID** - Per-triangle material identifier

## Usage

```bash
lightrt_cli input.usd --aov beauty,geom_normal,shading_normal,vertex_color,vertex_opacity,depth,material_id
```

Or render specific passes:

```bash
# Just depth pass
lightrt_cli input.usd --aov depth

# Multiple passes
lightrt_cli input.usd --aov geom_normal,shading_normal,depth
```

## Implementation Details

The AOV rendering is implemented through:

1. **Header** (`cli/aov_rendering.hh`) - AOV rendering structures
2. **Implementation** (`cli/aov_rendering.cc`) - Core rendering functions
3. **CLI Integration** (`cli/main.cc`) - Command line parsing and rendering loop

## AOV Render Options

```cpp
struct AOVRenderOptions {
  bool beauty = true;           // Standard color output
  bool geom_normal = false;     // Geometry normals
  bool shading_normal = false;  // Normals after transformation
  bool vertex_color = false;    // Vertex displayColor
  bool vertex_opacity = false;  // Vertex displayOpacity
  bool depth = false;           // Distance to hit point
  bool material_id = false;     // Per-triangle material ID
};
```

## Example Usage

```bash
# Render all passes
lightrt_cli scene.usd --aov beauty,geom_normal,shading_normal,vertex_color,vertex_opacity,depth,material_id

# Just depth
lightrt_cli scene.usd --aov depth

# Geometry normals only
lightrt_cli scene.usd --aov geom_normal
```

## Output Files

When multiple AOV outputs are requested, separate output files are created:
- `beauty.png` - Standard beauty render
- `geom_normal.png` - Geometry normals
- `depth.png` - Depth values
- etc.

Or use `--aov-output-file` to specify custom output filename.

