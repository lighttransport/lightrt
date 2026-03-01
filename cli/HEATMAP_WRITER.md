# Heatmap Writer Usage

## Overview

HeatmapWriter provides zero-dependency image writer for BVH traversal visualization with multiple colormaps and metrics.

## Usage Example

### Render Image with Profiling

```cpp
// Render image and collect per-pixel profile data
TraversalProfile* profiles = renderImageProfiled(
    bvh, width, height,
    camera_pos, camera_dir, camera_up, fov_y);

// Write heatmap
HeatmapWriter::writeHeatmap("nodes.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Viridis);
```

### Available Metrics

| Metric | Description |
|--------|-------------|
| `NodesVisited` | Nodes visited per ray |
| `LeafVisits` | Leaf nodes visited |
| `PrimsTested` | Primitive tests per ray |
| `MaxDepth` | Traversal depth |

### Colormaps

```cpp
// Grayscale: Black to white
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Grayscale);

// Heat: Black → Red → Yellow → White
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::PrimsTested,
                             Colormap::Heat);

// Jet: Blue → Cyan → Green → Yellow → Red
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::MaxDepth,
                             Colormap::Jet);

// Viridis: Purple → Blue → Green → Yellow
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::MaxDepth,
                             Colormap::Viridis);

// Turbo: Google's improved rainbow
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Turbo);

// Plasma: Purple → Pink → Orange → Yellow
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Plasma);

// Inferno: Black → Purple → Red → Yellow
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Inferno);

// Cool: Cyan to Magenta
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Cool);

// Hot: Black → Red → Yellow → White (classic)
HeatmapWriter::writeHeatmap("out.bmp", profiles, width, height,
                             HeatmapWriter::Metric::NodesVisited,
                             Colormap::Hot);
```

## Direct Colormap API

```cpp
// Write image with float data
HeatmapWriter::writeImage("out.bmp", float_data, width, height,
                          Colormap::Plasma);

// Write image with uint data
HeatmapWriter::writeImage("out.bmp", uint_data, width, height,
                          max_value, Colormap::Hot);
```

## Image Formats

- **BMP**: Windows Bitmap (24-bit RGB, uncompressed)
- **TGA**: Truevision TGA (24-bit RGB, uncompressed)
- **PPM**: Portable Pixmap (binary P6)
- **PNG**: PNG (24-bit RGB, DEFLATE compressed, no zlib dependency)

