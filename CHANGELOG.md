# Changelog

All notable changes to the Dam Geometry Transformer (Goldie Geotechnics QGIS tool).
Versioning follows the filename convention `dam_geometry_transformer_v<N>.py`,
with the internal `VERSION` constant kept in sync.

## v73 — 2026-06-15

### Added
- **DWG input support.** All CAD reads funnel through one chokepoint
  (`_parse_dxf_entities`); a binary AutoCAD DWG is transparently converted to
  DXF (cached by path+mtime+size) via the best available backend — ODA File
  Converter, `ezdxf`+ODA, LibreDWG (`dwg2dxf`), then GDAL's CAD driver — with an
  actionable "install ODA File Converter" error if none are present. The file
  browser and labels accept `.dwg`.
- **LWPOLYLINE parsing.** The text DXF parser now reads `LWPOLYLINE` (single
  elevation in group 38, per-vertex bulge in 42), normalised to the existing
  `POLYLINE` shape. Required because DWG→DXF converters emit contour strings as
  LWPOLYLINE — without it a converted file parsed to zero geometry.
- **Smart source-CRS picker (Input tab).** CAD files carry no CRS, and NZ data
  is usually in a meridional circuit rather than NZTM2000. "Smart detect" ranks
  NZ CRSs (NZTM2000, NZMG, all NZGD2000 + NZGD1949 meridional circuits) by how
  close each one lands to the current map-canvas centre, so the circuit that
  drops the dam onto the viewed aerial ranks first. "Test selected CRS on map"
  drops the outline onto the canvas to confirm visually. The chosen CRS flows
  through `self._data_crs` → `step2_extract` and reprojects to NZTM2000 on Run.

### Fixed
- **Polygon-method DEM corruption — self-intersecting rings.**
  `cut_outer_toe_to_terrain` builds the variable-Z outer toe by walking each
  outer-crest vertex outward until it meets terrain; at concave corners — or
  where some vertices hit near the crest while neighbours miss and snap back to
  the artificial-deep toe (e.g. a shelterbelt in a DSM) — adjacent toe points
  cross, producing a self-intersecting "bowtie". Used as the DEM clip mask, the
  even-odd fill rule treats the doubly-enclosed lobe as outside and punches a
  NoData hole (the "big missing chunk" + white wedge at the corner). New
  `_repair_ring()` repairs self-intersections (GEOS MakeValid, `buffer(0)`
  fallback, largest part, Z preserved by nearest-vertex remap) at the toe's
  source and again defensively at the DEM clip in `_build_dem`.
- **Silent geometry loss in offsets.** `_offset_ring_xy` now warns when an
  inward offset splits the ring (dam narrower than the design batters + crest
  width allow) instead of silently dropping a lobe of the reservoir floor.

### Known limitations / next
- The 4-ring model represents one simple dam. Shared-embankment twin-cell dams
  (one outer toe, two inner toes) and variable crest width/elevation are not
  yet generalised — for now run each cell separately via the multi-dam
  clustering filter and compose by terrain-priority order in HEC-RAS.
- The QGIS TIN-interpolation path still falls back to scipy `griddata`; clean
  const-Z constructed rings interpolate fine either way, so this is a polish
  item, not a correctness one.

## v63–v72 — prior sessions (condensed)
- **v72** — Manual-entry "build dam from one ring" for incomplete DXFs (Lone Star).
- **v71** — Output layer names tied to the Dam Name field via `_layer_name()`.
- **v70** — Auto-select first spatial cluster on multi-dam load.
- **v69** — "Detected dams" overview plot.
- **v68** — Spatial ring clustering by centroid, immune to layer mislabelling.
- **v67** — Plot Temp Key Lines warns when fewer than 4 rings are plotted.
- **v66** — Dam-name label placed below the trace (outside the perimeter).
- **v65** — Vectorised the scipy DEM clip with `matplotlib.path.Path.contains_points`.
- **v64** — Synced the internal `VERSION` constant to the filename version.
- **v63** — Established the versioned-filename convention.
