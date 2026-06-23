# Changelog

All notable changes to the Dam Geometry Transformer (Goldie Geotechnics QGIS tool).
Versioning follows the filename convention `dam_geometry_transformer_v<N>.py`,
with the internal `VERSION` constant kept in sync.

## v77 — 2026-06-16

### Fixed
- **Sump-chopped inner toe warped the inner batter (Schouten Dam 03).** Where
  the basin-floor ring skirts an off-centre sump, the DXF draws it flat /
  chopped on the sump side, so the inner toe didn't follow the concentric
  pattern and the sump fell *outside* the basin (modelled as a hole in the
  batter instead of a pocket). When a sump is detected, `step4_identify` now
  rebuilds the inner toe as a **clean concentric ring offset inward from the
  inner crest** (sized to the basin floor), at the basin invert — your "min
  elevation excluding the sump → invert; batter slope → offset; draw the ring"
  recipe. Verified on the real DXF: the rebuilt ring is convex, ~matches the
  basin area (17,614 vs 18,673 m²), and brings the sump *inside* the basin so
  it models as a pocket. Normal/sumpless dams are unaffected (only triggers
  when a sump is present).

## v76 — 2026-06-16

### Fixed
- **Sump taken as the inner toe (Schouten Dam Concept 03) → spillway
  truncation.** Tested the classifier headless on the real DXF and found two
  bugs, now fixed:
  1. **`step3_classify` crashed** (`new_open` referenced before assignment)
     whenever the input had no open lines — i.e. exactly when you filtered to
     the clean design layer (`POND 2`). Now initialised unconditionally.
  2. **`_filter_sumps_from_const_z` missed the sump.** The sump is OFF-CENTRE
     (centroid at the basin's east edge), so the old "centroid inside the next
     ring's shrunk bbox" test failed and the sump was taken as the inner toe;
     mixed-in DTM contours also defeated the old "compare to the immediately-
     next ring" area test. Redesigned: the inner toe is the largest-area ring
     in the lowest elevation band (the basin floor); smaller, deeper, interior
     rings are sumps. Verified — inner toe is now **120.05 m** (basin floor)
     instead of 119.05 m (the sump) on both the design layer and all-layers,
     with no regression on normal/sumpless dams.

  With the inner toe correct, the inner-batter H:V comes out ~3.5:1 (design)
  instead of ~16:1, so the spillway inner transition no longer over-extends
  and truncates.

## v75 — 2026-06-16

### Added
- **Interior sump support.** A sump (a small ring sitting below the basin
  floor — e.g. the 119.05 m / 573 m² pocket in Schouten Dam Concept 03, 1 m
  below the 120.05 m basin floor) is now carried through classification
  (`kl['sumps']`) instead of just being discarded. New **"Model interior
  sump(s) in the DEM"** checkbox (Geometry tab, default on): each sump is
  modelled as an **invert ring** at the sump level plus a **rim** at basin
  invert, offset outboard by the wall run (`sump_wall_hv`, default 1.5:1), so
  the basin floor stays flat out to the sump edge and only a short wall drops
  to the invert. Unticked, the sump is ignored (flat basin). Either way the
  sump is never used as the inner toe.

### Fixed / explained
- **Spillway transition truncating when a sump is present.** Root cause: when
  the sump is taken as the inner toe, the inner-batter H:V estimate comes out
  ~16:1 instead of the ~3.5:1 design slope, which blows out the spillway inner
  transition (`inner_ext = dep × inner_hv`) and self-intersects the inner arc
  — truncating the ramp back to the crest, especially after dropping the
  spillway. Keeping the sump out of the inner-toe pick restores the correct
  slope. (The auto sump-filter already excludes it when the rings are the
  design layer only; reading mixed DTM-contour layers can defeat it — filter
  to the design layer.)

## v74 — 2026-06-15

### Added
- **Ring visibility + selection on the Geometry tab.** Each row's "#" cell is
  now a checkbox that shows/hides that ring in the DXF plan view, and selecting
  a row highlights its ring (bold + halo, the rest dimmed). "Isolate selected
  ring" and "Show all rings" buttons declutter in one click. Makes role
  assignment reliable when many contours overlap and matching by colour alone
  is impractical.

### Fixed
- **"Plot Temp Key Lines" ignored the source CRS.** It tagged the temp layers
  EPSG:2193 even when the DXF/DWG was in a meridional circuit, so the rings
  plotted far from the dam. They are now tagged with the picked source CRS
  (`_source_crs_authid`) and QGIS reprojects them onto the canvas — matching
  "Test selected CRS on map". Polygon-mode previews stay NZTM2000 (they're
  already reprojected at validate time).

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
