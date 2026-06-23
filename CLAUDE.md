# Dam Geometry Transformer — Project Guide & Session Handoff

**Goldie Geotechnics.** A single-file QGIS tool that turns DXF/DWG dam geometry
(concentric design contours, or a crest polygon + dimensions) into elevation
point clouds and DEMs for breach assessment (HEC-RAS 2D) and dam design.

## Current state
- **Latest: v79** — `dam_geometry_transformer_v79.py` (~12k lines, one file).
- Internal `VERSION` constant is kept in sync with the filename (shows in the
  window title + run banner).
- **Convention:** every deployed change bumps the filename **and** `VERSION`
  (v63 → v79 so far) and adds a `CHANGELOG.md` entry. Keep that up.
- **CRS:** output is always NZTM2000 (EPSG:2193) / NZVD2016.
- **Run** in the QGIS Python console:
  `exec(Path('.../dam_geometry_transformer_v79.py').read_text())`

### ⚠️ Build/verify environment
This repo is edited in a sandbox **without a working QGIS Python** (the distro
QGIS targets a different interpreter). So QGIS-side code (the PyQt UI,
`processing.run`, `QgsGeometry`) cannot be run here. It is instead verified
against the **same engines QGIS uses** — `shapely` (GEOS) and `pyproj` (PROJ) —
plus a headless AST-extraction harness for the pure-Python parser/classifier.
**The user runs the real tool in QGIS to confirm.** Always say what was verified
this way vs. what still needs a live QGIS run; don't claim "it works" otherwise.

## Input modes
1. **DXF auto** — read concentric design contours, classify into 4 key rings.
2. **DXF + anchor** — assign one ring, construct the other 3 by offset/slope.
3. **Polygon + terrain** — draw the crest polygon + type dimensions, construct
   4 rings, cut the outer toe to terrain.

## Methodology — rules the user insisted on (do NOT violate)
1. **Build DEMs from clean CONSTRUCTED geometry, not raw contours.** Gridding
   raw contours terraces (flat-triangle facets, crest spikes). The 4 const-Z
   rings → TIN gives perfect planar batters; that's why the parametric build
   exists.
2. **Batter H:V comes from CONTOUR-TO-CONTOUR spacing, NEVER crest-to-toe.** The
   toe can be mis-placed; the spacing between contours is the design truth
   (`step4b_detect_slopes` → `CFG['inner_hv']`/`['outer_hv']`). If crest-to-toe
   disagrees with the contour slope, the **toe** is wrong — warn, don't use it.
3. **Outer toe = artificial-deep const-Z ring → TIN (uniform slope) → TRIM to
   terrain.** Never feed a variable-Z toe into the TIN (introduces noise); the
   variable-Z toe is only the trim/clip boundary.
4. **The inner toe is the basin floor, NEVER the sump.** A sump is a small,
   deeper, interior pocket.
5. **Build up in ordered steps** (extrude / cut, like clay) — each step must
   reduce cleanly into the next while carrying the previous step's information.

## This session (v73 → v79) — see `CHANGELOG.md` for full detail
- **v73** DWG input (transparent DWG→DXF via ODA / ezdxf+ODA / LibreDWG /
  GDAL CAD driver, cached) + **LWPOLYLINE** parsing + DEM **self-intersecting-
  ring repair** (`_repair_ring`, fixes the bowtie / "big missing chunk" where a
  cut-to-terrain toe folds at a concave corner) + **smart NZ source-CRS picker**
  (ranks NZGD2000/1949 meridional circuits by where they land on the current
  map-canvas centre; "Test selected CRS on map").
- **v74** Geometry-tab ring **visibility checkboxes** + selection highlight +
  isolate/show-all; fixed **"Plot Temp Key Lines"** tagging EPSG:2193 instead of
  the picked source CRS.
- **v75** Interior **sump support** — model as a basin pocket (invert ring + a
  rim at basin invert so the basin stays flat to the sump edge, no funnel).
- **v76** Fixed sump taken as inner toe — off-centre-sump-robust
  `_filter_sumps_from_const_z` (inner toe = largest ring in the lowest Z band) +
  the `new_open` UnboundLocalError in `step3_classify` that crashed
  design-layer-only filtering.
- **v77** *(superseded)* rebuilt inner toe as a uniform offset of the inner
  crest — wrong, it drifted off the real (non-uniform) basin.
- **v78** rebuild inner toe = **convex hull of (basin floor ∪ sump)** — keeps the
  DXF basin shape and rounding everywhere, only bulges to swallow the sump so it
  models as a pocket (only when the basin is essentially convex).
- **v79** spillway uses the **contour-derived slope** (`CFG['inner_hv']`/
  `['outer_hv']`) instead of recomputing crest-to-toe; warns if crest-to-toe
  diverges >30% from the contour slope (toe probably mis-identified).

## Outstanding / next priorities
1. **TIN interpolation always fails → scipy fallback with NO breaklines.**
   `processing.run("qgis:tininterpolation", …)` raises `'NoneType' object has no
   attribute 'sourceCrs'` because the temp point/breakline layers are added with
   `addMapLayer(lyr, False)` and the algorithm can't resolve them; it drops to
   `_dem_scipy` (linear griddata, crest/spillway breaklines NOT enforced → rough
   batters). **Fix:** write the point + breakline layers to temp GPKG files and
   reference the file paths in `INTERPOLATION_DATA`, or pass a
   `QgsProcessingContext` carrying the project. In `_build_dem`. HIGH value —
   improves every DEM.
2. **Degenerate cut-to-terrain on cut-into-slope dams.** When terrain sits at or
   above the crest at the outer perimeter, `cut_outer_toe_to_terrain` finds
   intersections ~0 m out → near-vertical outer batter (it warns "DEGENERATE
   CUT"). The fill-embankment + trim model doesn't fit a dam cut into a slope.
   Two real cases: (a) terrain is a **DSM** including the existing structure →
   user needs **bare-earth**; (b) **genuine cut dam** (crest ≈ ground) → needs a
   different surface model (dam-where-above-ground merged with terrain).
3. **Twin-cell shared-embankment dams** (Ngāi Tahu Farm 1/2 & 3/4): one outer
   toe, two inner toes, shared berm, different crest levels. Not generalised.
   Workaround: process each cell separately (multi-dam spatial cluster filter)
   and compose in RAS Mapper by terrain priority. Planned: a multi-cell
   parametric build anchored on the digitised crest rings.
4. **Variable crest elevation/width** for side-hill dams (falling-grade crest).
   `CFG['crest']` is currently a single value.
5. **Sump-aware slope detection:** `step4b_detect_slopes` still includes the
   inner toe as one of its contour pairs in the median; make it strictly
   contour-to-contour (toe only as the cross-check) for full toe-independence.

## Architecture quick-reference (key functions)
- **DWG→DXF:** `_ensure_dxf`, `_convert_dwg_to_dxf` (+ `_convert_via_*`), cached.
- **Parse:** `_parse_dxf_entities` (POLYLINE / LWPOLYLINE / LINE; bulge→arc via
  `_bulge_to_arc_points`).
- **Extract/reproject:** `_extract_from_dxf`, `step2_extract` (reprojects from
  `CFG['data_crs']` to NZTM2000).
- **Classify:** `step3_classify` → `step4_identify` (`_filter_sumps_from_const_z`,
  + inner-toe convex-hull-over-sump) → `step4b_detect_slopes` (contour slopes →
  `CFG['inner_hv']`/`['outer_hv']`) → `step4c_var_z_outer_toe` / `step4d`.
- **Construct:** `construct_dam_rings_from_anchor`, `_offset_ring_xy` (GEOS
  buffer), `_offset_ring_inward`, `_repair_ring` (GEOS MakeValid).
- **Points/DEM:** `step5_points` (4 const-Z rings + sump pocket), `step6_spillway`,
  `step7_outputs`, `_build_dem` (TIN → `_apply_constant_slope_batter` → clip;
  fallback `_dem_scipy`), `cut_outer_toe_to_terrain`, `step7c_drape_to_terrain`.
- **CRS:** `_rank_nz_crs_candidates`, `_source_crs_authid`, picker UI
  (`_smart_detect_source_crs`, `_test_source_crs_on_map`).
- **Slopes:** `_hv_for_ring_pair`, `_detect_design_hv` (contour median),
  `_estimate_batter_hv` (crest-to-toe — now ONLY a cross-check).

## Test data in repo
- `NGAI TAHU DAM D.dwg` — AutoCAD 2000 DWG, **meridional-circuit** coords
  (~Mt Pleasant / EPSG:2124), 0.2 m `DESIGN_Contours` 192.40–198.80 m, plus
  `DAM 1`/`DAM 2` (a twin-cell shared-embankment job). All LWPOLYLINE — needs the
  v73 LWPOLYLINE support + a converter to read.
- `DAM_DESIGN_02.dxf` — Schouten Dam 03 (Densem Contracting), old-style POLYLINE,
  has an **off-centre sump** (119.05 m) below the basin floor (120.05 m), design
  slope 3.5:1, an `FSL`/`DAM WL` at 123.05, crest 123.95. Also carries
  `DTM_POND 02_contours` (existing ground) — filter to the `POND 2` design layer.

## Conventions
- EPSG:2193 / NZVD2016; en-dashes only in UI text; additive-only changes
  preferred; `StepLogger` (`LOG`) for output; non-modal `show()` for
  canvas-interaction dialogs; `CFG` global dict for run params.
- Branch for development: `claude/affectionate-lamport-hs7xn9`. PR #1 is open
  against `main`.
