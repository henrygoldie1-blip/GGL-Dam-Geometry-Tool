"""
Dam Geometry Transformer for QGIS
===================================
Goldie Geotechnics

Transforms DXF-sourced dam geometry into elevation point clouds and DEMs
for use in breach assessment (HEC-RAS 2D) and dam design workflows.

Input:  GeoPackage/DXF with concentric polylines defining dam cross-section
Output: Classified point cloud (CSV + GPKG), key lines (GPKG), DEM (GeoTIFF)

Run: exec(open('/path/to/dam_geometry_transformer.py').read())

CRS: NZTM2000 (EPSG:2193) / NZVD2016
"""

import os
import csv
import math
import traceback
from collections import defaultdict

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    print("[Dam Geometry Transformer] WARNING: numpy not found. "
          "scipy DEM fallback will not be available.")

from qgis.core import (
    QgsProject, QgsVectorLayer, QgsFeature, QgsGeometry, QgsField,
    QgsPointXY, QgsPoint, QgsLineString, QgsPolygon,
    QgsWkbTypes, QgsVectorFileWriter,
    QgsRasterLayer, QgsCoordinateReferenceSystem, QgsRectangle,
    QgsCoordinateTransform,
    QgsLineSymbol, QgsFillSymbol, QgsSingleSymbolRenderer,
    QgsPalLayerSettings, QgsTextFormat, QgsTextBufferSettings,
    QgsVectorLayerSimpleLabeling, QgsProperty,
)
try:
    from qgis.analysis import QgsInterpolator
    INTERP_SOURCE_POINTS = QgsInterpolator.SourcePoints
    INTERP_SOURCE_BREAKLINES = QgsInterpolator.SourceStructureLines
except (ImportError, AttributeError):
    INTERP_SOURCE_POINTS = 0
    INTERP_SOURCE_BREAKLINES = 1

from qgis.gui import QgsMapToolEmitPoint
from PyQt5.QtCore import QVariant, Qt
from PyQt5.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QGridLayout, QLabel,
    QLineEdit, QComboBox, QCheckBox, QGroupBox, QPushButton,
    QFileDialog, QMessageBox, QDoubleSpinBox, QSpinBox,
    QTabWidget, QWidget, QRadioButton, QButtonGroup, QFrame,
    QTableWidget, QTableWidgetItem, QHeaderView, QSizePolicy,
    QSplitter, QScrollArea, QSlider, QApplication,
)
from PyQt5.QtGui import QFont, QCursor, QColor
import processing

# Matplotlib for in-dialog plotting (DXF preview + cross-section).
# Optional - dialog still works without it (preview just hidden).
try:
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_qt5agg import (
        FigureCanvasQTAgg as _FigureCanvas)
    HAS_MPL = True
except ImportError:
    HAS_MPL = False
    _FigureCanvas = None
    Figure = None


CRS_EPSG = 2193
TOOL_NAME = "Dam Geometry Transformer"
VERSION = "79"


# =============================================================================
# LOGGING - structured step reporting
# =============================================================================

class StepLogger:
    """Structured logger with step tracking for clear error context."""

    def __init__(self):
        self.current_step = 0
        self.total_steps = 7
        self.step_name = ""
        self.warnings = []
        self.errors = []

    def start_step(self, name):
        self.current_step += 1
        self.step_name = name
        msg = f"[{self.current_step}/{self.total_steps}] {name}"
        print(f"\n{'='*60}")
        print(f"  {msg}")
        print(f"{'='*60}")

    def info(self, msg):
        print(f"  {msg}")

    def detail(self, msg):
        print(f"    {msg}")

    def warn(self, msg):
        full = f"WARNING ({self.step_name}): {msg}"
        self.warnings.append(full)
        print(f"  WARNING: {msg}")

    def error(self, msg):
        full = f"ERROR ({self.step_name}): {msg}"
        self.errors.append(full)
        print(f"  ERROR: {msg}")

    def success(self, msg="Done"):
        print(f"  OK: {msg}")

    def summary(self):
        lines = []
        if self.warnings:
            lines.append(f"\n{len(self.warnings)} warning(s):")
            for w in self.warnings:
                lines.append(f"  WARNING: {w}")
        if self.errors:
            lines.append(f"\n{len(self.errors)} error(s):")
            for e in self.errors:
                lines.append(f"  ERROR: {e}")
        if not self.errors:
            lines.append("\nAll steps completed successfully.")
        return "\n".join(lines)


LOG = StepLogger()


# =============================================================================
# MAP CLICK TOOL
# =============================================================================

class SpillwayPickTool(QgsMapToolEmitPoint):
    """Map click tool that transforms coordinates to NZTM2000 (EPSG:2193)."""

    def __init__(self, canvas, dialog, e_spin, n_spin):
        super().__init__(canvas)
        self.dialog = dialog
        self.e_spin = e_spin
        self.n_spin = n_spin
        self.canvas = canvas
        self._prev = canvas.mapTool()
        self.setCursor(QCursor(Qt.CrossCursor))
        # Target CRS is always NZTM2000
        self._target_crs = QgsCoordinateReferenceSystem("EPSG:2193")

    def canvasReleaseEvent(self, event):
        pt = self.toMapCoordinates(event.pos())

        # Transform from canvas CRS to NZTM2000 if needed
        canvas_crs = self.canvas.mapSettings().destinationCrs()
        if canvas_crs.isValid() and canvas_crs != self._target_crs:
            xform = QgsCoordinateTransform(
                canvas_crs, self._target_crs, QgsProject.instance())
            pt = xform.transform(pt)
            print(f"[SpillwayPick] Transformed to NZTM2000: "
                  f"({pt.x():.1f}, {pt.y():.1f})")
        else:
            print(f"[SpillwayPick] NZTM2000: ({pt.x():.1f}, {pt.y():.1f})")

        self.e_spin.setValue(pt.x())
        self.n_spin.setValue(pt.y())
        self.canvas.setMapTool(self._prev)
        self.dialog.show()
        self.dialog.raise_()
        self.dialog.activateWindow()


# =============================================================================
# NZ SOURCE-CRS DETECTION  (DXF/DWG files carry no CRS)
# =============================================================================
#
# NZ survey data is very often in a meridional circuit, not NZTM2000. All 28
# NZGD2000 circuits share the same false origin, so the file coordinates alone
# cannot tell them apart - every circuit places the data somewhere in NZ. The
# disambiguator is the map the user is already looking at: rank candidates by
# how close each one lands to the current canvas centre, so the circuit that
# drops the dam onto the viewed aerial ranks first. The user confirms visually
# with 'Test on map'.

_NZ_CIRCUITS_2000 = {
    2105: "Mount Eden 2000", 2106: "Bay of Plenty 2000",
    2107: "Poverty Bay 2000", 2108: "Hawke's Bay 2000",
    2109: "Taranaki 2000", 2110: "Tuhirangi 2000",
    2111: "Wanganui 2000", 2112: "Wairarapa 2000",
    2113: "Wellington 2000", 2114: "Collingwood 2000",
    2115: "Nelson 2000", 2116: "Karamea 2000",
    2117: "Buller 2000", 2118: "Grey 2000",
    2119: "Amuri 2000", 2120: "Marlborough 2000",
    2121: "Hokitika 2000", 2122: "Okarito 2000",
    2123: "Jacksons Bay 2000", 2124: "Mount Pleasant 2000",
    2125: "Gawler 2000", 2126: "Timaru 2000",
    2127: "Lindis Peak 2000", 2128: "Mount Nicholas 2000",
    2129: "Mount York 2000", 2130: "Observation Point 2000",
    2131: "North Taieri 2000", 2132: "Bluff 2000",
}


def _rank_nz_crs_candidates(cx, cy, ref_pt=None, ref_crs=None):
    """Rank NZ projected CRSs by where they place the point (cx, cy).

    Returns a list of dicts (best first):
        {'epsg', 'name', 'lat', 'lon', 'in_nz', 'dist_km'}

    If ref_pt (a QgsPointXY) and ref_crs are given - normally the current
    map-canvas centre - candidates are ranked by how close the reprojected
    point lands to ref_pt, so the circuit that drops the geometry onto the
    area the user is viewing ranks first. Otherwise they're ranked by landing
    inside NZ, then North-to-South.
    """
    try:
        wgs = QgsCoordinateReferenceSystem("EPSG:4326")
    except Exception:
        return []
    candidates = [(2193, "NZTM2000"), (27200, "NZMG (New Zealand Map Grid)")]
    candidates += sorted(_NZ_CIRCUITS_2000.items())
    # Legacy NZGD1949 circuits - validated at runtime so wrong codes drop out.
    for epsg in range(27205, 27233):
        candidates.append((epsg, None))

    ref_wgs = None
    if ref_pt is not None and ref_crs is not None:
        try:
            if ref_crs.isValid() and ref_crs != wgs:
                ref_wgs = QgsCoordinateTransform(
                    ref_crs, wgs, QgsProject.instance()).transform(ref_pt)
            else:
                ref_wgs = ref_pt
        except Exception:
            ref_wgs = None

    out = []
    seen = set()
    for epsg, name in candidates:
        if epsg in seen:
            continue
        seen.add(epsg)
        try:
            crs = QgsCoordinateReferenceSystem(f"EPSG:{epsg}")
            if not crs.isValid():
                continue
            desc = crs.description() or ""
            if name is None:
                if "Circuit" not in desc:
                    continue
                name = desc.split("/")[-1].strip() or desc
            p = QgsCoordinateTransform(
                crs, wgs, QgsProject.instance()).transform(QgsPointXY(cx, cy))
            lon, lat = p.x(), p.y()
            if not (math.isfinite(lon) and math.isfinite(lat)):
                continue
        except Exception:
            continue
        in_nz = (166.0 <= lon <= 179.2) and (-47.6 <= lat <= -34.0)
        dist_km = None
        if ref_wgs is not None:
            dist_km = math.hypot(
                (lon - ref_wgs.x()) * math.cos(math.radians(lat)) * 111.0,
                (lat - ref_wgs.y()) * 111.0)
        out.append({'epsg': epsg, 'name': name, 'lat': lat, 'lon': lon,
                    'in_nz': in_nz, 'dist_km': dist_km})

    if ref_wgs is not None:
        out.sort(key=lambda c: c['dist_km'] if c['dist_km'] is not None
                 else 1e9)
    else:
        out.sort(key=lambda c: (not c['in_nz'], -c['lat']))
    return out


# =============================================================================
# GUI DIALOG
# =============================================================================

class TransformerDialog(QDialog):
    def __init__(self, iface, parent=None):
        super().__init__(parent)
        self.iface = iface
        self.canvas = iface.mapCanvas()
        self.setWindowTitle(f"{TOOL_NAME} v{VERSION} - Goldie Geotechnics")

        # ------------------------------------------------------------------
        # Sizing. We want everything that needs to be visible to be visible
        # on first open: mode pill at the top, tab bar, all controls in the
        # active tab (the Polygon Mode tab in particular is dense - 7
        # parameter spinboxes + layer/role combos + terrain combo + preview
        # button + status label), matplotlib plan view and long section on
        # the Geometry tab, the Run button at the bottom.
        #
        # Minimum: 1200 x 800 - below this the matplotlib figures and the
        # parameter grids stop being usable.
        # On a 4K screen the previous 1500x980 cap was way too small.
        # Open at 95% of the available screen so all panels breathe,
        # and try to start maximised (user can always restore). Falls
        # back to a comfortable default if anything weird happens.
        self.setMinimumWidth(1200)
        self.setMinimumHeight(800)
        DEFAULT_W, DEFAULT_H = 1900, 1100
        opened_maximised = False
        try:
            screen = QApplication.primaryScreen()
            avail = screen.availableGeometry() if screen else None
            if avail is not None:
                # First sizing pass at 95% of screen so the dialog has
                # a reasonable restored-size to fall back to. Then we
                # request maximised state.
                w = max(1200, int(avail.width() * 0.95))
                h = max(800, int(avail.height() * 0.92))
                self.resize(w, h)
                self.move(
                    avail.x() + (avail.width() - w) // 2,
                    avail.y() + (avail.height() - h) // 2)
                try:
                    self.setWindowState(self.windowState()
                                        | Qt.WindowMaximized)
                    opened_maximised = True
                except Exception:
                    pass
            else:
                self.resize(DEFAULT_W, DEFAULT_H)
        except Exception:
            # If anything goes wrong (older PyQt, headless test, etc.)
            # fall back to a fixed default size
            self.resize(DEFAULT_W, DEFAULT_H)
        # As a belt-and-braces second try for maximisation, queue it
        # for after the dialog is shown.
        if not opened_maximised:
            try:
                from qgis.PyQt.QtCore import QTimer
                QTimer.singleShot(0, self.showMaximized)
            except Exception:
                pass

        self.result_params = None
        self._pick_tool = None
        self._data_crs = None
        # Layer id of the temporary "test CRS on map" preview, if shown.
        self._crs_preview_layer_id = None
        # Preview-analysis state (populated when DXF is loaded)
        self._preview = None        # dict from preview_analyse_dxf
        self._role_widgets = []     # list of QComboBox per visible table row
        self._row_to_ring_idx = []  # displayed-row -> index in all_rings (const+var)
        # Plan-view ring visibility + selection (Geometry tab). With many
        # detected rings, matching by colour alone is impractical, so the
        # ring table's '#' cells are checkable (toggle plan-view visibility)
        # and selecting a row highlights that ring.
        self._ring_visible = {}        # ring index -> bool (default visible)
        self._selected_ring_idx = None # ring highlighted from the table
        self._table_building = False   # guard: suppress itemChanged on rebuild
        self._role_assignments = {} # role -> index in _preview.all_rings (const+var)
        self._terrain_layer = None  # selected QgsRasterLayer or None
        # Phase 2 - constructed (anchor + params) geometry
        self._constructed_kl = None     # dict of role -> ring (None until built)
        # Variable-Z outer toe polylines from each method. Both can
        # coexist; the radio buttons on the Geometry tab choose which
        # one is COPIED INTO kl['outer_toe'] (the active ring used
        # downstream for plan view, long section, DEM mask, CSV).
        # Each value is None or a dict matching kl['outer_toe'] shape:
        #   {'coords': [(x,y,z),...], 'z_min': ..., 'z_max': ...,
        #    'z_mean': ..., 'z_std': ..., 'npts': ..., 'method': str,
        #    'is_variable_z': True}
        self._var_z_outer_toes = {'method1': None, 'method2': None}
        self._active_var_z_method = 'method1'
        # True when the dam has been moved relative to the DXF datum by
        # something OTHER than "snap outer toe to ground" - i.e. the
        # cut/fill-balance snap, the max-embankment-height snap, or a
        # manual z_offset edit/slider drag. When this is set, the DXF's
        # baked-in outer toe (Method 1) is STALE: the dam no longer sits
        # where the DXF contours said it would, so the toe must be
        # re-derived from the terrain intersection (Method 2). Snap-to-
        # ground and Reset clear this flag (they realign the dam to the
        # DXF toe / reset the datum). Used at output time to force
        # Method 2 priority. See _force_method2_if_dam_moved().
        self._dam_moved_off_dxf_toe = False
        self._buildup_anchor_role = None
        self._build_error = None
        # Long-section view state
        self._section_angle_deg = None  # None = use default (low->high). Set
                                        # by user via slider or snap button.
        # Polygon-mode preview layers (added to QGIS project on Preview
        # Construction click, removed when re-clicked or mode is changed)
        self._polygon_preview_layer_ids = []
        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout()

        title = QLabel(TOOL_NAME)
        title.setFont(QFont("", 14, QFont.Bold))
        title.setAlignment(Qt.AlignCenter)
        layout.addWidget(title)
        sub = QLabel("Goldie Geotechnics - DXF to Point Cloud / DEM Pipeline")
        sub.setAlignment(Qt.AlignCenter)
        layout.addWidget(sub)
        layout.addSpacing(6)

        # ----------------------------------------------------------------
        # MODE PILL: select which input pipeline drives the run
        # ----------------------------------------------------------------
        # Three modes are supported:
        #  * "DXF (auto)"      - good DXF, full ring auto-identification
        #  * "DXF + anchor"    - bad/sparse DXF, user picks one ring as
        #                          anchor and constructs the rest (Phase 2)
        #  * "Polygon + terrain" - no DXF; one polygon + parameters,
        #                          DEM is clipped to terrain (Phase 3)
        # Switching modes flips which inputs are used at Run, but ALL
        # three modes feed the same step5/step6/step7 pipeline and can
        # have a spillway cut in.
        # LEGACY: the "Build mode" pill at the top of the dialog used
        # to switch between DXF auto, DXF+anchor, and Polygon+terrain.
        # That choice now lives on the Input tab as a simple DXF vs
        # Polygon radio. The pill widgets are still constructed (so any
        # code path that references self.rb_mode_dxf etc. keeps working
        # and the existing default = DXF mode is preserved internally),
        # but the pill is hidden from the user.
        pill_frame = QFrame()
        pill_frame.setFrameShape(QFrame.StyledPanel)
        pill_layout = QHBoxLayout()
        pill_layout.setContentsMargins(8, 4, 8, 4)
        pill_label = QLabel("<b>Build mode:</b>")
        pill_layout.addWidget(pill_label)
        self.rb_mode_dxf = QRadioButton("DXF (auto-detect rings)")
        self.rb_mode_anchor = QRadioButton("DXF + anchor (construct from one ring)")
        self.rb_mode_polygon = QRadioButton("Polygon + terrain drape")
        self.rb_mode_dxf.setChecked(True)  # default
        self._mode_group = QButtonGroup(self)
        self._mode_group.addButton(self.rb_mode_dxf, 0)
        self._mode_group.addButton(self.rb_mode_anchor, 1)
        self._mode_group.addButton(self.rb_mode_polygon, 2)
        self._mode_group.buttonClicked.connect(self._on_mode_changed)
        pill_layout.addWidget(self.rb_mode_dxf)
        pill_layout.addWidget(self.rb_mode_anchor)
        pill_layout.addWidget(self.rb_mode_polygon)
        pill_layout.addStretch()
        pill_frame.setLayout(pill_layout)
        pill_frame.setVisible(False)  # hidden in unified UI
        layout.addWidget(pill_frame)
        layout.addSpacing(6)

        tabs = QTabWidget()
        self._tabs = tabs   # so _on_mode_changed can jump tabs

        # --- TAB 1: Input & Elevations ---
        tab1 = QWidget()
        t1 = QVBoxLayout()

        # Dam name (used to label the outer toe perimeter in figures)
        grp_name = QGroupBox("Dam")
        gn = QGridLayout()
        gn.setColumnStretch(0, 0)
        gn.setColumnStretch(1, 1)
        gn.setHorizontalSpacing(6)
        gn.addWidget(QLabel("Name:"), 0, 0)
        self.txt_dam_name = QLineEdit("")
        self.txt_dam_name.setPlaceholderText(
            "e.g. Proposed Neil Kingston Dam (default: Proposed Dam)")
        gn.addWidget(self.txt_dam_name, 0, 1)
        grp_name.setLayout(gn)
        t1.addWidget(grp_name)

        # ===== Unified input-source picker ==============================
        # One mutually-exclusive choice: DXF *or* polygon. Widgets for
        # each path are grouped below; only the selected group is
        # visible. Downstream pipeline (Geometry tab, Method 1/2, DEM
        # build, outputs) is identical for both.
        grp_src = QGroupBox("Input source")
        gs0 = QGridLayout()
        self.rb_input_dxf = QRadioButton("DXF (conceptual design sketch)")
        self.rb_input_polygon = QRadioButton(
            "Polygon (single ring + design parameters)")
        self.rb_input_dxf.setChecked(True)
        self.btng_input_source = QButtonGroup(self)
        self.btng_input_source.addButton(self.rb_input_dxf, 1)
        self.btng_input_source.addButton(self.rb_input_polygon, 2)
        gs0.addWidget(self.rb_input_dxf, 0, 0)
        gs0.addWidget(self.rb_input_polygon, 0, 1)
        grp_src.setLayout(gs0)
        t1.addWidget(grp_src)

        # ===== DXF input group (shown when input source = DXF) ===========
        self.grp_input_dxf = QGroupBox("DXF input")
        g1 = QGridLayout()
        g1.setColumnStretch(0, 0)
        g1.setColumnStretch(1, 1)
        g1.setColumnStretch(2, 0)
        g1.setHorizontalSpacing(6)

        # DXF / DWG direct read (preferred)
        g1.addWidget(QLabel("DXF/DWG file:"), 0, 0)
        self.txt_dxf = QLineEdit("")
        self.txt_dxf.setPlaceholderText(
            "Browse to DXF or DWG file (preserves arcs)")
        g1.addWidget(self.txt_dxf, 0, 1)
        btn_dxf = QPushButton("Browse DXF/DWG...")
        btn_dxf.clicked.connect(self._browse_dxf)
        g1.addWidget(btn_dxf, 0, 2)

        # OR use loaded layer
        g1.addWidget(QLabel("- OR -"), 1, 0, 1, 3, Qt.AlignCenter)

        g1.addWidget(QLabel("QGIS layer:"), 2, 0)
        self.cmb_layer = QComboBox()
        self._populate_layers()
        g1.addWidget(self.cmb_layer, 2, 1)
        self.chk_auto_layer = QCheckBox("Auto-detect (all vector layers)")
        self.chk_auto_layer.setChecked(True)
        self.chk_auto_layer.toggled.connect(
            lambda c: self.cmb_layer.setEnabled(not c))
        self.cmb_layer.setEnabled(False)
        g1.addWidget(self.chk_auto_layer, 3, 0, 1, 2)

        # DXF LAYER FILTER. Some DXFs contain TWO dams on separate
        # layers (e.g. "DAM 11" / "DAM 12" or
        # "DTM_DAM 11 Concept A_contours" / "DTM_DAM 12 CONCEPT A_contours").
        # The default behaviour (read all entities) then mixes both dams
        # into one classification, producing nonsense rings. The filter
        # lets the user pick which dam to import; entities on any other
        # layer are dropped before classification. Multi-select via the
        # dropdown (Ctrl-click) is supported - the user picks all the
        # layers belonging to one dam. Auto-populated from the DXF when
        # the file is picked.
        g1.addWidget(QLabel("DXF layers:"), 4, 0)
        self.cmb_dxf_layer_filter = QComboBox()
        self.cmb_dxf_layer_filter.addItem("(all layers)", None)
        self.cmb_dxf_layer_filter.setToolTip(
            "If the DXF contains multiple dams on separate layers, pick "
            "which layer (or 'Dam #' group) to import. Auto-populated "
            "once a DXF is picked.")
        g1.addWidget(self.cmb_dxf_layer_filter, 4, 1)
        # Re-run the preview when the user picks a different layer so the
        # Geometry tab refreshes for the chosen dam, and re-highlight the
        # selected dam in the overview plot.
        def _on_filter_changed(_i):
            try:
                self._render_dam_overview()
            except Exception:
                pass
            if self.txt_dxf.text().strip():
                self._run_preview_analysis()
        self.cmb_dxf_layer_filter.currentIndexChanged.connect(
            _on_filter_changed)
        self.btn_dxf_layer_refresh = QPushButton("Re-scan DXF")
        self.btn_dxf_layer_refresh.setToolTip(
            "Re-read the DXF file and refresh the layer list.")
        self.btn_dxf_layer_refresh.clicked.connect(
            self._populate_dxf_layer_filter)
        g1.addWidget(self.btn_dxf_layer_refresh, 4, 2)

        # ----- Input CRS: smart picker (files carry no CRS) -----
        g1.addWidget(QLabel("Input CRS:"), 5, 0)
        self.cmb_src_crs = QComboBox()
        self.cmb_src_crs.addItem(
            "Assume NZTM2000 (EPSG:2193) - no reprojection", None)
        self.cmb_src_crs.setToolTip(
            "Source CRS of the DXF/DWG. CAD files store no CRS, so use "
            "'Smart detect' to list the NZ CRSs that place the dam on real "
            "ground (ranked by your current map view), then 'Test on map' to "
            "confirm which one lands on the dam.")
        g1.addWidget(self.cmb_src_crs, 5, 1)
        self.btn_detect_crs = QPushButton("Smart detect")
        self.btn_detect_crs.setToolTip(
            "Analyse the file's coordinates and rank the NZ CRSs by how close "
            "each one drops the geometry to your current map view (pan to the "
            "dam site first). With a QGIS layer instead of a file, reads the "
            "layer's CRS.")
        self.btn_detect_crs.clicked.connect(self._smart_detect_source_crs)
        g1.addWidget(self.btn_detect_crs, 5, 2)

        self.btn_test_crs = QPushButton("Test selected CRS on map")
        self.btn_test_crs.setToolTip(
            "Drop the file's outline onto the canvas using the selected CRS. "
            "QGIS reprojects it over your basemap, so the right circuit lands "
            "on the dam and the wrong ones land elsewhere. Try the candidates "
            "until it matches, then leave it selected.")
        self.btn_test_crs.clicked.connect(self._test_source_crs_on_map)
        g1.addWidget(self.btn_test_crs, 6, 1)
        self.btn_clear_crs_preview = QPushButton("Clear preview")
        self.btn_clear_crs_preview.clicked.connect(self._clear_crs_preview)
        g1.addWidget(self.btn_clear_crs_preview, 6, 2)

        self.lbl_data_crs = QLabel(
            "Assuming NZTM2000. If this file is in a meridional circuit, "
            "click 'Smart detect'.")
        self.lbl_data_crs.setWordWrap(True)
        g1.addWidget(self.lbl_data_crs, 7, 0, 1, 3)
        # Connect only now that the status label exists - addItem() above can
        # fire currentIndexChanged during construction.
        self.cmb_src_crs.currentIndexChanged.connect(self._on_src_crs_changed)

        g1.addWidget(QLabel("Output CRS:"), 8, 0)
        g1.addWidget(QLabel("EPSG:2193 (NZTM2000) - always"), 8, 1)

        # PLOT TEMP KEY LINES. Pushes the inner toe / inner crest / outer
        # crest / outer toe rings to the QGIS canvas as temporary layers
        # so the user can place the spillway accurately against the real
        # dam geometry - WITHOUT running the full pipeline or any cut-to-
        # terrain. Reflects the dam selected in multi-dam DXFs. Mirrored
        # by a button on the Elevations tab.
        self.btn_plot_keylines_input = QPushButton("Plot Temp Key Lines")
        self.btn_plot_keylines_input.setToolTip(
            "Plot the inner toe, inner crest, outer crest and outer toe "
            "on the map as temporary layers, so you can pick the "
            "spillway location accurately. No cut-to-terrain is run. In "
            "multi-dam DXFs this plots the currently-selected dam.")
        self.btn_plot_keylines_input.clicked.connect(
            self._plot_temp_key_lines)
        g1.addWidget(self.btn_plot_keylines_input, 9, 0, 1, 2)
        self.lbl_keyline_status_input = QLabel("")
        self.lbl_keyline_status_input.setWordWrap(True)
        g1.addWidget(self.lbl_keyline_status_input, 9, 2)

        self.grp_input_dxf.setLayout(g1)
        t1.addWidget(self.grp_input_dxf)

        # ===== Polygon input group (shown when input source = Polygon) ===
        self.grp_input_polygon = QGroupBox("Polygon input")
        gpoly = QGridLayout()
        # Keep labels tight against their inputs: column 0 (labels) does
        # not stretch; column 1 (inputs) does. Without this QGridLayout
        # splits available width evenly and labels drift far from inputs.
        gpoly.setColumnStretch(0, 0)
        gpoly.setColumnStretch(1, 1)
        gpoly.setColumnStretch(2, 1)
        gpoly.setColumnStretch(3, 0)
        gpoly.setHorizontalSpacing(6)
        gpoly.addWidget(QLabel("Polygon layer:"), 0, 0)
        self.cmb_input_poly_layer = QComboBox()
        self._populate_polygon_layers(self.cmb_input_poly_layer)
        gpoly.addWidget(self.cmb_input_poly_layer, 0, 1, 1, 2)
        btn_refresh_poly = QPushButton("Refresh")
        btn_refresh_poly.setToolTip("Re-read line/polygon layers from project")
        btn_refresh_poly.clicked.connect(
            lambda: self._populate_polygon_layers(self.cmb_input_poly_layer))
        gpoly.addWidget(btn_refresh_poly, 0, 3)

        gpoly.addWidget(QLabel("Polygon represents:"), 1, 0)
        self.cmb_input_poly_role = QComboBox()
        # Polygon can be ANY of the 4 design rings. Per the requirements
        # doc, most commonly a crest or inner toe ring; outer toe is
        # rare but valid (e.g. when user knows the dam footprint).
        self.cmb_input_poly_role.addItem(
            "Inner crest (top of upstream batter)", 'inner_crest')
        self.cmb_input_poly_role.addItem(
            "Outer crest (top of downstream batter)", 'outer_crest')
        self.cmb_input_poly_role.addItem(
            "Inner toe (bottom of upstream batter)", 'inner_toe')
        self.cmb_input_poly_role.addItem(
            "Outer toe (downstream batter base)", 'outer_toe')
        gpoly.addWidget(self.cmb_input_poly_role, 1, 1, 1, 3)

        gpoly.addWidget(QLabel("Polygon elevation:"), 2, 0)
        self.spn_input_poly_z = QDoubleSpinBox()
        self.spn_input_poly_z.setRange(-100, 3000)
        self.spn_input_poly_z.setDecimals(2)
        self.spn_input_poly_z.setSuffix(" m")
        self.spn_input_poly_z.setValue(0.0)
        self.spn_input_poly_z.setToolTip(
            "Elevation of the polygon's design role (NZVD2016)")
        gpoly.addWidget(self.spn_input_poly_z, 2, 1)

        gpoly.addWidget(QLabel("Dam depth:"), 3, 0)
        self.spn_input_poly_depth = QDoubleSpinBox()
        self.spn_input_poly_depth.setRange(0.1, 100.0)
        self.spn_input_poly_depth.setDecimals(2)
        self.spn_input_poly_depth.setSuffix(" m")
        self.spn_input_poly_depth.setValue(4.0)
        self.spn_input_poly_depth.setToolTip(
            "Vertical distance from crest to invert")
        gpoly.addWidget(self.spn_input_poly_depth, 3, 1)

        gpoly.addWidget(QLabel("Crest width:"), 4, 0)
        self.spn_input_poly_crest_w = QDoubleSpinBox()
        self.spn_input_poly_crest_w.setRange(0.5, 100.0)
        self.spn_input_poly_crest_w.setDecimals(2)
        self.spn_input_poly_crest_w.setSuffix(" m")
        self.spn_input_poly_crest_w.setValue(5.0)
        gpoly.addWidget(self.spn_input_poly_crest_w, 4, 1)

        gpoly.addWidget(QLabel("Inner batter H:V:"), 5, 0)
        self.spn_input_poly_inner_hv = QDoubleSpinBox()
        self.spn_input_poly_inner_hv.setRange(0.1, 20.0)
        self.spn_input_poly_inner_hv.setDecimals(2)
        self.spn_input_poly_inner_hv.setSuffix(" : 1")
        self.spn_input_poly_inner_hv.setValue(3.5)
        gpoly.addWidget(self.spn_input_poly_inner_hv, 5, 1)

        gpoly.addWidget(QLabel("Outer batter H:V:"), 6, 0)
        self.spn_input_poly_outer_hv = QDoubleSpinBox()
        self.spn_input_poly_outer_hv.setRange(0.1, 20.0)
        self.spn_input_poly_outer_hv.setDecimals(2)
        self.spn_input_poly_outer_hv.setSuffix(" : 1")
        self.spn_input_poly_outer_hv.setValue(3.5)
        gpoly.addWidget(self.spn_input_poly_outer_hv, 6, 1)

        gpoly.addWidget(QLabel("Artificial deep offset:"), 7, 0)
        self.spn_input_poly_deep = QDoubleSpinBox()
        self.spn_input_poly_deep.setRange(1.0, 100.0)
        self.spn_input_poly_deep.setDecimals(1)
        self.spn_input_poly_deep.setSuffix(" m below crest")
        self.spn_input_poly_deep.setValue(15.0)
        self.spn_input_poly_deep.setToolTip(
            "How deep to place the artificial outer toe used by the "
            "TIN. Has no effect on the final clipped DEM - the polygon "
            "clip to the active outer toe (Method 2 cut to terrain) "
            "trims to the actual dam-meets-ground line.")
        gpoly.addWidget(self.spn_input_poly_deep, 7, 1)

        # Cut/fill balance snap. When the user hasn't decided on a depth
        # yet, this sweeps candidate depths and picks the one where
        # fill volume (embankment above natural ground) matches
        # cut volume (reservoir + below-ground embankment) times the
        # multiplier. Default multiplier 0.85 reflects typical compacted
        # earthfill bulking (1 m3 cut yields ~0.85 m3 fill).
        gpoly.addWidget(QLabel("Cut/fill multiplier:"), 8, 0)
        self.spn_input_poly_cf_mult = QDoubleSpinBox()
        self.spn_input_poly_cf_mult.setRange(0.1, 5.0)
        self.spn_input_poly_cf_mult.setDecimals(2)
        self.spn_input_poly_cf_mult.setSingleStep(0.05)
        self.spn_input_poly_cf_mult.setValue(0.85)
        self.spn_input_poly_cf_mult.setToolTip(
            "Target ratio of fill / cut. 0.85 is a typical bulking "
            "factor for compacted earthfill (1 m3 cut yields ~0.85 m3 "
            "of fill). Set 1.0 for exact balance, < 1.0 if some cut "
            "material is unsuitable for fill.")
        gpoly.addWidget(self.spn_input_poly_cf_mult, 8, 1)

        self.btn_input_poly_snap_cf = QPushButton(
            "Snap depth to balance cut / fill")
        self.btn_input_poly_snap_cf.setToolTip(
            "Sweep candidate depths and pick the one whose fill volume "
            "matches cut * multiplier. Requires a terrain raster.")
        self.btn_input_poly_snap_cf.clicked.connect(
            self._snap_polygon_depth_to_cut_fill_balance)
        gpoly.addWidget(self.btn_input_poly_snap_cf, 8, 2, 1, 2)

        # Construct button - live preview is the goal, but explicit
        # build keeps things deterministic if the user wants to see
        # the construction before running the full pipeline.
        self.btn_input_poly_build = QPushButton(
            "Build rings from polygon (auto-runs Method 2 if terrain loaded)")
        self.btn_input_poly_build.clicked.connect(
            self._build_from_polygon_input)
        gpoly.addWidget(self.btn_input_poly_build, 9, 0, 1, 4)

        self.lbl_input_poly_status = QLabel(
            "<i>Pick a polygon layer + role + elevation + depth + "
            "slopes, then click Build. If a terrain raster is loaded, "
            "Method 2 (cut to terrain) runs automatically so the DEM is "
            "ready to Run. Use 'Snap depth' to balance cut/fill before "
            "Build if you haven't decided on a depth.</i>")
        self.lbl_input_poly_status.setWordWrap(True)
        gpoly.addWidget(self.lbl_input_poly_status, 10, 0, 1, 4)

        self.grp_input_polygon.setLayout(gpoly)
        t1.addWidget(self.grp_input_polygon)
        # Hidden until polygon input is selected
        self.grp_input_polygon.setVisible(False)

        # Auto-detect CRS on startup
        self._detect_crs()

        # Terrain DEM picker (used for cross-section plots and the ground-cut
        # logic when overrides are applied)
        grp_terrain = QGroupBox("Terrain DEM (existing ground surface)")
        gt = QGridLayout()
        gt.setColumnStretch(0, 0)
        gt.setColumnStretch(1, 1)
        gt.setColumnStretch(2, 0)
        gt.setHorizontalSpacing(6)
        gt.addWidget(QLabel("Layer:"), 0, 0)
        self.cmb_terrain = QComboBox()
        self.cmb_terrain.addItem("(none)", None)
        self._populate_raster_layers()
        self.cmb_terrain.currentIndexChanged.connect(self._on_terrain_changed)
        gt.addWidget(self.cmb_terrain, 0, 1)
        btn_refresh_t = QPushButton("Refresh")
        btn_refresh_t.setToolTip("Re-read raster layers from the project")
        btn_refresh_t.clicked.connect(self._populate_raster_layers)
        gt.addWidget(btn_refresh_t, 0, 2)
        gt.addWidget(QLabel(
            "Used for cross-section plots and (when overrides applied) for "
            "intersecting the outer batter with existing ground."),
            1, 0, 1, 3)
        grp_terrain.setLayout(gt)
        t1.addWidget(grp_terrain)

        grp_el = QGroupBox("Elevations (m NZVD2016)")
        g2 = QGridLayout()
        g2.setColumnStretch(0, 0)
        g2.setColumnStretch(1, 1)
        g2.setHorizontalSpacing(6)
        self.chk_auto_elev = QCheckBox("Auto-detect from Z coordinates")
        self.chk_auto_elev.setChecked(True)
        self.chk_auto_elev.toggled.connect(self._toggle_elev)
        g2.addWidget(self.chk_auto_elev, 0, 0, 1, 2)

        for row, label, attr, default in [
            (1, "Dam invert (inner toe):", "spn_invert", 335.0),
            (2, "Crest elevation:", "spn_crest", 339.0),
            (3, "Outer toe lowest:", "spn_toe", 336.0),
        ]:
            g2.addWidget(QLabel(label), row, 0)
            s = QDoubleSpinBox()
            s.setRange(0, 9999); s.setDecimals(2); s.setValue(default)
            s.setSuffix(" m")
            setattr(self, attr, s)
            g2.addWidget(s, row, 1)

        grp_el.setLayout(g2)
        t1.addWidget(grp_el)
        self._toggle_elev(True)

        # Mirror of the Input-group "Plot Temp Key Lines" button - placed
        # here too because the user typically sets elevations and then
        # wants to see the rings before picking the spillway. Both
        # buttons call the same handler.
        self.btn_plot_keylines_elev = QPushButton(
            "Plot Temp Key Lines (for spillway placement)")
        self.btn_plot_keylines_elev.setToolTip(
            "Plot the inner toe, inner crest, outer crest and outer toe "
            "on the map as temporary layers so you can pick the spillway "
            "accurately. No cut-to-terrain is run.")
        self.btn_plot_keylines_elev.clicked.connect(
            self._plot_temp_key_lines)
        t1.addWidget(self.btn_plot_keylines_elev)
        self.lbl_keyline_status_elev = QLabel("")
        self.lbl_keyline_status_elev.setWordWrap(True)
        t1.addWidget(self.lbl_keyline_status_elev)

        grp_pt = QGroupBox("Point Generation")
        g3 = QGridLayout()
        g3.setColumnStretch(0, 0)
        g3.setColumnStretch(1, 1)
        g3.setHorizontalSpacing(6)
        g3.addWidget(QLabel("Line point spacing:"), 0, 0)
        self.spn_spacing = QDoubleSpinBox()
        self.spn_spacing.setRange(0.05, 10.0); self.spn_spacing.setValue(0.1)
        self.spn_spacing.setSuffix(" m")
        g3.addWidget(self.spn_spacing, 0, 1)
        grp_pt.setLayout(g3)
        t1.addWidget(grp_pt)

        # Detected-dams overview plot. For multi-dam DXFs the spatial
        # cluster entries in the "DXF layers" dropdown are labelled by
        # coordinates, which are hard to tell apart at a glance. This
        # small plan plot draws every detected dam cluster and highlights
        # the one currently selected in the dropdown, so the user can
        # confirm they've picked the right dam by looking at its shape
        # and position rather than parsing 7-digit eastings.
        if HAS_MPL:
            self.grp_dam_overview = QGroupBox("Detected dams (selected highlighted)")
            gdo = QVBoxLayout()
            self._dam_overview_fig = Figure(figsize=(5, 3), tight_layout=True)
            self._dam_overview_canvas = _FigureCanvas(self._dam_overview_fig)
            self._dam_overview_canvas.setMinimumHeight(220)
            self._dam_overview_canvas.setSizePolicy(
                QSizePolicy.Expanding, QSizePolicy.Fixed)
            gdo.addWidget(self._dam_overview_canvas)
            self.grp_dam_overview.setLayout(gdo)
            t1.addWidget(self.grp_dam_overview)
            # Hidden until a multi-dam DXF is detected
            self.grp_dam_overview.setVisible(False)
            # Cache of cluster dicts for the current DXF (set by the
            # populate method; consumed by the render method).
            self._dam_overview_clusters = []
            self._dam_overview_rings = []

        t1.addStretch()
        tab1.setLayout(t1)
        tabs.addTab(tab1, "Input && Elevations")

        # ---- Wire the input-source radios so the right input widgets show ---
        try:
            self._update_input_source_visibility()
            self.rb_input_dxf.toggled.connect(
                self._on_input_source_changed)
            self.rb_input_polygon.toggled.connect(
                self._on_input_source_changed)
        except Exception:
            pass

        # --- NEW TAB: Geometry (DXF preview + ring assignment) ---
        tab_geom = self._build_geometry_tab()
        tabs.addTab(tab_geom, "Geometry")

        # --- TAB: Spillway ---
        tab2 = QWidget()
        t2 = QVBoxLayout()
        self.chk_spillway = QCheckBox("Generate spillway")
        self.chk_spillway.setChecked(True)
        self.chk_spillway.toggled.connect(self._toggle_spill)
        t2.addWidget(self.chk_spillway)

        self.grp_spill = QGroupBox("Spillway Parameters")
        g4 = QGridLayout()

        g4.addWidget(QLabel("Easting (NZTM2000):"), 0, 0)
        self.spn_se = QDoubleSpinBox()
        self.spn_se.setRange(0, 9999999); self.spn_se.setDecimals(1)
        self.spn_se.setValue(0.0); self.spn_se.setGroupSeparatorShown(False)
        g4.addWidget(self.spn_se, 0, 1)

        g4.addWidget(QLabel("Northing (NZTM2000):"), 1, 0)
        self.spn_sn = QDoubleSpinBox()
        self.spn_sn.setRange(0, 9999999); self.spn_sn.setDecimals(1)
        self.spn_sn.setValue(0.0); self.spn_sn.setGroupSeparatorShown(False)
        g4.addWidget(self.spn_sn, 1, 1)

        self.btn_pick = QPushButton("Pick from Map")
        self.btn_pick.setToolTip(
            "Hide dialog, click map to capture spillway location.")
        self.btn_pick.clicked.connect(self._start_pick)
        g4.addWidget(self.btn_pick, 0, 2, 2, 1)

        for row, label, attr, lo, hi, dec, default, suffix in [
            (2, "Freeboard (depth below crest):", "spn_sd", 0.01, 10, 3, 0.900, " m"),
            (3, "Flat width:", "spn_sw", 0.5, 100, 1, 20.0, " m"),
            (4, "Batter (H:V):", "spn_sb", 0.5, 10, 1, 3.0, " : 1"),
        ]:
            g4.addWidget(QLabel(label), row, 0)
            s = QDoubleSpinBox()
            s.setRange(lo, hi); s.setDecimals(dec); s.setValue(default)
            s.setSuffix(suffix)
            setattr(self, attr, s)
            g4.addWidget(s, row, 1)

        self.grp_spill.setLayout(g4)
        t2.addWidget(self.grp_spill)
        t2.addStretch()
        tab2.setLayout(t2)
        tabs.addTab(tab2, "Spillway")

        # --- LEGACY: Polygon Mode tab is no longer added to the tab
        # widget. Its widgets are still constructed (so any code path
        # that references them via self.cmb_polygon_layer etc. keeps
        # working), but the user-visible polygon workflow now lives on
        # the unified Input tab. The 'tab_poly' widget is built and
        # parented to the dialog (invisible) so widget references
        # remain valid.
        tab_poly = self._build_polygon_mode_tab()
        tab_poly.setParent(self)
        tab_poly.setVisible(False)

        # --- TAB 3: DEM & Output ---
        tab3 = QWidget()
        t3 = QVBoxLayout()

        grp_dem = QGroupBox("DEM Generation")
        g5 = QGridLayout()
        self.chk_dem = QCheckBox("Generate DEM raster")
        self.chk_dem.setChecked(True)
        g5.addWidget(self.chk_dem, 0, 0, 1, 2)
        g5.addWidget(QLabel("Cell size:"), 1, 0)
        self.spn_res = QDoubleSpinBox()
        self.spn_res.setRange(0.1, 10); self.spn_res.setValue(0.1)
        self.spn_res.setSuffix(" m")
        g5.addWidget(self.spn_res, 1, 1)
        self.chk_bl = QCheckBox("Use breaklines in TIN (recommended)")
        self.chk_bl.setChecked(True)
        g5.addWidget(self.chk_bl, 2, 0, 1, 2)
        grp_dem.setLayout(g5)
        t3.addWidget(grp_dem)

        # The legacy "Drape DEM to terrain" toggle is removed. The DEM
        # is now always clipped to the active variable-Z outer toe
        # polygon (selected via Method 1 / Method 2 radio on the
        # Geometry tab). The cell-level drape was redundant with the
        # polygon clip and produced an identical output. We retain the
        # widget references as harmless stubs so any code path that
        # still reads them gets sensible defaults.
        self.chk_drape = QCheckBox()
        self.chk_drape.setChecked(False)
        self.chk_drape.setVisible(False)
        self.cmb_drape_terrain = QComboBox()
        self.cmb_drape_terrain.addItem("(unused)", None)
        self.cmb_drape_terrain.setVisible(False)

        grp_out = QGroupBox("Output")
        g6 = QGridLayout()
        g6.addWidget(QLabel("Output directory:"), 0, 0)
        self.txt_out = QLineEdit(
            os.path.join(os.path.expanduser("~"), "dam_geometry_output"))
        g6.addWidget(self.txt_out, 0, 1)
        btn_br = QPushButton("Browse...")
        btn_br.clicked.connect(self._browse)
        g6.addWidget(btn_br, 0, 2)
        self.chk_csv = QCheckBox("Export point cloud CSV")
        self.chk_csv.setChecked(True)
        g6.addWidget(self.chk_csv, 1, 0, 1, 3)
        grp_out.setLayout(g6)
        t3.addWidget(grp_out)

        grp_adv = QGroupBox("Advanced (usually leave defaults)")
        g7 = QGridLayout()
        for row, label, attr, lo, hi, dec, default, suffix in [
            (0, "Min ring area:", "spn_ma", 1, 100000, 0, 500, " m2"),
            (1, "Min ring vertices:", "spn_mv", 3, 500, 0, 10, ""),
            (2, "Stitch tolerance:", "spn_st", 0.001, 5, 3, 0.050, " m"),
            (3, "Const Z threshold:", "spn_zt", 0.001, 5, 3, 0.050, " m"),
        ]:
            g7.addWidget(QLabel(label), row, 0)
            if dec == 0 and suffix == "":
                s = QSpinBox()
                s.setRange(int(lo), int(hi)); s.setValue(int(default))
            else:
                s = QDoubleSpinBox()
                s.setRange(lo, hi); s.setDecimals(dec); s.setValue(default)
                s.setSuffix(suffix)
            setattr(self, attr, s)
            g7.addWidget(s, row, 1)
        grp_adv.setLayout(g7)
        t3.addWidget(grp_adv)

        t3.addStretch()
        tab3.setLayout(t3)
        tabs.addTab(tab3, "DEM && Output")

        layout.addWidget(tabs)

        # Buttons
        brow = QHBoxLayout()
        btn_run = QPushButton("Run")
        btn_run.setFont(QFont("", 11, QFont.Bold))
        btn_run.setMinimumHeight(36)
        btn_run.clicked.connect(self._on_run)
        btn_cancel = QPushButton("Cancel")
        btn_cancel.clicked.connect(self.reject)
        brow.addStretch()
        brow.addWidget(btn_cancel)
        brow.addWidget(btn_run)
        layout.addLayout(brow)
        self.setLayout(layout)

    def _populate_layers(self):
        self.cmb_layer.clear()
        for lid, lyr in QgsProject.instance().mapLayers().items():
            if isinstance(lyr, QgsVectorLayer):
                self.cmb_layer.addItem(lyr.name(), lid)

    def _toggle_elev(self, auto):
        for s in (self.spn_invert, self.spn_crest, self.spn_toe):
            s.setEnabled(not auto)

    def _toggle_spill(self, on):
        self.grp_spill.setEnabled(on)

    def _browse(self):
        d = QFileDialog.getExistingDirectory(self, "Output", self.txt_out.text())
        if d:
            self.txt_out.setText(d)

    def _browse_dxf(self):
        f, _ = QFileDialog.getOpenFileName(
            self, "Select DXF or DWG File", "",
            "CAD files (*.dxf *.dwg);;DXF files (*.dxf);;"
            "DWG files (*.dwg);;All Files (*)")
        if f:
            self.txt_dxf.setText(f)
            # New file: reset the source-CRS picker to the default (assume
            # NZTM2000). The user can Smart-detect a circuit afterwards.
            try:
                self.cmb_src_crs.setCurrentIndex(0)
            except Exception:
                pass
            # Populate the layer filter BEFORE preview - if the user
            # picks a multi-dam DXF we want them to be able to filter to
            # one dam before the auto-classify runs (otherwise the
            # preview shows a jumbled set of rings from both dams).
            self._populate_dxf_layer_filter()
            self._run_preview_analysis()

    def _populate_dxf_layer_filter(self):
        """Scan the picked DXF for layers carrying line geometry and
        populate the layer-filter dropdown. Detects multi-dam files by
        looking for repeated "Dam N" tokens and offers per-dam group
        entries so the user can import one dam at a time.

        Multi-dam detection: case-insensitive search for "DAM <number>"
        in layer names. Layers sharing the same number are grouped, and
        a "Dam N (all related layers)" entry is offered for each group.
        Individual layer entries are also offered for fine control.
        Preserves the current selection if the layer still exists.
        """
        import os, re
        dxf_path = self.txt_dxf.text().strip()
        prev = self.cmb_dxf_layer_filter.currentData()
        try:
            self.cmb_dxf_layer_filter.blockSignals(True)
            self.cmb_dxf_layer_filter.clear()
            self.cmb_dxf_layer_filter.addItem("(all layers)", None)
            if not dxf_path or not os.path.isfile(dxf_path):
                return
            # Layer scan: pull all unique layer names from POLYLINE/LINE
            # entities. Reuse _parse_dxf_entities (cheap for a one-shot
            # layer enumeration; the polylines are dropped after).
            try:
                entities = _parse_dxf_entities(dxf_path)
            except Exception as e:
                LOG.warn(f"Could not scan DXF layers: {e}")
                return
            from collections import Counter
            layer_counts = Counter()
            for e in entities:
                if e.get('type') in ('POLYLINE', 'LINE') and e.get('layer'):
                    layer_counts[e['layer']] += 1
            if not layer_counts:
                return

            # ---- SPATIAL CLUSTER DETECTION (robust to mislabelling) ----
            # Layer names can lie - e.g. a "DAM 12" layer that actually
            # contains some of Dam 11's rings (CAD mislabelling). Geometry
            # location never lies, so cluster the closed-ring centroids
            # spatially: well-separated clusters are different dams,
            # regardless of layer name. This is the PREFERRED grouping;
            # the layer-name grouping below is kept as a secondary option.
            clusters = self._spatial_ring_clusters(entities)
            # Cache for the overview plot + show/hide the plot group.
            self._dam_overview_clusters = clusters
            try:
                if hasattr(self, 'grp_dam_overview'):
                    self.grp_dam_overview.setVisible(len(clusters) >= 2)
            except Exception:
                pass
            if len(clusters) >= 2:
                self.cmb_dxf_layer_filter.insertSeparator(
                    self.cmb_dxf_layer_filter.count())
                for ci, cl in enumerate(clusters):
                    cx, cy = cl['centroid']
                    self.cmb_dxf_layer_filter.addItem(
                        f"\u25c9 Dam at ({cx:,.0f}, {cy:,.0f}) "
                        f"- {cl['n']} rings [by location]",
                        {'type': 'bbox', 'bbox': cl['bbox'],
                         'label': f"Dam @ ({cx:.0f}, {cy:.0f})"})
                LOG.info(
                    f"DXF contains {len(clusters)} spatial ring clusters "
                    f"(likely {len(clusters)} dams). The 'by location' "
                    f"entries filter by physical position, so they're "
                    f"immune to layer mislabelling. Prefer these over the "
                    f"'by layer' entries if the DXF layers look mixed up.")

            # ---- Layer-name grouping (secondary) ----
            # Token = "DAM <N>" with optional spaces. Layers sharing the
            # same number are grouped. Kept as an option, but flagged as
            # potentially mislabelled when spatial clusters disagree.
            dam_pattern = re.compile(r'DAM\s*(\d+)', re.IGNORECASE)
            groups = {}  # N -> list of layer names
            for lname in layer_counts:
                m = dam_pattern.search(lname)
                if m:
                    n = int(m.group(1))
                    groups.setdefault(n, []).append(lname)

            multi_dam = len(groups) >= 2
            if multi_dam:
                self.cmb_dxf_layer_filter.insertSeparator(
                    self.cmb_dxf_layer_filter.count())
                for n in sorted(groups):
                    members = sorted(groups[n])
                    total_n = sum(layer_counts[L] for L in members)
                    self.cmb_dxf_layer_filter.addItem(
                        f"Dam {n} (all {len(members)} layers, "
                        f"{total_n} polylines) [by layer name]",
                        {'type': 'layers', 'layers': members})

            # Individual layer entries, sorted alphabetically. Skip the
            # "0" default layer and pure-numeric junk-code layers (these
            # are DXF artefacts, not real layers).
            self.cmb_dxf_layer_filter.insertSeparator(
                self.cmb_dxf_layer_filter.count())
            real_layers = [L for L in sorted(layer_counts)
                           if L.strip() and not L.strip().isdigit()
                           and not L.startswith('$$$')]
            for L in real_layers:
                self.cmb_dxf_layer_filter.addItem(
                    f"{L} ({layer_counts[L]} polylines)",
                    {'type': 'layers', 'layers': [L]})

            # Restore previous selection if it still exists; otherwise,
            # for a multi-dam DXF, auto-select the FIRST spatial cluster
            # (the largest dam by ring count). Leaving the dropdown on
            # "(all layers)" for a multi-dam file means the initial
            # preview runs on BOTH dams' rings jumbled together, which
            # auto-classify can't disambiguate - so it assigns no roles
            # and "Plot Temp Key Lines" reports "no rings available yet".
            # Defaulting to one clean dam avoids that dead state.
            selected_idx = None
            if prev is not None:
                idx = self.cmb_dxf_layer_filter.findData(prev)
                if idx >= 0:
                    selected_idx = idx
            if selected_idx is None and len(clusters) >= 2:
                # Find the first "[by location]" entry (largest cluster)
                for i in range(self.cmb_dxf_layer_filter.count()):
                    d = self.cmb_dxf_layer_filter.itemData(i)
                    if isinstance(d, dict) and d.get('type') == 'bbox':
                        selected_idx = i
                        break
            if selected_idx is not None:
                self.cmb_dxf_layer_filter.setCurrentIndex(selected_idx)
        finally:
            self.cmb_dxf_layer_filter.blockSignals(False)
        # Draw the overview now that the dropdown is populated
        try:
            self._render_dam_overview()
        except Exception:
            pass

    def _spatial_ring_clusters(self, entities, gap_factor=3.0):
        """Cluster closed-ring centroids spatially into separate dams.

        Returns a list of cluster dicts sorted by ring count (largest
        first):
          {'centroid': (cx, cy), 'bbox': (xmin, ymin, xmax, ymax),
           'n': ring_count, 'rings': [ [(x,y),...], ... ]}

        'rings' holds simplified outlines (XY only) for the overview
        plot. Method: collect every closed-polyline centroid + outline,
        then do a 1-D gap-based split on whichever axis (X or Y) has the
        larger spread - dams in a multi-dam DXF are typically laid out
        side by side, so one axis separates them cleanly. A "gap" is a
        sorted-centroid spacing more than gap_factor x the median
        spacing. Dependency-free, robust for the 2-4 dam case. Returns
        [] if fewer than 2 clusters (single dam - no split needed).
        """
        items = []  # (cx, cy, ring_xy)
        for e in entities:
            if e.get('type') != 'POLYLINE' or not e.get('closed'):
                continue
            vs = e.get('vertices', [])
            if len(vs) < 4:
                continue
            n = len(vs)
            cx = sum(v['x'] for v in vs) / n
            cy = sum(v['y'] for v in vs) / n
            # Decimate the outline for plotting (cap ~60 pts/ring so the
            # overview stays light even with 4000-vertex contours).
            target = 60
            step = max(1, (n + target - 1) // target)
            ring_xy = [(vs[i]['x'], vs[i]['y']) for i in range(0, n, step)]
            items.append((cx, cy, ring_xy))
        if len(items) < 2:
            return []

        xs = [it[0] for it in items]
        ys = [it[1] for it in items]
        spread_x = max(xs) - min(xs)
        spread_y = max(ys) - min(ys)
        axis = 0 if spread_x >= spread_y else 1
        vals = sorted(set(it[axis] for it in items))
        if len(vals) < 2:
            return []
        gaps = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
        gaps_sorted = sorted(gaps)
        med = gaps_sorted[len(gaps_sorted) // 2] if gaps_sorted else 0.0
        if med <= 0:
            med = (max(vals) - min(vals)) / max(1, len(vals))
        split_threshold = max(gap_factor * med, 50.0)
        boundaries = [vals[i + 1] for i in range(len(vals) - 1)
                      if (vals[i + 1] - vals[i]) > split_threshold]
        if not boundaries:
            return []

        edges = [-float('inf')] + boundaries + [float('inf')]
        buckets = [[] for _ in range(len(edges) - 1)]
        for it in items:
            v = it[axis]
            for bi in range(len(edges) - 1):
                if edges[bi] <= v < edges[bi + 1]:
                    buckets[bi].append(it)
                    break
        clusters = []
        for b in buckets:
            if not b:
                continue
            bxs = [p[0] for p in b]; bys = [p[1] for p in b]
            clusters.append({
                'centroid': (sum(bxs) / len(bxs), sum(bys) / len(bys)),
                'bbox': (min(bxs), min(bys), max(bxs), max(bys)),
                'n': len(b),
                'rings': [it[2] for it in b],
            })
        clusters.sort(key=lambda c: -c['n'])
        return clusters if len(clusters) >= 2 else []

    def _render_dam_overview(self):
        """Draw all detected dam clusters in the overview plot, with the
        cluster matching the current dropdown selection highlighted.

        Only meaningful when 2+ spatial clusters exist (multi-dam DXF);
        the group is hidden otherwise. The selected cluster is matched by
        comparing the dropdown's bbox payload to each cluster's bbox.
        """
        if not HAS_MPL or not hasattr(self, '_dam_overview_fig'):
            return
        clusters = getattr(self, '_dam_overview_clusters', [])
        self._dam_overview_fig.clear()
        if len(clusters) < 2:
            self._dam_overview_canvas.draw_idle()
            return
        ax = self._dam_overview_fig.add_subplot(111)
        ax.set_aspect('equal')

        # Which cluster is selected? Match the dropdown bbox payload.
        sel_bbox = None
        try:
            data = self.cmb_dxf_layer_filter.currentData()
            if isinstance(data, dict) and data.get('type') == 'bbox':
                sel_bbox = tuple(data['bbox'])
        except Exception:
            pass

        def _bbox_match(cb, sb):
            if sb is None:
                return False
            return all(abs(a - b) < 1.0 for a, b in zip(cb, sb))

        for ci, cl in enumerate(clusters):
            selected = _bbox_match(cl['bbox'], sel_bbox)
            colour = '#d62728' if selected else '#999999'
            lw = 1.4 if selected else 0.6
            alpha = 1.0 if selected else 0.5
            for ring in cl['rings']:
                if len(ring) < 2:
                    continue
                rx = [p[0] for p in ring] + [ring[0][0]]
                ry = [p[1] for p in ring] + [ring[0][1]]
                ax.plot(rx, ry, color=colour, linewidth=lw, alpha=alpha)
            # Centroid marker + label
            cx, cy = cl['centroid']
            ax.plot(cx, cy, marker='o', color=colour,
                    markersize=7 if selected else 4, alpha=alpha)
            label = f"Dam {ci + 1}\n({cx:,.0f}, {cy:,.0f})\n{cl['n']} rings"
            ax.annotate(
                label, (cx, cy), fontsize=8,
                color='black' if selected else '#666',
                weight='bold' if selected else 'normal',
                ha='center', va='bottom',
                xytext=(0, 8), textcoords='offset points')

        if sel_bbox is not None:
            ax.set_title("Selected dam highlighted in red", fontsize=9)
        else:
            ax.set_title("Pick a '[by location]' entry to highlight a dam",
                         fontsize=9)
        ax.tick_params(labelsize=7)
        ax.ticklabel_format(useOffset=False, style='plain')
        try:
            self._dam_overview_fig.tight_layout()
        except Exception:
            pass
        self._dam_overview_canvas.draw_idle()

    def _populate_raster_layers(self):
        """Re-scan the project for QgsRasterLayer entries and populate the
        terrain combo. Preserves the current selection if possible."""
        # Avoid triggering the change handler while we rebuild the list
        try:
            self.cmb_terrain.blockSignals(True)
            current_id = self.cmb_terrain.currentData()
            self.cmb_terrain.clear()
            self.cmb_terrain.addItem("(none)", None)
            for lid, lyr in QgsProject.instance().mapLayers().items():
                if isinstance(lyr, QgsRasterLayer):
                    self.cmb_terrain.addItem(lyr.name(), lid)
            if current_id is not None:
                idx = self.cmb_terrain.findData(current_id)
                if idx >= 0:
                    self.cmb_terrain.setCurrentIndex(idx)
        finally:
            self.cmb_terrain.blockSignals(False)

    def _on_terrain_changed(self, idx):
        lid = self.cmb_terrain.currentData()
        if lid is None:
            self._terrain_layer = None
        else:
            self._terrain_layer = QgsProject.instance().mapLayer(lid)
        # Re-render section view if we already have a preview. If the user
        # hasn't picked a custom section angle, also re-seed the slider to
        # the new low-to-high default for this terrain.
        if self._preview is not None:
            if self._section_angle_deg is None:
                d = self._default_section_angle_deg()
                if d is not None:
                    self.sld_section_angle.blockSignals(True)
                    self.sld_section_angle.setValue(int(round(d)) % 360)
                    self.sld_section_angle.blockSignals(False)
                    self._section_angle_deg = float(d)
                    self.lbl_section_angle.setText(f"{int(d)%360}\u00b0")
            self._render_plan_view()
            self._update_long_section()

    # =================================================================
    # Unified input-source handling (DXF or polygon, picked on Input tab)
    # =================================================================

    def _populate_polygon_layers(self, combo):
        """Populate `combo` with line/polygon vector layers from the
        QGIS project. Used by the new unified polygon-input combo on
        the Input tab."""
        try:
            combo.blockSignals(True)
            current_id = combo.currentData()
            combo.clear()
            combo.addItem("(pick a layer)", None)
            for lid, lyr in QgsProject.instance().mapLayers().items():
                if not isinstance(lyr, QgsVectorLayer):
                    continue
                wkb = lyr.geometryType()
                if wkb in (1, 2):  # 1=Line, 2=Polygon
                    combo.addItem(lyr.name(), lid)
            if current_id is not None:
                idx = combo.findData(current_id)
                if idx >= 0:
                    combo.setCurrentIndex(idx)
        finally:
            combo.blockSignals(False)

    def _on_input_source_changed(self, _checked=False):
        # Push the choice into the legacy "build mode" radios + the
        # hidden polygon-mode checkbox so all downstream code paths
        # that read self.rb_mode_polygon / self.chk_polygon_mode keep
        # working unchanged. Without this, the run pipeline reads the
        # OLD checkbox state and tries to classify a DXF that doesn't
        # exist (or ignores the polygon construction entirely).
        polygon_selected = self.rb_input_polygon.isChecked()
        try:
            if polygon_selected:
                self.rb_mode_polygon.setChecked(True)
            else:
                self.rb_mode_dxf.setChecked(True)
        except Exception:
            pass
        try:
            self.chk_polygon_mode.setChecked(polygon_selected)
        except Exception:
            pass
        self._update_input_source_visibility()

    def _update_input_source_visibility(self):
        dxf_selected = self.rb_input_dxf.isChecked()
        try:
            self.grp_input_dxf.setVisible(dxf_selected)
            self.grp_input_polygon.setVisible(not dxf_selected)
        except Exception:
            pass

    def _build_from_polygon_input(self):
        """Construct the 4 design rings from the polygon-input widgets
        and stash the result so the Geometry tab + run pipeline use
        them. Unifies the polygon path with the DXF path: by the time
        the Geometry tab renders, both paths produce the same kl dict.

        Artificial deep outer toe Z = crest_z - deep_offset. The final
        DEM clip will trim it back to natural ground via Method 2 (cut
        to terrain) on the Geometry tab.
        """
        layer_id = self.cmb_input_poly_layer.currentData()
        if not layer_id:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Pick a polygon layer first.</font>")
            return
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer is None:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Selected layer not found in "
                "project. Click Refresh.</font>")
            return

        role = self.cmb_input_poly_role.currentData()
        p_z = float(self.spn_input_poly_z.value())
        depth = float(self.spn_input_poly_depth.value())
        crest_w = float(self.spn_input_poly_crest_w.value())
        inner_hv = float(self.spn_input_poly_inner_hv.value())
        outer_hv = float(self.spn_input_poly_outer_hv.value())
        deep_offset = float(self.spn_input_poly_deep.value())

        if depth <= 0 or crest_w <= 0 or inner_hv <= 0 or outer_hv <= 0:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Depth, crest width, and both H:V "
                "values must be > 0.</font>")
            return

        # Derive design elevations from polygon role + Z + depth.
        if role in ('inner_crest', 'outer_crest'):
            crest_z = p_z
            invert_z = crest_z - depth
        elif role == 'inner_toe':
            invert_z = p_z
            crest_z = invert_z + depth
        else:  # outer_toe
            invert_z = p_z + (depth * 0.5)
            crest_z = invert_z + depth

        outer_toe_z_artificial = crest_z - deep_offset

        # Read polygon geometry
        try:
            feats = list(layer.getFeatures())
            if not feats:
                self.lbl_input_poly_status.setText(
                    "<font color='#c00'>Layer has no features.</font>")
                return
            feat = feats[0]
            geom = feat.geometry()
            if geom is None or geom.isEmpty():
                self.lbl_input_poly_status.setText(
                    "<font color='#c00'>Feature has empty geometry.</font>")
                return
            # Extract the outer ring of the polygon (or the polyline
            # vertices, for a line layer). QGIS uses MultiPolygon /
            # MultiLineString as the storage type even when the
            # geometry has only one part - so we have to handle both
            # single-part and multi-part cases. For multi-part with
            # >1 part, take the largest (by area for polygons; by
            # length for lines).
            ring_pts_q = None
            if geom.type() == 2:  # polygon-typed layer
                if geom.isMultipart():
                    try:
                        parts = geom.asMultiPolygon()
                    except Exception:
                        parts = []
                    # Each part is [outer_ring, *holes]; outer_ring is
                    # a list of QgsPointXY. Pick the part with largest
                    # outer-ring area.
                    if parts:
                        def _part_area(p):
                            if not p or not p[0]:
                                return 0.0
                            xy = [(pt.x(), pt.y()) for pt in p[0]]
                            try:
                                return abs(shoelace(xy))
                            except Exception:
                                return 0.0
                        biggest = max(parts, key=_part_area)
                        ring_pts_q = biggest[0]
                else:
                    try:
                        poly_data = geom.asPolygon()
                        if poly_data and poly_data[0]:
                            ring_pts_q = poly_data[0]
                    except Exception:
                        pass
            else:  # line-typed layer
                if geom.isMultipart():
                    try:
                        parts = geom.asMultiPolyline()
                    except Exception:
                        parts = []
                    if parts:
                        def _line_len(pts):
                            return sum(
                                math.hypot(pts[i+1].x() - pts[i].x(),
                                           pts[i+1].y() - pts[i].y())
                                for i in range(len(pts) - 1))
                        ring_pts_q = max(parts, key=_line_len)
                else:
                    try:
                        ring_pts_q = geom.asPolyline()
                    except Exception:
                        pass
            if not ring_pts_q:
                self.lbl_input_poly_status.setText(
                    "<font color='#c00'>Could not extract a ring from "
                    "the selected feature (no vertices returned).</font>")
                return
            anchor_xy = [(p.x(), p.y()) for p in ring_pts_q]
            if anchor_xy and anchor_xy[0] != anchor_xy[-1]:
                anchor_xy.append(anchor_xy[0])
            if len(anchor_xy) < 4:
                self.lbl_input_poly_status.setText(
                    f"<font color='#c00'>Polygon has only "
                    f"{len(anchor_xy)} vertices; need at least 4.</font>")
                return
        except Exception as e:
            self.lbl_input_poly_status.setText(
                f"<font color='#c00'>Failed to read polygon: {e}</font>")
            return

        try:
            ring_area = abs(shoelace([(x, y) for x, y in anchor_xy]))
        except Exception:
            ring_area = 0.0
        anchor_ring = {
            'coords': [(x, y, p_z) for x, y in anchor_xy],
            'z_mean': p_z, 'z_min': p_z, 'z_max': p_z, 'z_std': 0.0,
            'area': ring_area, 'npts': len(anchor_xy),
        }

        params = {
            'crest_z': crest_z, 'invert_z': invert_z,
            'outer_toe_z': outer_toe_z_artificial,
            'crest_width': crest_w,
            'inner_hv': inner_hv, 'outer_hv': outer_hv,
        }
        sp = float(self.spn_spacing.value()
                   if hasattr(self, 'spn_spacing') else 0.1)
        try:
            kl = construct_dam_rings_from_anchor(
                anchor_ring, role, params, sp=sp)
        except ValueError as e:
            self.lbl_input_poly_status.setText(
                f"<font color='#c00'>Construction failed: {e}</font>")
            return
        except Exception as e:
            self.lbl_input_poly_status.setText(
                f"<font color='#c00'>Construction error: {e}</font>")
            return

        # Stash via existing _constructed_kl / _preview state - same
        # path the DXF flow uses, so Geometry tab + run pipeline work
        # identically.
        self._constructed_kl = kl
        all_rings = [kl['inner_toe'], kl['inner_crest'],
                     kl['outer_crest'], kl['outer_toe']]
        self._preview = {
            'success': True, 'errors': [], 'warnings': [],
            'auto_classified': kl,
            'all_const_z': all_rings,
            'all_rings': all_rings,
            'var_z': [],
            'auto_indices': {
                'inner_toe': 0, 'inner_crest': 1,
                'outer_crest': 2, 'outer_toe': 3,
            },
            'polygon_mode': True,
        }
        self._role_assignments = dict(self._preview['auto_indices'])
        CFG['invert'] = invert_z
        CFG['crest'] = crest_z
        CFG['toe_low'] = outer_toe_z_artificial
        CFG['inner_hv'] = inner_hv
        CFG['outer_hv'] = outer_hv
        CFG['polygon_mode'] = True

        # Propagate values into the LEGACY hidden polygon-mode widgets
        # so _collect_run_settings and the run pipeline see the polygon
        # input and skip the DXF classify step. Without this, the run
        # pipeline reads the old (default 0.0 / None) values and either
        # tries to read a DXF that doesn't exist (-> "Only 2 const-Z
        # rings found" error from step3) or constructs a bogus dam.
        try:
            self.chk_polygon_mode.setChecked(True)
        except Exception:
            pass
        try:
            self.cmb_polygon_layer.setCurrentIndex(
                max(0, self.cmb_polygon_layer.findData(layer_id)))
        except Exception:
            pass
        try:
            idx_role = self.cmb_polygon_role.findData(role)
            if idx_role >= 0:
                self.cmb_polygon_role.setCurrentIndex(idx_role)
        except Exception:
            pass
        for spin_name, val in [
            ('spn_polygon_z', p_z),
            ('spn_p_crest_z', crest_z),
            ('spn_p_invert_z', invert_z),
            ('spn_p_crest_w', crest_w),
            ('spn_p_inner_hv', inner_hv),
            ('spn_p_outer_hv', outer_hv),
        ]:
            try:
                getattr(self, spin_name).setValue(val)
            except Exception:
                pass
        # Set the artificial-deep target via overshoot spinbox if present
        try:
            self.spn_p_overshoot.setValue(deep_offset)
        except Exception:
            pass

        try: self._refresh_ring_table()
        except Exception: pass
        try: self._render_plan_view()
        except Exception: pass
        try: self._update_long_section()
        except Exception: pass

        # Stash the artificial-deep outer toe coords on a stable key
        # (nominal_const_coords) so the Reset button on the Geometry
        # tab can restore this state after Method 2 (cut to terrain) or
        # a z_offset shift mangles things. Keeping the same name the
        # cut_outer_toe_to_terrain function uses means its existing
        # "stash on first cut" logic becomes a no-op for polygon mode
        # (preserves the artificial deep, not the const-Z step4c output).
        try:
            ot_dict = kl['outer_toe']
            ot_dict['nominal_const_coords'] = [
                (c[0], c[1], c[2]) for c in ot_dict.get('coords', [])
                if len(c) >= 3]
            ot_dict['nominal_const_z'] = ot_dict.get('z_mean')
        except Exception:
            pass

        # NO auto-Method-2. The user wants to see the artificial deep
        # toe state first, then optionally balance cut/fill, then
        # optionally snap to terrain. Each step is a deliberate click.
        self.lbl_input_poly_status.setText(
            f"<font color='#080'>OK. Built 4 rings: invert "
            f"{invert_z:.2f} m, crest {crest_z:.2f} m, artificial outer "
            f"toe {outer_toe_z_artificial:.2f} m.</font><br>"
            f"<i>Switch to the Geometry tab to:<br>"
            f"&nbsp;&nbsp;1. Inspect the artificial deep toe state (now)<br>"
            f"&nbsp;&nbsp;2. Optionally click 'Snap to balance cut / fill' "
            f"to find a crest elevation<br>"
            f"&nbsp;&nbsp;3. Optionally click 'Run Method 2 now' on the "
            f"Outer toe method group to trim to terrain<br>"
            f"&nbsp;&nbsp;4. Click 'Reset to artificial deep toe' to "
            f"start over if things go haywire</i>")

    def _snap_polygon_depth_to_cut_fill_balance(self):
        """Sweep dam depth values to find the one where fill volume
        (embankment above natural ground) equals cut volume (reservoir
        cut + embankment cut below natural ground) times the user's
        bulking-factor multiplier.

        Useful when the user has a polygon at one of the design rings
        but no firm depth in mind - this finds a depth that balances
        material on/off site, which is typically the cheapest design.

        Multiplier semantics:
            mult = 1.0   -> equal cut and fill
            mult = 0.85  -> 1 m3 cut yields 0.85 m3 of fill (typical for
                            most embankment materials after compaction)
        """
        # Require terrain raster
        terrain_layer = self._terrain_layer
        if terrain_layer is None:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Snap needs a terrain raster - pick "
                "one on this tab first.</font>")
            return
        layer_id = self.cmb_input_poly_layer.currentData()
        if not layer_id:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Pick a polygon layer first.</font>")
            return
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer is None:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Polygon layer not found in project."
                "</font>")
            return

        mult = float(self.spn_input_poly_cf_mult.value())
        role = self.cmb_input_poly_role.currentData()
        p_z = float(self.spn_input_poly_z.value())
        crest_w = float(self.spn_input_poly_crest_w.value())
        inner_hv = float(self.spn_input_poly_inner_hv.value())
        outer_hv = float(self.spn_input_poly_outer_hv.value())

        # Read polygon coords once
        try:
            feats = list(layer.getFeatures())
            if not feats:
                self.lbl_input_poly_status.setText(
                    "<font color='#c00'>Layer has no features.</font>")
                return
            geom = feats[0].geometry()
            if geom is None or geom.isEmpty():
                self.lbl_input_poly_status.setText(
                    "<font color='#c00'>Feature has empty geometry.</font>")
                return
            if geom.type() == 2:
                if geom.isMultipart():
                    parts = geom.asMultiPolygon()
                    if not parts:
                        self.lbl_input_poly_status.setText(
                            "<font color='#c00'>No usable polygon parts."
                            "</font>")
                        return
                    ring_pts_q = max(parts,
                        key=lambda p: abs(shoelace(
                            [(pt.x(), pt.y()) for pt in p[0]])) if p[0] else 0)[0]
                else:
                    ring_pts_q = geom.asPolygon()[0]
            else:
                ring_pts_q = (geom.asMultiPolyline()[0]
                              if geom.isMultipart()
                              else geom.asPolyline())
            anchor_xy = [(p.x(), p.y()) for p in ring_pts_q]
            if anchor_xy and anchor_xy[0] != anchor_xy[-1]:
                anchor_xy.append(anchor_xy[0])
        except Exception as e:
            self.lbl_input_poly_status.setText(
                f"<font color='#c00'>Failed to read polygon: {e}</font>")
            return

        # Sweep candidate depths. Range 1 m to 30 m at 0.5 m resolution
        # is a sensible search space for engineering dams; refine to 0.1 m
        # around the best value.
        best_depth = None
        best_score = float('inf')
        best_cut = best_fill = 0.0
        depths = [round(d * 0.5, 2) for d in range(2, 60)]  # 1.0 .. 29.5
        # Coarse pass
        for depth in depths:
            try:
                cut, fill = self._compute_cut_fill_for_depth(
                    anchor_xy, role, p_z, depth, crest_w,
                    inner_hv, outer_hv, terrain_layer)
            except Exception:
                continue
            if cut <= 0:
                # No reservoir cut yet - dam is too small
                continue
            target_fill = cut * mult
            score = abs(fill - target_fill)
            if score < best_score:
                best_score = score
                best_depth = depth
                best_cut = cut
                best_fill = fill
        if best_depth is None:
            self.lbl_input_poly_status.setText(
                "<font color='#c00'>Snap failed - no candidate depth "
                "produced a sensible cut/fill balance. Try a different "
                "polygon role or check the terrain raster.</font>")
            return
        # Refine pass: ±0.5 m around best at 0.1 m
        fine_lo = max(0.5, best_depth - 0.5)
        fine_hi = best_depth + 0.5
        d = fine_lo
        while d <= fine_hi:
            try:
                cut, fill = self._compute_cut_fill_for_depth(
                    anchor_xy, role, p_z, d, crest_w,
                    inner_hv, outer_hv, terrain_layer)
                if cut > 0:
                    score = abs(fill - cut * mult)
                    if score < best_score:
                        best_score = score
                        best_depth = round(d, 2)
                        best_cut = cut
                        best_fill = fill
            except Exception:
                pass
            d = round(d + 0.1, 3)
        # Push the best depth into the spinbox and rebuild
        try:
            self.spn_input_poly_depth.setValue(best_depth)
        except Exception:
            pass
        self.lbl_input_poly_status.setText(
            f"<font color='#080'>Snap: depth = {best_depth:.2f} m. "
            f"Cut = {best_cut:,.0f} m\u00b3, fill = {best_fill:,.0f} "
            f"m\u00b3 (ratio fill/cut = "
            f"{(best_fill/best_cut if best_cut > 0 else 0):.2f}; "
            f"target {mult:.2f}). Rebuilding...</font>")
        # Rebuild with the new depth
        try:
            self._build_from_polygon_input()
        except Exception as e:
            self.lbl_input_poly_status.setText(
                f"<font color='#c00'>Rebuild after snap failed: {e}"
                f"</font>")

    def _compute_cut_fill_for_depth(self, anchor_xy, role, p_z, depth,
                                      crest_w, inner_hv, outer_hv,
                                      terrain_layer, sample_res=2.0):
        """Compute (cut_volume, fill_volume) for a candidate dam.

        Algorithm:
          1. Derive crest_z and invert_z from polygon role + Z + depth
          2. Construct the 4 rings analytically
          3. Sample terrain on a grid covering the outer_toe footprint
          4. For each grid cell:
              - If inside inner_toe: dam_z = invert_z (reservoir floor)
              - Else: dam_z follows the design batter slope from the
                nearest crest down to the toe; clamp at invert_z on
                inner side and at toe_low on outer side
              - fill += max(0, dam_z - terrain_z) * cell_area
              - cut  += max(0, terrain_z - dam_z) * cell_area
        Returns (cut, fill) in cubic metres.
        """
        # Derive elevations
        if role in ('inner_crest', 'outer_crest'):
            crest_z = p_z
            invert_z = crest_z - depth
        elif role == 'inner_toe':
            invert_z = p_z
            crest_z = invert_z + depth
        else:  # outer_toe
            invert_z = p_z + depth * 0.5
            crest_z = invert_z + depth
        artificial_otz = crest_z - 15.0  # not used for volumes but needed by construct

        try:
            anchor_ring = {
                'coords': [(x, y, p_z) for x, y in anchor_xy],
                'z_mean': p_z, 'z_min': p_z, 'z_max': p_z, 'z_std': 0.0,
                'area': abs(shoelace([(x, y) for x, y in anchor_xy])),
                'npts': len(anchor_xy),
            }
            params = {
                'crest_z': crest_z, 'invert_z': invert_z,
                'outer_toe_z': artificial_otz,
                'crest_width': crest_w,
                'inner_hv': inner_hv, 'outer_hv': outer_hv,
            }
            kl = construct_dam_rings_from_anchor(
                anchor_ring, role, params, sp=1.0)
        except Exception:
            return 0.0, 0.0

        # Build polygons and bounding box
        try:
            ot_coords = kl['outer_toe']['coords']
            it_coords = kl['inner_toe']['coords']
            ot_q = [QgsPointXY(c[0], c[1]) for c in ot_coords]
            it_q = [QgsPointXY(c[0], c[1]) for c in it_coords]
            ot_poly = QgsGeometry.fromPolygonXY([ot_q])
            it_poly = QgsGeometry.fromPolygonXY([it_q])
            # Also build inner_crest and outer_crest polygons for proper
            # crest-surface detection (see _snap_z_offset_to_cut_fill_balance
            # for why the d_in < d_out heuristic is wrong on crest cells).
            ic_q_inner = [QgsPointXY(c[0], c[1])
                          for c in kl['inner_crest']['coords']]
            oc_q_outer = [QgsPointXY(c[0], c[1])
                          for c in kl['outer_crest']['coords']]
            ic_poly = QgsGeometry.fromPolygonXY([ic_q_inner])
            oc_poly = QgsGeometry.fromPolygonXY([oc_q_outer])
        except Exception:
            return 0.0, 0.0

        xs = [c[0] for c in ot_coords]; ys = [c[1] for c in ot_coords]
        xmin, xmax = min(xs), max(xs)
        ymin, ymax = min(ys), max(ys)

        oc_xy = [(c[0], c[1]) for c in kl['outer_crest']['coords']]
        ic_xy = [(c[0], c[1]) for c in kl['inner_crest']['coords']]

        cell_area = sample_res * sample_res
        cut_total = 0.0
        fill_total = 0.0
        dp = terrain_layer.dataProvider()
        if dp is None:
            return 0.0, 0.0

        y = ymin
        while y <= ymax:
            x = xmin
            while x <= xmax:
                p = QgsPointXY(x, y)
                pg = QgsGeometry.fromPointXY(p)
                if not ot_poly.contains(pg):
                    x += sample_res
                    continue
                try:
                    val, ok = dp.sample(p, 1)
                except Exception:
                    ok = False; val = None
                if not ok or val is None:
                    x += sample_res
                    continue
                terrain_z = float(val)

                # Piecewise dam profile based on which ring polygon
                # contains the cell. See _snap_z_offset_to_cut_fill_balance
                # for the rationale.
                if it_poly.contains(pg):
                    # Reservoir floor - count regardless of where terrain is
                    dam_z = invert_z
                    is_reservoir = True
                elif ic_poly.contains(pg):
                    # Inner batter
                    d_inner = self._min_dist_to_polyline(x, y, ic_xy)
                    dam_z = max(crest_z - d_inner / inner_hv, invert_z)
                    is_reservoir = False
                elif oc_poly.contains(pg):
                    # Crest surface (flat top)
                    dam_z = crest_z
                    is_reservoir = False
                else:
                    # Outer batter
                    d_outer = self._min_dist_to_polyline(x, y, oc_xy)
                    dam_z = crest_z - d_outer / outer_hv
                    is_reservoir = False
                # Reservoir cells contribute regardless of sign.
                # Embankment cells contribute fill only when dam > terrain
                # (i.e. embankment exists there); cells where design batter
                # projects below ground are OUTSIDE the actual dam and
                # are skipped (no spurious cut).
                if is_reservoir:
                    if terrain_z > dam_z:
                        cut_total += (terrain_z - dam_z) * cell_area
                    elif dam_z > terrain_z:
                        fill_total += (dam_z - terrain_z) * cell_area
                else:
                    if dam_z > terrain_z:
                        fill_total += (dam_z - terrain_z) * cell_area
                    # else: cell is outside actual dam, skip
                x += sample_res
            y += sample_res
        return cut_total, fill_total

    @staticmethod
    def _min_dist_to_polyline(x, y, polyline_xy):
        """Shortest distance from point (x, y) to a polyline (list of
        (x, y) tuples). Used by the cut/fill snap to find which side of
        the dam crest a sample point falls on."""
        best = float('inf')
        for i in range(len(polyline_xy) - 1):
            ax, ay = polyline_xy[i]
            bx, by = polyline_xy[i + 1]
            ex = bx - ax; ey = by - ay
            l2 = ex * ex + ey * ey
            if l2 < 1e-10:
                d = math.hypot(x - ax, y - ay)
            else:
                t = ((x - ax) * ex + (y - ay) * ey) / l2
                t = max(0.0, min(1.0, t))
                px = ax + t * ex; py = ay + t * ey
                d = math.hypot(x - px, y - py)
            if d < best:
                best = d
        return best

    def _on_polygon_terrain_changed(self, idx):
        try:
            lid = self.cmb_polygon_terrain.currentData()
        except Exception:
            lid = None
        if lid is None:
            # Fall back to Input tab terrain
            try:
                input_lid = self.cmb_terrain.currentData()
                self._terrain_layer = (
                    QgsProject.instance().mapLayer(input_lid)
                    if input_lid else None)
            except Exception:
                pass
        else:
            self._terrain_layer = QgsProject.instance().mapLayer(lid)
        # Refresh long section so the new terrain shows immediately
        try:
            self._update_long_section()
        except Exception:
            pass
        try:
            self._render_plan_view()
        except Exception:
            pass

    # =================================================================
    # Polygon Mode tab construction (Phase 3 - last-resort DEM builder)
    # =================================================================
    def _build_polygon_mode_tab(self):
        # Outer wrapper: tab → scroll area → content widget. The scroll
        # area ensures every control in the dense polygon-mode tab
        # remains accessible if the user shrinks the dialog below the
        # tab's natural height.
        tab = QWidget()
        tab_layout = QVBoxLayout()
        tab_layout.setContentsMargins(0, 0, 0, 0)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        content = QWidget()
        outer = QVBoxLayout()

        # Status indicator (driven by the mode pill, no longer a checkbox)
        self.lbl_polygon_status = QLabel(
            "<b>Polygon Mode is INACTIVE.</b> "
            "Switch to 'Polygon + terrain drape' on the Build mode pill "
            "above to activate this tab.")
        self.lbl_polygon_status.setWordWrap(True)
        self.lbl_polygon_status.setStyleSheet(
            "QLabel { background-color: #fff3cd; padding: 6px; "
            "border: 1px solid #ffeaa7; border-radius: 3px; }")
        outer.addWidget(self.lbl_polygon_status)

        # Hidden checkbox kept for backwards-compat with the existing
        # _on_run code path. Driven by the mode pill, not the user.
        self.chk_polygon_mode = QCheckBox("(internal)")
        self.chk_polygon_mode.setChecked(False)
        self.chk_polygon_mode.setVisible(False)
        outer.addWidget(self.chk_polygon_mode)

        info = QLabel(
            "<i>Polygon Mode is the last-resort dam-DEM builder. Provide "
            "a single closed polygon (any QGIS line or polygon layer), "
            "say which design ring it represents (inner toe, inner crest, "
            "or outer crest) and its elevation, fill in the design "
            "parameters, and the tool will construct the 4 design rings "
            "analytically. The outer batter is deliberately overshot "
            "below natural ground; the 'Drape DEM to terrain' step on "
            "the DEM &amp; Output tab then clips the result so the dam "
            "drapes onto real terrain.</i>")
        info.setWordWrap(True)
        outer.addWidget(info)

        # Polygon source
        grp_src = QGroupBox("1. Polygon source")
        gs = QGridLayout()
        gs.addWidget(QLabel("Polygon layer:"), 0, 0)
        self.cmb_polygon_layer = QComboBox()
        # Populate with line + polygon vector layers
        for lid, lyr in QgsProject.instance().mapLayers().items():
            if isinstance(lyr, QgsVectorLayer):
                gtype = lyr.geometryType()
                # 1=Line, 2=Polygon
                if gtype in (1, 2):
                    self.cmb_polygon_layer.addItem(
                        f"{lyr.name()} ({'line' if gtype == 1 else 'polygon'})",
                        lid)
        if self.cmb_polygon_layer.count() == 0:
            self.cmb_polygon_layer.addItem("(no line/polygon layers loaded)", None)
        gs.addWidget(self.cmb_polygon_layer, 0, 1, 1, 2)

        gs.addWidget(QLabel("Feature (FID):"), 1, 0)
        self.spn_polygon_fid = QSpinBox()
        self.spn_polygon_fid.setRange(-1, 99999)
        self.spn_polygon_fid.setValue(-1)
        self.spn_polygon_fid.setSpecialValueText("(use first feature)")
        self.spn_polygon_fid.setToolTip(
            "Feature ID to use. -1 (default) uses the first feature in "
            "the layer.")
        gs.addWidget(self.spn_polygon_fid, 1, 1)
        grp_src.setLayout(gs)
        outer.addWidget(grp_src)

        # Polygon role + elevation
        grp_role = QGroupBox("2. What does this polygon represent?")
        gr = QGridLayout()
        gr.addWidget(QLabel("Role:"), 0, 0)
        self.cmb_polygon_role = QComboBox()
        self.cmb_polygon_role.addItem("Inner crest (top of upstream batter)",
                                      "inner_crest")
        self.cmb_polygon_role.addItem("Outer crest (top of downstream batter)",
                                      "outer_crest")
        self.cmb_polygon_role.addItem("Inner toe (bottom of upstream batter)",
                                      "inner_toe")
        gr.addWidget(self.cmb_polygon_role, 0, 1)

        gr.addWidget(QLabel("Polygon elevation (m, NZVD2016):"), 1, 0)
        self.spn_polygon_z = QDoubleSpinBox()
        self.spn_polygon_z.setRange(-100, 3000)
        self.spn_polygon_z.setDecimals(3)
        self.spn_polygon_z.setValue(0.0)
        self.spn_polygon_z.setSuffix(" m")
        gr.addWidget(self.spn_polygon_z, 1, 1)
        grp_role.setLayout(gr)
        outer.addWidget(grp_role)

        # Design parameters
        grp_par = QGroupBox("3. Design parameters")
        gp = QGridLayout()
        for row, label, attr, lo, hi, dec, default, suffix in [
            (0, "Crest elevation:",  "spn_p_crest_z",  -100, 3000, 3,  0.0, " m"),
            (1, "Invert elevation (inner toe):",
                                     "spn_p_invert_z", -100, 3000, 3,  0.0, " m"),
            (2, "Crest width:",      "spn_p_crest_w",   0.1,  100, 2,  6.0, " m"),
            (3, "Inner batter H:V:", "spn_p_inner_hv",  0.1,   20, 2,  3.0, " : 1"),
            (4, "Outer batter H:V:", "spn_p_outer_hv",  0.1,   20, 2,  3.0, " : 1"),
        ]:
            gp.addWidget(QLabel(label), row, 0)
            s = QDoubleSpinBox()
            s.setRange(lo, hi); s.setDecimals(dec); s.setValue(default)
            s.setSuffix(suffix)
            setattr(self, attr, s)
            gp.addWidget(s, row, 1)

        gp.addWidget(QLabel("Outer batter overshoot below terrain:"), 5, 0)
        self.spn_p_overshoot = QDoubleSpinBox()
        self.spn_p_overshoot.setRange(1.0, 100.0)
        self.spn_p_overshoot.setDecimals(1)
        self.spn_p_overshoot.setValue(15.0)
        self.spn_p_overshoot.setSuffix(" m")
        self.spn_p_overshoot.setToolTip(
            "How far below the lowest terrain elevation near the dam to "
            "project the artificial outer toe. Larger values guarantee "
            "the drape step clips properly on undulating ground; smaller "
            "values mean less wasted DEM area. 15 m is a safe default.")
        gp.addWidget(self.spn_p_overshoot, 5, 1)

        gp.addWidget(QLabel(
            "Terrain raster (for Method 2 terrain intersection):"), 6, 0)
        self.cmb_polygon_terrain = QComboBox()
        self.cmb_polygon_terrain.addItem("(use Input tab terrain)", None)
        for lid, lyr in QgsProject.instance().mapLayers().items():
            if isinstance(lyr, QgsRasterLayer):
                self.cmb_polygon_terrain.addItem(lyr.name(), lid)
        # When the polygon-mode terrain is changed, also push it into
        # self._terrain_layer so the long section's ground line samples
        # the right raster.
        self.cmb_polygon_terrain.currentIndexChanged.connect(
            self._on_polygon_terrain_changed)
        gp.addWidget(self.cmb_polygon_terrain, 6, 1)
        grp_par.setLayout(gp)
        outer.addWidget(grp_par)

        note = QLabel(
            "<i>Spillway: configured on the Spillway tab. Use the Pick "
            "from Map button there to select a spillway location near "
            "the inner crest after enabling polygon mode.<br><br>"
            "After 'Preview Construction', the rendered dam DEM is "
            "automatically clipped to the active variable-Z outer toe "
            "polygon (Method 1 or Method 2 - selectable on the Geometry "
            "tab). No separate drape step.</i>")
        note.setWordWrap(True)
        outer.addWidget(note)

        # Preview button - constructs rings analytically and pushes them
        # into the Geometry tab visuals (plan view + long section) so the
        # user can verify before pressing Run.
        prv_row = QHBoxLayout()
        self.btn_polygon_preview = QPushButton("Preview Construction")
        self.btn_polygon_preview.setToolTip(
            "Read the polygon + parameters above and analytically "
            "construct the 4 design rings. Pushes the result into the "
            "Geometry tab so you can see the plan view + long section "
            "before running the full pipeline.")
        self.btn_polygon_preview.clicked.connect(self._preview_polygon_construction)
        self.lbl_polygon_preview_status = QLabel(
            "<i>(no preview yet)</i>")
        self.lbl_polygon_preview_status.setWordWrap(True)
        prv_row.addWidget(self.btn_polygon_preview)
        prv_row.addWidget(self.lbl_polygon_preview_status, stretch=1)
        outer.addLayout(prv_row)

        # Step 2: Cut to terrain. This intersects the constructed outer
        # batter with the terrain raster, producing a variable-Z outer
        # toe. The long section then shows the dam as it actually sits
        # cut into terrain, with the orange dots varying as the section
        # is rotated.
        cut_row = QHBoxLayout()
        self.btn_polygon_cut = QPushButton("Cut to terrain")
        self.btn_polygon_cut.setToolTip(
            "Step 2: walk outward from the outer crest at design slope "
            "until each ray hits terrain. The intersections become the "
            "variable-Z outer toe. After this the long section shows "
            "the dam cut into terrain - rotate the section line to see "
            "how the cut depth varies around the perimeter. Press "
            "Preview Construction first.")
        self.btn_polygon_cut.clicked.connect(
            self._cut_outer_toe_to_terrain_button)
        self.lbl_polygon_cut_status = QLabel(
            "<i>(run 'Preview Construction' first, then 'Cut to terrain')"
            "</i>")
        self.lbl_polygon_cut_status.setWordWrap(True)
        cut_row.addWidget(self.btn_polygon_cut)
        cut_row.addWidget(self.lbl_polygon_cut_status, stretch=1)
        outer.addLayout(cut_row)

        outer.addStretch()
        content.setLayout(outer)
        scroll.setWidget(content)
        tab_layout.addWidget(scroll)
        tab.setLayout(tab_layout)
        return tab

    # =================================================================
    # Mode pill handler + polygon-mode preview
    # =================================================================
    def _on_mode_changed(self, btn):
        """Mode pill click handler. Updates the hidden polygon-mode
        checkbox (which _on_run reads), the status label on the Polygon
        Mode tab, and tab visibility/focus."""
        is_polygon = self.rb_mode_polygon.isChecked()
        is_anchor = self.rb_mode_anchor.isChecked()
        is_dxf = self.rb_mode_dxf.isChecked()

        # The hidden checkbox is now the source-of-truth driver of the
        # polygon-mode pipeline branch in run(); keep it synced.
        self.chk_polygon_mode.setChecked(is_polygon)

        # Update the Polygon Mode tab status banner
        if is_polygon:
            self.lbl_polygon_status.setText(
                "<b>Polygon Mode is ACTIVE.</b> Run will use the polygon "
                "+ parameters below, ignoring any DXF/layer input. "
                "Press 'Preview Construction' to see the rings before "
                "running.")
            self.lbl_polygon_status.setStyleSheet(
                "QLabel { background-color: #d4edda; padding: 6px; "
                "border: 1px solid #c3e6cb; border-radius: 3px; }")
            # Jump to the Polygon Mode tab so the user can fill it in
            try:
                idx = self._tabs.indexOf(
                    self._tabs.findChild(QWidget, ""))  # placeholder
            except Exception:
                idx = -1
            # Better: scan tabs by title
            for ti in range(self._tabs.count()):
                if "Polygon" in self._tabs.tabText(ti):
                    self._tabs.setCurrentIndex(ti)
                    break
        else:
            self.lbl_polygon_status.setText(
                "<b>Polygon Mode is INACTIVE.</b> Switch to "
                "'Polygon + terrain drape' on the Build mode pill above "
                "to activate this tab.")
            self.lbl_polygon_status.setStyleSheet(
                "QLabel { background-color: #fff3cd; padding: 6px; "
                "border: 1px solid #ffeaa7; border-radius: 3px; }")
            # Tidy up any polygon-preview map layers when leaving the mode
            try:
                self._clear_polygon_preview_layers()
            except Exception:
                pass

        # In anchor mode, auto-tick "Use Constructed for Run" if a
        # constructed kl exists; the user can still untick it.
        if is_anchor:
            try:
                if self._constructed_kl is not None:
                    self.chk_use_constructed.setChecked(True)
                # Jump to Geometry tab where the build-up panel lives
                for ti in range(self._tabs.count()):
                    if self._tabs.tabText(ti) == "Geometry":
                        self._tabs.setCurrentIndex(ti)
                        break
            except Exception:
                pass

        # DXF mode: nothing to change beyond the pill, the existing
        # Input + Geometry tabs continue to drive the flow.

    def _preview_polygon_construction(self):
        """Read polygon + params, construct the 4 rings analytically, and
        push them into the Geometry tab visuals (plan view + long section)
        so the user can verify before Run."""
        try:
            # Gather inputs
            layer_id = self.cmb_polygon_layer.currentData()
            if not layer_id:
                self.lbl_polygon_preview_status.setText(
                    "<font color='#c00'>No polygon layer selected.</font>")
                return
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer is None:
                self.lbl_polygon_preview_status.setText(
                    "<font color='#c00'>Polygon layer not in project "
                    "anymore.</font>")
                return

            # Pick the feature
            fid_val = self.spn_polygon_fid.value()
            target_fid = None if fid_val < 0 else int(fid_val)
            feature = None
            for f in layer.getFeatures():
                if target_fid is None or f.id() == target_fid:
                    feature = f
                    break
            if feature is None:
                self.lbl_polygon_preview_status.setText(
                    "<font color='#c00'>No matching feature.</font>")
                return

            geom = feature.geometry()
            if geom is None or geom.isEmpty():
                self.lbl_polygon_preview_status.setText(
                    "<font color='#c00'>Selected feature has empty "
                    "geometry.</font>")
                return

            # Extract coords (same logic as step1c)
            coords_xy = []
            gtype = geom.type()
            if gtype == 1:
                if geom.isMultipart():
                    pl = geom.asMultiPolyline()
                    if pl and pl[0]:
                        coords_xy = [(p.x(), p.y()) for p in pl[0]]
                else:
                    coords_xy = [(p.x(), p.y()) for p in geom.asPolyline()]
            elif gtype == 2:
                if geom.isMultipart():
                    mp = geom.asMultiPolygon()
                    if mp and mp[0] and mp[0][0]:
                        coords_xy = [(p.x(), p.y()) for p in mp[0][0]]
                else:
                    pg = geom.asPolygon()
                    if pg and pg[0]:
                        coords_xy = [(p.x(), p.y()) for p in pg[0]]
            if len(coords_xy) < 4:
                self.lbl_polygon_preview_status.setText(
                    f"<font color='#c00'>Polygon has only "
                    f"{len(coords_xy)} vertices.</font>")
                return
            if coords_xy[0] != coords_xy[-1]:
                coords_xy.append(coords_xy[0])

            # Reproject to NZTM2000 if needed
            layer_crs = layer.crs()
            target_crs = QgsCoordinateReferenceSystem(f"EPSG:{CRS_EPSG}")
            if layer_crs.isValid() and layer_crs != target_crs:
                xform = QgsCoordinateTransform(
                    layer_crs, target_crs, QgsProject.instance())
                reproj = []
                for (x, y) in coords_xy:
                    pt = xform.transform(QgsPointXY(x, y))
                    reproj.append((pt.x(), pt.y()))
                coords_xy = reproj
                if coords_xy[0] != coords_xy[-1]:
                    coords_xy.append(coords_xy[0])

            # Build pseudo-ring + params
            p_z = float(self.spn_polygon_z.value())
            role = self.cmb_polygon_role.currentData()
            coords3d = [(x, y, p_z) for (x, y) in coords_xy]
            polygon_ring = {
                'coords': coords3d,
                'z_mean': p_z, 'z_min': p_z, 'z_max': p_z, 'z_std': 0.0,
                'area': shoelace(coords3d), 'npts': len(coords3d),
            }

            # Auto-couple polygon elevation to role's design elevation
            crest_z = float(self.spn_p_crest_z.value())
            invert_z = float(self.spn_p_invert_z.value())
            if role in ('inner_crest', 'outer_crest'):
                if abs(crest_z - p_z) > 0.01:
                    crest_z = p_z
            elif role == 'inner_toe':
                if abs(invert_z - p_z) > 0.01:
                    invert_z = p_z

            # Sanity check: invert and crest must form a sensible dam.
            # A common mistake is leaving the invert spinbox at its
            # default 0.0 m while the crest is at e.g. 605 m, which
            # makes the constructor compute a 605 m embankment and
            # offsets of >1500 m on each ring. Catch that here with a
            # clear message rather than letting the construct produce
            # a giant useless geometry.
            depth = crest_z - invert_z
            if depth <= 0:
                self.lbl_polygon_preview_status.setText(
                    f"<font color='#c00'>Crest elevation ({crest_z:.2f} m) "
                    f"must be > invert elevation ({invert_z:.2f} m). Set "
                    f"both values sensibly on the Polygon Mode tab.</font>")
                return
            if depth > 100:
                self.lbl_polygon_preview_status.setText(
                    f"<font color='#c00'>Implausible dam depth "
                    f"({depth:.1f} m = crest {crest_z:.2f} \u2212 invert "
                    f"{invert_z:.2f}). This is usually a missing invert "
                    f"elevation - the default 0.00 m is being used. Set "
                    f"the invert spinbox to your actual reservoir invert "
                    f"on the Polygon Mode tab before previewing.</font>")
                return

            # Sample terrain min for artificial outer toe
            tid = self.cmb_polygon_terrain.currentData()
            terrain = (QgsProject.instance().mapLayer(tid) if tid
                       else self._terrain_layer)
            overshoot = float(self.spn_p_overshoot.value())
            tmin = _terrain_min_in_bbox(terrain, coords3d) if terrain else None
            if tmin is not None:
                artificial_otz = tmin - overshoot
            else:
                artificial_otz = invert_z - overshoot

            params = {
                'crest_z': crest_z,
                'invert_z': invert_z,
                'outer_toe_z': artificial_otz,
                'crest_width': float(self.spn_p_crest_w.value()),
                'inner_hv': float(self.spn_p_inner_hv.value()),
                'outer_hv': float(self.spn_p_outer_hv.value()),
            }
            sp = 2.0  # preview spacing - coarse is fine for visuals

            kl = construct_dam_rings_from_anchor(
                polygon_ring, role, params, sp=sp)

            # Push into the visual state. Set _constructed_kl + a minimal
            # _preview so the existing Geometry tab visuals render.
            self._constructed_kl = kl
            rings = [kl['inner_toe'], kl['inner_crest'],
                     kl['outer_crest'], kl['outer_toe']]
            self._preview = {
                'success': True,
                'errors': [],
                'warnings': [],
                'all_const_z': rings,
                'var_z': [],
                'all_rings': rings,
                'n_const': 4,
                'auto_classified': kl,
                'auto_indices': {
                    'inner_toe': 0, 'inner_crest': 1,
                    'outer_crest': 2, 'outer_toe': 3,
                },
            }
            # Force the Use-Constructed checkbox so the visuals + Run use
            # the polygon-mode rings, not the (non-existent) DXF rings.
            try:
                self.chk_use_constructed.setChecked(True)
            except Exception:
                pass

            # Refresh the visuals
            try:
                self._render_plan_view()
            except Exception as e:
                self.lbl_polygon_preview_status.setText(
                    f"<font color='#a60'>Construction succeeded but plan-"
                    f"view render failed: {e}</font>")
                return
            try:
                self._update_long_section()
            except Exception:
                pass  # long-section needs terrain etc., not fatal

            # Push the constructed rings onto the QGIS map canvas as
            # temporary vector layers, so the user can see WHERE each
            # ring sits when they click "Pick from Map" for the spillway.
            # Without this, the Pick tool gives them no visual reference
            # in polygon mode (their only loaded data is the input
            # polygon + terrain raster - they wouldn't know where the
            # inner crest actually is).
            try:
                self._update_polygon_preview_layers(kl)
            except Exception as e:
                # Non-fatal - matplotlib visuals still work
                print(f"[Polygon Preview] Could not push layers to map: {e}")

            self.lbl_polygon_preview_status.setText(
                f"<font color='#080'>OK.</font> Built rings: "
                f"inner_toe z={kl['inner_toe']['z_mean']:.2f}, "
                f"inner_crest z={kl['inner_crest']['z_mean']:.2f}, "
                f"outer_crest z={kl['outer_crest']['z_mean']:.2f}, "
                f"outer_toe z={kl['outer_toe']['z_mean']:.2f} "
                f"(artificial, will drape to terrain). "
                f"Rings added to map as 'Polygon Preview - *'. "
                f"Use them as a visual reference when picking the "
                f"spillway location on the map.")
        except Exception as e:
            import traceback
            traceback.print_exc()
            self.lbl_polygon_preview_status.setText(
                f"<font color='#c00'>Preview failed: {e}</font>")

    def _update_polygon_preview_layers(self, kl):
        """Push the four constructed rings to the QGIS map canvas as
        memory vector layers so the user has a visual reference for the
        spillway pick. Cleans up any previous preview layers first.

        Layer naming: 'Polygon Preview - inner_crest', etc. Stored in
        self._polygon_preview_layer_ids so we can remove them next time
        Preview is clicked or the mode pill is flipped away from polygon.
        """
        # Cleanup previous preview layers
        existing = getattr(self, '_polygon_preview_layer_ids', [])
        for lid in existing:
            try:
                QgsProject.instance().removeMapLayer(lid)
            except Exception:
                pass
        self._polygon_preview_layer_ids = []

        # Build one layer per role
        role_colours = {
            'inner_toe':   (31, 119, 180),    # blue
            'inner_crest': (44, 160, 44),     # green
            'outer_crest': (214, 39, 40),     # red
            'outer_toe':   (255, 127, 14),    # orange
        }
        for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
            ring = kl.get(role)
            if ring is None:
                continue
            coords = ring['coords']
            if not coords:
                continue
            # Ensure closure
            pts_xy = [(c[0], c[1]) for c in coords]
            if pts_xy[0] != pts_xy[-1]:
                pts_xy.append(pts_xy[0])

            name = f"Polygon Preview - {role}"
            lyr = QgsVectorLayer(
                f"LineStringZ?crs=EPSG:{CRS_EPSG}", name, "memory")
            pr = lyr.dataProvider()
            pr.addAttributes([
                QgsField("role", QVariant.String),
                QgsField("z", QVariant.Double),
            ])
            lyr.updateFields()
            f = QgsFeature()
            z = ring['z_mean']
            f.setGeometry(QgsGeometry.fromPolyline(
                [QgsPoint(c[0], c[1], z) for c in pts_xy]))
            f.setAttributes([role, z])
            pr.addFeatures([f])
            lyr.updateExtents()

            # Apply a coloured solid line style, slightly thicker for
            # the design rings so they stand out against terrain
            try:
                r, g, b = role_colours[role]
                sym = QgsLineSymbol.createSimple({
                    'color': f'{r},{g},{b}',
                    'width': '0.8',
                    'line_style': 'solid',
                })
                lyr.setRenderer(QgsSingleSymbolRenderer(sym))
            except Exception:
                pass

            QgsProject.instance().addMapLayer(lyr)
            self._polygon_preview_layer_ids.append(lyr.id())

    def _clear_polygon_preview_layers(self):
        """Remove any polygon-mode preview layers from the project (called
        when the user switches away from polygon mode)."""
        existing = getattr(self, '_polygon_preview_layer_ids', [])
        for lid in existing:
            try:
                QgsProject.instance().removeMapLayer(lid)
            except Exception:
                pass
        self._polygon_preview_layer_ids = []

    def _source_crs_authid(self):
        """Authid of the input/source CRS for previews (e.g. 'EPSG:2124' when a
        meridional circuit is picked), or NZTM2000 by default. CAD files carry
        no CRS, so DXF/DWG preview geometry sits in the file's own
        coordinates; tagging temp layers with this CRS lets QGIS reproject
        them onto the canvas correctly - the same thing 'Test selected CRS on
        map' does."""
        crs = getattr(self, '_data_crs', None)
        try:
            if crs is not None and crs.isValid() and crs.authid():
                return crs.authid()
        except Exception:
            pass
        return f"EPSG:{CRS_EPSG}"

    def _plot_temp_key_lines(self):
        """Push the four design rings (inner toe, inner crest, outer
        crest, outer toe) to the QGIS map canvas as temporary memory
        layers, so the user has an accurate visual reference for placing
        the spillway BEFORE running the full pipeline or any cut-to-
        terrain operation.

        Works in both modes:
          - DXF mode: uses the current role-to-ring mapping from the
            Geometry tab (auto-detected + any manual overrides), with the
            current z_offset applied so the lines sit at the right
            elevation. In multi-dam DXFs this reflects the selected dam
            (the layer filter has already narrowed the preview).
          - Polygon mode: uses the constructed rings.

        The rings shown are the AS-DESIGNED rings (outer toe at its
        current state - artificial deep or already cut). No cut-to-
        terrain is performed; this is purely a plotting convenience.

        Layers are named 'Temp Key Lines - <role>' and tracked so a
        repeat click cleans up the previous set first.
        """
        # Resolve the current kl. Prefer the constructed kl (polygon /
        # anchor build-up); else the DXF role-to-ring mapping.
        kl = None
        z_off = 0.0
        try:
            if self._constructed_kl:
                kl = self._constructed_kl
            else:
                kl = self._current_role_to_ring()
                # DXF rings are stored in DXF datum; apply the current
                # z_offset so the plotted lines sit at NZVD2016 elevation.
                z_off = float(self._z_offset_value())
        except Exception as e:
            self._set_keyline_status(
                f"<font color='#c00'>Could not resolve rings: {e}</font>")
            return
        if not kl or not any(kl.get(r) for r in
                             ('inner_toe', 'inner_crest',
                              'outer_crest', 'outer_toe')):
            # No roles assigned at all. Most common cause: a multi-dam
            # DXF on "(all layers)" - auto-classify can't disambiguate
            # two dams' rings, so it assigns nothing. Tell the user to
            # pick a single dam (the spatial "[by location]" entry).
            multi = len(getattr(self, '_dam_overview_clusters', [])) >= 2
            if multi:
                self._set_keyline_status(
                    "<font color='#c00'>No rings assigned.</font> This DXF "
                    "has multiple dams - on '(all layers)' the auto-detect "
                    "can't tell them apart. Pick a single dam in the 'DXF "
                    "layers' dropdown (the '\u25c9 ... [by location]' "
                    "entries), then plot again.")
            else:
                self._set_keyline_status(
                    "<font color='#c00'>No rings assigned yet.</font> In "
                    "DXF mode, browse a DXF and check the Geometry tab's "
                    "'Detected rings' table has roles assigned. In polygon "
                    "mode, click Build first.")
            return

        n = self._push_temp_key_lines(kl, z_offset=z_off)
        tag = self._current_dam_tag()
        # Report which roles were available. If auto-detect only assigned
        # some roles (common when one dam in a multi-dam DXF has fewer or
        # ambiguous contours), the user gets fewer than 4 lines - flag
        # exactly which are missing so they can assign them in the
        # Geometry tab's ring table before plotting again.
        present = [r for r in ('inner_toe', 'inner_crest',
                               'outer_crest', 'outer_toe') if kl.get(r)]
        missing = [r for r in ('inner_toe', 'inner_crest',
                               'outer_crest', 'outer_toe') if not kl.get(r)]
        if missing:
            self._set_keyline_status(
                f"<font color='#c60'>Plotted only {n} of 4 key lines "
                f"for [{tag}]</font> - missing: {', '.join(missing)}. "
                f"Auto-detect didn't assign {'these roles' if len(missing) > 1 else 'this role'} "
                f"for this dam. Open the Geometry tab and assign "
                f"{'them' if len(missing) > 1 else 'it'} in the 'Detected "
                f"rings' table, then plot again. (Any other 'Temp Key "
                f"Lines [...]' layers on the map belong to a different "
                f"dam you plotted earlier.)")
        else:
            self._set_keyline_status(
                f"<font color='#080'>Plotted {n} key line(s)</font> to the "
                f"map as 'Temp Key Lines [{tag}] - *'. Use them as a "
                f"reference for the spillway pick. They're temporary - "
                f"re-plot the same dam to refresh, plot a different dam to "
                f"add it alongside, or run the pipeline to replace them.")

    def _current_dam_tag(self):
        """Build a short unique identifier for the current dam, used to
        name temp key-line layers so multiple dams in one QGIS project
        don't collide. Priority:
          1. The selected multi-dam layer filter ('Dam 11' group) -> the
             'Dam N' token, the strongest signal for multi-dam DXFs.
          2. The Dam Name field (e.g. 'Proposed Dam') if set and not the
             default placeholder.
          3. The DXF basename (without extension).
          4. 'Dam' as a last resort.
        Whitespace collapsed; result kept short.
        """
        import os, re
        # 1. Multi-dam filter selection
        try:
            data = self.cmb_dxf_layer_filter.currentData()
            if data:
                # New dict payloads: spatial (bbox) or layer-name.
                if isinstance(data, dict):
                    if data.get('type') == 'bbox':
                        # Use the human label set when the entry was built
                        lbl = data.get('label')
                        if lbl:
                            return lbl[:32]
                        x0, y0, x1, y1 = data['bbox']
                        return f"Dam @ ({(x0+x1)/2:.0f}, {(y0+y1)/2:.0f})"
                    if data.get('type') == 'layers':
                        for lname in data.get('layers', []):
                            m = re.search(r'DAM\s*(\d+)', lname,
                                          re.IGNORECASE)
                            if m:
                                return f"Dam {m.group(1)}"
                        layers = data.get('layers') or []
                        if layers:
                            return str(layers[0])[:24]
                # Legacy list payload
                elif isinstance(data, (list, tuple)):
                    for lname in data:
                        m = re.search(r'DAM\s*(\d+)', lname, re.IGNORECASE)
                        if m:
                            return f"Dam {m.group(1)}"
                    if data:
                        return str(data[0])[:24]
        except Exception:
            pass
        # 2. Dam Name field
        try:
            nm = self.txt_dam_name.text().strip()
            if nm and nm.lower() != "proposed dam":
                return nm[:24]
        except Exception:
            pass
        # 3. DXF basename
        try:
            p = self.txt_dxf.text().strip()
            if p:
                return os.path.splitext(os.path.basename(p))[0][:24]
        except Exception:
            pass
        return "Dam"

    def _push_temp_key_lines(self, kl, z_offset=0.0):
        """Create one memory LineStringZ layer per design ring and add
        them to the project. Returns the number of layers created.

        Layer names carry a per-dam tag ('Temp Key Lines [Dam 11] -
        outer_crest') so multiple dams in the same QGIS project don't
        collide. Re-plotting the SAME dam cleans up that dam's previous
        layers (tracked per tag); plotting a DIFFERENT dam leaves the
        other dam's layers in place so both can be viewed together."""
        tag = self._current_dam_tag()
        # Per-dam cleanup: only remove temp layers for THIS tag, so a
        # different dam's layers survive. _temp_keyline_layer_ids is now
        # a dict {tag: [layer_ids]}.
        store = getattr(self, '_temp_keyline_layer_ids', None)
        if not isinstance(store, dict):
            # Migrate from the old flat-list form (clear it once)
            if isinstance(store, list):
                for lid in store:
                    try:
                        QgsProject.instance().removeMapLayer(lid)
                    except Exception:
                        pass
            store = {}
            self._temp_keyline_layer_ids = store
        for lid in store.get(tag, []):
            try:
                QgsProject.instance().removeMapLayer(lid)
            except Exception:
                pass
        store[tag] = []

        role_colours = {
            'inner_toe':   (31, 119, 180),    # blue
            'inner_crest': (44, 160, 44),     # green
            'outer_crest': (214, 39, 40),     # red
            'outer_toe':   (255, 127, 14),    # orange
        }
        count = 0
        # Preview rings for DXF/DWG input are in the FILE's own coordinates
        # (reprojection to NZTM2000 happens at Run, not preview), so tag the
        # temp layers with the picked source CRS and let QGIS reproject onto
        # the canvas. Polygon-mode rings are already in NZTM2000.
        if self._preview is not None and self._preview.get('polygon_mode'):
            keyline_crs = f"EPSG:{CRS_EPSG}"
        else:
            keyline_crs = self._source_crs_authid()
        for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
            ring = kl.get(role)
            if ring is None:
                continue
            coords = ring.get('coords')
            if not coords:
                continue
            pts_xy = [(c[0], c[1]) for c in coords]
            if pts_xy and pts_xy[0] != pts_xy[-1]:
                pts_xy.append(pts_xy[0])  # close the ring
            z = float(ring.get('z_mean', 0.0)) + z_offset

            name = f"Temp Key Lines [{tag}] - {role}"
            lyr = QgsVectorLayer(
                f"LineStringZ?crs={keyline_crs}", name, "memory")
            pr = lyr.dataProvider()
            pr.addAttributes([
                QgsField("role", QVariant.String),
                QgsField("z", QVariant.Double),
                QgsField("dam", QVariant.String),
            ])
            lyr.updateFields()
            feat = QgsFeature()
            feat.setGeometry(QgsGeometry.fromPolyline(
                [QgsPoint(c[0], c[1], z) for c in pts_xy]))
            feat.setAttributes([role, z, tag])
            pr.addFeatures([feat])
            lyr.updateExtents()
            try:
                r, g, b = role_colours[role]
                sym = QgsLineSymbol.createSimple({
                    'color': f'{r},{g},{b}',
                    'width': '0.8',
                    'line_style': 'solid',
                })
                lyr.setRenderer(QgsSingleSymbolRenderer(sym))
            except Exception:
                pass
            QgsProject.instance().addMapLayer(lyr)
            store[tag].append(lyr.id())
            count += 1
        return count

    def _set_keyline_status(self, html):
        """Set the temp-key-lines status on whichever status labels
        exist (Input tab + Elevations tab both carry a button)."""
        for attr in ('lbl_keyline_status_input',
                     'lbl_keyline_status_elev'):
            lbl = getattr(self, attr, None)
            if lbl is not None:
                try:
                    lbl.setText(html)
                except Exception:
                    pass

    def _on_anchor_deep_toggled(self, on=None):
        """Toggle handler for 'Artificially deep outer toe (for terrain
        cut)' on the DXF + anchor build panel. Mirrors polygon-mode
        overshoot. When ticked: enable the outer_toe_z override checkbox
        and spinbox, compute outer_toe_z = terrain_min - overshoot
        (sampled from the loaded terrain raster within the dam bbox),
        and trigger a rebuild. When unticked: leave the override
        checkbox state alone (so the user can still edit manually) but
        let the user revisit it - and trigger a rebuild from the now-
        non-deep value."""
        try:
            is_on = bool(on) if on is not None else self.chk_anchor_deep.isChecked()
        except Exception:
            is_on = False
        try:
            self.spn_anchor_overshoot.setEnabled(is_on)
        except Exception:
            pass
        if not is_on:
            # Don't force any value change; just refresh.
            try:
                self._rebuild_constructed()
            except Exception:
                pass
            return

        # Ticked: try to compute terrain_min and push it into outer_toe_z
        # override so _rebuild_constructed picks it up.
        if self._terrain_layer is None:
            self.lbl_build_status.setText(
                "<font color='#c00'>Artificially deep mode needs a "
                "terrain raster. Load one on the Input & Elevations "
                "tab first.</font>")
            return
        # Use the anchor ring's bbox for terrain min sampling, falling
        # back to outer_crest if available.
        anchor = self._anchor_ring()
        if anchor is None or not anchor.get('coords'):
            self.lbl_build_status.setText(
                "<font color='#c00'>Pick an anchor ring first so the "
                "tool knows where to sample terrain.</font>")
            return
        try:
            tmin = _terrain_min_in_bbox(
                self._terrain_layer, anchor['coords'])
            if tmin is None:
                self.lbl_build_status.setText(
                    "<font color='#c00'>Could not sample terrain in "
                    "the dam bbox (raster might not cover it).</font>")
                return
            overshoot = float(self.spn_anchor_overshoot.value())
            # CRITICAL DATUM FIX: tmin is in terrain datum (NZVD2016 for
            # LINZ DEMs), but the outer_toe_z spinbox feeds into
            # construct_dam_rings_from_anchor which uses the same datum
            # as the anchor ring (DXF datum at preview time, before any
            # z_offset is applied). So we must convert NZVD2016 -> DXF
            # by subtracting z_offset (since DXF + z_offset = NZVD2016).
            z_offset_val = float(self._z_offset_value())
            new_toe_z_nzvd = float(tmin) - overshoot   # NZVD2016
            new_toe_z_dxf = new_toe_z_nzvd - z_offset_val  # DXF
            # Force the outer_toe_z override on, set the DXF-datum value
            chk, sp = self._buildup_widgets['outer_toe_z']
            chk.blockSignals(True); sp.blockSignals(True)
            chk.setChecked(True)
            sp.setEnabled(True)
            sp.setValue(new_toe_z_dxf)
            chk.blockSignals(False); sp.blockSignals(False)
            # Status is set inside _rebuild_constructed; add a deep tag
            self._rebuild_constructed()
            # Append our own note (show both datums so the user can
            # verify the conversion makes sense)
            self.lbl_build_status.setText(
                self.lbl_build_status.text() + "<br>"
                f"<i>Artificially deep: terrain min {tmin:.2f} m "
                f"(NZVD2016) \u2212 overshoot {overshoot:.1f} m = outer "
                f"toe at {new_toe_z_nzvd:.2f} m (NZVD2016) = "
                f"{new_toe_z_dxf:.2f} m (DXF datum, what the spinbox "
                f"holds). Click 'Cut to terrain' below to clip.</i>")
        except Exception as e:
            import traceback; traceback.print_exc()
            self.lbl_build_status.setText(
                f"<font color='#c00'>Artificially deep mode failed: "
                f"{e}</font>")

    def _store_var_z_method(self, method_key, outer_toe_dict):
        """Snapshot an outer_toe ring dict into the dialog's var-Z
        method storage so the user can later switch between methods.

        method_key: 'method1' or 'method2'
        outer_toe_dict: a kl['outer_toe']-shaped dict with variable Z.
        """
        if method_key not in ('method1', 'method2') or not outer_toe_dict:
            return
        # Deep-copy only the fields we need so subsequent mutations
        # to kl['outer_toe'] don't bleed into stored snapshots.
        coords = list(outer_toe_dict.get('coords') or [])
        if not coords:
            return
        snapshot = {
            'coords': [(c[0], c[1], c[2]) for c in coords if len(c) >= 3],
            'z_min': outer_toe_dict.get('z_min'),
            'z_max': outer_toe_dict.get('z_max'),
            'z_mean': outer_toe_dict.get('z_mean'),
            'z_std': outer_toe_dict.get('z_std'),
            'npts': len(coords),
            'method': method_key,
            'is_variable_z': True,
            'nominal_const_z': outer_toe_dict.get('nominal_const_z'),
            'nominal_const_coords': list(
                outer_toe_dict.get('nominal_const_coords') or []),
        }
        self._var_z_outer_toes[method_key] = snapshot
        self._refresh_otm_status()

    def _refresh_otm_status(self):
        """Update the radio buttons' enabled state and the status label
        based on which methods have been populated."""
        try:
            m1 = self._var_z_outer_toes.get('method1')
            m2 = self._var_z_outer_toes.get('method2')
            self.rb_otm_method1.setEnabled(m1 is not None)
            self.rb_otm_method2.setEnabled(m2 is not None)
            parts = []
            if m1 is not None:
                parts.append(
                    f"Method 1: {m1.get('npts',0)} pts, Z "
                    f"{m1.get('z_min',0):.2f}-{m1.get('z_max',0):.2f} m")
            else:
                parts.append("Method 1: <i>not available (no partial "
                             "contours in this input)</i>")
            if m2 is not None:
                parts.append(
                    f"Method 2: {m2.get('npts',0)} pts, Z "
                    f"{m2.get('z_min',0):.2f}-{m2.get('z_max',0):.2f} m")
            else:
                parts.append("Method 2: <i>not run yet (click button "
                             "above)</i>")
            self.lbl_otm_status.setText("<br>".join(parts))
        except Exception:
            pass

    def _apply_active_var_z_method(self):
        """Copy the active method's saved polyline into kl['outer_toe']
        on whichever kl object is current (preview's auto_classified and
        any constructed kl). Refreshes plan view + long section."""
        method = self._active_var_z_method
        src = self._var_z_outer_toes.get(method)
        if src is None:
            return
        # Apply to preview's auto_classified kl
        try:
            kl = self._preview['auto_classified']
            ot = kl.get('outer_toe')
            if ot is not None:
                # Stash const-Z source the first time we modify
                if 'nominal_const_coords' not in ot:
                    ot['nominal_const_z'] = ot.get('z_mean')
                    ot['nominal_const_coords'] = list(
                        ot.get('coords') or [])
                ot['coords'] = list(src['coords'])
                ot['z_min'] = src['z_min']; ot['z_max'] = src['z_max']
                ot['z_mean'] = src['z_mean']; ot['z_std'] = src['z_std']
                ot['npts'] = src['npts']
                ot['is_variable_z'] = True
                ot['method'] = method
        except Exception:
            pass
        # And to the constructed kl (DXF+anchor or polygon mode)
        try:
            ckl = self._constructed_kl
            if ckl:
                ot = ckl.get('outer_toe')
                if ot is not None:
                    if 'nominal_const_coords' not in ot:
                        ot['nominal_const_z'] = ot.get('z_mean')
                        ot['nominal_const_coords'] = list(
                            ot.get('coords') or [])
                    ot['coords'] = list(src['coords'])
                    ot['z_min'] = src['z_min']; ot['z_max'] = src['z_max']
                    ot['z_mean'] = src['z_mean']
                    ot['z_std'] = src['z_std']; ot['npts'] = src['npts']
                    ot['is_variable_z'] = True
                    ot['method'] = method
        except Exception:
            pass
        try: self._render_plan_view()
        except Exception: pass
        try: self._update_long_section()
        except Exception: pass

    def _on_otm_method_changed(self, btn_id, checked):
        """Radio toggle handler. Swap kl['outer_toe'] to use the
        selected method's polyline and refresh visuals."""
        if not checked:
            return  # only react to the newly-checked one
        method = 'method1' if btn_id == 1 else 'method2'
        if self._var_z_outer_toes.get(method) is None:
            # Method not populated - revert silently
            return
        self._active_var_z_method = method
        self._apply_active_var_z_method()

    def _cut_outer_toe_to_terrain_button(self):
        """Step 2 of the construct-and-cut workflow for DXF + anchor and
        Polygon modes. Walks outward from the constructed outer_crest at
        the design slope until each ray hits terrain, replacing
        kl['outer_toe'] with a variable-Z polyline that sits on natural
        ground. After this the long section shows the dam cut into
        terrain and the orange dots vary with the section rotation.

        Reads the terrain raster from:
          - Polygon Mode tab: cmb_polygon_terrain
          - DXF + anchor: the main terrain layer (self._terrain_layer)
          - Falls back to the drape terrain combo if neither is set
        Requires _constructed_kl to be populated (run Preview Construction
        or have the build-up panel construct the rings first).
        """
        # Identify the kl to operate on. Try constructed first (DXF+anchor /
        # polygon mode), then preview's auto_classified (DXF auto mode).
        # Either way we need the 4 design rings present.
        kl = getattr(self, '_constructed_kl', None)
        if not kl:
            try:
                kl = self._preview['auto_classified']
            except Exception:
                kl = None
        if not kl or not kl.get('outer_crest'):
            msg = ("No design rings yet. Load a DXF and let auto-detect "
                   "run, or assign anchor+params in DXF+anchor mode, or "
                   "press 'Preview Construction' in Polygon Mode.")
            for lbl_name in ('lbl_polygon_cut_status',
                              'lbl_anchor_cut_status',
                              'lbl_otm_status'):
                try:
                    getattr(self, lbl_name).setText(
                        f"<font color='#c00'>{msg}</font>")
                except Exception:
                    pass
            return

        # Find a terrain layer to cut against. Priority: polygon-mode
        # combo, then DXF terrain, then drape terrain.
        terrain = None
        try:
            tid = self.cmb_polygon_terrain.currentData()
            if tid:
                terrain = QgsProject.instance().mapLayer(tid)
        except Exception:
            pass
        if terrain is None and getattr(self, '_terrain_layer', None):
            terrain = self._terrain_layer
        if terrain is None:
            try:
                tid = self.cmb_drape_terrain.currentData()
                if tid:
                    terrain = QgsProject.instance().mapLayer(tid)
            except Exception:
                pass
        if terrain is None:
            msg = ("No terrain raster selected. Load one on Input & "
                   "Elevations or pick one in Polygon Mode / DEM & "
                   "Output drape section.")
            try:
                self.lbl_polygon_cut_status.setText(
                    f"<font color='#c00'>{msg}</font>")
            except Exception:
                pass
            try:
                self.lbl_anchor_cut_status.setText(
                    f"<font color='#c00'>{msg}</font>")
            except Exception:
                pass
            return

        # Read params from whichever panel is the source of truth for
        # the constructed kl. The buildup widgets (spn_p_*, _buildup_widgets)
        # only hold meaningful values when an anchor has been picked AND
        # _populate_buildup_defaults has run. In pure DXF auto mode (no
        # anchor selected), those widgets hold their spinbox-minimum
        # defaults (crest_z=0.000, outer_hv=0.10) which would produce
        # nonsense cuts. So:
        #   1. Prefer the kl rings' own elevations and the inferred-
        #      metrics H:V values (these reflect the actual DXF geometry)
        #   2. Only fall back to buildup widgets if an anchor is selected
        #      (DXF+anchor mode where the user is overriding inferred
        #      values intentionally)
        params = {}
        anchor_selected = False
        try:
            anchor_selected = bool(self._anchor_role())
        except Exception:
            pass

        # 1. Start from kl/inferred (the source of truth for DXF rings)
        try:
            params['crest_z'] = float(kl['outer_crest']['z_mean'])
        except Exception:
            pass
        try:
            metrics = compute_inferred_metrics(
                self._current_role_to_ring(), preview=self._preview)
            if metrics.get('outer_hv') and metrics['outer_hv'] > 0:
                params['outer_hv'] = float(metrics['outer_hv'])
        except Exception:
            pass

        # 2. If anchor selected AND override checkbox ticked, use buildup
        #    widget values - these represent intentional overrides.
        if anchor_selected:
            try:
                chk_cz, sp_cz = self._buildup_widgets.get('crest_z', (None, None))
                if chk_cz is not None and chk_cz.isChecked():
                    params['crest_z'] = float(sp_cz.value())
                chk_oh, sp_oh = self._buildup_widgets.get('outer_hv', (None, None))
                if chk_oh is not None and chk_oh.isChecked():
                    if float(sp_oh.value()) > 0:
                        params['outer_hv'] = float(sp_oh.value())
            except Exception:
                pass

        # 3. Polygon mode falls back to spn_p_* (only if step 1-2 left holes)
        if 'outer_hv' not in params or params.get('outer_hv', 0) <= 0.5:
            try:
                v = float(self.spn_p_outer_hv.value())
                if v > 0.5:
                    params['outer_hv'] = v
            except Exception:
                pass
        if 'crest_z' not in params or params.get('crest_z', 0) == 0:
            try:
                v = float(self.spn_p_crest_z.value())
                if v != 0:
                    params['crest_z'] = v
            except Exception:
                pass
        # 4. Last-resort CFG fallback
        if 'outer_hv' not in params:
            params['outer_hv'] = float(CFG.get('outer_hv', 3.0))
        if 'crest_z' not in params:
            params['crest_z'] = float(CFG.get('crest', 0.0))

        # Sanity check - refuse to run with clearly broken values
        if params['outer_hv'] < 0.5:
            msg = (f"outer_hv = {params['outer_hv']:.2f}:1 is too low "
                   f"(near-vertical batter). Pick an anchor + tick the "
                   f"outer batter H:V override, or check the inferred "
                   f"metrics on the Geometry tab.")
            for lbl_name in ('lbl_otm_status', 'lbl_polygon_cut_status',
                              'lbl_anchor_cut_status'):
                try:
                    getattr(self, lbl_name).setText(
                        f"<font color='#c00'>{msg}</font>")
                except Exception:
                    pass
            return
        if params['crest_z'] == 0:
            msg = ("crest_z is 0 - cannot run cut. Inferred metrics not "
                   "populated. Check that the DXF auto-detected rings or "
                   "set the crest elevation override.")
            for lbl_name in ('lbl_otm_status', 'lbl_polygon_cut_status',
                              'lbl_anchor_cut_status'):
                try:
                    getattr(self, lbl_name).setText(
                        f"<font color='#c00'>{msg}</font>")
                except Exception:
                    pass
            return
        LOG.info(f"Cut to terrain: using outer_hv={params['outer_hv']:.2f}, "
                 f"crest_z={params['crest_z']:.2f}")

        try:
            # DATUM HANDLING: at preview time the constructed/DXF rings
            # are in DXF datum but the terrain raster is in NZVD2016.
            # Pass the current z_offset so the cut function can convert
            # terrain samples into ring datum before comparison and
            # storage. (After Run shifts everything to NZVD2016 the
            # offset is effectively reset; the function defaults to 0.)
            z_offset_val = float(self._z_offset_value())
            cut_outer_toe_to_terrain(
                kl, terrain, params=params,
                step=max(0.2, float(
                    self.spn_spacing.value()
                    if hasattr(self, 'spn_spacing') else 1.0)),
                ring_to_terrain_offset=z_offset_val)
        except Exception as e:
            import traceback; traceback.print_exc()
            msg = f"Cut failed: {e}"
            try:
                self.lbl_polygon_cut_status.setText(
                    f"<font color='#c00'>{msg}</font>")
            except Exception:
                pass
            try:
                self.lbl_anchor_cut_status.setText(
                    f"<font color='#c00'>{msg}</font>")
            except Exception:
                pass
            return

        ot = kl.get('outer_toe', {})
        # Snapshot the cut result into Method 2 storage and activate it.
        self._store_var_z_method('method2', ot)
        self._active_var_z_method = 'method2'
        try:
            self.rb_otm_method2.setChecked(True)
        except Exception:
            pass
        # Detect a degenerate cut (toe ended up basically on the crest)
        # by measuring the mean outward distance from each outer_toe
        # vertex to the nearest outer_crest vertex.
        warn = ""
        try:
            oc_coords = (kl.get('outer_crest') or {}).get('coords') or []
            if oc_coords and ot.get('coords'):
                dists = []
                for tc in ot['coords']:
                    best_d = float('inf')
                    for cc in oc_coords:
                        d = ((tc[0]-cc[0])**2 + (tc[1]-cc[1])**2) ** 0.5
                        if d < best_d:
                            best_d = d
                    dists.append(best_d)
                mean_d = sum(dists) / len(dists)
                if mean_d < 1.0:
                    warn = (
                        f"<br><font color='#c00'><b>WARNING:</b> mean "
                        f"distance from toe to crest = {mean_d:.2f} m. "
                        f"Toe sits nearly directly under the crest "
                        f"(near-vertical batter). This usually means the "
                        f"loaded terrain raster includes the existing "
                        f"dam structure (LiDAR DSM, not bare earth). "
                        f"Try DXF auto mode (Method 1, partial contours) "
                        f"instead, or load a bare-earth DEM that excludes "
                        f"the dam. See the QGIS log for full diagnostics."
                        f"</font>")
        except Exception:
            pass
        status = (
            f"<font color='#080'>OK.</font> Variable-Z outer toe: "
            f"{ot.get('z_min', 0):.2f} - {ot.get('z_max', 0):.2f} m "
            f"(mean {ot.get('z_mean', 0):.2f}, {ot.get('npts', 0)} pts). "
            f"Long section now shows the cut.{warn}")
        try:
            self.lbl_polygon_cut_status.setText(status)
        except Exception:
            pass
        try:
            self.lbl_anchor_cut_status.setText(status)
        except Exception:
            pass
        # Refresh visuals so the long section picks up the new var-Z toe
        try:
            self._render_plan_view()
        except Exception:
            pass
        try:
            self._update_long_section()
        except Exception:
            pass
        # Push the updated outer toe to the polygon preview layers (so
        # the user can see the cut on the map canvas too)
        try:
            self._update_polygon_preview_layers(kl)
        except Exception:
            pass

    # =================================================================
    # Geometry tab construction
    # =================================================================
    def _build_geometry_tab(self):
        tab = QWidget()
        outer = QVBoxLayout()

        if not HAS_MPL:
            outer.addWidget(QLabel(
                "matplotlib not available in this QGIS Python environment - "
                "Geometry preview is disabled. Install matplotlib to enable."))
            tab.setLayout(outer)
            return tab

        # Status banner + manual-refresh button
        topbar = QHBoxLayout()
        self.lbl_geom_status = QLabel(
            "Browse a DXF on the Input tab to analyse its geometry.")
        topbar.addWidget(self.lbl_geom_status, stretch=1)
        btn_reanalyse = QPushButton("Re-analyse DXF")
        btn_reanalyse.clicked.connect(self._run_preview_analysis)
        topbar.addWidget(btn_reanalyse)
        outer.addLayout(topbar)

        # Plan view
        self._plan_fig = Figure(figsize=(6, 5), tight_layout=True)
        self._plan_canvas = _FigureCanvas(self._plan_fig)
        self._plan_canvas.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        plan_wrap = QWidget()
        pw_lay = QVBoxLayout()
        pw_lay.setContentsMargins(0, 0, 0, 0)
        pw_lay.addWidget(QLabel("DXF plan view (closed const-Z rings)"))
        pw_lay.addWidget(self._plan_canvas)
        plan_wrap.setLayout(pw_lay)

        # Right panel: ring table + inferred params
        right_panel = QWidget()
        rp = QVBoxLayout()
        rp.addWidget(QLabel("Detected rings - assign a role to each"))
        # Toggle: by default only the 4 candidate rings (auto-id picks) are
        # shown so the table stays uncluttered on DXFs with many DTM contours.
        # Toggle on to reveal everything when auto-id picked the wrong ring
        # and you need to swap to a hidden candidate.
        self.chk_show_all_rings = QCheckBox(
            "Show all detected rings (default: only the 4 key candidates)")
        self.chk_show_all_rings.setChecked(False)
        self.chk_show_all_rings.toggled.connect(
            lambda _: self._refresh_ring_table())
        rp.addWidget(self.chk_show_all_rings)
        # Interior sump handling. A sump (small ring deeper than the basin
        # floor) is always kept OUT of the inner-toe pick so the inner batter
        # slope stays correct. When this is ticked the sump is also modelled
        # in the DEM as a pocket (invert ring + a rim at basin invert that
        # pins the basin flat); unticked, it's ignored (flat basin).
        self.chk_include_sump = QCheckBox(
            "Model interior sump(s) in the DEM (else ignore - never used as "
            "inner toe either way)")
        self.chk_include_sump.setChecked(True)
        self.chk_include_sump.setToolTip(
            "A sump is a small ring sitting below the basin floor. It's never "
            "treated as the inner toe (that would wreck the inner batter "
            "slope and the spillway). Ticked: model it as a pocket - invert "
            "ring at the sump level plus a rim at basin invert so the basin "
            "stays flat up to the sump edge. Unticked: leave it out (flat "
            "basin floor).")
        rp.addWidget(self.chk_include_sump)
        self.tbl_rings = QTableWidget()
        self.tbl_rings.setColumnCount(6)
        self.tbl_rings.setHorizontalHeaderLabels(
            ["\u2713 #", "Z (m)", "pts", "extent (m)", "area (m\u00b2)", "Role"])
        hdr = self.tbl_rings.horizontalHeader()
        hdr.setSectionResizeMode(QHeaderView.ResizeToContents)
        hdr.setSectionResizeMode(5, QHeaderView.Stretch)
        self.tbl_rings.verticalHeader().setVisible(False)
        # Tick a row's '#' box to show/hide that ring in the plan view, and
        # click a row to highlight its ring - so you can isolate rings and
        # assign roles with certainty when many contours overlap.
        self.tbl_rings.itemChanged.connect(self._on_ring_item_changed)
        self.tbl_rings.itemSelectionChanged.connect(
            self._on_ring_selection_changed)
        rp.addWidget(self.tbl_rings, stretch=1)

        vis_row = QHBoxLayout()
        self.btn_isolate_ring = QPushButton("Isolate selected ring")
        self.btn_isolate_ring.setToolTip(
            "Hide every ring except the one selected in the table, so you "
            "can confirm exactly which contour it is before assigning a role.")
        self.btn_isolate_ring.clicked.connect(self._isolate_selected_ring)
        vis_row.addWidget(self.btn_isolate_ring)
        self.btn_show_all_ring_vis = QPushButton("Show all rings")
        self.btn_show_all_ring_vis.setToolTip(
            "Make every detected ring visible again in the plan view.")
        self.btn_show_all_ring_vis.clicked.connect(self._show_all_rings_visible)
        vis_row.addWidget(self.btn_show_all_ring_vis)
        rp.addLayout(vis_row)

        # Inferred params (read-only - editing comes in Phase 2)
        # Manual-entry toggle: when a DXF has incomplete rings (e.g.
        # only one complete const-Z ring because the spillway cut the
        # others, or rings are missing), the user assigns a role to the
        # ONE good ring, ticks "Manual entry", types the missing design
        # parameters, and builds the full 4-ring dam from that anchor.
        # This reuses construct_dam_rings_from_anchor (the same engine
        # polygon mode uses) but anchored on a classified DXF ring.
        self.chk_manual_params = QCheckBox(
            "Manual entry (build dam from one assigned ring)")
        self.chk_manual_params.setToolTip(
            "Tick this when the DXF doesn't have all four clean rings "
            "(missing, or cut by the spillway). Assign a role to the one "
            "complete const-Z ring above, then type the design parameters "
            "below and click Build. The other three rings are constructed "
            "from your anchor ring using its own elevation as the datum.")
        self.chk_manual_params.toggled.connect(self._on_manual_params_toggled)
        rp.addWidget(self.chk_manual_params)

        grp_inf = QGroupBox("Inferred design parameters")
        gi = QGridLayout()
        self._inf_labels = {}     # read-only display labels (auto mode)
        self._inf_edits = {}      # editable spinboxes (manual mode)
        # (key, label, decimals, min, max, step, suffix, editable_in_manual)
        # crest_z / invert_z etc. are derived from the anchor + geometry;
        # the user types the GEOMETRIC params (crest width, depth via
        # crest_z, batters) and the anchor's own Z fixes the datum.
        rows = [
            ('crest_z',     "Crest elevation:",        3, -100.0, 5000.0, 0.1, " m"),
            ('invert_z',    "Invert elevation:",       3, -100.0, 5000.0, 0.1, " m"),
            ('outer_toe_z', "Outer toe elevation:",    3, -100.0, 5000.0, 0.1, " m"),
            ('depth',       "Depth (crest \u2212 invert):", 3, 0.0, 500.0, 0.1, " m"),
            ('crest_width', "Crest width:",            2, 0.1, 200.0, 0.5, " m"),
            ('inner_hv',    "Inner batter H:V:",       2, 0.1, 20.0, 0.25, " :1"),
            ('outer_hv',    "Outer batter H:V:",       2, 0.1, 20.0, 0.25, " :1"),
        ]
        for i, (key, label, dec, lo, hi, step, suf) in enumerate(rows):
            gi.addWidget(QLabel(label), i, 0)
            # Read-only display label (shown in auto mode)
            lbl = QLabel("\u2014")
            f = lbl.font(); f.setBold(True); lbl.setFont(f)
            gi.addWidget(lbl, i, 1)
            self._inf_labels[key] = lbl
            # Editable spinbox (shown in manual mode), hidden initially
            spn = QDoubleSpinBox()
            spn.setRange(lo, hi); spn.setDecimals(dec)
            spn.setSingleStep(step); spn.setSuffix(suf)
            spn.setVisible(False)
            gi.addWidget(spn, i, 1)
            self._inf_edits[key] = spn
        # outer_toe_z in manual mode is auto-set very deep (artificial)
        # the same way the rest of the tool treats the pre-cut toe, so we
        # don't ask the user for it. It's derived on build.
        self._build_from_ring_btn = QPushButton(
            "Build dam from assigned ring")
        self._build_from_ring_btn.setToolTip(
            "Construct all four rings from the single assigned anchor "
            "ring plus the parameters above. Enabled only in Manual "
            "entry mode with exactly one ring assigned.")
        self._build_from_ring_btn.clicked.connect(
            self._build_dam_from_assigned_ring)
        self._build_from_ring_btn.setVisible(False)
        gi.addWidget(self._build_from_ring_btn, len(rows), 0, 1, 2)
        self.lbl_manual_build_status = QLabel("")
        self.lbl_manual_build_status.setWordWrap(True)
        self.lbl_manual_build_status.setVisible(False)
        gi.addWidget(self.lbl_manual_build_status, len(rows) + 1, 0, 1, 2)
        grp_inf.setLayout(gi)
        rp.addWidget(grp_inf)

        # Vertical offset (DXF -> NZVD2016 datum correction)
        grp_off = QGroupBox("Vertical offset (datum correction)")
        go = QGridLayout()
        go.addWidget(QLabel("DXF \u2192 DEM offset:"), 0, 0)
        self.spn_z_offset = QDoubleSpinBox()
        self.spn_z_offset.setRange(-9999.0, 9999.0)
        self.spn_z_offset.setDecimals(3)
        self.spn_z_offset.setSingleStep(0.1)
        self.spn_z_offset.setSuffix(" m")
        self.spn_z_offset.setValue(0.0)
        self.spn_z_offset.setToolTip(
            "Vertical shift applied to all DXF Z values to align them with "
            "the DEM datum (NZVD2016). Negative values shift the design DOWN.")
        self.spn_z_offset.valueChanged.connect(self._on_z_offset_changed)
        go.addWidget(self.spn_z_offset, 0, 1)
        self.btn_snap_toe = QPushButton("Snap outer toe to ground")
        self.btn_snap_toe.setToolTip(
            "Set the offset so that the outer toe sits on the DEM ground, "
            "minimising the mean delta around the outer-toe perimeter.")
        self.btn_snap_toe.clicked.connect(self._snap_outer_toe_to_ground)
        go.addWidget(self.btn_snap_toe, 0, 2)
        # Alternative snap: balance cut and fill volumes. Useful when
        # there's no outer toe polygon to match against terrain (polygon
        # mode, or DXF without a meaningful outer toe). Sweeps z_offset
        # values, samples terrain across the dam footprint, and picks
        # the offset where fill = cut * multiplier. The default mult
        # (0.85) reflects typical earthfill bulking.
        go.addWidget(QLabel("Cut/fill multiplier:"), 1, 0)
        self.spn_z_offset_cf_mult = QDoubleSpinBox()
        self.spn_z_offset_cf_mult.setRange(0.1, 5.0)
        self.spn_z_offset_cf_mult.setDecimals(2)
        self.spn_z_offset_cf_mult.setSingleStep(0.05)
        self.spn_z_offset_cf_mult.setValue(0.85)
        self.spn_z_offset_cf_mult.setToolTip(
            "Target ratio of fill / cut. 0.85 is a typical bulking factor "
            "for compacted earthfill (1 m\u00b3 cut yields ~0.85 m\u00b3 "
            "of compacted fill). Set 1.0 for exact balance.")
        go.addWidget(self.spn_z_offset_cf_mult, 1, 1)
        self.btn_snap_cut_fill = QPushButton(
            "Snap to balance cut / fill")
        self.btn_snap_cut_fill.setToolTip(
            "Sweep z_offset values; pick the one where fill volume "
            "(embankment above ground) = cut volume (reservoir + "
            "below-ground embankment) x multiplier. Needs a terrain "
            "raster and a constructed dam (DXF auto-detected or polygon "
            "Built).")
        self.btn_snap_cut_fill.clicked.connect(
            self._snap_z_offset_to_cut_fill_balance)
        go.addWidget(self.btn_snap_cut_fill, 1, 2)
        # Third snap: force a target maximum embankment height. The
        # embankment height at any crest station = crest_z - terrain_z
        # directly beneath the crest there (this is the vertical distance
        # from crest down to where the outer batter meets natural ground,
        # i.e. the toe). The MAX height occurs where terrain is lowest
        # under the crest line. The user enters a target (e.g. 3.95 m)
        # and this snap shifts z_offset so that the tallest section of
        # the dam is exactly that height. Solved directly (no sweep):
        #   height(off) = (crest_z + off) - terrain_min
        #   target      = (crest_z + off) - terrain_min
        #   off         = target + terrain_min - crest_z
        go.addWidget(QLabel("Max embankment ht:"), 2, 0)
        self.spn_max_emb_height = QDoubleSpinBox()
        self.spn_max_emb_height.setRange(0.1, 200.0)
        self.spn_max_emb_height.setDecimals(2)
        self.spn_max_emb_height.setSingleStep(0.05)
        self.spn_max_emb_height.setSuffix(" m")
        self.spn_max_emb_height.setValue(3.95)
        self.spn_max_emb_height.setToolTip(
            "Target maximum embankment height: the vertical distance "
            "from the crest down to natural ground at the tallest "
            "section of the dam (where terrain is lowest beneath the "
            "crest line).")
        go.addWidget(self.spn_max_emb_height, 2, 1)
        self.btn_snap_max_height = QPushButton(
            "Snap to max embankment height")
        self.btn_snap_max_height.setToolTip(
            "Shift z_offset so the tallest section of the dam equals the "
            "target height. Samples terrain along the outer-crest line, "
            "finds the lowest ground, and sets the crest so "
            "crest_z - lowest_ground = target. Needs a terrain raster "
            "and a constructed dam (DXF auto-detected or polygon Built).")
        self.btn_snap_max_height.clicked.connect(
            self._snap_z_offset_to_max_embankment_height)
        go.addWidget(self.btn_snap_max_height, 2, 2)
        # Reset: undo any Method 2 cut + z_offset shift. Restores the
        # outer toe to its as-constructed artificial-deep state (the
        # state the user sees right after Build in polygon mode, or
        # after step4d in DXF mode). Useful when the snaps produced
        # absurd results and the user wants to start over without
        # rebuilding the dam from scratch.
        self.btn_reset_artificial = QPushButton(
            "Reset to artificial deep toe (undo snaps + Method 2)")
        self.btn_reset_artificial.setToolTip(
            "Restore z_offset = 0 and the outer toe ring to its "
            "as-constructed artificial-deep design polygon. Use this "
            "if Snap-to-Ground, Snap-cut/fill or Method 2 gave a bad "
            "result and you want to go back to the clean design state.")
        self.btn_reset_artificial.clicked.connect(
            self._reset_to_artificial_deep_toe)
        go.addWidget(self.btn_reset_artificial, 3, 0, 1, 3)
        # Slider for live raise/drop. The slider holds 0.1 m steps over
        # +/- 50 m around the spinbox value at the time the slider's
        # 'centre' was last set. Both widgets sync to each other, but the
        # spinbox is authoritative for the actual offset value.
        go.addWidget(QLabel("Lift / drop:"), 4, 0)
        self.sld_z_offset = QSlider(Qt.Horizontal)
        self.sld_z_offset.setRange(-500, 500)         # +/- 50 m in 0.1 m
        self.sld_z_offset.setValue(0)
        self.sld_z_offset.setTickPosition(QSlider.TicksBelow)
        self.sld_z_offset.setTickInterval(100)        # tick every 10 m
        self.sld_z_offset.setToolTip(
            "Drag to raise (right) or drop (left) the design in 0.1 m "
            "steps. Range is +/- 50 m around the current spinbox value.")
        self._sld_z_offset_centre = 0.0  # spinbox value at slider==0
        self.sld_z_offset.valueChanged.connect(
            self._on_z_offset_slider_changed)
        go.addWidget(self.sld_z_offset, 4, 1, 1, 2)
        self.lbl_snap_status = QLabel(
            "(adjust manually, or click Snap once outer_toe is assigned "
            "and a terrain DEM is selected)")
        self.lbl_snap_status.setWordWrap(True)
        f = self.lbl_snap_status.font(); f.setItalic(True)
        self.lbl_snap_status.setFont(f)
        go.addWidget(self.lbl_snap_status, 5, 0, 1, 3)
        grp_off.setLayout(go)
        rp.addWidget(grp_off)

        # ----- Outer toe method selector -----------------------------
        # Both methods produce a variable-Z outer toe polyline. Method 1
        # reads the DXF's partial open contours (their endpoints touch
        # the outer toe ring at natural-ground Z). Method 2 walks the
        # design batter outward from outer_crest until it hits the
        # loaded terrain raster. The dialog stores both results
        # separately on self._var_z_outer_toes, and this selector
        # decides which one is COPIED INTO kl['outer_toe'] (the active
        # ring used by plan view, long section, DEM mask, points CSV).
        grp_otm = QGroupBox("Outer toe ring source (variable-Z polyline)")
        gotm = QVBoxLayout()
        info_otm = QLabel(
            "<i>Method 1 reads contour endpoints in the DXF (drone-survey "
            "intent). Method 2 walks the design batter outward until it "
            "hits the terrain raster (LiDAR intersection). Both produce a "
            "variable-Z polyline; pick which one feeds the DEM mask and "
            "the points CSV outer_toe.</i>")
        info_otm.setWordWrap(True)
        gotm.addWidget(info_otm)
        from qgis.PyQt.QtWidgets import QRadioButton, QButtonGroup
        self.rb_otm_method1 = QRadioButton(
            "Method 1: DXF partial contours")
        self.rb_otm_method1.setToolTip(
            "Use the variable-Z polyline derived from the DXF's partial "
            "open contour endpoints (step4c). Reflects what the drone "
            "survey actually recorded at the dam-meets-ground line.")
        self.rb_otm_method2 = QRadioButton(
            "Method 2: terrain intersection (cut to terrain)")
        self.rb_otm_method2.setToolTip(
            "Walk outward from outer_crest at design batter slope until "
            "intersection with the loaded terrain raster. Geometrically "
            "perfect: outer toe sits exactly on the design slope, "
            "clipped at natural ground.")
        # Default: Method 1 if DXF was loaded, else Method 2
        self.rb_otm_method1.setChecked(True)
        self.btng_otm = QButtonGroup(self)
        self.btng_otm.addButton(self.rb_otm_method1, 1)
        self.btng_otm.addButton(self.rb_otm_method2, 2)
        gotm.addWidget(self.rb_otm_method1)
        gotm.addWidget(self.rb_otm_method2)
        # Cut-to-terrain button (works in ALL modes - DXF auto, DXF+anchor,
        # polygon). Replaces the now-redundant build-panel and polygon-
        # tab Cut buttons (though those remain as shortcuts).
        self.btn_otm_cut = QPushButton(
            "Run Method 2 now (cut to terrain)")
        self.btn_otm_cut.setToolTip(
            "Execute the terrain cut against the loaded terrain raster, "
            "store the result, and switch to Method 2. Re-run any time "
            "the terrain raster or design slopes change.")
        self.btn_otm_cut.clicked.connect(self._cut_outer_toe_to_terrain_button)
        gotm.addWidget(self.btn_otm_cut)
        self.lbl_otm_status = QLabel(
            "<i>Method 1 fills automatically if the DXF has partial "
            "contours. Click 'Run Method 2 now' to populate Method 2.</i>")
        self.lbl_otm_status.setWordWrap(True)
        gotm.addWidget(self.lbl_otm_status)
        self.btng_otm.idToggled.connect(self._on_otm_method_changed)
        grp_otm.setLayout(gotm)
        rp.addWidget(grp_otm)

        # Build dam from anchor + parameters (Phase 2)
        grp_build = QGroupBox("Build dam from anchor + parameters")
        gb = QGridLayout()
        gb.setColumnStretch(2, 1)
        gb.addWidget(QLabel("Anchor ring:"), 0, 0)
        self.cmb_anchor = QComboBox()
        # Populated dynamically as roles are assigned
        self.cmb_anchor.addItem("(none)", "")
        self.cmb_anchor.currentIndexChanged.connect(self._on_anchor_changed)
        gb.addWidget(self.cmb_anchor, 0, 1, 1, 2)

        # 6 override rows: (label, attr_name, suffix, decimals, is_hv)
        self._buildup_widgets = {}  # key -> (checkbox, spinbox)
        rows = [
            ('crest_z',     "Crest elevation:",   " m",  3, False),
            ('invert_z',    "Invert elevation:",  " m",  3, False),
            ('outer_toe_z', "Outer toe elevation:", " m", 3, False),
            ('crest_width', "Crest width:",       " m",  2, False),
            ('inner_hv',    "Inner batter H:V:",  " : 1", 2, True),
            ('outer_hv',    "Outer batter H:V:",  " : 1", 2, True),
        ]
        for i, (key, lbl, suffix, dec, is_hv) in enumerate(rows, start=1):
            chk = QCheckBox("override")
            chk.setToolTip(
                "Tick to override the value below (the default comes from "
                "the anchor ring elevation or inferred metrics).")
            chk.toggled.connect(
                lambda _on, k=key: self._on_buildup_override_changed(k))
            gb.addWidget(chk, i, 0)
            gb.addWidget(QLabel(lbl), i, 1)
            sp = QDoubleSpinBox()
            if is_hv:
                sp.setRange(0.1, 20.0)
            else:
                sp.setRange(-9999.0, 9999.0)
            sp.setDecimals(dec)
            sp.setSingleStep(0.1)
            sp.setSuffix(suffix)
            sp.setEnabled(False)
            sp.valueChanged.connect(
                lambda _v, k=key: self._on_buildup_param_changed(k))
            gb.addWidget(sp, i, 2)
            self._buildup_widgets[key] = (chk, sp)

        # Toggle: use constructed geometry for the Run pipeline
        self.chk_use_constructed = QCheckBox(
            "Use constructed geometry for Run pipeline")
        self.chk_use_constructed.setToolTip(
            "When ticked, the Run pipeline replaces the DXF-derived rings "
            "with the rings constructed from the anchor + parameters above. "
            "Use this for sparse DXFs (missing inner toe / inner crest) or "
            "when the DXF rings are unreliable.")
        self.chk_use_constructed.toggled.connect(self._on_use_constructed)
        gb.addWidget(self.chk_use_constructed, 7, 0, 1, 3)

        # Artificially deep mode for the outer toe (DXF + anchor only).
        # Mirrors the spn_p_overshoot widget on the Polygon Mode tab:
        # when ticked, the constructed outer_toe_z is forced to
        # terrain_min - overshoot (i.e. artificially below ground), so
        # the outer batter extends well past natural ground. After
        # construction the user clicks "Cut to terrain" to clip back
        # to the actual ground intersection.
        self.chk_anchor_deep = QCheckBox(
            "Artificially deep outer toe (for terrain cut)")
        self.chk_anchor_deep.setToolTip(
            "Force outer toe to terrain_min minus overshoot below. The "
            "outer batter will extend well past natural ground; click "
            "'Cut to terrain' afterwards to clip back to the actual "
            "ground line. Requires a terrain raster on the Input & "
            "Elevations tab. Equivalent to Polygon Mode's overshoot.")
        self.chk_anchor_deep.toggled.connect(self._on_anchor_deep_toggled)
        gb.addWidget(self.chk_anchor_deep, 8, 0, 1, 2)
        self.spn_anchor_overshoot = QDoubleSpinBox()
        self.spn_anchor_overshoot.setRange(1.0, 100.0)
        self.spn_anchor_overshoot.setDecimals(1)
        self.spn_anchor_overshoot.setValue(15.0)
        self.spn_anchor_overshoot.setSuffix(" m below terrain min")
        self.spn_anchor_overshoot.setEnabled(False)
        self.spn_anchor_overshoot.valueChanged.connect(
            lambda _v: self._on_anchor_deep_toggled(
                self.chk_anchor_deep.isChecked()))
        gb.addWidget(self.spn_anchor_overshoot, 8, 2)

        self.lbl_build_status = QLabel(
            "(assign at least one role, pick an anchor, then construction "
            "will preview here)")
        self.lbl_build_status.setWordWrap(True)
        f = self.lbl_build_status.font(); f.setItalic(True)
        self.lbl_build_status.setFont(f)
        gb.addWidget(self.lbl_build_status, 9, 0, 1, 3)

        # Step 2: Cut to terrain (DXF + anchor mode). The constructed
        # outer toe is const-Z by design (parallel offset of outer
        # crest at CFG['toe_low']). Click this to walk outward from the
        # constructed outer crest until each ray hits the terrain
        # raster, producing a variable-Z outer toe that sits on natural
        # ground. The long section then shows the dam as it actually
        # sits cut into terrain.
        self.btn_anchor_cut = QPushButton("Cut to terrain")
        self.btn_anchor_cut.setToolTip(
            "Step 2: walk outward from the constructed outer crest at "
            "design slope until each ray hits terrain. The intersections "
            "become the variable-Z outer toe. Use after the rings are "
            "constructed (which happens automatically as you change "
            "anchor/parameters). Requires a terrain raster loaded on "
            "the Input & Elevations tab.")
        self.btn_anchor_cut.clicked.connect(
            self._cut_outer_toe_to_terrain_button)
        gb.addWidget(self.btn_anchor_cut, 10, 0, 1, 2)
        self.lbl_anchor_cut_status = QLabel("<i>(no cut yet)</i>")
        self.lbl_anchor_cut_status.setWordWrap(True)
        f2 = self.lbl_anchor_cut_status.font(); f2.setItalic(True)
        self.lbl_anchor_cut_status.setFont(f2)
        gb.addWidget(self.lbl_anchor_cut_status, 10, 2, 1, 1)

        grp_build.setLayout(gb)
        # HIDDEN: this whole group is redundant with the polygon input
        # on the Input tab. Both produce 4 design rings from one anchor
        # ring + parameters via construct_dam_rings_from_anchor. The
        # widgets stay in the dialog tree (so all the methods that
        # reference self.cmb_anchor, self._buildup_widgets, etc. keep
        # working) but the user no longer sees the panel. The Method 2
        # cut button now reads design params from the kl/inferred
        # metrics directly, so this group has no role in any user flow.
        # To use anchor-style construction with a DXF: load the DXF as
        # a QGIS layer (auto-detect already does this), then switch
        # Input source = Polygon on the Input tab and pick the ring you
        # want as the anchor polygon.
        grp_build.setVisible(False)
        rp.addWidget(grp_build)

        right_panel.setLayout(rp)

        # Wrap the parameter panel in a scroll area so its content
        # (inferred metrics + Z offset + build-up + artificially-deep
        # + cut button + status) stays accessible even when the column
        # is narrow or the user has shrunk the dialog. Previously the
        # bottom of the build-up panel (cut button + status text) was
        # cropped on smaller screens.
        right_scroll = QScrollArea()
        right_scroll.setWidget(right_panel)
        right_scroll.setWidgetResizable(True)
        right_scroll.setFrameShape(QFrame.NoFrame)
        right_scroll.setMinimumWidth(400)

        # 3-column horizontal layout: plan view | parameters | long
        # section. On a 4K screen this finally uses the full width;
        # previously a vertical stack squashed the long section into a
        # short strip at the bottom and crammed the parameter column.
        # The user can drag any divider to rebalance.
        main_split = QSplitter(Qt.Horizontal)
        main_split.addWidget(plan_wrap)
        main_split.addWidget(right_scroll)

        # Long-section column - replaces the old bottom row. Same
        # widgets as before (rotation slider, V.E., section canvas)
        # just in a vertical stack inside its own column host.
        sec_host = QWidget()
        sec_outer = QVBoxLayout()
        sec_outer.setContentsMargins(0, 0, 0, 0)

        # Top row: rotation slider + degree label
        rot_row = QHBoxLayout()
        rot_row.addWidget(QLabel("Section rotation:"))
        self.sld_section_angle = QSlider(Qt.Horizontal)
        self.sld_section_angle.setRange(0, 359)      # 1° steps
        self.sld_section_angle.setValue(0)
        self.sld_section_angle.setToolTip(
            "Rotate the section line about the dam centroid (degrees, "
            "measured CCW from east). Live-updates the long section.")
        self.sld_section_angle.valueChanged.connect(
            self._on_section_angle_changed)
        rot_row.addWidget(self.sld_section_angle, stretch=1)
        self.lbl_section_angle = QLabel("0°")
        self.lbl_section_angle.setMinimumWidth(40)
        rot_row.addWidget(self.lbl_section_angle)
        # Quick-snap buttons for the high/low ground directions
        self.btn_section_lowhigh = QPushButton("Align low→high")
        self.btn_section_lowhigh.setToolTip(
            "Align the section line along the low-to-high ground gradient "
            "across the outer_crest perimeter.")
        self.btn_section_lowhigh.clicked.connect(self._snap_section_to_lowhigh)
        rot_row.addWidget(self.btn_section_lowhigh)
        # Vertical exaggeration. Default 5x because at true scale (V.E.=1)
        # a typical dam (200 m wide x 5 m tall) would render as a thin
        # strip with the design invisible. V.E. stretches the vertical
        # axis for legibility; the numerical H:V in the title is the TRUE
        # ratio and is unaffected by V.E. (slopes look 5x steeper than
        # reality at V.E.=5, but the numbers are honest).
        rot_row.addWidget(QLabel("V.E.:"))
        self.spn_ve = QDoubleSpinBox()
        self.spn_ve.setRange(1.0, 50.0)
        self.spn_ve.setSingleStep(1.0)
        self.spn_ve.setDecimals(1)
        self.spn_ve.setValue(5.0)
        self.spn_ve.setToolTip(
            "Vertical exaggeration for the section plot. Default 5 makes "
            "the dam visible (true-scale 1.0 makes a typical 200m x 5m "
            "dam look like a thin strip). The numerical H:V in the title "
            "is unaffected by V.E. - the *visual* slope on the plot is "
            "V.E.x steeper than reality, but the numbers tell the truth.")
        self.spn_ve.valueChanged.connect(lambda _v: self._update_long_section())
        rot_row.addWidget(self.spn_ve)
        # Toggle to overlay intermediate batter contour crossings
        self.chk_show_contours = QCheckBox("Show all contours")
        self.chk_show_contours.setChecked(True)
        self.chk_show_contours.setToolTip(
            "Overlay crossings of every detected constant-Z ring on the "
            "long section. For Neil-Kingston-style DXFs with 0.2 m contour "
            "rings, this reveals the actual batter slope pattern at every "
            "elevation step (regular spacing = constant slope).")
        self.chk_show_contours.toggled.connect(
            lambda _on: self._update_long_section())
        rot_row.addWidget(self.chk_show_contours)
        sec_outer.addLayout(rot_row)

        # Section canvas — full width of its column. Minimum height
        # keeps the chart readable; the splitters let the user pull it
        # taller or wider.
        self._section_fig = Figure(figsize=(7, 5.5), tight_layout=True)
        self._section_canvas = _FigureCanvas(self._section_fig)
        self._section_canvas.setMinimumHeight(320)
        self._section_canvas.setMinimumWidth(420)
        self._section_canvas.setSizePolicy(
            QSizePolicy.Expanding, QSizePolicy.Expanding)
        sec_outer.addWidget(QLabel(
            "Long section across the dam (centroid-through, rotatable). "
            "Section axis is shown on the plan view (left). "
            "Drag the vertical dividers to rebalance the columns."))
        sec_outer.addWidget(self._section_canvas, stretch=1)
        sec_host.setLayout(sec_outer)
        main_split.addWidget(sec_host)

        # 3-column proportions: plan view (40%) | params (25%) | section (35%)
        # On a 1920px screen that's roughly 770 / 480 / 670 px.
        # On a 4K (3840px) the columns scale to 1540 / 960 / 1340 px.
        main_split.setStretchFactor(0, 8)
        main_split.setStretchFactor(1, 5)
        main_split.setStretchFactor(2, 7)
        main_split.setSizes([770, 480, 670])

        outer.addWidget(main_split, stretch=1)

        tab.setLayout(outer)
        return tab

    # =================================================================
    # Geometry tab behaviour
    # =================================================================
    def _run_preview_analysis(self):
        """Read the DXF currently in the file textbox, classify its rings,
        and refresh the Geometry tab widgets."""
        if not HAS_MPL:
            return
        path = self.txt_dxf.text().strip()
        if not path:
            self.lbl_geom_status.setText(
                "No DXF selected. Browse one on the Input tab.")
            return
        if not os.path.exists(path):
            self.lbl_geom_status.setText(f"DXF not found: {path}")
            return

        # Use the dialog's current classification params - same as run()
        classify_params = {
            'min_area': self.spn_ma.value(),
            'min_verts': int(self.spn_mv.value()),
            'z_thresh': self.spn_zt.value(),
            'stitch_tol': self.spn_st.value(),
            'auto_elev': self.chk_auto_elev.isChecked(),
            'invert': self.spn_invert.value(),
            'crest': self.spn_crest.value(),
            'toe_low': self.spn_toe.value(),
            # Pass the layer filter so the preview shows only entities
            # for the selected dam in multi-dam DXFs.
            'dxf_layer_filter': self.cmb_dxf_layer_filter.currentData(),
        }

        QApplication = None
        try:
            from PyQt5.QtWidgets import QApplication
            QApplication.setOverrideCursor(QCursor(Qt.WaitCursor))
        except Exception:
            pass
        try:
            preview = preview_analyse_dxf(path, classify_params)
        finally:
            if QApplication is not None:
                try:
                    QApplication.restoreOverrideCursor()
                except Exception:
                    pass

        self._preview = preview
        # Reset role assignments
        self._role_assignments = dict(preview.get('auto_indices') or {})

        # Method 1 capture: if step4c populated a variable-Z outer toe
        # from partial contours, snapshot it into the dialog's method
        # storage and default the selector to Method 1.
        try:
            self._var_z_outer_toes = {'method1': None, 'method2': None}
            self._active_var_z_method = 'method1'
            kl0 = preview.get('auto_classified') or {}
            ot0 = kl0.get('outer_toe') or {}
            if ot0.get('is_variable_z') and ot0.get('coords'):
                self._store_var_z_method('method1', ot0)
                try:
                    self.rb_otm_method1.setChecked(True)
                except Exception:
                    pass
            else:
                self._refresh_otm_status()
        except Exception:
            pass

        n_const = len(preview['all_const_z'])
        n_var = len(preview.get('var_z') or [])
        n_assigned = len(self._role_assignments)
        if not preview['success']:
            self.lbl_geom_status.setText(
                f"Analysis failed: {'; '.join(preview['errors'])}")
        elif n_const + n_var == 0:
            self.lbl_geom_status.setText(
                "No closed rings found in this DXF.")
        else:
            counts = f"{n_const} constant-Z"
            if n_var:
                counts += f" + {n_var} variable-Z"
            counts += " ring(s)"
            auto = preview.get('auto_classified')
            if auto and n_assigned == 4:
                self.lbl_geom_status.setText(
                    f"Detected {counts}. All 4 roles auto-assigned - "
                    f"review and adjust if needed. Variable-Z rings appear "
                    f"as V1, V2 ... in the picker.")
            elif auto:
                self.lbl_geom_status.setText(
                    f"Detected {counts}. Auto-assigned {n_assigned}/4 roles. "
                    f"Complete the remaining assignment(s) in the table.")
            else:
                msg = preview['warnings'][0] if preview['warnings'] else \
                      "Auto-identification incomplete."
                self.lbl_geom_status.setText(
                    f"Detected {counts}. {msg}")

        self._refresh_ring_table()
        self._render_plan_view()
        self._update_inferred_params()
        # Set the section rotation slider to the low-to-high default
        # (only if the user hasn't already chosen a custom angle).
        if self._section_angle_deg is None:
            default = self._default_section_angle_deg()
            if default is not None:
                self.sld_section_angle.blockSignals(True)
                self.sld_section_angle.setValue(int(round(default)) % 360)
                self.sld_section_angle.blockSignals(False)
                self._section_angle_deg = float(default)
                self.lbl_section_angle.setText(f"{int(default)%360}\u00b0")
        self._update_long_section()
        self._refresh_anchor_options()
        # If an anchor is selected, also populate defaults
        if self._anchor_role():
            self._populate_buildup_defaults()
            self._rebuild_constructed()

    def _refresh_ring_table(self):
        """Rebuild the ring table from self._preview.

        When 'show all detected rings' is off (default), only show:
          - rings currently assigned to a role (so the table stays tight when
            auto-id picked the 4 cleanly)
          - if no roles are assigned at all (auto-id failed), all rings are
            shown so the user can pick manually
        Toggle on to always show all detected rings.
        """
        self._table_building = True
        if self._preview is None:
            self.tbl_rings.setRowCount(0)
            self._role_widgets = []
            self._row_to_ring_idx = []
            self._table_building = False
            return

        rings = self._preview['all_rings']
        n_const = self._preview.get('n_const', len(rings))
        show_all = self.chk_show_all_rings.isChecked()
        assigned = set(self._role_assignments.values())
        # Default behaviour:
        #   - All 4 dam roles assigned (typically by auto-id): show only those
        #     4 rings so the table stays tight.
        #   - Fewer than 4 assigned: show all rings so the user can complete
        #     the assignment (the plan view still highlights the assigned ones
        #     in colour, so the partial state is visible there).
        # Toggle 'Show all detected rings' overrides to always show all.
        # IMPORTANT: var-Z rings are ALWAYS available even when the default
        # behaviour would hide them, because the actual outer toe of a real
        # dam is usually a var-Z polyline and the user must be able to see
        # and assign it.
        if show_all or len(assigned) < 4:
            indices_to_show = list(range(len(rings)))
        else:
            indices_to_show = sorted(assigned)
            # Always include var-Z rings so the user can spot them
            for i in range(n_const, len(rings)):
                if i not in indices_to_show:
                    indices_to_show.append(i)
            indices_to_show.sort()

        self.tbl_rings.setRowCount(len(indices_to_show))
        self._role_widgets = []
        self._row_to_ring_idx = list(indices_to_show)

        # Per-ring colour palette - used by BOTH the table (column 0
        # background) and the plan view (line + index-label colour). If
        # a ring is role-assigned, its colour comes from the role
        # palette; otherwise it gets a stable per-index colour from
        # this palette so the user can visually match the row to the
        # ring on the plan view.
        unassigned_palette = [
            '#9467bd', '#8c564b', '#e377c2', '#7f7f7f',
            '#bcbd22', '#17becf', '#a02c2c', '#5f6d8e',
            '#9c8550', '#3a8754', '#c34b94', '#6b489d',
        ]
        idx_to_role = {idx: role for role, idx
                       in self._role_assignments.items()}
        role_colours_local = {
            'inner_toe':   '#1f77b4', 'inner_crest': '#2ca02c',
            'outer_crest': '#d62728', 'outer_toe':   '#ff7f0e',
        }
        # Build a stable index->colour map for ALL rings (not just those
        # shown in the table). The plan view iterates every ring; if a
        # ring isn't in the map it gets a fallback gray that doesn't
        # match the table colour. Building for every index keeps the
        # plan view and table consistent regardless of which rings are
        # shown vs hidden by the default-key-candidates filter.
        self._ring_colour_by_idx = {}
        unassigned_counter = 0
        for i in range(len(rings)):
            role = idx_to_role.get(i)
            if role and role != 'ignore':
                self._ring_colour_by_idx[i] = role_colours_local[role]
            else:
                self._ring_colour_by_idx[i] = unassigned_palette[
                    unassigned_counter % len(unassigned_palette)]
                unassigned_counter += 1

        from qgis.PyQt.QtGui import QColor, QBrush
        for row, i in enumerate(indices_to_show):
            r = rings[i]
            is_var = i >= n_const
            xs = [c[0] for c in r['coords']]
            ys = [c[1] for c in r['coords']]
            ext = f"{max(xs)-min(xs):.0f} \u00d7 {max(ys)-min(ys):.0f}"
            # Mark var-Z rings explicitly so the user knows what they are
            id_label = f"V{i - n_const + 1}" if is_var else str(i + 1)
            id_item = QTableWidgetItem(id_label)
            # Background-colour the index cell so the row visibly
            # matches the plotted ring's colour. Use a light tint
            # rather than the saturated line colour so the text stays
            # readable.
            try:
                base_hex = self._ring_colour_by_idx.get(i, '#888888')
                qc = QColor(base_hex)
                # Lighten by mixing with white
                light = QColor(
                    int(qc.red()   * 0.35 + 255 * 0.65),
                    int(qc.green() * 0.35 + 255 * 0.65),
                    int(qc.blue()  * 0.35 + 255 * 0.65))
                id_item.setBackground(QBrush(light))
            except Exception:
                pass
            # Make the '#' cell a visibility checkbox for the plan view.
            id_item.setFlags((id_item.flags() | Qt.ItemIsUserCheckable)
                             & ~Qt.ItemIsEditable)
            id_item.setCheckState(
                Qt.Checked if self._ring_visible.get(i, True)
                else Qt.Unchecked)
            id_item.setToolTip("Tick to show this ring in the plan view; "
                               "untick to hide it.")
            self.tbl_rings.setItem(row, 0, id_item)
            if is_var:
                z_str = f"{r['z_min']:.2f}\u2013{r['z_max']:.2f}"
            else:
                z_str = f"{r['z_mean']:.3f}"
            self.tbl_rings.setItem(row, 1, QTableWidgetItem(z_str))
            self.tbl_rings.setItem(row, 2, QTableWidgetItem(str(r['npts'])))
            self.tbl_rings.setItem(row, 3, QTableWidgetItem(ext))
            self.tbl_rings.setItem(row, 4, QTableWidgetItem(f"{r['area']:.0f}"))
            cb = QComboBox()
            cb.addItem("(unassigned)", "")
            cb.addItem("Inner toe", "inner_toe")
            cb.addItem("Inner crest", "inner_crest")
            cb.addItem("Outer crest", "outer_crest")
            cb.addItem("Outer toe", "outer_toe")
            cb.addItem("Ignore", "ignore")
            # Pre-select the assigned role for this ring, if any
            for role, idx in self._role_assignments.items():
                if idx == i:
                    ci = cb.findData(role)
                    if ci >= 0:
                        cb.setCurrentIndex(ci)
                    break
            cb.currentIndexChanged.connect(
                lambda _, rr=row: self._on_role_changed(rr))
            self.tbl_rings.setCellWidget(row, 5, cb)
            self._role_widgets.append(cb)
        self._table_building = False

    def _on_ring_item_changed(self, item):
        """A '#'-cell checkbox toggled -> show/hide that ring in the plan."""
        if self._table_building or item is None or item.column() != 0:
            return
        if not self._row_to_ring_idx:
            return
        row = item.row()
        if row < 0 or row >= len(self._row_to_ring_idx):
            return
        ring_idx = self._row_to_ring_idx[row]
        self._ring_visible[ring_idx] = (item.checkState() == Qt.Checked)
        self._render_plan_view()

    def _on_ring_selection_changed(self):
        """Row selected -> highlight that ring in the plan view."""
        if self._table_building:
            return
        idx = None
        row = self.tbl_rings.currentRow()
        if self._row_to_ring_idx and 0 <= row < len(self._row_to_ring_idx):
            idx = self._row_to_ring_idx[row]
        self._selected_ring_idx = idx
        self._render_plan_view()

    def _isolate_selected_ring(self):
        """Hide every ring except the table's currently-selected one."""
        if self._preview is None or self._selected_ring_idx is None:
            return
        n = len(self._preview['all_rings'])
        sel = self._selected_ring_idx
        self._ring_visible = {i: (i == sel) for i in range(n)}
        self._refresh_ring_table()
        self._render_plan_view()

    def _show_all_rings_visible(self):
        """Make every ring visible in the plan view again."""
        if self._preview is None:
            return
        self._ring_visible = {}
        self._refresh_ring_table()
        self._render_plan_view()

    def _on_role_changed(self, row):
        """A role dropdown changed in displayed-row `row`. Translate through
        self._row_to_ring_idx and update self._role_assignments accordingly."""
        if self._preview is None or not self._row_to_ring_idx:
            return
        # Start from the existing assignments and update only what's visible
        # in the table - this preserves any assignments for rings that have
        # been filtered out of view.
        new_assignments = dict(self._role_assignments)
        # Strip any role currently held by a visible ring (so swaps work)
        visible_ring_indices = set(self._row_to_ring_idx)
        new_assignments = {r: i for r, i in new_assignments.items()
                           if i not in visible_ring_indices}
        # Add in the current visible-row assignments
        for displayed_row, cb in enumerate(self._role_widgets):
            role = cb.currentData()
            if not role or role == 'ignore':
                continue
            ring_idx = self._row_to_ring_idx[displayed_row]
            if role in new_assignments:
                # Conflict: another visible ring already holds this role.
                # Keep the first one, demote later duplicates to unassigned.
                cb.blockSignals(True)
                cb.setCurrentIndex(0)
                cb.blockSignals(False)
                continue
            new_assignments[role] = ring_idx
        self._role_assignments = new_assignments
        self._render_plan_view()
        self._update_inferred_params()
        self._update_cross_sections()
        # Phase 2: anchor dropdown depends on assignments
        self._refresh_anchor_options()
        if self._anchor_role():
            self._populate_buildup_defaults()
            self._rebuild_constructed()

    def _current_role_to_ring(self):
        """Return {role: ring_dict} for currently-assigned roles. Indexes
        into the combined const+var ring list so a variable-Z polyline
        can be assigned as outer_toe (or any other role)."""
        out = {}
        if self._preview is None:
            return out
        rings = self._preview['all_rings']
        for role, idx in self._role_assignments.items():
            if 0 <= idx < len(rings):
                out[role] = rings[idx]
        return out

    def _render_plan_view(self):
        """Plot every detected const-Z ring on the plan-view canvas. Tagged
        rings get a coloured outline matching the role; unassigned/ignored
        rings are grey. Each ring is annotated with its index."""
        if not HAS_MPL or self._preview is None:
            return
        self._plan_fig.clear()
        ax = self._plan_fig.add_subplot(111)
        ax.set_aspect('equal')
        rings = self._preview['all_rings']
        n_const = self._preview.get('n_const', len(rings))
        if not rings:
            ax.text(0.5, 0.5, "No rings", ha='center', va='center',
                    transform=ax.transAxes)
            self._plan_canvas.draw_idle()
            return

        # Colour scheme by role
        role_colours = {
            'inner_toe':   '#1f77b4',  # blue
            'inner_crest': '#2ca02c',  # green
            'outer_crest': '#d62728',  # red
            'outer_toe':   '#ff7f0e',  # orange
        }
        idx_to_role = {idx: role for role, idx in self._role_assignments.items()}
        # Pull the per-index colour map populated by _refresh_ring_table.
        # If not yet built (table hasn't been redrawn), fall back to a
        # gray for unassigned rings - the table will repopulate the map
        # next refresh.
        ring_colour_by_idx = getattr(self, '_ring_colour_by_idx', {})

        # Selection highlight: when a (visible) ring is selected in the table,
        # draw it bold with a halo and dim the rest so it's unmistakable.
        sel = self._selected_ring_idx
        if sel is not None and not self._ring_visible.get(sel, True):
            sel = None

        for i, r in enumerate(rings):
            # Visibility toggle from the ring table's '#' checkboxes.
            if not self._ring_visible.get(i, True):
                continue
            coords = r['coords']
            xs = [c[0] for c in coords]
            ys = [c[1] for c in coords]
            # Close the line visually. Ring dicts (from step3_classify and
            # _ring_dict_from_xy) strip the closing duplicate vertex, so
            # without re-adding the first point at the end, matplotlib
            # draws an open polyline with a visible gap between v(N-1)
            # and v0. Mirrors what the constructed-overlay block does.
            if xs and ys:
                xs.append(xs[0]); ys.append(ys[0])
            role = idx_to_role.get(i)
            is_var = i >= n_const
            is_selected = (sel is not None and i == sel)
            dim = (sel is not None and not is_selected)
            alpha = 0.18 if dim else 1.0
            # Colour priority: shared map (matches the ring table cell
            # background) -> role colour -> gray.
            colour = ring_colour_by_idx.get(
                i, role_colours.get(role, '#888888'))
            base_lw = 2.2 if role else 1.0
            lw = 3.6 if is_selected else base_lw
            # var-Z rings drawn with a dashed style so they stand out from
            # the dense const-Z contour stack
            ls = '--' if (is_var and role is None) else '-'
            if is_selected:
                # black halo behind the bold coloured line
                ax.plot(xs, ys, color='black', linewidth=lw + 2.6,
                        alpha=0.4, zorder=8)
            ax.plot(xs, ys, color=colour, linewidth=lw, linestyle=ls,
                    alpha=alpha,
                    label=role.replace('_', ' ').title() if role else None,
                    zorder=9 if is_selected else (3 if role else 2))
            # Index label at the topmost point. Show all labels when nothing
            # is selected; only the selected ring's when one is, to keep the
            # highlight clean. V-prefix for var-Z rings.
            if sel is None or is_selected:
                top_idx = max(range(len(coords)), key=lambda k: coords[k][1])
                id_label = f"V{i - n_const + 1}" if is_var else f"{i + 1}"
                ax.annotate(id_label, (xs[top_idx], ys[top_idx]),
                            fontsize=11 if is_selected else 10,
                            fontweight='bold', color=colour,
                            xytext=(6, 6), textcoords='offset points',
                            bbox=dict(boxstyle="round,pad=0.2",
                                      fc='white', ec=colour,
                                      lw=1.6 if is_selected else 1.0))

        # Overlay constructed rings (Phase 2) when build-up has produced a
        # kl, regardless of whether Use-Constructed-for-Run is ticked - the
        # user wants to see the construction before deciding to use it.
        #
        # EXCEPT in polygon mode: there, _preview['all_rings'] IS the
        # constructed rings (set by _build_from_polygon_input), so the
        # overlay would just draw the same 4 rings a second time. Any
        # subpixel vertex difference at the closure point of buffer()-
        # generated rings then appears as a "ghost" dotted extension at
        # one corner. Suppress the overlay in polygon mode.
        show_constructed_overlay = (
            self._constructed_kl is not None
            and not (self._preview is not None
                     and self._preview.get('polygon_mode')))
        if show_constructed_overlay:
            built_colours = {
                'inner_toe':   '#1f77b4', 'inner_crest': '#2ca02c',
                'outer_crest': '#d62728', 'outer_toe':   '#ff7f0e',
            }
            ls = '--' if self.chk_use_constructed.isChecked() else ':'
            lw = 2.4 if self.chk_use_constructed.isChecked() else 1.5
            label_added = False
            for role, colour in built_colours.items():
                ring = self._constructed_kl.get(role)
                if ring is None:
                    continue
                bxs = [c[0] for c in ring['coords']]
                bys = [c[1] for c in ring['coords']]
                # Close the line visually
                bxs.append(bxs[0]); bys.append(bys[0])
                lbl = "Constructed (build-up)" if not label_added else None
                ax.plot(bxs, bys, color=colour, linewidth=lw, linestyle=ls,
                        label=lbl, zorder=4, alpha=0.85)
                label_added = True

        # Overlay section axis line — through dam centroid at current
        # section angle. Drawn on top so the user can see exactly which
        # cut the long section corresponds to. Marker at the centroid +
        # arrowhead in the +direction so the section's left/right matches
        # the long section's left/right.
        center, direction = self._section_axis()
        if center is not None and direction is not None:
            L = self._section_half_length()
            x0 = center[0] - L * direction[0]
            y0 = center[1] - L * direction[1]
            x1 = center[0] + L * direction[0]
            y1 = center[1] + L * direction[1]
            ax.plot([x0, x1], [y0, y1], color='#9933cc', linewidth=1.6,
                    linestyle='-', alpha=0.85, zorder=6,
                    label='Section axis')
            ax.scatter([center[0]], [center[1]], color='#9933cc', s=40,
                        marker='o', edgecolors='white', linewidths=1.2,
                        zorder=7)
            # Arrowhead at +direction end (matches RIGHT side of long
            # section)
            ax.annotate('', xy=(x1, y1),
                         xytext=(center[0] + 0.85*L*direction[0],
                                 center[1] + 0.85*L*direction[1]),
                         arrowprops=dict(arrowstyle='->',
                                         color='#9933cc', lw=1.8),
                         zorder=7)
            # Mark where the section axis intersects each design ring -
            # large coloured dots that exactly match the corresponding
            # markers on the long section below. Lets the user visually
            # verify "the orange dot in the section IS where the purple
            # line crosses the orange ring", without needing to mentally
            # project chainage back to plan coordinates.
            xover_colours = {
                'inner_toe':   '#1f77b4', 'inner_crest': '#2ca02c',
                'outer_crest': '#d62728', 'outer_toe':   '#ff7f0e',
            }
            if self._is_constructed_active():
                xover_rings = dict(self._constructed_kl)
            else:
                xover_rings = self._current_role_to_ring()
            for role, colour in xover_colours.items():
                r = xover_rings.get(role)
                if r is None:
                    continue
                cr = self._ring_line_crossings(
                    r['coords'], center, direction)
                for t, _z in cr:
                    if abs(t) > L:
                        continue
                    px = center[0] + t * direction[0]
                    py = center[1] + t * direction[1]
                    ax.scatter([px], [py], color=colour, s=55,
                                marker='o', edgecolors='white',
                                linewidths=1.2, zorder=8)

        # De-duplicate legend entries
        handles, labels = ax.get_legend_handles_labels()
        seen = set(); kept = []
        for h, l in zip(handles, labels):
            if l and l not in seen:
                seen.add(l)
                kept.append((h, l))
        if kept:
            ax.legend([h for h, _ in kept], [l for _, l in kept],
                      loc='best', fontsize=8, framealpha=0.9)
        ax.set_xlabel("Easting (m)")
        ax.set_ylabel("Northing (m)")
        ax.grid(True, alpha=0.3)
        self._plan_canvas.draw_idle()

    def _update_inferred_params(self):
        """Recompute inferred design parameters from current role assignments
        and update the labels. Z elevations show the offset-adjusted values
        so what the user sees is what the design will look like in NZVD2016
        after the datum correction is applied."""
        # In manual-entry mode the editable spinboxes hold the user's
        # typed design values - don't overwrite them with auto-inferred
        # ones. (The read-only labels are hidden in this mode anyway.)
        if getattr(self, 'chk_manual_params', None) is not None \
                and self.chk_manual_params.isChecked():
            return
        if self._preview is None:
            for lbl in self._inf_labels.values():
                lbl.setText("\u2014")
            return
        m = compute_inferred_metrics(self._current_role_to_ring(),
                                      self._preview)
        offset = self._z_offset_value()
        def _fmt_m(v):  return f"{v:.2f} m" if v is not None else "\u2014"
        def _fmt_z(v):
            if v is None: return "\u2014"
            if abs(offset) > 1e-6:
                return f"{v + offset:.2f} m  (DXF {v:.2f} + {offset:+.2f})"
            return f"{v:.2f} m"
        def _fmt_hv(v, src):
            if v is None: return "\u2014"
            tag = ""
            if src == 'contours': tag = "  (from batter contours)"
            elif src == 'crest-to-toe': tag = "  (crest \u2192 toe)"
            return f"{v:.2f} : 1{tag}"
        self._inf_labels['crest_z'].setText(_fmt_z(m['crest_z']))
        self._inf_labels['invert_z'].setText(_fmt_z(m['invert_z']))
        self._inf_labels['outer_toe_z'].setText(_fmt_z(m['outer_toe_z']))
        self._inf_labels['depth'].setText(_fmt_m(m['depth']))
        self._inf_labels['crest_width'].setText(_fmt_m(m['crest_width']))
        self._inf_labels['inner_hv'].setText(
            _fmt_hv(m['inner_hv'], m.get('inner_hv_source')))
        self._inf_labels['outer_hv'].setText(
            _fmt_hv(m['outer_hv'], m.get('outer_hv_source')))

    def _z_offset_value(self):
        """Helper - safely read the offset spinbox (it may not exist yet if
        the dialog is mid-build)."""
        try:
            return float(self.spn_z_offset.value())
        except Exception:
            return 0.0

    def _on_manual_params_toggled(self, on):
        """Switch the Inferred-design-parameters panel between read-only
        display (auto mode) and editable spinboxes (manual mode).

        On entering manual mode, pre-fill the spinboxes from whatever the
        auto-inference produced (so the user starts from a sensible guess
        rather than zero), and seed crest_z / invert_z from the assigned
        anchor ring's own elevation."""
        for key, lbl in self._inf_labels.items():
            lbl.setVisible(not on)
        for key, spn in self._inf_edits.items():
            spn.setVisible(on)
        self._build_from_ring_btn.setVisible(on)
        if hasattr(self, 'lbl_manual_build_status'):
            self.lbl_manual_build_status.setVisible(on)
        if on:
            self._prefill_manual_params()

    def _prefill_manual_params(self):
        """Seed the manual-entry spinboxes with current best-guess values:
        inferred metrics where available, the assigned anchor ring's Z for
        the elevation datum, and sensible engineering defaults otherwise."""
        kl = self._current_role_to_ring()
        m = {}
        try:
            if self._preview is not None:
                m = compute_inferred_metrics(kl, self._preview) or {}
        except Exception:
            m = {}
        # Anchor ring Z (the one assigned role). Used to seed the datum.
        anchor_z = None
        anchor_role = None
        for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
            r = kl.get(role)
            if r is not None:
                anchor_z = float(r.get('z_mean', 0.0))
                anchor_role = role
                break
        # Defaults (typical NZ farm dam): crest width 5 m, batters 3:1,
        # 4 m structural depth if nothing better is known.
        defaults = {
            'crest_width': 5.0, 'inner_hv': 3.0, 'outer_hv': 3.0,
            'depth': 4.0,
        }
        # Seed crest/invert from anchor + role so the datum is the
        # anchor's own elevation (per the agreed behaviour).
        crest_z = m.get('crest_z')
        invert_z = m.get('invert_z')
        if anchor_z is not None and anchor_role is not None:
            depth = m.get('depth') or defaults['depth']
            if anchor_role == 'inner_toe':
                invert_z = anchor_z
                crest_z = anchor_z + depth
            elif anchor_role in ('inner_crest', 'outer_crest'):
                crest_z = anchor_z
                invert_z = anchor_z - depth
        vals = {
            'crest_z': crest_z if crest_z is not None else (anchor_z or 0.0),
            'invert_z': invert_z if invert_z is not None
                        else ((anchor_z or 0.0) - defaults['depth']),
            'outer_toe_z': m.get('outer_toe_z')
                           if m.get('outer_toe_z') is not None
                           else (invert_z or 0.0),
            'depth': m.get('depth') or defaults['depth'],
            'crest_width': m.get('crest_width') or defaults['crest_width'],
            'inner_hv': m.get('inner_hv') or defaults['inner_hv'],
            'outer_hv': m.get('outer_hv') or defaults['outer_hv'],
        }
        for key, spn in self._inf_edits.items():
            try:
                spn.blockSignals(True)
                spn.setValue(float(vals.get(key, 0.0)))
                spn.blockSignals(False)
            except Exception:
                pass

    def _build_dam_from_assigned_ring(self):
        """Manual-entry build: take the single assigned anchor ring from
        the role table + the typed design parameters, and construct the
        full 4-ring dam via construct_dam_rings_from_anchor (the same
        engine polygon mode uses). Handles DXFs with incomplete rings
        (missing, or cut by the spillway) - only one complete const-Z
        ring needs a role.

        The anchor ring's own Z is the datum; the typed crest_z / depth
        are interpreted against it. After building, the Vertical-offset
        controls (lift/drop, snap-to-ground) still apply before Run.
        """
        kl_assigned = self._current_role_to_ring()
        # Find the one assigned anchor ring + its role.
        anchor_role = None
        anchor_ring = None
        for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
            r = kl_assigned.get(role)
            if r is not None:
                anchor_role = role
                anchor_ring = r
                break
        if anchor_ring is None:
            self._set_manual_build_status(
                "<font color='#c00'>No ring assigned. Assign a role to "
                "one complete const-Z ring in the table above, then "
                "build.</font>")
            return
        if anchor_role == 'outer_toe':
            # Outer toe is variable-Z terrain-following; it can't anchor a
            # const-Z construction. Ask for one of the other three.
            self._set_manual_build_status(
                "<font color='#c00'>Anchor on a const-Z ring (inner toe, "
                "inner crest, or outer crest) - the outer toe is "
                "terrain-following and can't anchor the build.</font>")
            return

        # Read typed parameters
        try:
            crest_z = float(self._inf_edits['crest_z'].value())
            invert_z = float(self._inf_edits['invert_z'].value())
            crest_width = float(self._inf_edits['crest_width'].value())
            inner_hv = float(self._inf_edits['inner_hv'].value())
            outer_hv = float(self._inf_edits['outer_hv'].value())
        except Exception as e:
            self._set_manual_build_status(
                f"<font color='#c00'>Bad parameter value: {e}</font>")
            return

        # Outer toe Z: artificial-deep (well below invert) so the build
        # produces a clean const-Z toe; the real toe comes later from the
        # terrain cut (Method 2), same as every other flow in the tool.
        outer_toe_z = invert_z - 50.0

        params = {
            'crest_z': crest_z, 'invert_z': invert_z,
            'outer_toe_z': outer_toe_z, 'crest_width': crest_width,
            'inner_hv': inner_hv, 'outer_hv': outer_hv,
        }
        sp = float(self.spn_spacing.value()
                   if hasattr(self, 'spn_spacing') else 0.1)
        try:
            kl = construct_dam_rings_from_anchor(
                anchor_ring, anchor_role, params, sp=sp)
        except ValueError as e:
            self._set_manual_build_status(
                f"<font color='#c00'>Construction failed: {e}</font>")
            return
        except Exception as e:
            self._set_manual_build_status(
                f"<font color='#c00'>Construction error: {e}</font>")
            return

        # Stash exactly like the polygon/anchor flow so the Geometry tab,
        # long section, vertical-offset snaps and Run pipeline all work
        # identically on the constructed rings.
        self._constructed_kl = kl
        all_rings = [kl['inner_toe'], kl['inner_crest'],
                     kl['outer_crest'], kl['outer_toe']]
        self._preview = {
            'success': True, 'errors': [], 'warnings': [],
            'auto_classified': kl,
            'all_const_z': all_rings,
            'all_rings': all_rings,
            'auto_indices': {'inner_toe': 0, 'inner_crest': 1,
                             'outer_crest': 2, 'outer_toe': 3},
        }
        self._role_assignments = {'inner_toe': 0, 'inner_crest': 1,
                                  'outer_crest': 2, 'outer_toe': 3}
        # The constructed dam is in DXF datum (anchor's Z); the user can
        # still lift/drop it. It hasn't moved off any DXF toe yet.
        self._dam_moved_off_dxf_toe = False
        self._set_manual_build_status(
            f"<font color='#080'>Built 4 rings</font> from the "
            f"{anchor_role.replace('_', ' ')} anchor (Z={anchor_ring.get('z_mean', 0):.2f}). "
            f"Crest {crest_z:.2f}, invert {invert_z:.2f}, width "
            f"{crest_width:.1f} m, batters {inner_hv:.1f}:1 / "
            f"{outer_hv:.1f}:1. Use the Vertical offset controls to "
            f"lift/drop or snap before Run.")
        # Refresh all dependent views
        try:
            self._render_plan_view()
            self._update_long_section()
            self._refresh_ring_table()
        except Exception:
            pass

    def _set_manual_build_status(self, html):
        """Show status for the manual build under the inferred-params
        panel (re-using the keyline status label if present, else log)."""
        lbl = getattr(self, 'lbl_manual_build_status', None)
        if lbl is not None:
            try:
                lbl.setText(html)
                return
            except Exception:
                pass
        # Fallback: strip tags and log
        import re as _re
        LOG.info(_re.sub(r'<[^>]+>', '', html))

    def _on_z_offset_changed(self, _val=None):
        """Spinbox changed - re-centre the slider on the new value and
        refresh any visuals that depend on Z."""
        # Re-centre the slider so the new spinbox value corresponds to
        # slider position 0 (gives full +/- 50 m range either way from
        # here). Block signals to avoid recursion.
        try:
            self._sld_z_offset_centre = float(self.spn_z_offset.value())
            self.sld_z_offset.blockSignals(True)
            self.sld_z_offset.setValue(0)
            self.sld_z_offset.blockSignals(False)
        except Exception:
            pass
        if self._preview is None:
            return
        self._update_inferred_params()
        self._update_long_section()

    def _on_z_offset_slider_changed(self, slider_val):
        """Slider moved - convert to a delta in metres and push to the
        spinbox. The spinbox's valueChanged handler will refresh visuals."""
        # slider_val is an int in [-500, 500] representing 0.1 m steps.
        delta = slider_val / 10.0
        new_val = self._sld_z_offset_centre + delta
        # Manually dragging the lift/drop slider moves the dam relative
        # to the DXF datum, so the DXF's baked-in outer toe (Method 1) is
        # stale -> prefer the terrain-intersection toe (Method 2) at
        # output. A zero delta (slider back at centre) doesn't count.
        if abs(delta) > 1e-6:
            self._dam_moved_off_dxf_toe = True
        # Block the spinbox signal so it doesn't re-centre the slider
        # (which would reset our slider value to 0 mid-drag).
        self.spn_z_offset.blockSignals(True)
        self.spn_z_offset.setValue(new_val)
        self.spn_z_offset.blockSignals(False)
        # Manually fire the downstream refresh
        if self._preview is not None:
            self._update_inferred_params()
            self._update_long_section()

    def _on_section_angle_changed(self, deg):
        """Section rotation slider moved - update label and redraw."""
        self._section_angle_deg = float(deg)
        self.lbl_section_angle.setText(f"{int(deg)}\u00b0")
        # Re-render plan view too (the section axis line on the plan view
        # needs to follow the rotation)
        self._render_plan_view()
        self._update_long_section()

    def _snap_section_to_lowhigh(self):
        """Snap the section rotation to the low-to-high ground-gradient
        direction across the outer_crest perimeter."""
        deg = self._default_section_angle_deg()
        if deg is None:
            return
        # Push to slider (which fires _on_section_angle_changed)
        # Normalise into [0, 359]
        deg_int = int(round(deg)) % 360
        self.sld_section_angle.setValue(deg_int)

    def _reset_to_artificial_deep_toe(self):
        """Restore the outer toe ring to its as-constructed
        artificial-deep design polygon, and reset z_offset to 0.
        Undoes any Method 2 cut and any snap that shifted z_offset.

        The artificial deep coords are stashed under either:
          - ot['artificial_const_coords'] (set by step4d in DXF flow)
          - ot['nominal_const_coords'] (set by _build_from_polygon_input
            in polygon flow, or by the first cut_outer_toe_to_terrain
            call in DXF+anchor flow)
        Try each in turn; if neither exists, fall back to the current
        coords (nothing to reset).
        """
        kl = (self._constructed_kl
              if self._constructed_kl
              else self._current_role_to_ring())
        if not kl or 'outer_toe' not in kl:
            self.lbl_snap_status.setText(
                "Nothing to reset - no outer toe ring loaded.")
            return
        ot = kl['outer_toe']
        restored_from = None
        # Prefer artificial_const_coords (cleanest source of truth)
        if ot.get('artificial_const_coords'):
            ac = ot['artificial_const_coords']
            ot['coords'] = [(c[0], c[1], c[2]) for c in ac]
            ot['z_mean'] = float(ot.get('artificial_const_z',
                                         ac[0][2] if ac else 0.0))
            restored_from = 'artificial_const_coords (step4d)'
        elif ot.get('nominal_const_coords'):
            nc = ot['nominal_const_coords']
            ot['coords'] = [(c[0], c[1], c[2]) for c in nc]
            ot['z_mean'] = float(ot.get('nominal_const_z',
                                         nc[0][2] if nc else 0.0))
            restored_from = 'nominal_const_coords (build/pre-cut)'
        else:
            self.lbl_snap_status.setText(
                "No artificial-deep snapshot available to restore. "
                "Rebuild the dam (polygon mode: click Build; DXF mode: "
                "reload the DXF).")
            return
        ot['z_min'] = ot['z_mean']
        ot['z_max'] = ot['z_mean']
        ot['z_std'] = 0.0
        ot['npts'] = len(ot['coords'])
        ot['is_variable_z'] = False
        ot['cut_to_terrain'] = False
        ot['method'] = None

        # Clear any Method 2 snapshot so the radio doesn't re-apply
        try:
            self._var_z_outer_toes['method2'] = None
        except Exception:
            pass
        # Default the radio back to Method 1 (which may itself be empty)
        try:
            if self._var_z_outer_toes.get('method1') is not None:
                self._active_var_z_method = 'method1'
                self.rb_otm_method1.setChecked(True)
            self._refresh_otm_status()
        except Exception:
            pass

        # Reset z_offset to 0
        try:
            self.spn_z_offset.setValue(0.0)
        except Exception:
            pass
        try:
            self.sld_z_offset.setValue(0)
            self._sld_z_offset_centre = 0.0
        except Exception:
            pass
        # Reset clears the dam-moved flag - we're back to the clean
        # as-constructed state with z_offset 0.
        self._dam_moved_off_dxf_toe = False

        # Refresh visuals
        try: self._render_plan_view()
        except Exception: pass
        try: self._update_long_section()
        except Exception: pass

        self.lbl_snap_status.setText(
            f"Reset: outer toe restored from {restored_from}, "
            f"z_offset = 0.00 m. {ot['npts']} vertices at Z="
            f"{ot['z_mean']:.2f} m. Method 2 snapshot cleared.")

    def _snap_outer_toe_to_ground(self):
        """Auto-set the vertical offset so the outer toe sits on the DEM
        ground (minimising the mean delta around the outer-toe perimeter).
        Requires the outer_toe role to be assigned AND a terrain DEM."""
        if self._preview is None:
            self.lbl_snap_status.setText("No DXF loaded.")
            return
        ot = self._current_role_to_ring().get('outer_toe')
        if ot is None:
            self.lbl_snap_status.setText(
                "Assign a ring as 'Outer toe' first.")
            return
        if self._terrain_layer is None:
            self.lbl_snap_status.setText(
                "Select a terrain DEM on the Input tab first.")
            return
        coords = ot['coords']
        if not coords:
            self.lbl_snap_status.setText("Outer toe ring has no vertices.")
            return
        ll = llen(coords)
        if ll < 1.0:
            self.lbl_snap_status.setText("Outer toe ring is degenerate.")
            return
        dp = self._terrain_layer.dataProvider()
        if dp is None:
            self.lbl_snap_status.setText(
                "Terrain DEM has no data provider.")
            return
        n_samples = 120
        samples = []
        outside_count = 0
        for j in range(n_samples):
            ch = ll * j / n_samples
            pt = interp_ch(coords, ch)
            try:
                res = dp.sample(QgsPointXY(pt[0], pt[1]), 1)
                if res is None:
                    outside_count += 1
                    continue
                val, ok = res
                if not ok or val is None:
                    outside_count += 1
                    continue
                samples.append(float(val))
            except Exception:
                outside_count += 1
                continue
        if not samples:
            self.lbl_snap_status.setText(
                "No DEM samples available - outer toe perimeter may "
                "be outside the DEM extent.")
            return
        # Mean minimises the L2 mean-squared delta (the user's "average
        # delta"); also report the median + range for context.
        mean_z = sum(samples) / len(samples)
        samples_sorted = sorted(samples)
        n = len(samples_sorted)
        median_z = samples_sorted[n//2] if n % 2 \
                   else (samples_sorted[n//2-1] + samples_sorted[n//2])/2
        z_min = samples_sorted[0]; z_max = samples_sorted[-1]
        offset = mean_z - ot['z_mean']
        # Set the spinbox (silently re-renders via valueChanged signal)
        self.spn_z_offset.setValue(offset)
        # Snap-to-ground REALIGNS the dam so the DXF's own outer toe sits
        # on the ground. That makes Method 1 (the DXF toe) valid again,
        # so clear the "dam moved off DXF toe" flag - Method 1 stays the
        # preferred toe source at output.
        self._dam_moved_off_dxf_toe = False
        coverage = f"{len(samples)}/{n_samples} samples"
        if outside_count:
            coverage += f" ({outside_count} outside DEM)"
        self.lbl_snap_status.setText(
            f"Snapped: mean ground at outer toe perimeter = "
            f"{mean_z:.2f} m  (median {median_z:.2f}, range "
            f"{z_min:.2f} \u2013 {z_max:.2f}). "
            f"DXF outer toe = {ot['z_mean']:.2f} m \u2192 "
            f"offset = {offset:+.3f} m. {coverage}.")

    def _snap_z_offset_to_cut_fill_balance(self):
        """Sweep z_offset values; pick the one where fill volume (dam
        cells above terrain) = cut volume (dam cells below terrain)
        times the user's multiplier.

        Used when there's no outer toe polygon to anchor to terrain
        (polygon mode without partial contours, or DXF where the outer
        toe is artificial). Adjusts the SAME spinbox as Snap-to-Ground
        but uses a volumetric balance criterion rather than minimising
        the mean toe-to-ground delta.

        Algorithm:
          1. Sample terrain on a grid covering the dam's outer_toe ring
          2. Compute dam_z at each sample point ONCE (at z_offset=0)
             using piecewise design slopes
          3. For each candidate z_offset shift, dam_z' = dam_z + offset.
             Cut/fill follow as simple sums - no need to reconstruct
             rings, no need to re-sample terrain.
          4. Find offset where |fill - cut * mult| is minimised
        """
        # Validate state
        kl = self._current_role_to_ring()
        if not kl or not kl.get('outer_toe') or not kl.get('outer_crest'):
            self.lbl_snap_status.setText(
                "Need all 4 design rings - assign roles (DXF mode) or "
                "click Build (polygon mode) first.")
            return
        if self._terrain_layer is None:
            self.lbl_snap_status.setText(
                "Select a terrain DEM on the Input tab first.")
            return
        dp = self._terrain_layer.dataProvider()
        if dp is None:
            self.lbl_snap_status.setText(
                "Terrain DEM has no data provider.")
            return
        mult = float(self.spn_z_offset_cf_mult.value())

        # Gather geometry
        ot = kl['outer_toe']
        it = kl.get('inner_toe', {})
        oc = kl['outer_crest']
        ic = kl.get('inner_crest', {})
        ot_coords = ot['coords']
        it_coords = it.get('coords', [])
        oc_coords = oc['coords']
        ic_coords = ic.get('coords', [])
        if not ot_coords or not oc_coords:
            self.lbl_snap_status.setText(
                "Outer toe or outer crest ring is empty.")
            return

        crest_z = float(oc.get('z_mean', CFG.get('crest', 0)))
        invert_z = float(it.get('z_mean', CFG.get('invert', crest_z)))
        outer_hv = float(CFG.get('outer_hv', 3.5))
        inner_hv = float(CFG.get('inner_hv', 3.5))

        try:
            ot_q = [QgsPointXY(c[0], c[1]) for c in ot_coords]
            ot_poly = QgsGeometry.fromPolygonXY([ot_q])
            it_q = ([QgsPointXY(c[0], c[1]) for c in it_coords]
                    if it_coords else None)
            it_poly = (QgsGeometry.fromPolygonXY([it_q])
                       if it_q else None)
        except Exception as e:
            self.lbl_snap_status.setText(
                f"Failed to build polygons: {e}")
            return

        oc_xy = [(c[0], c[1]) for c in oc_coords]
        ic_xy = [(c[0], c[1]) for c in ic_coords] if ic_coords else oc_xy

        # Build polygons for all 4 rings so we can do proper containment
        # tests. The dam profile is piecewise:
        #   inside inner_toe       -> reservoir floor at invert_z
        #   between IT and IC      -> inner batter (slope from IC to IT)
        #   between IC and OC      -> CREST SURFACE at crest_z (FLAT)
        #   between OC and OT      -> outer batter (slope from OC outward)
        # The previous version used "nearest crest polyline" which made
        # crest-surface cells get sloped Z (since d_in or d_out > 0),
        # producing wildly wrong dam_z and absurd cut/fill totals.
        try:
            it_poly_for_test = it_poly
            ic_q = ([QgsPointXY(c[0], c[1]) for c in ic_coords]
                    if ic_coords else None)
            ic_poly = (QgsGeometry.fromPolygonXY([ic_q])
                       if ic_q else None)
            oc_q = [QgsPointXY(c[0], c[1]) for c in oc_coords]
            oc_poly = QgsGeometry.fromPolygonXY([oc_q])
        except Exception as e:
            self.lbl_snap_status.setText(
                f"Failed to build crest polygons: {e}")
            return

        xs = [c[0] for c in ot_coords]; ys = [c[1] for c in ot_coords]
        xmin, xmax = min(xs), max(xs)
        ymin, ymax = min(ys), max(ys)
        # Sample resolution: trade-off between accuracy and runtime.
        # 2 m gives < 0.5% error on volume vs 1 m for typical dams and
        # runs in ~1 s on 100x100 m footprints.
        sample_res = 2.0
        cell_area = sample_res * sample_res

        # Diagnostics counters - logged to console so absurd results can
        # be diagnosed without rerunning under a debugger.
        n_reservoir = n_inner_batter = n_crest = n_outer_batter = 0
        n_outside_terrain = 0

        # Pre-sample terrain and dam_z at every cell inside outer_toe.
        # Tag each cell with its region so the sweep can correctly skip
        # cells that are outside the ACTUAL dam.
        #   region = 'reservoir' - inside inner_toe, always counted
        #            (terrain > invert -> cut; invert > terrain -> fill)
        #   region = 'embankment' - outer batter or inner batter; only
        #            counted if dam_z > terrain at the swept offset
        #            (otherwise the cell is outside the actual dam, the
        #            design batter just projects through ground there)
        # This is the key fix from the broken previous version, which
        # treated every outer-batter cell as cut volume even when the
        # design batter was projecting 15 m below natural ground - those
        # cells aren't part of the real dam at all.
        cells = []  # (terrain_z, dam_z_at_offset_0, region)
        y = ymin
        while y <= ymax:
            x = xmin
            while x <= xmax:
                p = QgsPointXY(x, y)
                pg = QgsGeometry.fromPointXY(p)
                if not ot_poly.contains(pg):
                    x += sample_res
                    continue
                try:
                    val, ok = dp.sample(p, 1)
                except Exception:
                    ok = False; val = None
                if not ok or val is None:
                    n_outside_terrain += 1
                    x += sample_res
                    continue
                tz = float(val)
                # Determine which dam region this cell is in. Tests run
                # innermost-first so the order is unambiguous.
                if it_poly_for_test is not None and it_poly_for_test.contains(pg):
                    # Reservoir floor
                    dz = invert_z
                    region = 'reservoir'
                    n_reservoir += 1
                elif ic_poly is not None and ic_poly.contains(pg):
                    # Inner batter
                    d_in = self._min_dist_to_polyline(x, y, ic_xy)
                    dz = max(crest_z - d_in / inner_hv, invert_z)
                    region = 'embankment'
                    n_inner_batter += 1
                elif oc_poly.contains(pg):
                    # Crest surface (flat top)
                    dz = crest_z
                    region = 'embankment'
                    n_crest += 1
                else:
                    # Outer batter
                    d_out = self._min_dist_to_polyline(x, y, oc_xy)
                    dz = crest_z - d_out / outer_hv
                    region = 'embankment'
                    n_outer_batter += 1
                cells.append((tz, dz, region))
                x += sample_res
            y += sample_res

        if not cells:
            self.lbl_snap_status.setText(
                "No terrain samples landed inside the outer toe. Check "
                "that the terrain raster covers the dam.")
            return

        try:
            import numpy as np
            tz_arr = np.array([c[0] for c in cells])
            dz_arr = np.array([c[1] for c in cells])
            # Boolean mask: True for reservoir cells (always counted),
            # False for embankment cells (only count when dam above ground)
            is_reservoir = np.array([c[2] == 'reservoir' for c in cells])

            def _cut_fill_at_offset(off):
                """Compute (cut, fill) in m3 for a candidate z_offset.

                Reservoir cells: dam_z is invert (a constant), shifted
                by off. If terrain > shifted_invert: cut. If shifted_
                invert > terrain: fill (rare - reservoir floor above
                ground, would need fill to raise it).

                Embankment cells: dam_z is the design batter Z, shifted
                by off. If shifted_dam_z > terrain: fill (embankment
                above ground - actual dam). If shifted_dam_z < terrain:
                CELL IS OUTSIDE THE ACTUAL DAM, skip - the design batter
                projects below ground here but no dam exists there.
                """
                shifted = dz_arr + off
                diff = shifted - tz_arr  # +ve = dam above ground
                # Reservoir: count regardless of sign
                res_fill = float(diff[is_reservoir & (diff > 0)].sum())
                res_cut = float(-diff[is_reservoir & (diff < 0)].sum())
                # Embankment: count only where dam > terrain
                emb_fill = float(diff[(~is_reservoir) & (diff > 0)].sum())
                return ((res_cut + 0.0) * cell_area,
                        (res_fill + emb_fill) * cell_area)
        except Exception as e:
            self.lbl_snap_status.setText(
                f"Failed to vectorise samples: {e}")
            return

        # Log diagnostics: where did the samples land, and what is the
        # cut/fill at offset=0 (the as-built state)?
        try:
            LOG.info(
                f"Cut/fill snap: {len(cells)} samples in outer toe footprint "
                f"(reservoir={n_reservoir}, inner_batter={n_inner_batter}, "
                f"crest={n_crest}, outer_batter={n_outer_batter}, "
                f"terrain_missing={n_outside_terrain})")
            c0, f0 = _cut_fill_at_offset(0.0)
            LOG.info(
                f"Cut/fill snap @ offset=0: fill={f0:,.0f} m3 "
                f"(embankment above terrain), cut={c0:,.0f} m3 "
                f"(reservoir excavation), fill/cut="
                f"{(f0/c0 if c0 > 0 else 0):.2f} (target {mult:.2f})")
        except Exception:
            pass

        # Sweep candidate offsets. Range -20 m to +20 m at 0.1 m gives
        # 401 evaluations; each is a vectorised loop over the cells.
        try:
            offsets = np.arange(-20.0, 20.01, 0.1)
            best_off = 0.0
            best_score = float('inf')
            best_cut = best_fill = 0.0
            for off in offsets:
                cut, fill = _cut_fill_at_offset(float(off))
                if cut <= 0:
                    continue
                score = abs(fill - cut * mult)
                if score < best_score:
                    best_score = score
                    best_off = float(off)
                    best_cut = cut
                    best_fill = fill
        except Exception as e:
            self.lbl_snap_status.setText(f"Sweep failed: {e}")
            return

        if best_score == float('inf'):
            self.lbl_snap_status.setText(
                "No candidate offset gave a positive cut volume. The "
                "dam may sit entirely above terrain (no reservoir to "
                "excavate). Try lowering the invert or moving the "
                "polygon to a different elevation.")
            return

        # Apply the result
        try:
            self.spn_z_offset.setValue(round(best_off, 3))
        except Exception:
            pass
        # Cut/fill balance moves the dam relative to the DXF datum -> the
        # DXF's baked-in outer toe (Method 1) is stale; prefer Method 2.
        self._dam_moved_off_dxf_toe = True
        ratio = best_fill / best_cut if best_cut > 0 else 0
        self.lbl_snap_status.setText(
            f"Snapped: z_offset = {best_off:+.2f} m. Cut "
            f"{best_cut:,.0f} m\u00b3, fill {best_fill:,.0f} "
            f"m\u00b3 (fill/cut = {ratio:.2f}; target {mult:.2f}). "
            f"{len(cells)} terrain samples.")

    def _max_embankment_height_at_crest_z(self, oc_coords, crest_z,
                                          outer_hv, dp, step=0.5,
                                          max_walk=None,
                                          return_toe_list=False,
                                          densify_spacing=2.0):
        """Walk the outer batter outward from points along the outer-
        crest line until it intersects terrain, and return the MAX
        embankment height = max over stations of (crest_z - toe_z).

        The crest line is DENSIFIED first (default 2 m) so a low terrain
        point sitting BETWEEN two crest vertices is not missed - walking
        only the raw vertices can skip the controlling low ground,
        making the snap under-report the height vs the output cut which
        the design app reads. Walking densified stations catches it.

        This is the same ray-cast as cut_outer_toe_to_terrain (Method 2)
        but lightweight: it only needs the toe terrain Z at each station.
        The toe location moves as crest_z changes (a higher crest walks
        further out and hits lower ground), so this MUST be re-evaluated
        for each candidate crest_z - there is no closed form.

        crest_z and the returned height are in TERRAIN datum (we sample
        terrain directly and don't convert), so the caller works in a
        single consistent datum.

        Returns (max_height, n_hits, n_misses, controlling_idx) or, if
        return_toe_list, (max_height, n_hits, n_misses, idx, toe_z_list).
        max_height is None if no station produced an intersection.
        """
        raw = list(oc_coords)
        if len(raw) < 3 or outer_hv <= 0:
            empty = (None, 0, 0, -1)
            return empty + ([],) if return_toe_list else empty
        # Densify the crest line so between-vertex low ground is caught.
        # Use the dam centroid from the RAW ring (densify doesn't move it).
        ccx = sum(c[0] for c in raw) / len(raw)
        ccy = sum(c[1] for c in raw) / len(raw)
        try:
            # densify needs closed ring to cover the closing segment
            dr = list(raw)
            if (dr[0][0], dr[0][1]) != (dr[-1][0], dr[-1][1]):
                dr.append(dr[0])
            stations = densify(dr, densify_spacing)
            stations = [(c[0], c[1]) for c in stations]
        except Exception:
            stations = [(c[0], c[1]) for c in raw]
        n_st = len(stations)
        if max_walk is None:
            drop = 30.0
            try:
                rc = dp.sample(QgsPointXY(ccx, ccy), 1)
                if rc is not None:
                    gzc, okc = rc
                    if okc and gzc is not None:
                        drop = max(5.0, crest_z - float(gzc))
            except Exception:
                pass
            max_walk = max(60.0, drop * outer_hv * 1.5 + 40.0)

        best_h = None
        best_idx = -1
        n_hits = n_misses = 0
        toe_list = []
        for k in range(n_st):
            x, y = stations[k][0], stations[k][1]
            # Local tangent from neighbouring densified stations
            prev_idx = (k - 1) % n_st
            next_idx = (k + 1) % n_st
            tx = stations[next_idx][0] - stations[prev_idx][0]
            ty = stations[next_idx][1] - stations[prev_idx][1]
            tlen = math.hypot(tx, ty)
            if tlen < 1e-6:
                if return_toe_list:
                    toe_list.append(None)
                continue
            n1x, n1y = -ty / tlen, tx / tlen
            n2x, n2y = ty / tlen, -tx / tlen
            # Outward = away from outer-crest centroid
            if (ccx - x) * n1x + (ccy - y) * n1y < 0:
                nx, ny = n1x, n1y
            else:
                nx, ny = n2x, n2y
            prev_dz = None
            prev_walk = 0.0
            walked = step
            toe_z = None
            while walked <= max_walk:
                wx = x + nx * walked
                wy = y + ny * walked
                batter_z = crest_z - walked / outer_hv
                try:
                    res = dp.sample(QgsPointXY(wx, wy), 1)
                    if res is None:
                        walked += step; continue
                    gz, ok = res
                    if not ok or gz is None:
                        walked += step; continue
                    tz = float(gz)
                except Exception:
                    walked += step; continue
                dz = batter_z - tz
                if dz <= 0:
                    if prev_dz is not None and prev_dz > 0:
                        frac = prev_dz / (prev_dz - dz)
                        int_walk = prev_walk + frac * (walked - prev_walk)
                    else:
                        int_walk = 0.0
                    int_x = x + nx * int_walk
                    int_y = y + ny * int_walk
                    try:
                        res2 = dp.sample(QgsPointXY(int_x, int_y), 1)
                        if res2 is not None:
                            gz2, ok2 = res2
                            if ok2 and gz2 is not None:
                                toe_z = float(gz2)
                    except Exception:
                        pass
                    if toe_z is None:
                        toe_z = tz
                    break
                prev_dz = dz
                prev_walk = walked
                walked += step
            if toe_z is None:
                n_misses += 1
                if return_toe_list:
                    toe_list.append(None)
                continue
            n_hits += 1
            if return_toe_list:
                toe_list.append(toe_z)
            h = crest_z - toe_z
            if best_h is None or h > best_h:
                best_h = h
                best_idx = k
        if return_toe_list:
            return best_h, n_hits, n_misses, best_idx, toe_list
        return best_h, n_hits, n_misses, best_idx

    def _snap_z_offset_to_max_embankment_height(self):
        """Shift z_offset so the dam's tallest section equals a target
        maximum embankment height.

        The embankment height at a crest station is the vertical drop
        from the crest down to where the OUTER BATTER MEETS TERRAIN at
        the toe - not the ground directly under the crest. The toe is
        offset horizontally from the crest by (height x outer_HV), and
        that offset changes as the crest moves, so the relationship
        between z_offset and max height is NOT linear: a higher crest
        walks the batter further out and usually hits lower ground,
        making the height grow faster than the offset.

        Because the toe location is itself a function of the offset,
        this requires ITERATION. We sweep z_offset, and for each
        candidate re-walk the batter to terrain (the same ray-cast
        Method 2 uses) to find the true max height, then pick the offset
        whose max height matches the target. max_height(off) is
        monotonic increasing in off, so we binary-search.
        """
        kl = self._current_role_to_ring()
        if not kl or not kl.get('outer_crest'):
            self.lbl_snap_status.setText(
                "Need the outer crest ring - assign roles (DXF mode) or "
                "click Build (polygon mode) first.")
            return
        if self._terrain_layer is None:
            self.lbl_snap_status.setText(
                "Select a terrain DEM on the Input tab first.")
            return
        dp = self._terrain_layer.dataProvider()
        if dp is None:
            self.lbl_snap_status.setText(
                "Terrain DEM has no data provider.")
            return

        target = float(self.spn_max_emb_height.value())
        oc = kl['outer_crest']
        oc_coords = [(c[0], c[1]) for c in oc.get('coords', [])]
        if len(oc_coords) < 3:
            self.lbl_snap_status.setText("Outer crest ring is empty.")
            return

        # crest_z in RING datum; terrain sampled in terrain datum. The
        # helper works entirely in terrain datum, so we pass the crest
        # in terrain datum as (ring crest_z + z_offset). Solving for the
        # offset, we vary the crest's terrain-datum elevation directly:
        #   crest_terrain = crest_z_ring + off
        # and report the offset at the end.
        crest_z_ring = float(oc.get('z_mean', CFG.get('crest', 0)))
        # CRITICAL: use the SAME outer_hv the output-time Method 2 cut
        # will use, otherwise the snap predicts a toe at one batter angle
        # but the output walks a different angle and lands on different
        # ground - producing the exact mismatch we saw (snap says 3.90,
        # output CSV says 4.50). The output cut
        # (cut_outer_toe_to_terrain, called from step7_outputs / the
        # polygon-mode Run path) uses CFG['outer_hv']. So the snap must
        # too. Inferred metrics are only a fallback if CFG isn't set.
        outer_hv = float(CFG.get('outer_hv', 0) or 0)
        if outer_hv <= 0.5:
            try:
                metrics = compute_inferred_metrics(kl, preview=self._preview)
                if metrics.get('outer_hv') and metrics['outer_hv'] > 0.5:
                    outer_hv = float(metrics['outer_hv'])
            except Exception:
                pass
        if outer_hv <= 0.5:
            outer_hv = 3.0
        if outer_hv <= 0.5:
            self.lbl_snap_status.setText(
                f"Outer batter H:V = {outer_hv:.2f} is too low to walk a "
                f"batter. Check the inferred metrics.")
            return
        LOG.info(f"Max-height snap will walk batter at outer_hv="
                 f"{outer_hv:.3f} (matching output Method 2 cut).")

        self.lbl_snap_status.setText(
            "Iterating batter-to-terrain to hit target height...")
        try:
            from qgis.PyQt.QtWidgets import QApplication
            QApplication.processEvents()
        except Exception:
            pass

        def max_h_for_crest(crest_terrain_z):
            h, nh, nm, idx = self._max_embankment_height_at_crest_z(
                oc_coords, crest_terrain_z, outer_hv, dp,
                step=max(0.25, CFG.get('point_spacing', 1.0)))
            return h, nh, nm, idx

        # Bracket: max height is monotonic increasing in crest elevation.
        # A raised crest needs a longer batter walk to reach ground, which
        # the helper's max_walk now scales for. We don't need a huge
        # window - embankment heights are realistically a few to a few
        # tens of metres - so a +/-40 m crest window around the current
        # crest brackets any sane target while keeping the walk bounded.
        lo_c = crest_z_ring - 40.0   # very low crest -> small/zero height
        hi_c = crest_z_ring + 40.0   # very high crest -> large height
        h_lo, _, _, _ = max_h_for_crest(lo_c)
        h_hi, nh_hi, nm_hi, _ = max_h_for_crest(hi_c)
        if h_hi is None:
            self.lbl_snap_status.setText(
                "Batter never reached terrain even with a 40 m raise. "
                "Check the terrain raster actually covers the dam "
                "footprint (sample a point - is it returning NoData?), "
                "and that the outer batter H:V is sensible "
                f"(currently {outer_hv:.2f}:1).")
            return
        if h_lo is None:
            h_lo = 0.0  # treat a non-intersecting low crest as zero height
        if not (h_lo <= target <= h_hi):
            # Target outside achievable range
            self.lbl_snap_status.setText(
                f"Target {target:.2f} m is outside the achievable range "
                f"({h_lo:.2f}-{h_hi:.2f} m for crest +/-40 m). Pick a "
                f"target inside that range.")
            return

        # Binary search on crest-terrain-Z for max_h == target
        best_c = crest_z_ring
        best_h = None
        for _it in range(40):
            mid_c = 0.5 * (lo_c + hi_c)
            h_mid, nh, nm, idx = max_h_for_crest(mid_c)
            if h_mid is None:
                # No intersection at this crest - treat as height 0 (too low)
                lo_c = mid_c
                continue
            best_c = mid_c
            best_h = h_mid
            if abs(h_mid - target) < 0.01:
                break
            if h_mid < target:
                lo_c = mid_c
            else:
                hi_c = mid_c

        best_off = best_c - crest_z_ring
        try:
            self.spn_z_offset.setValue(round(best_off, 3))
        except Exception:
            pass
        # The max-height snap moves the dam relative to the DXF datum, so
        # the DXF's baked-in outer toe (Method 1) is now stale - the toe
        # must come from the terrain intersection at the new dam position.
        self._dam_moved_off_dxf_toe = True

        h_final, nh_f, nm_f, idx_f = max_h_for_crest(best_c)
        # Diagnostic: log per-vertex toe Z at the solved crest so it can
        # be compared against the output-time Method 2 cut. If the snap's
        # max height disagrees with the output CSV, this shows which
        # vertex walks to different ground.
        try:
            _h, _nh, _nm, _idx, toe_list = \
                self._max_embankment_height_at_crest_z(
                    oc_coords, best_c, outer_hv, dp,
                    step=max(0.2, CFG.get('point_spacing', 1.0)),
                    return_toe_list=True)
            if toe_list:
                tzs = [t for t in toe_list if t is not None]
                if tzs:
                    LOG.info(
                        f"Max-height snap toe Z at solved crest "
                        f"{best_c:.3f}: min={min(tzs):.3f} "
                        f"max={max(tzs):.3f} (height range "
                        f"{best_c - max(tzs):.3f}-{best_c - min(tzs):.3f} "
                        f"m). Output Method 2 cut should match this; if "
                        f"the CSV differs, compare outer_hv/crest_z in "
                        f"the [Cutting outer toe] log block.")
        except Exception:
            pass
        LOG.info(
            f"Max-embankment-height snap (iterative batter-to-terrain): "
            f"target={target:.2f} m, outer_hv={outer_hv:.2f}, "
            f"crest_z(ring)={crest_z_ring:.2f} m. Solved crest "
            f"elevation {best_c:.2f} m (terrain datum) -> "
            f"z_offset={best_off:+.3f} m. Resulting max height "
            f"{(h_final if h_final is not None else 0):.2f} m at vertex "
            f"{idx_f} ({nh_f} hits, {nm_f} misses).")
        self.lbl_snap_status.setText(
            f"Snapped: z_offset = {best_off:+.2f} m. Max embankment "
            f"height = {(h_final if h_final is not None else 0):.2f} m "
            f"(target {target:.2f} m), measured crest-to-toe at the "
            f"batter/terrain intersection. Controlling section at outer-"
            f"crest vertex {idx_f}. {nh_f} batter hits, {nm_f} misses.")

    # =================================================================
    # Phase 2 - anchor + parameter build-up
    # =================================================================
    def _refresh_anchor_options(self):
        """Update the anchor combobox based on currently-assigned roles."""
        # Block signals while we rebuild so we don't fire a chain of
        # re-renders during dialog state changes
        try:
            self.cmb_anchor.blockSignals(True)
            current = self.cmb_anchor.currentData()
            self.cmb_anchor.clear()
            self.cmb_anchor.addItem("(none - pick a role first)", "")
            for role in ('inner_toe', 'inner_crest', 'outer_crest',
                          'outer_toe'):
                if role in self._role_assignments:
                    self.cmb_anchor.addItem(
                        role.replace('_', ' ').title(), role)
            # Restore previous selection if it still applies
            if current:
                idx = self.cmb_anchor.findData(current)
                if idx >= 0:
                    self.cmb_anchor.setCurrentIndex(idx)
        finally:
            self.cmb_anchor.blockSignals(False)

    def _anchor_role(self):
        """Currently selected anchor role, or None."""
        d = self.cmb_anchor.currentData()
        return d if d else None

    def _anchor_ring(self):
        """The ring dict for the currently-selected anchor, or None."""
        role = self._anchor_role()
        if role is None:
            return None
        return self._current_role_to_ring().get(role)

    def _on_anchor_changed(self, _idx=None):
        """Anchor selection changed - reload defaults into the spinboxes for
        any parameter that ISN'T overridden, then re-render."""
        anchor_ring = self._anchor_ring()
        # Auto-fill defaults for non-overridden params
        if anchor_ring is not None:
            self._populate_buildup_defaults()
        self._on_use_constructed()  # re-evaluate which plot to show
        self._rebuild_constructed()

    def _populate_buildup_defaults(self):
        """Pre-fill the build-up spinboxes from the anchor + inferred
        metrics. Only updates spinboxes whose 'override' checkbox is OFF
        (so the user's explicit overrides are preserved)."""
        if self._preview is None:
            return
        anchor = self._anchor_ring()
        anchor_role = self._anchor_role()
        m = compute_inferred_metrics(self._current_role_to_ring(),
                                      self._preview)
        # Build defaults dict
        defaults = {
            'crest_z':     m.get('crest_z'),
            'invert_z':    m.get('invert_z'),
            'outer_toe_z': m.get('outer_toe_z'),
            'crest_width': m.get('crest_width'),
            'inner_hv':    m.get('inner_hv'),
            'outer_hv':    m.get('outer_hv'),
        }
        # If anchor's role provides a Z directly, that beats inferred
        if anchor is not None:
            if anchor_role == 'inner_crest' or anchor_role == 'outer_crest':
                defaults['crest_z'] = anchor['z_mean']
            elif anchor_role == 'inner_toe':
                defaults['invert_z'] = anchor['z_mean']
            elif anchor_role == 'outer_toe':
                defaults['outer_toe_z'] = anchor['z_mean']
        # Sensible fallbacks for HV / crest width so the spinboxes aren't 0
        if defaults['crest_width'] is None: defaults['crest_width'] = 5.0
        if defaults['inner_hv'] is None:    defaults['inner_hv'] = 3.5
        if defaults['outer_hv'] is None:    defaults['outer_hv'] = 3.5
        # If we don't have crest_z but have an anchor at the crest role, use
        # the anchor's z_mean. If we still don't have one, fall back to
        # something visible.
        for k in defaults:
            if defaults[k] is None:
                # As a last resort, leave 0 - user has to enter the value
                defaults[k] = 0.0
        # Push into spinboxes - only if the override checkbox is OFF
        for k, (chk, sp) in self._buildup_widgets.items():
            if not chk.isChecked():
                # Block signals so we don't trigger a rebuild for each one
                sp.blockSignals(True)
                sp.setValue(float(defaults[k]))
                sp.blockSignals(False)

    def _on_buildup_override_changed(self, key):
        """Override checkbox toggled - enable/disable the spinbox, then
        re-populate defaults (and rebuild) on enable."""
        chk, sp = self._buildup_widgets[key]
        sp.setEnabled(chk.isChecked())
        if not chk.isChecked():
            # Reverting to inferred default - reload
            self._populate_buildup_defaults()
        self._rebuild_constructed()

    def _on_buildup_param_changed(self, key):
        """A build-up spinbox value changed - re-construct."""
        self._rebuild_constructed()

    def _buildup_param_values(self):
        """Read all 6 build-up parameters (whether from override spinbox or
        the auto-filled default that's already in the spinbox)."""
        out = {}
        for k, (chk, sp) in self._buildup_widgets.items():
            out[k] = float(sp.value())
        return out

    def _rebuild_constructed(self):
        """Construct the 4 design rings from current anchor + parameters,
        store in self._constructed_kl, and refresh the plan view + sections
        if Use-Constructed mode is on."""
        self._constructed_kl = None
        self._build_error = None
        anchor_ring = self._anchor_ring()
        anchor_role = self._anchor_role()
        if anchor_ring is None or anchor_role is None:
            self.lbl_build_status.setText(
                "Pick an anchor ring (assign one of the 4 roles first).")
            self._render_plan_view()
            self._update_cross_sections()
            return
        params = self._buildup_param_values()
        try:
            sp = self.spn_spacing.value() if hasattr(self, 'spn_spacing') \
                 else 1.0
            kl = construct_dam_rings_from_anchor(
                anchor_ring, anchor_role, params, sp=sp)
            self._constructed_kl = kl
            # Compose a status line
            it = kl['inner_toe']; ic = kl['inner_crest']
            oc = kl['outer_crest']; ot = kl['outer_toe']
            self.lbl_build_status.setText(
                f"Constructed from {anchor_role.replace('_', ' ')}: "
                f"inner_toe @ {it['z_mean']:.2f} ({it['npts']} pts), "
                f"inner_crest @ {ic['z_mean']:.2f}, "
                f"outer_crest @ {oc['z_mean']:.2f}, "
                f"outer_toe @ {ot['z_mean']:.2f} ({ot['npts']} pts). "
                f"Crest width {params['crest_width']:.2f} m, "
                f"inner H:V {params['inner_hv']:.2f}, "
                f"outer H:V {params['outer_hv']:.2f}.")
        except Exception as e:
            self._build_error = str(e)
            self.lbl_build_status.setText(f"Construction failed: {e}")
        # Refresh visuals
        self._render_plan_view()
        self._update_cross_sections()

    def _on_use_constructed(self, _on=None):
        """Toggle of 'Use constructed geometry for Run pipeline' - just
        re-render so the plan view and cross-sections show the right thing."""
        self._render_plan_view()
        self._update_cross_sections()

    def _is_constructed_active(self):
        """Whether the constructed geometry should be shown/used."""
        try:
            return (self._constructed_kl is not None
                    and self.chk_use_constructed.isChecked())
        except Exception:
            return False

    def _update_cross_sections(self):
        """Kept for back-compat with call-sites that haven't been renamed.
        Forwards to the new long-section renderer."""
        self._update_long_section()

    # ----- Long-section geometry helpers ---------------------------------
    def _dam_centroid(self):
        """Return the (x, y) centroid of the dam, derived from the
        outer_crest ring (preferred), falling back to inner_crest /
        outer_toe / inner_toe in that order. None if no role is assigned."""
        if self._is_constructed_active():
            role_ring = dict(self._constructed_kl)
        else:
            role_ring = self._current_role_to_ring()
        for role in ('outer_crest', 'inner_crest', 'outer_toe', 'inner_toe'):
            r = role_ring.get(role)
            if r is None:
                continue
            xs = [c[0] for c in r['coords']]
            ys = [c[1] for c in r['coords']]
            return (sum(xs)/len(xs), sum(ys)/len(ys))
        return None

    def _default_section_angle_deg(self):
        """Compute the low-to-high ground-gradient direction across the
        outer_crest perimeter (in degrees CCW from east). Returns None if
        no outer_crest is assigned or terrain DEM is unavailable."""
        if self._is_constructed_active():
            role_ring = dict(self._constructed_kl)
        else:
            role_ring = self._current_role_to_ring()
        oc_ring = role_ring.get('outer_crest')
        if oc_ring is None or self._terrain_layer is None:
            return None
        ext = find_extreme_ground_perimeter_points(
            oc_ring['coords'], self._terrain_layer, n_samples=72)
        if ext is None:
            return None
        high_ch, high_z, low_ch, low_z = ext
        p_high = interp_ch(oc_ring['coords'], high_ch)
        p_low = interp_ch(oc_ring['coords'], low_ch)
        dx = p_high[0] - p_low[0]
        dy = p_high[1] - p_low[1]
        if math.hypot(dx, dy) < 1e-6:
            return None
        return math.degrees(math.atan2(dy, dx))

    def _current_section_angle_deg(self):
        """Effective section angle - the user's slider value if set,
        otherwise the low-to-high default."""
        if self._section_angle_deg is not None:
            return self._section_angle_deg
        return self._default_section_angle_deg()

    def _section_axis(self):
        """Return (centroid_xy, direction_unit_xy) for the current section
        line, or (None, None) if not computable."""
        c = self._dam_centroid()
        if c is None:
            return None, None
        deg = self._current_section_angle_deg()
        if deg is None:
            return c, None
        rad = math.radians(deg)
        return c, (math.cos(rad), math.sin(rad))

    def _section_half_length(self):
        """Half-length L of the section: from centroid out to ~10 m past
        the furthest outer_toe vertex on either side along the section
        direction."""
        c, d = self._section_axis()
        if c is None or d is None:
            return 100.0
        if self._is_constructed_active():
            role_ring = dict(self._constructed_kl)
        else:
            role_ring = self._current_role_to_ring()
        ring = role_ring.get('outer_toe') or role_ring.get('outer_crest')
        if ring is None:
            return 100.0
        # Project each ring vertex onto the section axis and pick the
        # maximum |projection|; add 10 m margin.
        max_proj = 0.0
        for p in ring['coords']:
            dxp = p[0] - c[0]
            dyp = p[1] - c[1]
            proj = abs(dxp*d[0] + dyp*d[1])
            if proj > max_proj:
                max_proj = proj
        return max_proj + 10.0

    def _ring_line_crossings(self, ring_coords, center, direction):
        """Find intersections of the infinite line (through center along
        direction) with the closed ring. Returns list of (signed_chainage,
        z) sorted by chainage. signed_chainage is the distance from center
        along direction (positive in +direction)."""
        cx, cy = center
        dx, dy = direction
        out = []
        n = len(ring_coords)
        for i in range(n):
            a = ring_coords[i]
            b = ring_coords[(i + 1) % n]
            ax_, ay_ = a[0], a[1]
            bx_, by_ = b[0], b[1]
            ex, ey = bx_ - ax_, by_ - ay_
            # Solve: a + s*(b-a) = center + t*direction
            #   s*ex - t*dx = cx - ax
            #   s*ey - t*dy = cy - ay
            det = ex * (-dy) - ey * (-dx)  # = -ex*dy + ey*dx = dx*ey - dy*ex
            if abs(det) < 1e-12:
                continue
            rhs1 = cx - ax_
            rhs2 = cy - ay_
            s = (rhs1 * (-dy) - rhs2 * (-dx)) / det
            t = (ex * rhs2 - ey * rhs1) / det
            if -1e-9 <= s <= 1 + 1e-9:
                az = a[2] if len(a) >= 3 else 0.0
                bz = b[2] if len(b) >= 3 else 0.0
                s_c = max(0.0, min(1.0, s))
                z = az + s_c * (bz - az)
                out.append((t, z))
        out.sort(key=lambda x: x[0])
        # Dedupe near-identical crossings (e.g. line through a vertex
        # registers in both adjacent segments)
        deduped = []
        for t, z in out:
            if deduped and abs(t - deduped[-1][0]) < 0.01:
                continue
            deduped.append((t, z))
        return deduped

    def _update_long_section(self):
        """Render the single long section through the dam centroid at the
        current section angle. Replaces the prior pair of per-perimeter-point
        cross-sections. The section axis is centroid-through, so both inner
        and outer batters project with the SAME foreshortening - meaning
        the apparent H:V on both sides should match the design when the
        axis is radial at that part of the perimeter.

        When the user has built rings from an anchor + parameters (the
        Build-Up panel), those constructed rings are ALSO drawn as a
        'theoretical' overlay - distinct markers (open squares) connected
        by a solid line. This lets the user compare the DXF-extracted
        geometry (data) against the cleanly-offset design (trend), exactly
        like overlaying a fit on a scatterplot.
        """
        if not HAS_MPL or self._preview is None:
            return

        # PRIMARY ring set for the section: the DXF role assignments,
        # unless the user has ticked "Use constructed for Run" in which
        # case the constructed kl is the primary.
        if self._is_constructed_active():
            role_ring = dict(self._constructed_kl)
            primary_label = "constructed"
        else:
            role_ring = self._current_role_to_ring()
            primary_label = "DXF-extracted"
        # SECONDARY (overlay) ring set: the OTHER one, if it exists.
        if (self._constructed_kl is not None
                and not self._is_constructed_active()):
            overlay_ring = dict(self._constructed_kl)
            overlay_label = "theoretical (anchor-built)"
        else:
            overlay_ring = None
            overlay_label = None

        def _empty(msg):
            self._section_fig.clear()
            ax = self._section_fig.add_subplot(111)
            ax.text(0.5, 0.5, msg, ha='center', va='center',
                    transform=ax.transAxes, fontsize=10, color='#666')
            ax.set_xticks([]); ax.set_yticks([])
            self._section_canvas.draw_idle()

        oc_ring = role_ring.get('outer_crest')
        if oc_ring is None:
            _empty("Assign 'Outer crest' to enable the long section.")
            return

        center, direction = self._section_axis()
        if center is None or direction is None:
            _empty("Assign at least one design role to position the "
                   "section line (centroid + direction).")
            return

        L = self._section_half_length()
        z_off = self._z_offset_value()

        # Compute design-ring crossings (shifted to NZVD2016 datum)
        role_colours = {
            'inner_toe':   '#1f77b4', 'inner_crest': '#2ca02c',
            'outer_crest': '#d62728', 'outer_toe':   '#ff7f0e',
        }
        crossings = {}  # role -> list of (chainage, z_shifted)
        for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
            r = role_ring.get(role)
            if r is None:
                continue
            cr = self._ring_line_crossings(r['coords'], center, direction)
            # Keep only crossings within +/- L
            cr = [(t, z + z_off) for t, z in cr if -L <= t <= L]
            crossings[role] = cr

        # Note: outer_toe Z comes from the ring coords. In DXF auto mode,
        # step4c_var_z_outer_toe will have promoted the outer toe to
        # variable-Z using the partial contour endpoints (see step4c) - so
        # the orange dots naturally show local ground elevation. In
        # DXF + anchor and polygon modes, the user clicks "Cut to terrain"
        # which replaces the const-Z outer_toe with a variable-Z ring
        # derived by walking outward at design slope until terrain is hit.
        # No terrain sampling needed here in the long section itself.
        outer_toe_snapped = False  # legacy flag, kept for title compat

        # Sample ground along section
        n_ground = 240
        offsets = []
        ground_zs = []
        if self._terrain_layer is not None:
            try:
                dp = self._terrain_layer.dataProvider()
            except Exception:
                dp = None
            if dp:
                for k in range(n_ground + 1):
                    t = -L + (2 * L) * k / n_ground
                    x = center[0] + t * direction[0]
                    y = center[1] + t * direction[1]
                    try:
                        res = dp.sample(QgsPointXY(x, y), 1)
                        if res is not None:
                            val, ok = res
                            if ok and val is not None:
                                offsets.append(t)
                                ground_zs.append(val)
                    except Exception:
                        pass

        # Draw
        self._section_fig.clear()
        ax = self._section_fig.add_subplot(111)

        if offsets:
            ax.plot(offsets, ground_zs, color='#8b6f47', linewidth=1.6,
                    label='Existing ground')
            ax.fill_between(offsets, min(ground_zs) - 1.0, ground_zs,
                            color='#d2b48c', alpha=0.35)

        # --- Intermediate batter contour crossings ---------------------
        # Plot crossings of every detected const-Z ring (skip the 4 key
        # design rings - they get larger markers below). This reveals the
        # actual contour spacing along the section line and is the most
        # honest diagnostic for the apparent slope question: if the
        # contour dots are evenly spaced on the section, the actual
        # slope is constant; if the spacing changes with rotation, you're
        # seeing foreshortening on the section axis.
        show_contours = False
        try:
            show_contours = self.chk_show_contours.isChecked()
        except Exception:
            pass
        if show_contours and self._preview is not None:
            # Identify the design rings so we can skip them
            design_ids = set()
            for ring in role_ring.values():
                if ring is not None:
                    design_ids.add(id(ring))
            # Only const-Z rings make sense as 0.2 m contour overlays
            # (var-Z polylines aren't contours). Use the const slice of
            # the combined list.
            n_const = self._preview.get('n_const', 0)
            contour_rings = (self._preview.get('all_rings') or [])[:n_const]
            # Filter by AREA (not Z): only rings whose area falls between
            # the inner_toe's and outer_toe's are actual dam batter
            # contours. Anything BIGGER is an outside-the-dam DTM contour
            # (natural ground at z below outer_toe); anything SMALLER is
            # a sump or internal feature. The previous Z-only bound was
            # too loose for rich DTM DXFs like Neil Kingston - it let
            # through outside-the-dam contours at z just below outer_toe
            # that visually sat under the dashed design line and made it
            # look like the contours were offset from the design rings.
            it_ring = role_ring.get('inner_toe')
            ot_ring = role_ring.get('outer_toe')
            ic_ring = role_ring.get('inner_crest')
            oc_ring = role_ring.get('outer_crest')
            if it_ring is not None and ot_ring is not None:
                a_lo = min(it_ring['area'], ot_ring['area'])
                a_hi = max(it_ring['area'], ot_ring['area'])
            else:
                # No bounds - permissive, but the design ring exclusion
                # will still skip the 4 key rings
                a_lo, a_hi = 0.0, float('inf')
            # Also keep a Z bound as a safety net (some rings might fall
            # in the area range but be at clearly wrong Z, e.g. a sump's
            # rim contour at the right area but inside-the-pond elevation)
            design_zs = [r['z_mean'] for r in role_ring.values()
                         if r is not None]
            if design_zs:
                z_lo = min(design_zs)
                z_hi = max(design_zs)
            else:
                z_lo, z_hi = float('-inf'), float('inf')

            # CHORD-DEVIATION FILTER. A real dam batter contour at z
            # between inner_toe_z and inner_crest_z (inner batter) or
            # between outer_toe_z and outer_crest_z (outer batter) should
            # cross the section axis close to where the linear chord
            # between the bounding design rings predicts. Rings whose
            # crossing deviates by more than ~5 m from EITHER predicted
            # chord position are likely a different DXF feature
            # (e.g. road outline, an unrelated DTM segment) and would
            # confuse the diagnostic. Compute the per-side chord
            # endpoints once.
            def _pick_for_chord(crossings):
                left = [c for c in crossings if c[0] < 0]
                right = [c for c in crossings if c[0] >= 0]
                return (max(left, key=lambda p: p[0]) if left else None,
                        min(right, key=lambda p: p[0]) if right else None)
            def _ring_lr_or_none(ring):
                if ring is None: return (None, None)
                return _pick_for_chord(self._ring_line_crossings(
                    ring['coords'], center, direction))
            ic_l, ic_r = _ring_lr_or_none(ic_ring)
            it_l, it_r = _ring_lr_or_none(it_ring)
            oc_l, oc_r = _ring_lr_or_none(oc_ring)
            ot_l, ot_r = _ring_lr_or_none(ot_ring)
            CHORD_TOL = 5.0  # m

            def _on_a_chord(t, z, end1, end2):
                """True if (t,z) sits within CHORD_TOL of the linear
                chord from end1=(t1,z1) to end2=(t2,z2)."""
                if end1 is None or end2 is None:
                    return False
                z1, z2 = end1[1], end2[1]
                if z < min(z1, z2) - 0.01 or z > max(z1, z2) + 0.01:
                    return False
                if abs(z2 - z1) < 1e-6:
                    return False
                f = (z - z1) / (z2 - z1)
                if f < -0.01 or f > 1.01:
                    return False
                t_pred = end1[0] + f * (end2[0] - end1[0])
                return abs(t - t_pred) < CHORD_TOL

            n_overlay = 0
            n_skipped_chord = 0
            for ring in contour_rings:
                if id(ring) in design_ids:
                    continue
                area = ring.get('area', 0)
                if not (a_lo <= area <= a_hi):
                    continue
                z = ring.get('z_mean', 0)
                if not (z_lo <= z <= z_hi):
                    continue
                cr_pts = self._ring_line_crossings(
                    ring['coords'], center, direction)
                # Use the crossing's INTERPOLATED Z (which equals z_mean
                # for true const-Z rings, but if there's any per-vertex
                # drift this lets it show up honestly rather than be
                # masked by z_mean)
                for t, zr in cr_pts:
                    if not (-L <= t <= L):
                        continue
                    # Chord-deviation gate: must lie close to either
                    # the inner-batter chord (inner_crest <-> inner_toe)
                    # or the outer-batter chord (outer_crest <-> outer_toe)
                    # on the matching side of the section.
                    if t < 0:
                        on_inner = _on_a_chord(t, zr + z_off, ic_l, it_l)
                        on_outer = _on_a_chord(t, zr + z_off, oc_l, ot_l)
                    else:
                        on_inner = _on_a_chord(t, zr + z_off, ic_r, it_r)
                        on_outer = _on_a_chord(t, zr + z_off, oc_r, ot_r)
                    if not (on_inner or on_outer):
                        n_skipped_chord += 1
                        continue
                    ax.scatter([t], [zr + z_off], color='#888888', s=14,
                                zorder=3, alpha=0.7,
                                label='Batter contours' if n_overlay == 0
                                      else None)
                    n_overlay += 1

        # --- Design ring crossings (4 key rings, larger markers) -----
        for role, pts in crossings.items():
            colour = role_colours[role]
            for t, z in pts:
                ax.scatter([t], [z], color=colour, s=70, zorder=5,
                            edgecolors='white', linewidths=1.5,
                            label=role.replace('_', ' '))

        # Connect design points to make the dam profile readable:
        # outer_toe -> outer_crest -> inner_crest -> inner_toe on each side.
        def _pick_lr(role):
            pts = crossings.get(role) or []
            left = [(t, z) for t, z in pts if t < 0]
            right = [(t, z) for t, z in pts if t >= 0]
            l = max(left, key=lambda p: p[0]) if left else None
            r = min(right, key=lambda p: p[0]) if right else None
            return l, r

        it_l, it_r = _pick_lr('inner_toe')
        ic_l, ic_r = _pick_lr('inner_crest')
        oc_l, oc_r = _pick_lr('outer_crest')
        ot_l, ot_r = _pick_lr('outer_toe')

        def _draw_chain(side):
            if side == 'left':
                seq = [ot_l, oc_l, ic_l, it_l]
            else:
                seq = [it_r, ic_r, oc_r, ot_r]
            xs = [p[0] for p in seq if p is not None]
            zs = [p[1] for p in seq if p is not None]
            if len(xs) >= 2:
                ax.plot(xs, zs, color='#333', linestyle='--',
                        linewidth=1.4, zorder=4)

        _draw_chain('left')
        _draw_chain('right')

        # Invert line - connects the two inner_toe crossings across the
        # bottom of the dam profile. Visually closes the trapezoid and
        # makes the foundation level explicit. Only drawn if both
        # crossings exist (i.e. the section line actually intersects the
        # inner_toe ring on both sides of the dam axis).
        if it_l is not None and it_r is not None:
            ax.plot([it_l[0], it_r[0]], [it_l[1], it_r[1]],
                    color='#1f77b4', linestyle='--', linewidth=1.2,
                    alpha=0.7, zorder=3,
                    label=f"invert ({(it_l[1] + it_r[1]) / 2:.2f} m)")

        # --- THEORETICAL (anchor-built) overlay --------------------------
        # If the user has Constructed rings AND is currently viewing the
        # DXF (i.e. constructed not yet committed via "Use Constructed for
        # Run"), overlay the constructed crossings so they can be visually
        # compared with the DXF data. Drawn as open SQUARES connected by a
        # clean purple chord on each side - distinct from the filled-circle
        # DXF markers so the eye separates data from trend.
        overlay_metrics = None  # filled below if overlay drawn
        if overlay_ring is not None:
            ov_crossings = {}
            for role in ('inner_toe', 'inner_crest',
                         'outer_crest', 'outer_toe'):
                r = overlay_ring.get(role)
                if r is None:
                    continue
                cr = self._ring_line_crossings(
                    r['coords'], center, direction)
                cr = [(t, z + z_off) for t, z in cr if -L <= t <= L]
                ov_crossings[role] = cr

            # Markers
            ov_color = '#7e3ff2'  # purple, distinct from any role colour
            first_marker = True
            for role, pts in ov_crossings.items():
                colour = role_colours.get(role, ov_color)
                for t, z in pts:
                    ax.scatter([t], [z], marker='s', s=85,
                                facecolors='white', edgecolors=colour,
                                linewidths=2.0, zorder=6,
                                label=(overlay_label if first_marker
                                       else None))
                    first_marker = False

            # Trend chord (theoretical batter line on each side)
            def _ov_pick_lr(role):
                pts = ov_crossings.get(role) or []
                left = [(t, z) for t, z in pts if t < 0]
                right = [(t, z) for t, z in pts if t >= 0]
                lp = max(left, key=lambda p: p[0]) if left else None
                rp = min(right, key=lambda p: p[0]) if right else None
                return lp, rp
            ov_it_l, ov_it_r = _ov_pick_lr('inner_toe')
            ov_ic_l, ov_ic_r = _ov_pick_lr('inner_crest')
            ov_oc_l, ov_oc_r = _ov_pick_lr('outer_crest')
            ov_ot_l, ov_ot_r = _ov_pick_lr('outer_toe')
            def _ov_chain(seq):
                xs = [p[0] for p in seq if p is not None]
                zs = [p[1] for p in seq if p is not None]
                if len(xs) >= 2:
                    ax.plot(xs, zs, color=ov_color, linestyle='-',
                            linewidth=2.0, alpha=0.85, zorder=5)
            _ov_chain([ov_ot_l, ov_oc_l, ov_ic_l, ov_it_l])
            _ov_chain([ov_it_r, ov_ic_r, ov_oc_r, ov_ot_r])

            # Invert line for the theoretical overlay (matches the
            # primary one in style but in overlay-purple so it's
            # distinguishable when both visible)
            if ov_it_l is not None and ov_it_r is not None:
                ax.plot([ov_it_l[0], ov_it_r[0]],
                        [ov_it_l[1], ov_it_r[1]],
                        color=ov_color, linestyle='--',
                        linewidth=1.2, alpha=0.6, zorder=3)

            # Metrics for the overlay (the build-up parameters give an
            # exact design H:V; we also compute the section's apparent H:V
            # for direct comparison with the DXF measured H:V)
            def _ov_hv(crest_pt, toe_pt):
                if crest_pt is None or toe_pt is None:
                    return None
                dh = abs(crest_pt[0] - toe_pt[0])
                dv = abs(crest_pt[1] - toe_pt[1])
                if dv < 0.01: return None
                return dh / dv
            overlay_metrics = {
                'outer_l': _ov_hv(ov_oc_l, ov_ot_l),
                'outer_r': _ov_hv(ov_oc_r, ov_ot_r),
                'inner_l': _ov_hv(ov_ic_l, ov_it_l),
                'inner_r': _ov_hv(ov_ic_r, ov_it_r),
            }

        # Annotate the apparent H:V slopes (measured FROM the section)
        # alongside the design H:V. The difference is exactly the
        # foreshortening - if the section axis is radial at that point of
        # the perimeter, apparent ~= design.
        m = compute_inferred_metrics(role_ring, self._preview)
        design_inner = m.get('inner_hv')
        design_outer = m.get('outer_hv')

        def _measured_hv(crest_pt, toe_pt):
            if crest_pt is None or toe_pt is None:
                return None
            dh = abs(crest_pt[0] - toe_pt[0])
            dv = abs(crest_pt[1] - toe_pt[1])
            if dv < 0.01:
                return None
            return dh / dv

        msr_outer_l = _measured_hv(oc_l, ot_l)
        msr_outer_r = _measured_hv(oc_r, ot_r)
        msr_inner_l = _measured_hv(ic_l, it_l)
        msr_inner_r = _measured_hv(ic_r, it_r)

        def _fmt(hv):
            return f"{hv:.2f}:1" if hv is not None else "n/a"

        deg = self._current_section_angle_deg() or 0.0
        # Indicate variable-Z outer toe in the title when present
        ot_role = role_ring.get('outer_toe')
        ot_var = (ot_role is not None
                  and ot_role.get('is_variable_z') is True)
        ot_note = (" Outer toe is variable-Z." if ot_var else "")
        title_lines = [
            f"Long section at {deg:.0f}\u00b0 (centroid-through). "
            f"Half-length {L:.0f} m. Z-offset {z_off:+.3f} m. "
            f"Primary: {primary_label}.{ot_note}",
            f"DXF measured H:V - OUTER (L/R) = {_fmt(msr_outer_l)} / "
            f"{_fmt(msr_outer_r)}    INNER (L/R) = "
            f"{_fmt(msr_inner_l)} / {_fmt(msr_inner_r)}    "
            f"DESIGN - inner {_fmt(design_inner)}, "
            f"outer {_fmt(design_outer)}",
        ]
        if overlay_metrics is not None:
            title_lines.append(
                f"Theoretical (anchor-built) H:V - "
                f"OUTER (L/R) = {_fmt(overlay_metrics['outer_l'])} / "
                f"{_fmt(overlay_metrics['outer_r'])}    "
                f"INNER (L/R) = {_fmt(overlay_metrics['inner_l'])} / "
                f"{_fmt(overlay_metrics['inner_r'])}")
        ax.set_title("\n".join(title_lines), fontsize=9)
        ax.set_xlabel("Distance along section (m, centred on dam)")
        ax.set_ylabel("Z (m, NZVD2016 after offset)")
        ax.grid(True, alpha=0.3)
        # Vertical line at the centroid
        ax.axvline(0, color='#aaa', linestyle=':', linewidth=1, zorder=2)
        # Apply vertical exaggeration via set_aspect. matplotlib's aspect
        # is "y units per x unit in display pixels": ve=1 -> 1 m vertical
        # = 1 m horizontal in pixels (TRUE scale, slopes shown at real
        # angle). ve=5 -> 1 m vertical = 5 m horizontal in pixels
        # (vertical stretched 5x, slopes look 5x steeper than they really
        # are). The numerical H:V in the title is unaffected by V.E.
        #
        # adjustable='datalim' (not 'box'): the axes box fills the
        # figure normally, and matplotlib expands the data limits along
        # the *long* axis to satisfy the aspect ratio. So we get a
        # nicely-sized plot using the full canvas, with extra horizontal
        # range around the dam (rather than a thin strip with whitespace
        # above and below). The V.E. is still exact - vertical scale is
        # still V.E. times horizontal scale on screen.
        try:
            ve = float(self.spn_ve.value())
        except Exception:
            ve = 1.0
        if ve > 0:
            ax.set_aspect(ve, adjustable='datalim')
        # Annotate V.E. on the plot for transparency
        ax.text(0.99, 0.02, f"V.E. = {ve:.1f}\u00d7",
                transform=ax.transAxes, ha='right', va='bottom',
                fontsize=8, color='#666',
                bbox=dict(boxstyle='round,pad=0.3',
                          facecolor='white', alpha=0.8, edgecolor='#ccc'))
        # Dedupe legend, place BELOW the plot in a horizontal row so it
        # doesn't obscure the section. Previously the legend used
        # loc='best' which often landed on top of the dam profile when
        # the plot was vertically squashed.
        h, l = ax.get_legend_handles_labels()
        seen = set(); kept = []
        for hi, li in zip(h, l):
            if li and li not in seen:
                seen.add(li); kept.append((hi, li))
        if kept:
            ax.legend([k[0] for k in kept], [k[1] for k in kept],
                       loc='upper center',
                       bbox_to_anchor=(0.5, -0.18),
                       fontsize=8, framealpha=0.9,
                       ncol=min(6, len(kept)))
        # Give the legend space below by tightening the layout with a
        # bottom margin reserved.
        try:
            self._section_fig.tight_layout(rect=[0, 0.05, 1, 1])
        except Exception:
            pass
        self._section_canvas.draw_idle()

    def _overlay_design_at_chainage(self, ax, role_ring, oc_coords, ch,
                                     sec_width):
        """Draw the design dam profile (crest, inner batter, outer batter)
        on top of the ground line at the perpendicular intersection through
        the given chainage on oc_coords.

        Method: cast a perpendicular line through the chainage point on
        outer_crest (the section axis) and find where that line crosses each
        of the assigned rings - using line-segment intersection, not
        nearest-vertex distance. For a closed ring the line typically crosses
        in two places (near side + far side, on opposite faces of the dam);
        we take the near-side crossing (smallest |offset|) which is the local
        cross-section.

        Design Z values are shifted by the user's vertical offset so the
        markers align with the (NZVD2016) existing-ground line.
        """
        z_off = self._z_offset_value()
        # Section axis: outward perpendicular through the chainage point
        oc_pt, perp = _outward_perpendicular(oc_coords, ch)
        if perp is None:
            return
        line_pt = (oc_pt[0], oc_pt[1])

        # outer crest at offset 0 (reference) - applying the Z offset
        oc_z_shifted = oc_pt[2] + z_off
        ax.scatter([0.0], [oc_z_shifted], color='#d62728', s=60, zorder=5,
                   label='Outer crest')

        # Each other ring contributes one point on the section, found by
        # line-ring intersection at the near-side crossing.
        order = [
            ('inner_toe',   '#1f77b4', '^', 'Inner toe'),
            ('inner_crest', '#2ca02c', 's', 'Inner crest'),
            # outer_crest handled above
            ('outer_toe',   '#ff7f0e', 'v', 'Outer toe'),
        ]
        # Collect plotted points (offset, z) for connector lines.
        # Key order matches the natural cross-section walk.
        plotted = {'outer_crest': (0.0, oc_z_shifted)}
        for role, colour, marker, label in order:
            ring = role_ring.get(role)
            if ring is None:
                continue
            t = _nearest_axis_offset(ring['coords'], line_pt, perp)
            if t is None:
                continue
            # Reject crossings further than the section's half-width (these
            # are far-side artefacts that survived because the closer crossing
            # didn't exist for some reason)
            if abs(t) > sec_width:
                continue
            z_shifted = ring['z_mean'] + z_off
            ax.scatter([t], [z_shifted], color=colour, s=60,
                       marker=marker, zorder=5, label=label)
            plotted[role] = (t, z_shifted)

        # Dashed connectors in physical-walk order: inner_toe -> inner_crest
        # -> outer_crest -> outer_toe
        walk = ['inner_toe', 'inner_crest', 'outer_crest', 'outer_toe']
        pts = [plotted.get(r) for r in walk]
        for a, b in zip(pts, pts[1:]):
            if a is None or b is None:
                continue
            ax.plot([a[0], b[0]], [a[1], b[1]],
                    color='#333', linestyle='--', linewidth=1.2, zorder=4)

    def _detect_crs(self):
        """Detect CRS from the first vector layer with features."""
        self._data_crs = None
        for lid, lyr in QgsProject.instance().mapLayers().items():
            if isinstance(lyr, QgsVectorLayer) and lyr.featureCount() > 0:
                crs = lyr.crs()
                if crs.isValid():
                    self._data_crs = crs
                    self.lbl_data_crs.setText(
                        f"{crs.authid()} ({crs.description()})")
                    return
        self.lbl_data_crs.setText("No valid CRS found")

    def _file_centroid_xy(self):
        """Centroid (x, y) of the loaded DXF/DWG geometry in its own file
        coordinates, or None. Used for source-CRS detection."""
        path = self.txt_dxf.text().strip()
        if not path or not os.path.isfile(path):
            return None
        try:
            ents = _parse_dxf_entities(path)
        except Exception as e:
            LOG.warn(f"Could not read file for CRS detection: {e}")
            return None
        xs = []
        ys = []
        for e in ents:
            if e.get('type') == 'POLYLINE':
                for v in e.get('vertices', []):
                    xs.append(v['x'])
                    ys.append(v['y'])
            elif e.get('type') == 'LINE':
                xs += [e['start'][0], e['end'][0]]
                ys += [e['start'][1], e['end'][1]]
        if not xs:
            return None
        return (sum(xs) / len(xs), sum(ys) / len(ys))

    def _smart_detect_source_crs(self):
        """Populate the Input-CRS combo with NZ CRSs ranked by where they
        place the file's geometry relative to the current map view (best
        guess first). Falls back to reading a layer CRS when there's no
        file selected."""
        cen = self._file_centroid_xy()
        if cen is None:
            self._detect_crs()  # legacy: read CRS from a loaded layer
            return
        cx, cy = cen
        ref_pt = None
        ref_crs = None
        try:
            ref_pt = self.canvas.extent().center()
            ref_crs = self.canvas.mapSettings().destinationCrs()
        except Exception:
            pass
        cands = _rank_nz_crs_candidates(cx, cy, ref_pt, ref_crs)
        if not cands:
            QMessageBox.warning(self, "Smart CRS detect",
                                "Could not evaluate CRS candidates.")
            return
        self.cmb_src_crs.blockSignals(True)
        self.cmb_src_crs.clear()
        self.cmb_src_crs.addItem(
            "Assume NZTM2000 (EPSG:2193) - no reprojection", None)
        for c in cands:
            if c['dist_km'] is not None:
                where = f"{c['dist_km']:.0f} km from view"
            else:
                where = "in NZ" if c['in_nz'] else "offshore"
            self.cmb_src_crs.addItem(
                f"EPSG:{c['epsg']} {c['name']} - {where} "
                f"({c['lat']:.3f}, {c['lon']:.3f})", c['epsg'])
        self.cmb_src_crs.blockSignals(False)
        # Best guess = first (already ranked) candidate.
        self.cmb_src_crs.setCurrentIndex(1)
        self._on_src_crs_changed(1)
        top = cands[0]
        tail = (f" (lands {top['dist_km']:.0f} km from your current view)"
                if top['dist_km'] is not None else "")
        self.lbl_data_crs.setText(
            f"Centroid E={cx:,.0f} N={cy:,.0f}. Best guess EPSG:{top['epsg']} "
            f"{top['name']}{tail}. Click 'Test selected CRS on map' to confirm "
            f"it lands on the dam, then leave it selected. Tip: pan to the dam "
            f"site first for the best ranking.")

    def _on_src_crs_changed(self, idx):
        """Combo selection -> self._data_crs (consumed by step2_extract)."""
        try:
            epsg = self.cmb_src_crs.currentData()
        except Exception:
            epsg = None
        if epsg is None:
            self._data_crs = None
            if hasattr(self, 'lbl_data_crs'):
                self.lbl_data_crs.setText(
                    "Input CRS: assuming NZTM2000 (no reprojection).")
            return
        crs = QgsCoordinateReferenceSystem(f"EPSG:{epsg}")
        if crs.isValid():
            self._data_crs = crs
            if hasattr(self, 'lbl_data_crs'):
                self.lbl_data_crs.setText(
                    f"Input CRS: {crs.authid()} {crs.description()} - will "
                    f"reproject to NZTM2000 on Run.")
        else:
            self._data_crs = None

    def _test_source_crs_on_map(self):
        """Drop the file's outline onto the canvas in the selected CRS so the
        user can see whether it lands on the right place over their basemap.
        QGIS reprojects on the fly: the wrong circuit lands elsewhere, the
        right one lands on the dam."""
        path = self.txt_dxf.text().strip()
        if not path or not os.path.isfile(path):
            QMessageBox.information(self, "Test CRS on map",
                                    "Pick a DXF/DWG file first.")
            return
        try:
            ents = _parse_dxf_entities(path)
        except Exception as e:
            QMessageBox.warning(self, "Test CRS on map",
                                f"Could not read file:\n{e}")
            return
        epsg = self.cmb_src_crs.currentData()
        crs_str = f"EPSG:{epsg}" if epsg else f"EPSG:{CRS_EPSG}"
        self._clear_crs_preview()
        lyr = QgsVectorLayer(f"LineString?crs={crs_str}",
                             "CRS test preview", "memory")
        pr = lyr.dataProvider()
        # Decimate for a snappy preview.
        nver = sum(len(e.get('vertices', [])) for e in ents
                   if e.get('type') == 'POLYLINE')
        stride = max(1, int(nver / 4000)) if nver else 1
        feats = []
        for e in ents:
            if e.get('type') == 'POLYLINE':
                vs = e.get('vertices', [])
                pts = [QgsPointXY(v['x'], v['y']) for v in vs[::stride]]
                if len(pts) < 2:
                    continue
                f = QgsFeature()
                f.setGeometry(QgsGeometry.fromPolylineXY(pts))
                feats.append(f)
            elif e.get('type') == 'LINE':
                f = QgsFeature()
                f.setGeometry(QgsGeometry.fromPolylineXY([
                    QgsPointXY(e['start'][0], e['start'][1]),
                    QgsPointXY(e['end'][0], e['end'][1])]))
                feats.append(f)
        if not feats:
            QMessageBox.warning(self, "Test CRS on map",
                                "No line geometry to preview.")
            return
        pr.addFeatures(feats)
        lyr.updateExtents()
        QgsProject.instance().addMapLayer(lyr)
        self._crs_preview_layer_id = lyr.id()
        # Deliberately do NOT zoom: keep the user's view on the dam so the
        # correct CRS makes the outline appear ON it, and a wrong CRS simply
        # doesn't show up in view. setActiveLayer lets them Ctrl+J / zoom-to-
        # layer manually if they want to chase a wrong one.
        try:
            self.iface.setActiveLayer(lyr)
            self.canvas.refresh()
        except Exception:
            pass
        nm = self.cmb_src_crs.currentText().split(" - ")[0]
        self.lbl_data_crs.setText(
            f"Previewing as {nm}. If the outline sits on the dam in your "
            f"aerial, leave this CRS selected. If it's not in view, that CRS "
            f"is wrong - pick another candidate and test again. 'Clear "
            f"preview' removes the test layer.")

    def _clear_crs_preview(self):
        """Remove the temporary CRS test-preview layer, if present."""
        lid = getattr(self, '_crs_preview_layer_id', None)
        if lid:
            try:
                QgsProject.instance().removeMapLayer(lid)
            except Exception:
                pass
        self._crs_preview_layer_id = None
        try:
            self.canvas.refresh()
        except Exception:
            pass

    def _start_pick(self):
        """Hide dialog and activate map click tool."""
        self.hide()
        self._pick_tool = SpillwayPickTool(
            self.canvas, self, self.spn_se, self.spn_sn)
        self.canvas.setMapTool(self._pick_tool)

    def _on_run(self):
        spillway_on = self.chk_spillway.isChecked()
        no_coords = self.spn_se.value() < 1 and self.spn_sn.value() < 1
        if spillway_on and no_coords:
            r = QMessageBox.question(
                self, "No spillway location",
                "Spillway enabled but no location set.\n"
                "Use 'Pick from Map' or enter coordinates.\n\n"
                "Continue without spillway?",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if r == QMessageBox.No:
                return
            spillway_on = False

        dam_name = self.txt_dam_name.text().strip() or "Proposed Dam"

        self.result_params = {
            'dam_name': dam_name,
            'dxf_path': self.txt_dxf.text().strip() or None,
            # Multi-dam DXFs: list of layer names to keep, or None to
            # accept everything. Set via the "DXF layers" dropdown on
            # the Input tab. Filters POLYLINE/LINE entities before
            # classification, so a 2-dam DXF can be split into two runs.
            'dxf_layer_filter': self.cmb_dxf_layer_filter.currentData(),
            'layer_name': None if self.chk_auto_layer.isChecked()
                          else self.cmb_layer.currentText(),
            'data_crs': self._data_crs,
            'auto_elev': self.chk_auto_elev.isChecked(),
            'invert': self.spn_invert.value(),
            'crest': self.spn_crest.value(),
            'toe_low': self.spn_toe.value(),
            'point_spacing': self.spn_spacing.value(),
            # Model interior sump(s) as basin pockets in the DEM.
            'include_sump': self.chk_include_sump.isChecked(),
            'spillway_enabled': spillway_on,
            'spill_e': self.spn_se.value(),
            'spill_n': self.spn_sn.value(),
            'spill_depth': self.spn_sd.value(),
            'spill_width': self.spn_sw.value(),
            'spill_batter': self.spn_sb.value(),
            'dem_enabled': self.chk_dem.isChecked(),
            'dem_res': self.spn_res.value(),
            'use_breaklines': self.chk_bl.isChecked(),
            'export_csv': self.chk_csv.isChecked(),
            'output_dir': self.txt_out.text(),
            'min_area': self.spn_ma.value(),
            'min_verts': int(self.spn_mv.value()),
            'stitch_tol': self.spn_st.value(),
            'z_thresh': self.spn_zt.value(),
            # Datum correction: shift applied to all DXF Z values so the
            # design aligns with the (NZVD2016) DEM. Applied to all ring Z
            # values just after step3_classify, so the rest of the pipeline
            # (point cloud, DEM, output files) lands in NZVD2016.
            'z_offset': self._z_offset_value(),
            # When the dam has been moved off the DXF datum by a non-
            # ground snap (cut/fill, max-height, manual slider), the
            # DXF's baked-in outer toe (Method 1) is stale and the output
            # must re-derive the toe from the terrain intersection
            # (Method 2). Ship the flag + the active method so run() can
            # force Method 2 priority. See _force_method2_at_output().
            'dam_moved_off_dxf_toe': bool(self._dam_moved_off_dxf_toe),
            'active_var_z_method': self._active_var_z_method,
            # Phase 2: constructed geometry overrides. When set, run()
            # bypasses step4_identify and uses these constructed rings as
            # the kl. CFG['outer_hv']/['inner_hv'] also get the override
            # values so step4b is skipped.
            'constructed_kl': (
                self._constructed_kl
                if (self._constructed_kl is not None
                    and self.chk_use_constructed.isChecked())
                else None),
            'constructed_inner_hv': (
                self._buildup_param_values()['inner_hv']
                if self._constructed_kl is not None
                   and self.chk_use_constructed.isChecked() else None),
            'constructed_outer_hv': (
                self._buildup_param_values()['outer_hv']
                if self._constructed_kl is not None
                   and self.chk_use_constructed.isChecked() else None),
            # Manual role assignments from the picker. We ship INDICES
            # into the combined const+var ring list (not the ring dicts
            # themselves) because the dialog holds raw DXF Z while run()
            # applies z_offset to its own ring objects - shipping objects
            # would mix datums. step3_classify is deterministic on the
            # same DXF so const_z[i] / var_z[j] line up between preview
            # and run.
            'role_override_indices': (
                dict(self._role_assignments)
                if self._role_assignments
                   and (self._constructed_kl is None
                        or not self.chk_use_constructed.isChecked()) else None),
            'n_const_in_preview': (
                self._preview.get('n_const')
                if self._preview is not None else None),
            # ---- Phase 3: Polygon Mode ----
            'polygon_mode': self.chk_polygon_mode.isChecked(),
            'polygon_layer_id': (
                self.cmb_polygon_layer.currentData()
                if self.chk_polygon_mode.isChecked() else None),
            'polygon_feature_fid': (
                None if self.spn_polygon_fid.value() < 0
                else int(self.spn_polygon_fid.value())),
            'polygon_role': self.cmb_polygon_role.currentData(),
            'polygon_z': float(self.spn_polygon_z.value()),
            'polygon_crest_z': float(self.spn_p_crest_z.value()),
            'polygon_invert_z': float(self.spn_p_invert_z.value()),
            'polygon_crest_width': float(self.spn_p_crest_w.value()),
            'polygon_inner_hv': float(self.spn_p_inner_hv.value()),
            'polygon_outer_hv': float(self.spn_p_outer_hv.value()),
            'terrain_overshoot': float(self.spn_p_overshoot.value()),
            # In polygon mode, prefer the polygon-tab terrain; else fall
            # back to Input-tab terrain (used by both modes for drape).
            'terrain_layer_id': (
                self.cmb_polygon_terrain.currentData()
                if (self.chk_polygon_mode.isChecked()
                    and self.cmb_polygon_terrain.currentData() is not None)
                else (self._terrain_layer.id()
                      if self._terrain_layer is not None else None)),
            # ---- Phase 3: Drape DEM to terrain ----
            'drape_to_terrain': self.chk_drape.isChecked(),
            'drape_terrain_id': (
                self.cmb_drape_terrain.currentData()
                if self.cmb_drape_terrain.currentData() is not None
                else (self._terrain_layer.id()
                      if self._terrain_layer is not None else None)),
        }
        self.accept()


# =============================================================================
# GLOBAL STATE
# =============================================================================

CFG = {}
CRS_EPSG = 2193  # Output always NZTM2000


# =============================================================================
# GEOMETRY UTILITIES
# =============================================================================

def shoelace(coords):
    n = len(coords)
    if n < 3: return 0.0
    a = sum(coords[i][0]*coords[(i+1)%n][1] - coords[(i+1)%n][0]*coords[i][1]
            for i in range(n))
    return abs(a) / 2.0


def pdist(a, b):
    return math.sqrt((a[0]-b[0])**2 + (a[1]-b[1])**2)


def is_closed(c, tol=1.0):
    return len(c) >= 3 and pdist(c[0], c[-1]) < tol


def zstats(c):
    zs = [p[2] for p in c]
    m = sum(zs)/len(zs)
    s = (sum((z-m)**2 for z in zs)/len(zs))**0.5
    return min(zs), max(zs), m, s


def llen(c):
    return sum(pdist(c[i], c[i+1]) for i in range(len(c)-1))


def densify(coords, sp):
    if len(coords) < 2: return list(coords)
    cum = [0.0]
    for i in range(1, len(coords)):
        cum.append(cum[-1] + pdist(coords[i-1], coords[i]))
    tot = cum[-1]
    if tot < sp: return list(coords)
    n = max(int(math.ceil(tot/sp)), 2)
    res, seg = [], 0
    for i in range(n+1):
        t = min(i*sp, tot)
        while seg < len(cum)-2 and cum[seg+1] < t:
            seg += 1
        sl = cum[seg+1] - cum[seg]
        f = 0.0 if sl < 1e-10 else max(0, min(1, (t-cum[seg])/sl))
        res.append((
            coords[seg][0] + f*(coords[seg+1][0]-coords[seg][0]),
            coords[seg][1] + f*(coords[seg+1][1]-coords[seg][1]),
            coords[seg][2] + f*(coords[seg+1][2]-coords[seg][2]),
        ))
    return res


def ch_nearest(coords, px, py):
    bd, bc, cum = float('inf'), 0.0, 0.0
    for i in range(len(coords)-1):
        sl = pdist(coords[i], coords[i+1])
        if sl < 1e-10: cum += sl; continue
        dx = coords[i+1][0]-coords[i][0]
        dy = coords[i+1][1]-coords[i][1]
        t = max(0, min(1, ((px-coords[i][0])*dx+(py-coords[i][1])*dy)/(dx*dx+dy*dy)))
        d = math.sqrt((px-coords[i][0]-t*dx)**2 + (py-coords[i][1]-t*dy)**2)
        if d < bd: bd, bc = d, cum+t*sl
        cum += sl
    return bc, bd


def interp_ch(coords, ch):
    cum = 0.0
    for i in range(len(coords)-1):
        sl = pdist(coords[i], coords[i+1])
        if cum+sl >= ch-1e-10:
            if sl < 1e-10: return coords[i]
            t = max(0, min(1, (ch-cum)/sl))
            return (coords[i][0]+t*(coords[i+1][0]-coords[i][0]),
                    coords[i][1]+t*(coords[i+1][1]-coords[i][1]),
                    coords[i][2]+t*(coords[i+1][2]-coords[i][2]))
        cum += sl
    return coords[-1]


def _ring_arc_with_gap(coords, ch_lo, ch_hi):
    """Return an open polyline tracing the closed ring `coords` with the
    chainage interval [ch_lo, ch_hi] omitted. The output starts at ch_hi
    (right edge of gap), wraps past the seam, and ends at ch_lo (left edge
    of gap), so consumers reading it as an open polyline see a clean gap
    where the spillway notch is.
    """
    if ch_lo is None or ch_hi is None or ch_lo >= ch_hi:
        return list(coords)
    total = llen(coords)
    if ch_hi - ch_lo >= total - 0.01:
        return []  # gap is essentially the entire ring

    # Cumulative chainage at each input vertex
    cums = [0.0]
    for i in range(1, len(coords)):
        cums.append(cums[-1] + pdist(coords[i-1], coords[i]))

    out = [interp_ch(coords, ch_hi)]  # right edge of gap
    # Forward: vertices with chainage > ch_hi (toward the seam at total)
    for i in range(len(coords)):
        if cums[i] > ch_hi + 1e-6:
            out.append(coords[i])
    # Wrap past the seam: vertices with chainage < ch_lo (from start of ring)
    for i in range(len(coords)):
        if cums[i] >= ch_lo - 1e-6:
            break
        # Skip the duplicate seam point if ring is closed and we already
        # have it as the last appended vertex
        if i == 0 and out and pdist(out[-1], coords[i]) < 1e-3:
            continue
        out.append(coords[i])
    out.append(interp_ch(coords, ch_lo))  # left edge of gap
    return out


# =============================================================================
# STEP 1: VALIDATE INPUT
# =============================================================================

def step1_validate():
    LOG.start_step("Validating input")

    use_dxf = CFG.get('dxf_path') is not None

    if use_dxf:
        dxf_path = CFG['dxf_path']
        if not os.path.isfile(dxf_path):
            raise ValueError(f"DXF file not found:\n{dxf_path}")
        LOG.info(f"DXF direct read: {os.path.basename(dxf_path)}")
        input_layers = None  # Signal DXF mode

    if not use_dxf and CFG['layer_name']:
        layers = QgsProject.instance().mapLayersByName(CFG['layer_name'])
        if not layers:
            avail = [l.name() for l in QgsProject.instance().mapLayers().values()
                     if isinstance(l, QgsVectorLayer)]
            raise ValueError(
                f"Layer '{CFG['layer_name']}' not found in project.\n\n"
                f"Available vector layers:\n  " + "\n  ".join(avail) if avail
                else "No vector layers loaded.")
        input_layers = layers
        LOG.info(f"Using specified layer: {CFG['layer_name']}")
    elif not use_dxf:
        input_layers = [l for l in QgsProject.instance().mapLayers().values()
                        if isinstance(l, QgsVectorLayer)]
        if not input_layers:
            raise ValueError(
                "No vector layers found in project.\n\n"
                "Load your DXF/GeoPackage first, or use Browse DXF.")
        LOG.info(f"Auto-detected {len(input_layers)} vector layer(s):")
        for l in input_layers:
            LOG.detail(f"{l.name()}: {l.featureCount()} features, "
                       f"CRS={l.crs().authid()}")

    # Check CRS (layer mode only)
    if input_layers:
        for l in input_layers:
            crs = l.crs()
            if crs.isValid():
                LOG.info(f"Layer '{l.name()}' CRS: {crs.authid()} "
                         f"({crs.description()})")
            else:
                LOG.warn(f"Layer '{l.name()}' has no valid CRS.")

        total = sum(l.featureCount() for l in input_layers)
        if total == 0:
            raise ValueError("Input layer(s) contain no features.")
        LOG.info(f"Total features across all layers: {total}")

    # Check output directory is writable
    out = CFG['output_dir']
    if not os.path.exists(out):
        try:
            os.makedirs(out)
            LOG.info(f"Created output directory: {out}")
        except OSError as e:
            raise ValueError(f"Cannot create output directory:\n{out}\n\n{e}")
    else:
        test_file = os.path.join(out, ".write_test")
        try:
            with open(test_file, 'w') as f:
                f.write("test")
            os.remove(test_file)
        except OSError as e:
            raise ValueError(
                f"Output directory is not writable:\n{out}\n\n{e}")

    LOG.success("Input validated")
    return input_layers


# =============================================================================
# STEP 2: EXTRACT GEOMETRY
# =============================================================================

def _bulge_to_arc_points(x1, y1, x2, y2, bulge, z):
    """Convert a DXF bulge between two vertices to arc points.
    Bulge = tan(included_angle / 4). Positive = CCW, negative = CW.
    Returns intermediate points (excludes start and end vertices)."""
    if abs(bulge) < 0.0001:
        return []

    dx = x2 - x1
    dy = y2 - y1
    chord = math.sqrt(dx**2 + dy**2)
    if chord < 1e-10:
        return []

    # Sagitta and radius from bulge
    s = abs(bulge) * chord / 2
    r = (chord**2 / 4 + s**2) / (2 * s)

    # Midpoint and normal to chord
    mx, my = (x1 + x2) / 2, (y1 + y2) / 2
    nx, ny = -dy / chord, dx / chord

    # Centre of arc
    d = r - s
    if bulge > 0:
        cx, cy = mx + d * nx, my + d * ny
    else:
        cx, cy = mx - d * nx, my - d * ny

    # Angles
    a1 = math.atan2(y1 - cy, x1 - cx)
    a2 = math.atan2(y2 - cy, x2 - cx)
    included = 4 * math.atan(abs(bulge))

    if bulge > 0:
        if a2 < a1:
            a2 += 2 * math.pi
    else:
        if a2 > a1:
            a2 -= 2 * math.pi

    # Adaptive point count: ~0.2m spacing along arc
    arc_len = abs(included) * r
    n = max(int(arc_len / 0.2), 4)

    pts = []
    for j in range(1, n):
        t = j / n
        a = a1 + t * (a2 - a1)
        pts.append((cx + r * math.cos(a), cy + r * math.sin(a), z))

    return pts


# =============================================================================
# DWG SUPPORT - convert AutoCAD binary DWG to DXF before parsing
# =============================================================================
#
# The text parser below reads ASCII DXF only. AutoCAD's binary DWG must be
# converted first. No pure-Python DWG reader is robust enough to depend on, so
# we shell out to whichever converter is installed, in order of fidelity:
#
#   1. ODA File Converter  - free official tool from the Open Design Alliance;
#                            converts every DWG version cleanly. Recommended.
#   2. ezdxf + odafc addon - same ODA engine, driven through ezdxf if present.
#   3. LibreDWG (dwg2dxf)  - open-source converter, if on PATH.
#   4. GDAL CAD driver     - always bundled with QGIS, but libopencad rejects
#                            many real-world DWGs (header/CRC quirks), so it is
#                            the last resort, not the first.
#
# The result is cached in the temp dir keyed by source path+mtime+size, so the
# layer scan, preview and final extract convert the file only once.

def _dwg_cache_path(dwg_path):
    """Stable temp path for the converted DXF, keyed by the DWG's path, mtime
    and size so an edited DWG invalidates the cache."""
    import tempfile, hashlib
    st = os.stat(dwg_path)
    key = f"{os.path.abspath(dwg_path)}|{st.st_mtime_ns}|{st.st_size}"
    tag = hashlib.sha1(key.encode("utf-8")).hexdigest()[:12]
    stem = os.path.splitext(os.path.basename(dwg_path))[0]
    cdir = os.path.join(tempfile.gettempdir(), "ggl_dwg_cache")
    os.makedirs(cdir, exist_ok=True)
    return os.path.join(cdir, f"{stem}_{tag}.dxf")


def _find_oda_converter():
    """Locate the ODA (or legacy Teigha) File Converter executable, else None."""
    import shutil, glob
    for n in ("ODAFileConverter", "TeighaFileConverter"):
        p = shutil.which(n) or shutil.which(n + ".exe")
        if p:
            return p
    pats = []
    for env in ("ProgramFiles", "ProgramFiles(x86)", "ProgramW6432"):
        base = os.environ.get(env)
        if base:
            pats.append(os.path.join(base, "ODA", "*", "ODAFileConverter*"))
            pats.append(os.path.join(base, "ODA", "*", "TeighaFileConverter*"))
    pats += ["/usr/bin/ODAFileConverter", "/usr/local/bin/ODAFileConverter",
             "/opt/*/ODAFileConverter"]
    for pat in pats:
        for c in sorted(glob.glob(pat)):
            if os.path.isfile(c):
                return c
    return None


def _convert_via_oda(dwg_path, out_dxf):
    """Drive ODA File Converter directly. It converts a whole folder, so the
    DWG is staged in a temp input folder and the produced DXF collected."""
    import subprocess, tempfile, shutil, glob
    exe = _find_oda_converter()
    if not exe:
        return False
    work = tempfile.mkdtemp(prefix="ggl_oda_")
    try:
        in_dir = os.path.join(work, "in")
        out_dir = os.path.join(work, "out")
        os.makedirs(in_dir)
        os.makedirs(out_dir)
        shutil.copyfile(dwg_path, os.path.join(in_dir, os.path.basename(dwg_path)))
        # ODAFileConverter IN OUT OUTVER OUTTYPE RECURSE AUDIT [FILTER]
        cmd = [exe, in_dir, out_dir, "ACAD2018", "DXF", "0", "1", "*.DWG"]
        # A headless Linux box needs a virtual display for the Qt-based GUI.
        if os.name != "nt" and not os.environ.get("DISPLAY"):
            xvfb = shutil.which("xvfb-run")
            if xvfb:
                cmd = [xvfb, "-a"] + cmd
        subprocess.run(cmd, timeout=300, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
        produced = (glob.glob(os.path.join(out_dir, "*.dxf"))
                    + glob.glob(os.path.join(out_dir, "*.DXF")))
        if produced and os.path.getsize(produced[0]) > 0:
            shutil.copyfile(produced[0], out_dxf)
            return True
        return False
    except Exception as e:
        LOG.detail(f"ODA File Converter failed: {e}")
        return False
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _convert_via_ezdxf(dwg_path, out_dxf):
    """Use ezdxf's odafc addon (needs ezdxf installed AND ODA File Converter
    present); ezdxf handles the headless conversion details."""
    try:
        from ezdxf.addons import odafc
    except Exception:
        return False
    try:
        doc = odafc.readfile(dwg_path)
        doc.saveas(out_dxf)
        return os.path.isfile(out_dxf) and os.path.getsize(out_dxf) > 0
    except Exception as e:
        LOG.detail(f"ezdxf/odafc conversion failed: {e}")
        return False


def _convert_via_libredwg(dwg_path, out_dxf):
    """Use LibreDWG's dwg2dxf, if on PATH."""
    import shutil, subprocess
    exe = shutil.which("dwg2dxf")
    if not exe:
        return False
    try:
        subprocess.run([exe, "-y", "-o", out_dxf, dwg_path], timeout=300,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return os.path.isfile(out_dxf) and os.path.getsize(out_dxf) > 0
    except Exception as e:
        LOG.detail(f"LibreDWG dwg2dxf failed: {e}")
        return False


def _convert_via_gdal(dwg_path, out_dxf):
    """Last resort: GDAL's CAD driver (always bundled with QGIS). libopencad
    rejects many real DWGs, so failure here is common and expected."""
    try:
        from osgeo import gdal
    except Exception:
        return False
    try:
        gdal.UseExceptions()
        src = gdal.OpenEx(dwg_path, gdal.OF_VECTOR)
        if src is None:
            return False
        gdal.VectorTranslate(out_dxf, src, format="DXF")
        src = None
        return os.path.isfile(out_dxf) and os.path.getsize(out_dxf) > 0
    except Exception as e:
        LOG.detail(f"GDAL CAD-driver conversion failed: {e}")
        return False


def _convert_dwg_to_dxf(dwg_path):
    """Convert a DWG to DXF using the best available backend. Returns the path
    to the converted DXF, or raises RuntimeError with install guidance if no
    converter could handle the file."""
    out_dxf = _dwg_cache_path(dwg_path)
    if os.path.isfile(out_dxf) and os.path.getsize(out_dxf) > 0:
        LOG.detail(f"Using cached DXF conversion: {os.path.basename(out_dxf)}")
        return out_dxf

    LOG.info(f"Converting DWG to DXF: {os.path.basename(dwg_path)}")
    backends = [
        ("ODA File Converter", _convert_via_oda),
        ("ezdxf + ODA", _convert_via_ezdxf),
        ("LibreDWG (dwg2dxf)", _convert_via_libredwg),
        ("GDAL CAD driver", _convert_via_gdal),
    ]
    for name, fn in backends:
        try:
            ok = fn(dwg_path, out_dxf)
        except Exception as e:
            LOG.detail(f"{name} backend errored: {e}")
            ok = False
        if ok:
            LOG.info(f"DWG converted via {name}.")
            return out_dxf

    raise RuntimeError(
        "Could not read the DWG - no working DWG-to-DXF converter was found.\n\n"
        f"File: {os.path.basename(dwg_path)}\n\n"
        "QGIS's built-in CAD reader (GDAL/libopencad) only handles a narrow "
        "range of DWGs and routinely rejects real-world files. To read DWGs "
        "reliably, install the free ODA File Converter:\n"
        "    https://www.opendesign.com/guestfiles/oda_file_converter\n\n"
        "Once installed, reopen the file and it will be detected automatically. "
        "Alternatively, open the DWG in AutoCAD / BricsCAD / Civil3D / 12d and "
        "'Save As' a DXF (R2000 or later), then load that DXF here.")


def _ensure_dxf(path):
    """Return an ASCII-DXF path for `path`. DXF (and other extensions) pass
    through unchanged; a .dwg is transparently converted to DXF and cached.
    This is the single hook that gives every read path - layer scan, preview
    and extract - DWG support."""
    if not path or not os.path.isfile(path):
        return path
    if path.lower().endswith(".dwg"):
        return _convert_dwg_to_dxf(path)
    return path


def _parse_dxf_entities(filepath):
    """Parse DXF/DWG geometry as plain text. Extracts POLYLINE and LWPOLYLINE
    (both with bulge arcs) and LINE entities. No external dependencies for
    DXF; a DWG is converted to DXF first (see _ensure_dxf).
    Returns list of entity dicts."""

    # DWG -> DXF up front so every caller (layer scan, preview, extract)
    # transparently supports binary AutoCAD DWG, not just ASCII DXF.
    filepath = _ensure_dxf(filepath)

    with open(filepath, 'r', errors='replace') as f:
        lines = [l.strip() for l in f.readlines()]

    entities = []
    i = 0
    in_entities = False

    while i < len(lines) - 1:
        code = lines[i]
        value = lines[i + 1]

        if code == '0' and value == 'SECTION':
            i += 2
            if i < len(lines) - 1 and lines[i] == '2' and lines[i+1] == 'ENTITIES':
                in_entities = True
                i += 2
                continue

        if code == '0' and value == 'ENDSEC':
            in_entities = False
            i += 2
            continue

        if not in_entities:
            i += 2
            continue

        # POLYLINE
        if code == '0' and value == 'POLYLINE':
            poly = {'type': 'POLYLINE', 'layer': '', 'closed': False,
                    'vertices': []}
            i += 2
            while i < len(lines) - 1:
                c, v = lines[i], lines[i + 1]
                if c == '8':
                    poly['layer'] = v
                elif c == '70':
                    poly['closed'] = bool(int(v) & 1)
                elif c == '0' and v == 'VERTEX':
                    vert = {'x': 0, 'y': 0, 'z': 0, 'bulge': 0}
                    i += 2
                    while i < len(lines) - 1:
                        vc, vv = lines[i], lines[i + 1]
                        if vc == '10': vert['x'] = float(vv)
                        elif vc == '20': vert['y'] = float(vv)
                        elif vc == '30': vert['z'] = float(vv)
                        elif vc == '42': vert['bulge'] = float(vv)
                        elif vc == '0': break
                        i += 2
                    poly['vertices'].append(vert)
                    continue
                elif c == '0' and v == 'SEQEND':
                    i += 2
                    break
                elif c == '0':
                    break
                i += 2
            entities.append(poly)
            continue

        # LWPOLYLINE (lightweight polyline). 2D: a single elevation (group
        # 38) applies to every vertex; vertices are 10/20 pairs with an
        # optional per-vertex bulge (42, applies to the segment starting at
        # that vertex). Normalised into the same dict shape as POLYLINE so
        # the extractor downstream needs no special case. This is the form
        # most DWG->DXF converters emit for contour strings, so without it a
        # converted file would parse to zero geometry.
        if code == '0' and value == 'LWPOLYLINE':
            poly = {'type': 'POLYLINE', 'layer': '', 'closed': False,
                    'vertices': []}
            elev = 0.0
            cur = None  # vertex being assembled (x set on 10, y on 20)
            i += 2
            while i < len(lines) - 1:
                c, v = lines[i], lines[i + 1]
                if c == '0':
                    break
                if c == '8':
                    poly['layer'] = v
                elif c == '70':
                    poly['closed'] = bool(int(float(v)) & 1)
                elif c == '38':
                    elev = float(v)
                elif c == '10':
                    if cur is not None:
                        poly['vertices'].append(cur)
                    cur = {'x': float(v), 'y': 0.0, 'z': 0.0, 'bulge': 0.0}
                elif c == '20':
                    if cur is not None:
                        cur['y'] = float(v)
                elif c == '42':
                    if cur is not None:
                        cur['bulge'] = float(v)
                i += 2
            if cur is not None:
                poly['vertices'].append(cur)
            # The single LWPOLYLINE elevation is the Z for every vertex.
            for vv in poly['vertices']:
                vv['z'] = elev
            entities.append(poly)
            continue

        # LINE
        if code == '0' and value == 'LINE':
            line = {'type': 'LINE', 'layer': '',
                    'start': [0, 0, 0], 'end': [0, 0, 0]}
            i += 2
            while i < len(lines) - 1:
                c, v = lines[i], lines[i + 1]
                if c == '8': line['layer'] = v
                elif c == '10': line['start'][0] = float(v)
                elif c == '20': line['start'][1] = float(v)
                elif c == '30': line['start'][2] = float(v)
                elif c == '11': line['end'][0] = float(v)
                elif c == '21': line['end'][1] = float(v)
                elif c == '31': line['end'][2] = float(v)
                elif c == '0': break
                i += 2
            entities.append(line)
            continue

        i += 2

    return entities


def _extract_from_dxf(dxf_path):
    """Read line geometry directly from DXF file. No external dependencies.
    Parses the DXF as text, extracts POLYLINE and LINE entities, and
    converts arc segments (bulge values) to smooth point sequences."""

    LOG.info(f"Reading DXF: {os.path.basename(dxf_path)}")

    entities = _parse_dxf_entities(dxf_path)

    # Multi-dam filter. CFG['dxf_layer_filter'] is one of:
    #   None                                  -> keep everything
    #   {'type':'layers','layers':[...]}      -> keep entities on those
    #                                            layers (by layer name)
    #   {'type':'bbox','bbox':(x0,y0,x1,y1)}  -> keep entities whose
    #                                            CENTROID falls in the box
    #                                            (spatial - robust to
    #                                            layer mislabelling)
    #   [layer, ...]  (legacy list form)      -> treated as 'layers'
    flt = None
    try:
        flt = CFG.get('dxf_layer_filter')
    except Exception:
        pass
    if flt:
        before = len(entities)
        ftype = None
        if isinstance(flt, dict):
            ftype = flt.get('type')
        elif isinstance(flt, (list, tuple)):
            ftype = 'layers'
            flt = {'type': 'layers', 'layers': list(flt)}

        if ftype == 'bbox':
            x0, y0, x1, y1 = flt['bbox']
            # Pad the box a little so a ring whose centroid sits right on
            # the cluster edge isn't dropped.
            pad = 5.0
            x0 -= pad; y0 -= pad; x1 += pad; y1 += pad

            def _centroid(e):
                if e.get('type') == 'POLYLINE':
                    vs = e.get('vertices', [])
                    if not vs:
                        return None
                    return (sum(v['x'] for v in vs) / len(vs),
                            sum(v['y'] for v in vs) / len(vs))
                if e.get('type') == 'LINE':
                    s, en = e.get('start'), e.get('end')
                    if s and en:
                        return ((s[0] + en[0]) / 2.0, (s[1] + en[1]) / 2.0)
                return None

            kept = []
            for e in entities:
                c = _centroid(e)
                if c is None:
                    continue
                if x0 <= c[0] <= x1 and y0 <= c[1] <= y1:
                    kept.append(e)
            entities = kept
            LOG.info(f"Spatial filter active (by location): keeping "
                     f"entities with centroid in "
                     f"({flt['bbox'][0]:.0f}, {flt['bbox'][1]:.0f})-"
                     f"({flt['bbox'][2]:.0f}, {flt['bbox'][3]:.0f}) "
                     f"-> {len(entities)}/{before} entities. This is "
                     f"immune to layer mislabelling.")
        elif ftype == 'layers':
            keep = set(flt.get('layers', []))
            entities = [e for e in entities if e.get('layer') in keep]
            LOG.info(f"Layer filter active (by layer name): keeping "
                     f"entities on {sorted(keep)} -> "
                     f"{len(entities)}/{before} entities.")

    # Catalogue
    from collections import Counter
    type_counts = Counter(e['type'] for e in entities)
    layer_counts = Counter(e['layer'] for e in entities)
    LOG.info(f"DXF layers: {dict(layer_counts)}")
    LOG.detail(f"Entity types: {dict(type_counts)}")

    all_lines = []
    arc_count = 0
    straight_count = 0

    for e in entities:
        if e['type'] == 'LINE':
            s, en = e['start'], e['end']
            all_lines.append([(s[0], s[1], s[2]), (en[0], en[1], en[2])])
            straight_count += 1

        elif e['type'] == 'POLYLINE':
            verts = e['vertices']
            if len(verts) < 2:
                continue

            has_bulge = any(abs(v['bulge']) > 0.001 for v in verts)

            if has_bulge:
                # Build flattened polyline with arc points
                coords = []
                nv = len(verts)
                for vi in range(nv):
                    v = verts[vi]
                    coords.append((v['x'], v['y'], v['z']))

                    if abs(v['bulge']) > 0.001:
                        next_vi = (vi + 1) % nv
                        nxt = verts[next_vi]
                        arc_pts = _bulge_to_arc_points(
                            v['x'], v['y'], nxt['x'], nxt['y'],
                            v['bulge'], v['z'])
                        coords.extend(arc_pts)

                if e['closed'] and len(coords) >= 3:
                    if pdist(coords[0], coords[-1]) > 0.01:
                        coords.append(coords[0])

                if len(coords) >= 2:
                    all_lines.append(coords)
                    arc_count += 1
            else:
                coords = [(v['x'], v['y'], v['z']) for v in verts]
                if e['closed'] and len(coords) >= 3:
                    if pdist(coords[0], coords[-1]) > 0.01:
                        coords.append(coords[0])
                if len(coords) >= 2:
                    all_lines.append(coords)
                    straight_count += 1

    LOG.info(f"Extracted: {arc_count} arc polylines (arcs preserved), "
             f"{straight_count} straight polylines/lines")

    if not all_lines:
        raise ValueError(
            "No polyline geometry found in DXF.\n\n"
            "Check that the file contains POLYLINE entities.")

    return all_lines


def _extract_from_layers(input_layers):
    """Extract line geometry from QGIS vector layers."""
    all_lines = []
    for layer in input_layers:
        count = 0
        skipped_type = 0
        skipped_empty = 0

        for feat in layer.getFeatures():
            geom = feat.geometry()
            if geom is None or geom.isEmpty() or geom.isNull():
                skipped_empty += 1
                continue
            if geom.type() != QgsWkbTypes.LineGeometry:
                skipped_type += 1
                continue
            verts = []
            vi = geom.vertices()
            while vi.hasNext():
                v = vi.next()
                z = v.z()
                if math.isnan(z) or math.isinf(z):
                    z = 0.0
                verts.append((v.x(), v.y(), z))
            if len(verts) < 2:
                skipped_empty += 1
                continue
            if geom.isMultipart():
                multi = geom.asMultiPolyline()
                idx = 0
                for part in multi:
                    pc = verts[idx:idx+len(part)]
                    idx += len(part)
                    if len(pc) >= 2:
                        all_lines.append(pc)
                        count += 1
            else:
                all_lines.append(verts)
                count += 1

        LOG.info(f"{layer.name()}: {count} lines extracted")
        if skipped_type:
            LOG.detail(f"Skipped {skipped_type} non-line features "
                       f"(polygons/3DFACEs/points)")
        if skipped_empty:
            LOG.detail(f"Skipped {skipped_empty} empty/short features")

    if not all_lines:
        raise ValueError(
            "No line geometry found in any input layer.\n\n"
            "Check that your DXF/GeoPackage contains polyline features.\n"
            "3DFACE (triangle mesh) entities are not used - the tool needs "
            "the contour polylines.")

    return all_lines


def step2_extract(input_layers):
    """Extract geometry from DXF or layers, check Z, reproject."""
    LOG.start_step("Extracting line geometry")

    # Dispatch: DXF direct read or QGIS layer
    if CFG.get('dxf_path'):
        all_lines = _extract_from_dxf(CFG['dxf_path'])
    else:
        all_lines = _extract_from_layers(input_layers)

    LOG.info(f"Total lines extracted: {len(all_lines)}")

    # Check Z values
    has_z = any(abs(c[2]) > 0.1 for line in all_lines for c in line)
    if not has_z:
        raise ValueError(
            "All Z coordinates are 0. The input geometry has no elevation data.\n\n"
            "If using DXF: check the file contains 3D polylines.\n"
            "If using QGIS layer: ensure the DXF was imported with "
            "'Preserve Z values' enabled.")

    # Reproject to NZTM2000 if data CRS differs
    data_crs = CFG.get('data_crs')
    target_crs = QgsCoordinateReferenceSystem("EPSG:2193")

    if data_crs and data_crs.isValid() and data_crs != target_crs:
        LOG.info(f"Reprojecting from {data_crs.authid()} to EPSG:2193 (NZTM2000)...")
        xform = QgsCoordinateTransform(data_crs, target_crs,
                                       QgsProject.instance())
        reprojected = []
        for line in all_lines:
            new_line = []
            for x, y, z in line:
                pt = xform.transform(QgsPointXY(x, y))
                new_line.append((pt.x(), pt.y(), z))
            reprojected.append(new_line)
        all_lines = reprojected
        sample = all_lines[0][0] if all_lines and all_lines[0] else None
        if sample:
            LOG.detail(f"Sample reprojected: "
                       f"({sample[0]:.1f}, {sample[1]:.1f}, {sample[2]:.2f})")
        LOG.success(f"{len(all_lines)} lines reprojected to NZTM2000")
    else:
        if data_crs and data_crs.isValid():
            LOG.info(f"Data already in {data_crs.authid()}")
        else:
            LOG.warn("No data CRS detected. Assuming NZTM2000.")
        LOG.success(f"{len(all_lines)} lines with Z values")

    return all_lines


# =============================================================================
# STEP 3: CLASSIFY RINGS
# =============================================================================

def stitch(segments, tol):
    if not segments: return []
    def pk(pt):
        return (round(pt[0]/tol)*tol, round(pt[1]/tol)*tol,
                round(pt[2]/tol)*tol)
    em = defaultdict(list)
    for i, c in enumerate(segments):
        em[pk(c[0])].append((i, 'S'))
        em[pk(c[-1])].append((i, 'E'))
    used, chains = set(), []
    for si in range(len(segments)):
        if si in used: continue
        chain, ci, ce = [], si, 'S'
        while ci not in used:
            used.add(ci)
            c = segments[ci]
            if ce == 'S':
                chain.extend(c if not chain else c[1:])
                nk = pk(c[-1])
            else:
                r = list(reversed(c))
                chain.extend(r if not chain else r[1:])
                nk = pk(c[0])
            nxt = False
            for idx, end in em.get(nk, []):
                if idx not in used:
                    ci, ce, nxt = idx, end, True
                    break
            if not nxt: break
        if len(chain) >= 3:
            chains.append(chain)
    return chains


def step3_classify(all_lines):
    LOG.start_step("Classifying rings")

    ma = CFG['min_area']
    mv = CFG['min_verts']
    zt = CFG['z_thresh']

    # Dam centre from Z-bearing lines
    zxs = [c[0] for l in all_lines for c in l if abs(c[2]) > 1]
    zys = [c[1] for l in all_lines for c in l if abs(c[2]) > 1]
    if not zxs:
        raise ValueError(
            "No lines found with non-zero Z coordinates in the dam area.\n\n"
            "Check that the DXF polylines have elevation data.")

    dcx = sum(zxs)/len(zxs)
    dcy = sum(zys)/len(zys)
    dr = max(max(zxs)-min(zxs), max(zys)-min(zys))
    LOG.info(f"Dam centre: ({dcx:.0f}, {dcy:.0f}), extent ~{dr:.0f} m")

    closed, opens, shorts = [], [], []
    filtered_out = 0
    for coords in all_lines:
        cx = sum(c[0] for c in coords)/len(coords)
        cy = sum(c[1] for c in coords)/len(coords)
        if pdist((cx, cy), (dcx, dcy)) > dr * 2:
            filtered_out += 1
            continue
        if is_closed(coords):
            if shoelace(coords) > ma and len(coords) >= mv:
                closed.append(coords)
        elif len(coords) <= 5:
            shorts.append(coords)
        else:
            opens.append(coords)

    if filtered_out:
        LOG.info(f"Filtered {filtered_out} distant features (annotations etc)")
    LOG.info(f"Closed rings: {len(closed)}")
    LOG.info(f"Short segments (<= 5 pts): {len(shorts)}")
    LOG.info(f"Open lines: {len(opens)}")

    # Stitch short segments
    if shorts:
        stitched = stitch(shorts, CFG['stitch_tol'])
        added = 0
        for ch in stitched:
            if is_closed(ch) and shoelace(ch) > ma and len(ch) >= mv:
                closed.append(ch)
                added += 1
            elif len(ch) >= 3:
                opens.append(ch)
        if added:
            LOG.info(f"Stitched segments into {added} additional closed ring(s)")

    # Stitch open lines
    new_open = []   # always defined: read below even when there are no opens
    if opens:
        so = stitch(opens, tol=1.0)
        added = 0
        for ch in so:
            if is_closed(ch, 2.0) and shoelace(ch) > ma:
                closed.append(ch)
                added += 1
            else:
                new_open.append(ch)
        if added:
            LOG.info(f"Stitched open lines into {added} additional closed ring(s)")

    # Split by Z variability
    const_z, var_z = [], []
    for c in closed:
        zn, zx, zm, zs = zstats(c)
        info = {'coords': c, 'area': shoelace(c),
                'z_min': zn, 'z_max': zx, 'z_mean': zm, 'z_std': zs,
                'npts': len(c)}
        (const_z if zs < zt else var_z).append(info)

    LOG.info(f"Constant-Z rings: {len(const_z)}")
    LOG.info(f"Variable-Z rings: {len(var_z)}")

    # Drop rings whose Z is clearly outside the dam (z=0 frames/blocks,
    # annotation rectangles, property boundaries drawn flat at zero). The
    # dam centre is computed from Z-bearing lines (|z| > 1), so we already
    # know the dam sits at a known elevation band. Any closed ring whose
    # z_mean is >> below the lowest Z-bearing line, or unrealistically
    # near zero when the dam is at +200 m NZVD2016, is junk.
    if const_z:
        dam_z_lo = min(c[2] for l in all_lines for c in l if abs(c[2]) > 1)
        dam_z_hi = max(c[2] for l in all_lines for c in l if abs(c[2]) > 1)
        # Allow a generous skirt below the lowest dam Z (some toe rings
        # may sit below) and above the highest (e.g. crest fence). 50 m
        # below / 20 m above the known dam band is plenty - anything
        # further is definitely junk.
        z_floor = dam_z_lo - 50.0
        z_ceil = dam_z_hi + 20.0
        before = len(const_z)
        const_z = [r for r in const_z
                   if z_floor <= r['z_mean'] <= z_ceil]
        dropped = before - len(const_z)
        if dropped:
            LOG.info(f"Dropped {dropped} const-Z ring(s) outside dam Z "
                     f"band [{z_floor:.1f}, {z_ceil:.1f}] m (likely DXF "
                     f"frames or annotation blocks at z=0)")

    if len(const_z) < 3:
        raise ValueError(
            f"Only {len(const_z)} constant-elevation rings found "
            f"(need at least 3).\n\n"
            f"This could mean:\n"
            f"  - The DXF polylines don't have Z values\n"
            f"  - The Z threshold ({zt} m) is too tight\n"
            f"  - The min area filter ({ma} m2) is excluding valid rings\n"
            f"  - The geometry isn't closed polylines\n\n"
            f"Try adjusting the Advanced thresholds.")

    LOG.success(f"{len(const_z)} constant-Z + {len(var_z)} variable-Z rings")

    # Partial open contours - these are open polylines at non-zero Z
    # within the dam vicinity. They typically represent batter contours
    # that terminate where the dam meets ground (i.e. the contour goes
    # to ground level on the outer batter and the polyline ends at the
    # ground intersection). Their endpoints encode the variable-Z outer
    # toe of the dam in plan: the closed outer toe ring gives the XY
    # trace, the partial contour endpoints give the local ground
    # elevation at each touch point on that trace.
    partial_contours = []
    if new_open:
        # Z bounds for "in the dam" range (dam_z_lo and dam_z_hi were
        # computed above from |z|>1 lines).
        try:
            z_lo = dam_z_lo - 5.0  # allow some slop below
            z_hi = dam_z_hi + 5.0
        except Exception:
            z_lo, z_hi = -float('inf'), float('inf')
        for ch in new_open:
            zn, zx, zm, zs = zstats(ch)
            if zs >= zt:
                continue  # only const-Z open polylines as partial contours
            if zm == 0.0 or zm < z_lo or zm > z_hi:
                continue
            cx_ = sum(c[0] for c in ch) / len(ch)
            cy_ = sum(c[1] for c in ch) / len(ch)
            if pdist((cx_, cy_), (dcx, dcy)) > dr * 1.5:
                continue
            partial_contours.append({
                'coords': ch,
                'z': zm,
                'npts': len(ch),
                'start_xy': (ch[0][0], ch[0][1]),
                'end_xy':   (ch[-1][0], ch[-1][1]),
            })
        if partial_contours:
            zs_pc = [p['z'] for p in partial_contours]
            LOG.info(f"Partial contour open polylines: {len(partial_contours)} "
                     f"(Z range {min(zs_pc):.2f} - {max(zs_pc):.2f} m). "
                     f"Endpoints will be used to compute variable-Z outer toe.")
    return {'const_z': const_z, 'var_z': var_z,
            'partial_contours': partial_contours}


# =============================================================================
# STEP 4: IDENTIFY KEY LINES
# =============================================================================

def step4_identify(classified):
    LOG.start_step("Identifying key dam lines")

    cr = sorted(classified['const_z'], key=lambda r: r['area'])
    vr = classified['var_z']

    # Deduplicate. The original criterion was area-only with tol = 50 m2
    # or 0.1% of area, which is too permissive: it merged a 35-vertex
    # FOOTPRINT polygon with a 946-vertex DTM contour at the same z just
    # because their areas happened to land within 50 m2 of each other.
    # The merged pick was then wrong (the small-vertex FOOTPRINT got
    # promoted as outer_crest). A real duplicate is the SAME ring drawn
    # twice: it has the same area, the same Z to within tolerance, AND a
    # similar vertex count. Require all three.
    dd = [cr[0]]
    dupes = 0
    for r in cr[1:]:
        prev = dd[-1]
        area_tol = max(50.0, prev['area'] * 0.001)
        npts_max = max(r['npts'], prev['npts'])
        # Vertex counts of a true duplicate should differ by less than
        # half. A 35-vs-946 split (97%) is clearly two different rings.
        npts_close = (abs(r['npts'] - prev['npts'])
                      < 0.5 * max(npts_max, 1))
        z_close = abs(r['z_mean'] - prev['z_mean']) < 0.05
        if (abs(r['area'] - prev['area']) > area_tol
                or not npts_close
                or not z_close):
            dd.append(r)
        else:
            dupes += 1
    if dupes:
        LOG.info(f"Removed {dupes} duplicate ring(s)")
    cr = dd

    # Filter out potential sump rings - small rings inside the dam that
    # aren't part of the embankment proper (e.g. an interior collection sump
    # with its own contours). A ring qualifies as a sump if its area is
    # less than 25% of the next-smallest ring AND its centroid sits inside
    # the next ring's bbox. Multi-contour sumps get peeled off iteratively.
    cr, sumps = _filter_sumps_from_const_z(cr)
    if sumps:
        LOG.info(f"Filtered {len(sumps)} potential sump ring(s) "
                 f"(small interior rings, treated as not part of dam):")
        for s in sumps:
            LOG.detail(f"  Z={s['z_mean']:.2f}, area={s['area']:.0f} m\u00b2, "
                       f"layer={s.get('layer', '?')}")

    if len(cr) < 3:
        raise ValueError(
            f"After deduplication, only {len(cr)} rings remain.\n"
            f"Need at least 3 (inner toe + inner crest + outer crest).")

    # -------------------------------------------------------------------
    # Identify crest by MAX ELEVATION
    # Both inner and outer crest are at the highest Z in the ring set.
    # Inner crest = smallest area at max Z
    # Outer crest = largest area at max Z
    # This is more robust than "biggest area gap" which fails when
    # the outermost batter ring creates a bigger gap than the crest.
    # -------------------------------------------------------------------
    max_z = max(r['z_mean'] for r in cr)
    crest_rings = [r for r in cr if abs(r['z_mean'] - max_z) < 0.1]

    if len(crest_rings) < 2:
        # Fallback: try biggest gap approach
        LOG.warn(f"Only {len(crest_rings)} ring(s) at max Z ({max_z:.2f}). "
                 f"Falling back to biggest area gap method.")
        gaps = [(cr[i]['area']-cr[i-1]['area'], i) for i in range(1, len(cr))]
        gaps.sort(reverse=True)
        mg, gi = gaps[0]
        ic = cr[gi - 1]
        oc = cr[gi]
    else:
        crest_rings.sort(key=lambda r: r['area'])
        ic = crest_rings[0]   # smallest area at max Z = inner crest
        oc = crest_rings[-1]  # largest area at max Z = outer crest
        LOG.info(f"Crest identified at max Z = {max_z:.2f} m "
                 f"({len(crest_rings)} rings at this elevation)")

    it = cr[0]  # innermost ring = inner toe

    # Find indices in sorted list for batter split
    ic_idx = cr.index(ic)
    oc_idx = cr.index(oc)

    # Sanity check: inner crest Z should be > inner toe Z
    if ic['z_mean'] < it['z_mean']:
        LOG.warn(f"Inner crest Z ({ic['z_mean']:.2f}) < inner toe Z "
                 f"({it['z_mean']:.2f}). Check data integrity.")

    # When a sump was filtered out, the basin-floor ring is usually drawn flat /
    # chopped where it skirts the sump, which warps the inner batter there and
    # leaves the sump OUTSIDE the basin (so it would model as a hole in the
    # batter, not a pocket). Fix it by extending the inner toe just enough to
    # swallow the sump: take the convex hull of (basin floor + sump). That keeps
    # the basin floor's actual shape and rounding everywhere else (it coincides
    # with the DXF ring except over the sump bulge) and brings the sump inside.
    # Only do this when the basin floor is essentially convex, so an
    # intentionally concave basin isn't wiped out. Mutated IN PLACE so the plan
    # view, the role map and the DEM all use it.
    if sumps and it.get('coords') and len(it['coords']) >= 3:
        try:
            basin_g = QgsGeometry.fromPolygonXY(
                [[QgsPointXY(c[0], c[1]) for c in it['coords']]])
            basin_hull = basin_g.convexHull()
            ba = basin_g.area()
            if (ba > 0 and basin_hull and not basin_hull.isEmpty()
                    and ba / max(basin_hull.area(), 1e-9) > 0.95):
                combined = QgsGeometry(basin_g)
                for s in sumps:
                    sc = s.get('coords')
                    if sc and len(sc) >= 3:
                        sg = QgsGeometry.fromPolygonXY(
                            [[QgsPointXY(c[0], c[1]) for c in sc]])
                        u = combined.combine(sg)
                        if u and not u.isEmpty():
                            combined = u
                hull = combined.convexHull()
                poly = hull.asPolygon() if hull and not hull.isEmpty() else None
                if poly and poly[0] and len(poly[0]) >= 4:
                    ring = poly[0]
                    if ring[0] == ring[-1]:
                        ring = ring[:-1]
                    z = it['z_mean']
                    it['coords'] = [(p.x(), p.y(), z) for p in ring]
                    it['npts'] = len(it['coords'])
                    it['area'] = abs(shoelace([(p.x(), p.y()) for p in ring]))
                    LOG.info(f"Sump present: extended the inner toe to enclose "
                             f"the sump (convex bridge); coincides with the DXF "
                             f"basin floor elsewhere. area {it['area']:.0f} m2.")
            else:
                LOG.info("Sump present but basin floor is non-convex; leaving "
                         "the inner toe as drawn (no sump bridge).")
        except Exception as e:
            LOG.warn(f"Could not extend inner toe over the sump ({e}); keeping "
                     f"the DXF basin-floor ring.")

    # Print full ring table
    LOG.info(f"")
    LOG.info(f"{'Z (m)':>8} {'Area (m2)':>10} {'Pts':>5}  Role")
    LOG.info(f"{'-'*50}")
    for i, r in enumerate(cr):
        role = ""
        if r is it: role = "<-- INNER TOE (invert)"
        elif r is ic: role = "<-- INNER CREST"
        elif r is oc:
            crest_gap = oc['area'] - ic['area']
            role = f"<-- OUTER CREST (gap={crest_gap:.0f} m2)"
        LOG.info(f"{r['z_mean']:>8.2f} {r['area']:>10.0f} {r['npts']:>5}  {role}")

    # Sanity: crest gap should be clearly larger than typical batter gaps
    batter_gaps = []
    for i in range(1, len(cr)):
        if cr[i] is not ic and cr[i] is not oc:
            batter_gaps.append(cr[i]['area'] - cr[i-1]['area'])
    if batter_gaps:
        avg_batter_gap = sum(batter_gaps) / len(batter_gaps)
        crest_gap = oc['area'] - ic['area']
        ratio = crest_gap / avg_batter_gap if avg_batter_gap > 0 else float('inf')
        if ratio < 3:
            LOG.warn(f"Crest gap ({crest_gap:.0f} m2) is only {ratio:.1f}x "
                     f"average batter gap ({avg_batter_gap:.0f} m2). "
                     f"Crest identification may be uncertain.")

    # Outer toe
    ot = None
    if vr:
        vr.sort(key=lambda r: r['area'], reverse=True)
        ot = vr[0]
        LOG.info(f"")
        LOG.info(f"Outer toe: Z=[{ot['z_min']:.2f}, {ot['z_max']:.2f}], "
                 f"area={ot['area']:.0f} m2, {ot['npts']} pts")
    else:
        LOG.warn("No variable-Z ring found for outer toe. "
                 "Using outermost constant-Z ring as fallback.")
        ot = cr[-1]

    # Auto elevations
    if CFG['auto_elev']:
        CFG['invert'] = round(it['z_mean'], 2)
        CFG['crest'] = round(ic['z_mean'], 2)
        CFG['toe_low'] = round(ot['z_min'], 2)
        LOG.info(f"")
        LOG.info(f"Auto-detected elevations:")
        LOG.detail(f"Invert:    {CFG['invert']:.2f} m NZVD2016")
        LOG.detail(f"Crest:     {CFG['crest']:.2f} m NZVD2016")
        LOG.detail(f"Toe (low): {CFG['toe_low']:.2f} m NZVD2016")
    else:
        LOG.info(f"Using manual elevations:")
        LOG.detail(f"Invert:    {CFG['invert']:.2f} m")
        LOG.detail(f"Crest:     {CFG['crest']:.2f} m")
        LOG.detail(f"Toe (low): {CFG['toe_low']:.2f} m")

    height = CFG['crest'] - CFG['toe_low']
    LOG.info(f"Max embankment height: {height:.2f} m")

    if height <= 0:
        raise ValueError(
            f"Embankment height is {height:.2f} m (crest must be above toe).\n"
            f"Check elevation values or auto-detection results.")
    if height > 30:
        LOG.warn(f"Embankment height {height:.1f} m seems very large. "
                 f"Check elevations.")

    LOG.success("Key lines identified")
    # Build outer_batter list. The last ring in cr[oc_idx:] is, by
    # construction, the same object as `ot` (the outer toe). Downstream,
    # step4c_var_z_outer_toe and cut_outer_toe_to_terrain mutate
    # kl['outer_toe'] in place to promote it to variable-Z. If
    # outer_batter[-1] aliases the same object, that mutation also
    # silently corrupts outer_batter[-1] - which the constant-slope
    # batter post-processor (_apply_constant_slope_batter) reads as the
    # const-Z toe reference for its design-slope estimate. Variable-Z
    # data in that reference produces visible artifacts (ripples) on
    # the outer batter surface of the rendered DEM.
    # Fix: store a SHALLOW COPY of ot as outer_batter[-1] so it stays
    # const-Z regardless of what step4c or cut do to kl['outer_toe'].
    outer_batter_list = list(cr[oc_idx:])
    if outer_batter_list and outer_batter_list[-1] is ot:
        # Shallow copy: ot's fields are scalars + a coords list. The
        # coords list itself doesn't get mutated by step4c (it replaces
        # the 'coords' field with a new list); only the dict keys get
        # reassigned. A shallow copy of the dict is enough isolation.
        outer_batter_list[-1] = dict(ot)
    return {
        'inner_toe': it, 'inner_crest': ic,
        'outer_crest': oc, 'outer_toe': ot,
        'inner_batter': cr[:oc_idx], 'outer_batter': outer_batter_list,
        # Interior sump rings filtered out of the dam-ring set above (so they
        # are never mistaken for the inner toe). Carried so step5 can model
        # them as basin pockets when 'include sump' is on.
        'sumps': sumps,
        # Pass partial contours through so step4c can use them
        'partial_contours': classified.get('partial_contours', []),
    }


# =============================================================================
# STEP 4c: BUILD VARIABLE-Z OUTER TOE FROM PARTIAL CONTOUR ENDPOINTS
# =============================================================================

def step4c_var_z_outer_toe(kl):
    """Promote the outer_toe ring from constant-Z to variable-Z using
    the endpoints of partial open contours from the DXF.

    Background: in a drone-survey DXF of a dam cut into a slope, the
    DXF contains many partial open contour polylines at intermediate
    elevations. These contours terminate where the contour line meets
    natural ground (the contour goes to ground on the outer batter, and
    the polyline ends at that ground intersection). Empirically the
    endpoints of these partial contours sit EXACTLY on the outer toe
    ring (verified to 0.000 m on the Neil Kingston DXF). So at each
    touch point on the outer toe ring's XY trace, the partial contour
    Z is the true ground elevation there.

    Algorithm:
        For each partial contour endpoint:
            Project onto the closest segment of the outer toe ring
            Record (chainage_along_ring, contour_z) as a Z sample
        For each vertex of the outer toe ring:
            If a Z sample sits very close to that vertex, use it
            Otherwise interpolate Z linearly from the nearest sampled
            chainages on either side around the ring perimeter
        Update outer_toe['coords'] with (x, y, new_z) per vertex
        Recompute z_mean, z_min, z_max, z_std

    Falls through unchanged if no partial contours were detected (e.g.
    sparse DXF, polygon mode), keeping const-Z behaviour intact.
    """
    partials = kl.get('partial_contours') or []
    if not partials:
        LOG.detail("No partial contours; outer toe stays const-Z.")
        return kl

    ot = kl.get('outer_toe')
    if ot is None or not ot.get('coords'):
        return kl

    ot_coords = ot['coords']
    n_ot = len(ot_coords)
    if n_ot < 4:
        return kl

    # Filter partial contours to plausible dam Z range. The outer toe
    # is the bottom of the outer batter; the outer crest is the top.
    # Variable ground at the outer toe can sensibly range from below
    # the design outer toe (where ground is lower than the design
    # assumed) up to nearly the outer crest (where ground rises high
    # enough that the batter barely exists).
    crest_z = kl['outer_crest']['z_mean']
    nominal_toe_z = ot['z_mean']
    # Use a generous band: from 2 m below nominal toe up to crest
    z_min_allow = nominal_toe_z - 5.0
    z_max_allow = crest_z + 0.1
    usable = [p for p in partials
              if z_min_allow <= p['z'] <= z_max_allow]
    if not usable:
        LOG.detail(f"No partial contours in plausible Z range "
                   f"[{z_min_allow:.2f}, {z_max_allow:.2f}]; "
                   f"outer toe stays const-Z.")
        return kl

    LOG.start_step("Building variable-Z outer toe from partial contours")
    LOG.info(f"Using {len(usable)} partial contour(s) in Z range "
             f"[{min(p['z'] for p in usable):.2f}, "
             f"{max(p['z'] for p in usable):.2f}] m")

    # Precompute cumulative chainage along the outer toe ring
    ring_xy = [(c[0], c[1]) for c in ot_coords]
    seg_lens = []
    cum = [0.0]
    for k in range(n_ot - 1):
        ax, ay = ring_xy[k]
        bx, by = ring_xy[k + 1]
        d = math.hypot(bx - ax, by - ay)
        seg_lens.append(d)
        cum.append(cum[-1] + d)
    perim = cum[-1] if cum[-1] > 0 else 1.0
    # For a closed ring, the last vertex equals the first; cum[-1] is
    # the perimeter. Treat chainages modulo perim.

    # Project each partial contour endpoint onto the outer toe ring
    # to get its chainage. Then accumulate (chainage, z) samples.
    samples = []  # list of (chainage, z)
    for p in usable:
        for endpoint in (p['start_xy'], p['end_xy']):
            ex, ey = endpoint
            best_d2 = float('inf')
            best_seg = 0
            best_t = 0.0
            for k in range(n_ot - 1):
                ax, ay = ring_xy[k]
                bx, by = ring_xy[k + 1]
                dx, dy = bx - ax, by - ay
                l2 = dx * dx + dy * dy
                if l2 < 1e-12:
                    continue
                t = ((ex - ax) * dx + (ey - ay) * dy) / l2
                t = max(0.0, min(1.0, t))
                px = ax + t * dx
                py = ay + t * dy
                d2 = (ex - px) ** 2 + (ey - py) ** 2
                if d2 < best_d2:
                    best_d2 = d2
                    best_seg = k
                    best_t = t
            if best_d2 > 4.0:  # >2m off the ring - probably not a touch
                continue
            ch_proj = cum[best_seg] + best_t * seg_lens[best_seg]
            samples.append((ch_proj, p['z']))

    if not samples:
        LOG.warn("No partial contour endpoints projected onto the outer "
                 "toe ring; keeping const-Z outer toe.")
        return kl

    # Some endpoints will fall on the same chainage (multiple contours
    # converging at one point on the ring). Bucket by chainage and take
    # the mean Z per bucket. Buckets are 0.5 m wide (well below the
    # 1 m default vertex spacing of the ring).
    samples.sort(key=lambda s: s[0])
    buckets = []  # list of (chainage_mean, z_mean)
    bucket_w = 0.5
    cur_ch = samples[0][0]
    cur_zs = [samples[0][1]]
    for ch, z in samples[1:]:
        if ch - cur_ch <= bucket_w:
            cur_zs.append(z)
        else:
            buckets.append((cur_ch, sum(cur_zs) / len(cur_zs)))
            cur_ch = ch
            cur_zs = [z]
    buckets.append((cur_ch, sum(cur_zs) / len(cur_zs)))

    LOG.info(f"Collapsed {len(samples)} endpoint samples into "
             f"{len(buckets)} distinct touch points on the outer toe ring "
             f"(Z range {min(b[1] for b in buckets):.2f} - "
             f"{max(b[1] for b in buckets):.2f} m).")

    # Now interpolate Z at every vertex on the outer toe ring using the
    # sampled buckets, treating the chainage axis as circular (mod perim).
    # For each vertex chainage, find the surrounding two samples and
    # linearly interpolate.
    sample_chs = [b[0] for b in buckets]
    sample_zs = [b[1] for b in buckets]
    nb = len(buckets)

    def interp_at(ch):
        # Find the two surrounding samples on the circle
        # ch is in [0, perim)
        ch = ch % perim
        # Binary search would be faster but n_ot is small enough
        for k in range(nb):
            ch_k = sample_chs[k]
            ch_next = sample_chs[(k + 1) % nb]
            if ch_next < ch_k:  # wrap-around segment
                # Segment from ch_k to ch_next + perim
                if ch >= ch_k or ch < ch_next:
                    ch_a = ch_k
                    ch_b = ch_next + perim
                    ch_target = ch if ch >= ch_k else ch + perim
                    z_a = sample_zs[k]
                    z_b = sample_zs[(k + 1) % nb]
                    span = ch_b - ch_a
                    if span < 1e-9:
                        return z_a
                    return z_a + (z_b - z_a) * (ch_target - ch_a) / span
            else:
                if ch_k <= ch <= ch_next:
                    ch_a, ch_b = ch_k, ch_next
                    z_a = sample_zs[k]
                    z_b = sample_zs[(k + 1) % nb]
                    span = ch_b - ch_a
                    if span < 1e-9:
                        return z_a
                    return z_a + (z_b - z_a) * (ch - ch_a) / span
        # Should not reach here unless single sample
        return sample_zs[0]

    new_coords = []
    for k, (x, y) in enumerate(ring_xy):
        z_new = interp_at(cum[k])
        new_coords.append((x, y, z_new))

    # Update the outer toe in place
    zs_new = [c[2] for c in new_coords]
    z_min_new, z_max_new = min(zs_new), max(zs_new)
    z_mean_new = sum(zs_new) / len(zs_new)
    z_std_new = (sum((z - z_mean_new) ** 2 for z in zs_new)
                 / len(zs_new)) ** 0.5
    # Stash the original const-Z reference so the rings CSV (the
    # "perfect geometry" file) can still use the flat design value.
    # The rings CSV is the source of truth for design slopes / crest
    # width / idealised volume - the dam-on-terrain (variable Z) lives
    # in the points CSV.
    # Update the outer toe IN PLACE. kl['outer_toe'] keeps its identity
    # in all_rings and in any role_assignments index map, so the dialog
    # role-assignment lookup keeps working. The aliasing risk with
    # outer_batter[-1] is handled at the source: step4_identify now
    # stores a shallow copy of the outer toe ring as outer_batter[-1],
    # so mutating kl['outer_toe'] here can't corrupt that reference.
    if 'nominal_const_z' not in ot:
        ot['nominal_const_z'] = ot.get('z_mean')
        ot['nominal_const_coords'] = [(c[0], c[1], c[2]) for c in ot_coords
                                        if len(c) >= 3]
    ot['coords'] = new_coords
    ot['z_min'] = z_min_new
    ot['z_max'] = z_max_new
    ot['z_mean'] = z_mean_new
    ot['z_std'] = z_std_new
    ot['npts'] = len(new_coords)
    ot['is_variable_z'] = True
    LOG.success(f"Outer toe is now variable-Z: "
                f"{z_min_new:.2f} - {z_max_new:.2f} m "
                f"(mean {z_mean_new:.2f}, std {z_std_new:.3f}).")
    return kl


# =============================================================================
# STEP 4d: BUILD ARTIFICIAL DEEP OUTER TOE (parallel offset, deep Z)
# =============================================================================

def step4d_build_artificial_deep_outer_toe(kl, terrain_layer=None):
    """Build the artificially-deep, geometrically-perfect outer toe ring
    that feeds the TIN and the constant-slope post-processor.

    This is the SOURCE OF TRUTH for the dam's design geometry. The XY
    trace is a parallel offset of outer_crest outward at the design
    slope; the Z is well below any natural ground in the dam area
    (terrain_min - 5 m, or crest_z - 20 m fallback). Used by:
        - step5_points (TIN input)
        - _apply_constant_slope_batter (slope reference + clamp)
    Both reference the same ring, so they agree everywhere - no kink at
    the outer toe boundary.

    The active variable-Z outer toe (Method 1 or Method 2) at
    kl['outer_toe']['coords'] is UNCHANGED by this step. That polygon
    is used downstream ONLY as the mask polygon for _build_dem's final
    clip step - it trims the perfect DEM to actual dam-meets-ground.

    Stores on kl['outer_toe']:
        - artificial_const_coords: parallel-offset XY ring at Z=toe_low
        - artificial_const_z: the deep Z value
    Also replaces kl['outer_batter'][-1] with a new const-Z entry whose
    coords are the artificial deep ring, so the post-processor reads
    matching geometry.
    """
    oc = kl.get('outer_crest')
    if not oc or not oc.get('coords'):
        LOG.warn("step4d: no outer_crest available - skipping")
        return kl

    ic = kl.get('inner_crest')
    crest_z = float(CFG.get('crest', oc.get('z_mean', 0)))
    outer_hv = float(CFG.get('outer_hv', 3.5))
    if outer_hv <= 0:
        LOG.warn(f"step4d: invalid outer_hv {outer_hv}; using 3.5")
        outer_hv = 3.5

    # Determine artificial deep Z. Goal: well below any natural ground
    # so the constant-slope batter extends past terrain everywhere
    # before being clipped by the active variable-Z mask polygon.
    terrain_min = None
    if terrain_layer is not None:
        try:
            terrain_min = _terrain_min_in_bbox(terrain_layer, oc['coords'])
        except Exception:
            terrain_min = None
    if terrain_min is not None:
        toe_low_target = float(terrain_min) - 5.0
        LOG.info(f"step4d: terrain_min in dam bbox = {terrain_min:.2f} m; "
                 f"setting artificial deep toe at {toe_low_target:.2f} m")
    else:
        toe_low_target = crest_z - 20.0
        LOG.warn(f"step4d: no terrain available; falling back to "
                 f"crest_z - 20 = {toe_low_target:.2f} m")

    CFG['toe_low'] = round(toe_low_target, 2)

    # Horizontal offset distance at design slope
    height = crest_z - CFG['toe_low']
    D = height * outer_hv
    LOG.info(f"step4d: artificial deep outer toe Z={CFG['toe_low']:.2f}, "
             f"horizontal offset from outer_crest = {D:.2f} m "
             f"(crest {crest_z:.2f} - toe {CFG['toe_low']:.2f}) * outer_hv {outer_hv:.2f}")

    # Reference geometry for "outward" direction. Use inner_crest if
    # available (it sits inside the dam, so outer_crest is offset
    # outward AWAY from it). Fall back to outer_crest's own centroid.
    ref_geom = None
    if ic and ic.get('coords') and len(ic['coords']) >= 3:
        try:
            ref_geom = QgsGeometry.fromPolylineXY(
                [QgsPointXY(c[0], c[1]) for c in ic['coords']])
        except Exception:
            ref_geom = None
    if ref_geom is None:
        ccx = sum(c[0] for c in oc['coords']) / len(oc['coords'])
        ccy = sum(c[1] for c in oc['coords']) / len(oc['coords'])
        try:
            ref_geom = QgsGeometry.fromPointXY(QgsPointXY(ccx, ccy))
        except Exception:
            LOG.warn("step4d: could not build ref geom for outward direction")
            return kl

    # Build parallel offset of outer_crest outward by D
    sp = float(CFG.get('point_spacing', 0.1))
    artificial_xy = _offset_ring_xy(oc['coords'], ref_geom, D, sp)
    if not artificial_xy or len(artificial_xy) < 4:
        LOG.warn("step4d: parallel offset failed - falling back to "
                 "DXF outer toe trace at deep Z")
        artificial_xy = [(c[0], c[1])
                         for c in (kl['outer_toe'].get('coords') or [])]
        if not artificial_xy:
            LOG.error("step4d: no fallback coords; aborting")
            return kl

    # Store the artificial deep coords on the outer_toe (separate from
    # the variable-Z 'coords' field which remains the mask polygon).
    artificial_coords_xyz = [(x, y, CFG['toe_low']) for x, y in artificial_xy]
    kl['outer_toe']['artificial_const_coords'] = artificial_coords_xyz
    kl['outer_toe']['artificial_const_z'] = CFG['toe_low']

    # Replace outer_batter[-1] with a const-Z entry whose coords match
    # the artificial deep ring. step4b's slope detection runs BEFORE
    # this step (so the intermediate const-Z contours still drive HV
    # detection); we only replace the last entry that the post-processor
    # uses as the toe reference. The entry must carry all fields any
    # downstream consumer might expect - area, perim, centroid, etc -
    # so missing-key errors don't surface at step5/step6/step7.
    try:
        ring_area = abs(shoelace(
            [(c[0], c[1]) for c in artificial_coords_xyz]))
    except Exception:
        ring_area = 0.0
    try:
        ring_perim = llen([(c[0], c[1]) for c in artificial_coords_xyz])
    except Exception:
        ring_perim = 0.0
    cx = sum(c[0] for c in artificial_coords_xyz) / max(1, len(artificial_coords_xyz))
    cy = sum(c[1] for c in artificial_coords_xyz) / max(1, len(artificial_coords_xyz))
    new_obr_last = {
        'coords': artificial_coords_xyz,
        'z_mean': CFG['toe_low'],
        'z_min': CFG['toe_low'],
        'z_max': CFG['toe_low'],
        'z_std': 0.0,
        'npts': len(artificial_coords_xyz),
        'area': ring_area,
        'perim': ring_perim,
        'centroid': (cx, cy),
        'is_variable_z': False,
        'name': 'artificial_deep_outer_toe',
    }
    obr = kl.get('outer_batter', [])
    if obr:
        kl['outer_batter'] = list(obr[:-1]) + [new_obr_last]
    else:
        kl['outer_batter'] = [new_obr_last]

    LOG.success(f"step4d: artificial deep outer toe built - "
                f"{len(artificial_xy)} vertices, Z={CFG['toe_low']:.2f}, "
                f"offset {D:.2f} m outward from outer_crest")
    return kl


# =============================================================================
# STEP 4b: DETECT DESIGN BATTER SLOPES FROM CONSTANT-Z CONTOUR RINGS
# =============================================================================
# Strategy: a well-formed design DXF contains constant-Z contour rings on the
# batter at clean elevation increments. Consecutive pairs of such contours are
# true parallel offsets at known Z step, so H:V = (perpendicular distance) /
# (Z step) is recoverable directly from geometry. Median across all pairs is
# robust against corner-tightening and topology changes (e.g. spillway notch).

def _hv_for_ring_pair(lower, upper, n_samples=30):
    """Measure H:V for one (lower, upper) const-Z ring pair.
    Returns the IQR-clean median HV, or None if invalid."""
    v_step = upper['z_mean'] - lower['z_mean']
    if v_step < 0.05:
        return None
    upr_coords = upper['coords']
    lo_geom = QgsGeometry.fromPolylineXY(
        [QgsPointXY(c[0], c[1]) for c in lower['coords']])
    ll = llen(upr_coords)
    if ll < 1.0:
        return None
    hs = []
    for j in range(n_samples):
        ch = ll * (j + 0.5) / n_samples
        pt = interp_ch(upr_coords, ch)
        near = _nearest_on_geom(lo_geom, pt[0], pt[1])
        h = math.sqrt((pt[0]-near.x())**2 + (pt[1]-near.y())**2)
        hs.append(h)
    hs.sort()
    n = len(hs)
    # If horizontal distance is ~0 across the board (coincident XY rings, e.g.
    # a footprint duplicate offset only in Z), skip - this isn't a real pair
    if hs[n//2] < 0.05:
        return None
    # IQR-clean median - tightens at corners is normal, but extreme outliers
    # from topology mismatch (e.g. spillway notch) should be excluded
    q1 = hs[n//4]; q3 = hs[3*n//4]
    iqr = q3 - q1
    clean = [h for h in hs if (q1 - 1.5*iqr) <= h <= (q3 + 1.5*iqr)]
    if not clean:
        clean = hs
    nc = len(clean)
    med_h = clean[nc//2] if nc % 2 else (clean[nc//2-1] + clean[nc//2]) / 2
    return med_h / v_step


def _detect_design_hv(batter_rings, label):
    """Detect design batter H:V from a list of constant-Z rings.

    For every consecutive pair (sorted by Z), measure HV via
    _hv_for_ring_pair. Return the median HV across all valid pairs.

    Returns None if no usable pairs (need at least one with substantial
    Z step and non-coincident XY)."""
    rings = [r for r in (batter_rings or []) if r.get('z_std', 0) < 0.05]
    if len(rings) < 2:
        LOG.detail(f"  {label}: only {len(rings)} const-Z ring(s), "
                   f"need >=2 to derive slope")
        return None

    rings = sorted(rings, key=lambda r: r['z_mean'])
    pair_hvs = []
    for lo, up in zip(rings, rings[1:]):
        hv = _hv_for_ring_pair(lo, up)
        if hv is not None and 0.5 <= hv <= 20.0:
            pair_hvs.append(hv)
            LOG.detail(f"  {label}: Z {lo['z_mean']:.2f}->{up['z_mean']:.2f} "
                       f"(step {up['z_mean']-lo['z_mean']:.2f}m): "
                       f"HV = {hv:.3f}:1")
    if not pair_hvs:
        return None
    pair_hvs.sort()
    n = len(pair_hvs)
    med = pair_hvs[n//2] if n % 2 else (pair_hvs[n//2-1] + pair_hvs[n//2]) / 2
    return med


def step4b_detect_slopes(kl):
    """Populate CFG['outer_hv'] and CFG['inner_hv'] by analysing the
    constant-Z contour rings collected during ring classification.

    For each batter side, every pair of consecutive const-Z rings gives a
    measurement; the median across pairs is taken as the design slope.

    Falls back to 3.0:1 with a warning if detection fails (insufficient
    contour data for that batter)."""
    LOG.start_step("Detecting design batter slopes from contours")

    # Inner batter: inner_toe is the design floor, plus any inner-side
    # constant-Z contours from step4. Add inner_crest so the toe-to-crest
    # pair is always considered.
    inner_rings = list(kl.get('inner_batter', []))
    if kl.get('inner_toe'):
        inner_rings.append(kl['inner_toe'])
    if kl.get('inner_crest'):
        inner_rings.append(kl['inner_crest'])

    # Outer batter: outer toe + intermediate contours + outer crest
    outer_rings = list(kl.get('outer_batter', []))
    if kl.get('outer_toe'):
        outer_rings.append(kl['outer_toe'])
    if kl.get('outer_crest'):
        outer_rings.append(kl['outer_crest'])

    outer_hv = _detect_design_hv(outer_rings, "outer")
    inner_hv = _detect_design_hv(inner_rings, "inner")

    DEFAULT_HV = 3.5
    if outer_hv is None and inner_hv is not None:
        outer_hv = inner_hv
        LOG.warn(f"Outer slope detection failed; using inner H:V "
                 f"({outer_hv:.2f}:1) as a fallback (symmetric assumption)")
    if inner_hv is None and outer_hv is not None:
        inner_hv = outer_hv
        LOG.warn(f"Inner slope detection failed; using outer H:V "
                 f"({inner_hv:.2f}:1) as a fallback (symmetric assumption)")
    if outer_hv is None:
        outer_hv = DEFAULT_HV
        LOG.warn(f"Outer slope could not be detected from contours; "
                 f"defaulting to {DEFAULT_HV:.1f}:1")
    if inner_hv is None:
        inner_hv = DEFAULT_HV
        LOG.warn(f"Inner slope could not be detected from contours; "
                 f"defaulting to {DEFAULT_HV:.1f}:1")

    CFG['outer_hv'] = outer_hv
    CFG['inner_hv'] = inner_hv
    LOG.success(f"Design slopes: outer H:V = {outer_hv:.2f}:1, "
                f"inner H:V = {inner_hv:.2f}:1")


# =============================================================================
# PREVIEW ANALYSIS (called from the dialog when a DXF is selected)
# =============================================================================
# Runs DXF parsing + ring classification + (best-effort) identification, but
# tolerant of sparse DXFs that don't have enough rings for auto-identification
# (e.g. Dam_02.dxf with only crest + spillway-broken outer toe). Returns
# everything the Geometry tab needs to visualise the DXF and let the user
# assign ring roles manually.

def preview_analyse_dxf(dxf_path, classify_params):
    """Parse a DXF and classify its rings without running the full pipeline.

    classify_params is a dict with min_area, min_verts, z_thresh, stitch_tol.
    These come from the dialog's current values.

    Returns a dict:
      {
        'success': bool,
        'all_const_z': [list of const-Z ring dicts],
        'var_z': [list of variable-Z ring dicts],
        'all_rings': all_const_z + var_z (the combined list the picker
                     uses - any ring, const or var, is addressable here
                     by a single index),
        'n_const': len(all_const_z) - split point between const and var
                   in all_rings,
        'auto_classified': dict mapping role name -> ring dict, OR None
                           if auto-identification failed,
        'auto_indices': dict mapping role name -> index into all_rings.
                        Note: this is the COMBINED index, so a var-Z
                        outer_toe will have an index >= n_const.
        'errors': list of error strings,
        'warnings': list of warning strings,
      }
    """
    global CFG, LOG
    saved_cfg, saved_log = CFG, LOG
    out = {
        'success': False,
        'all_const_z': [],
        'var_z': [],
        'all_rings': [],   # combined const + var, addressable by single index
        'n_const': 0,      # split point: indices < n_const are const-Z
        'auto_classified': None,
        'auto_indices': {},
        'errors': [],
        'warnings': [],
    }
    try:
        CFG = dict(classify_params)
        LOG = StepLogger()

        try:
            all_lines = _extract_from_dxf(dxf_path)
        except Exception as e:
            out['errors'].append(f"DXF read failed: {e}")
            return out

        try:
            classified = step3_classify(all_lines)
        except Exception as e:
            out['errors'].append(f"Ring classification failed: {e}")
            return out

        out['all_const_z'] = classified['const_z']
        out['var_z'] = classified['var_z']
        # Combined ring list: const-Z first (indices 0..n_const-1), then
        # var-Z (indices n_const..). The UI uses this as a single
        # addressable list so any ring - const or variable - can be
        # assigned to any role. This matters because the actual outer toe
        # of most dams is a VARIABLE-Z polyline draped to follow the
        # ground, NOT a constant-Z design contour.
        out['n_const'] = len(classified['const_z'])
        out['all_rings'] = list(classified['const_z']) + list(classified['var_z'])

        # Best-effort identification. step4_identify can raise on sparse data.
        try:
            kl = step4_identify(classified)
            # Promote outer toe to variable-Z using partial contour
            # endpoints if available. This makes the preview's long
            # section show the dam-meets-ground line correctly before
            # the user clicks Run.
            try:
                step4c_var_z_outer_toe(kl)
            except Exception:
                pass
            out['auto_classified'] = kl
            # Map ring -> index in all_rings (searches BOTH const and var).
            # step4_identify prefers a var-Z ring for outer_toe when one
            # exists, so this is where the var-Z outer toe gets its
            # auto-assignment index.
            id_map = {}
            for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
                r = kl.get(role)
                if r is None:
                    continue
                for i, ring in enumerate(out['all_rings']):
                    if ring is r:
                        id_map[role] = i
                        break
            out['auto_indices'] = id_map
        except Exception as e:
            out['warnings'].append(
                f"Auto-identification didn't complete ({e}). "
                f"Assign rings manually in the table below.")

        out['warnings'].extend(LOG.warnings)
        out['errors'].extend(LOG.errors)
        out['success'] = True
        return out

    finally:
        CFG = saved_cfg
        LOG = saved_log


def _ring_line_intersections(ring_coords, line_pt, line_dir):
    """Intersect an infinite line (line_pt + t*line_dir) with every segment
    of a closed ring. Returns a list of (t, (ix, iy)) tuples, where t is the
    signed scalar offset along line_dir from line_pt, and (ix, iy) is the
    intersection point. line_dir does NOT need to be unit length, but it
    helps to pass it as a unit vector so t reads as a distance.
    """
    if not ring_coords:
        return []
    px, py = line_dir
    out = []
    n = len(ring_coords)
    for i in range(n):
        a = ring_coords[i]
        b = ring_coords[(i + 1) % n]
        # Skip the duplicated closing edge on a [..., a0, a0] closed ring
        if i == n - 1 and abs(a[0]-ring_coords[0][0]) < 1e-9 and \
                abs(a[1]-ring_coords[0][1]) < 1e-9:
            continue
        sx = b[0] - a[0]
        sy = b[1] - a[1]
        # 2x2 system:  [sx, -px] [s] = [lpx - ax]
        #              [sy, -py] [t]   [lpy - ay]
        det = sx * (-py) - sy * (-px)
        if abs(det) < 1e-12:
            continue
        rhs_x = line_pt[0] - a[0]
        rhs_y = line_pt[1] - a[1]
        s = (rhs_x * (-py) - rhs_y * (-px)) / det
        t = (sx * rhs_y - sy * rhs_x) / det
        if 0.0 <= s <= 1.0:
            ix = a[0] + s * sx
            iy = a[1] + s * sy
            out.append((t, (ix, iy)))
    return out


def _nearest_axis_offset(ring_coords, line_pt, line_dir):
    """Return the signed offset (along line_dir from line_pt) of the
    closed-ring intersection nearest to line_pt. Picks the smallest |t|
    among all intersections - this is the near-side crossing of the line
    with the ring, ignoring the far-side crossing on the opposite face of
    the dam. Returns None if the line doesn't intersect the ring."""
    ixs = _ring_line_intersections(ring_coords, line_pt, line_dir)
    if not ixs:
        return None
    ixs.sort(key=lambda x: abs(x[0]))
    return ixs[0][0]


def _outward_perpendicular(ring_coords, chainage, reference_geom=None):
    """Compute the unit outward perpendicular to the ring tangent at the
    given chainage. If reference_geom is provided (a QgsGeometry of a ring
    that lies INSIDE the source ring), the perpendicular is flipped so it
    points AWAY from that geometry; otherwise it's flipped to point away
    from the ring's centroid (rough proxy for outward).
    """
    pt = interp_ch(ring_coords, chainage)
    ll = llen(ring_coords)
    delta = min(5.0, ll * 0.02)
    p0 = interp_ch(ring_coords, max(0.0, chainage - delta))
    p1 = interp_ch(ring_coords, min(ll, chainage + delta))
    tx, ty = p1[0]-p0[0], p1[1]-p0[1]
    tm = math.sqrt(tx*tx + ty*ty)
    if tm < 1e-9:
        return pt, None
    px, py = -ty/tm, tx/tm
    if reference_geom is not None:
        near = _nearest_on_geom(reference_geom, pt[0], pt[1])
        if (px*(near.x()-pt[0]) + py*(near.y()-pt[1])) > 0:
            px, py = -px, -py
    else:
        cx = sum(c[0] for c in ring_coords) / len(ring_coords)
        cy = sum(c[1] for c in ring_coords) / len(ring_coords)
        if (px*(cx-pt[0]) + py*(cy-pt[1])) > 0:
            px, py = -px, -py
    return pt, (px, py)


def compute_inferred_metrics(role_to_ring, preview=None):
    """Compute the headline design parameters from the currently-assigned
    rings. Uses proper perpendicular ray intersection (not nearest-vertex
    distance), so values are robust to coarse 10-vertex DAM B polygons.

    When the `preview` dict is supplied AND contains an auto-classified
    set with intermediate batter contours, the H:V values fall back to
    consecutive-contour-pair detection on those rings (more accurate and
    less reliant on the outer_toe ring, which can be unreliable when it
    represents a natural-ground intersection rather than a clean design
    parallel offset).
    """
    metrics = {
        'crest_z': None, 'invert_z': None, 'outer_toe_z': None,
        'depth': None, 'crest_width': None,
        'inner_hv': None, 'outer_hv': None,
        'outer_hv_source': None,  # 'contours' or 'crest-to-toe' or None
        'inner_hv_source': None,
    }
    it = role_to_ring.get('inner_toe')
    ic = role_to_ring.get('inner_crest')
    oc = role_to_ring.get('outer_crest')
    ot = role_to_ring.get('outer_toe')

    if it is not None:
        metrics['invert_z'] = it['z_mean']
    if ot is not None:
        metrics['outer_toe_z'] = ot['z_mean']
    if ic is not None:
        metrics['crest_z'] = ic['z_mean']
    elif oc is not None:
        metrics['crest_z'] = oc['z_mean']

    if metrics['crest_z'] is not None and metrics['invert_z'] is not None:
        metrics['depth'] = metrics['crest_z'] - metrics['invert_z']

    def _median_perp_offset(source_ring, target_ring, ref_geom=None,
                             n_samples=36):
        """For each of n_samples evenly-spaced chainages on source_ring,
        cast an outward perpendicular ray and intersect target_ring. The
        signed offset of the NEAREST intersection (smallest |t|) is the
        local perpendicular distance. Returns the IQR-clean median of
        |offset| across samples."""
        if not source_ring or not target_ring:
            return None
        src = source_ring['coords']
        tgt = target_ring['coords']
        if not src or not tgt:
            return None
        ll = llen(src)
        if ll < 1.0:
            return None
        offsets = []
        for j in range(n_samples):
            ch = ll * (j + 0.5) / n_samples
            pt, perp = _outward_perpendicular(src, ch, ref_geom)
            if perp is None:
                continue
            t = _nearest_axis_offset(tgt, pt, perp)
            if t is None:
                continue
            offsets.append(abs(t))
        if not offsets:
            return None
        offsets.sort()
        n = len(offsets)
        if n >= 8:
            q1 = offsets[n//4]; q3 = offsets[3*n//4]
            iqr = q3 - q1
            clean = [o for o in offsets if (q1-1.5*iqr) <= o <= (q3+1.5*iqr)]
            if clean:
                offsets = clean
        n = len(offsets)
        return offsets[n//2] if n % 2 else (offsets[n//2-1] + offsets[n//2]) / 2

    # Crest width: inner_crest -> outer_crest, perpendicular ray method.
    # Sample along whichever ring has more vertices (denser = better median).
    if ic is not None and oc is not None:
        if oc.get('npts', 0) >= ic.get('npts', 0):
            metrics['crest_width'] = _median_perp_offset(oc, ic)
        else:
            metrics['crest_width'] = _median_perp_offset(ic, oc)

    # Slope detection: prefer consecutive-contour pairs from auto-classified
    # batter rings (treats every intermediate const-Z contour as a clean
    # parallel design offset). Falls back to crest-to-toe perpendicular ray
    # when no intermediates are available.
    kl = (preview or {}).get('auto_classified') if preview else None
    if kl:
        # Outer
        outer_pool = list(kl.get('outer_batter') or [])
        if oc: outer_pool.append(oc)
        if ot: outer_pool.append(ot)
        try:
            hv = _detect_design_hv(outer_pool, "outer (preview)")
        except Exception:
            hv = None
        if hv is not None:
            metrics['outer_hv'] = hv
            metrics['outer_hv_source'] = 'contours'
        # Inner
        inner_pool = list(kl.get('inner_batter') or [])
        if ic: inner_pool.append(ic)
        if it: inner_pool.append(it)
        try:
            hv = _detect_design_hv(inner_pool, "inner (preview)")
        except Exception:
            hv = None
        if hv is not None:
            metrics['inner_hv'] = hv
            metrics['inner_hv_source'] = 'contours'

    # Fall back to crest-to-toe perpendicular distance (using line-ring
    # intersection so it's accurate even on coarse polygons), only if the
    # contour-pair approach didn't yield a result.
    if metrics['inner_hv'] is None and ic is not None and it is not None:
        v = abs(ic['z_mean'] - it['z_mean'])
        if v > 0.05:
            # Sample on whichever side has more vertices
            if it.get('npts', 0) >= ic.get('npts', 0):
                h = _median_perp_offset(it, ic)
            else:
                h = _median_perp_offset(ic, it)
            if h is not None and h > 0.01:
                metrics['inner_hv'] = h / v
                metrics['inner_hv_source'] = 'crest-to-toe'
    if metrics['outer_hv'] is None and oc is not None and ot is not None:
        v = abs(oc['z_mean'] - ot['z_mean'])
        if v > 0.05:
            if ot.get('npts', 0) >= oc.get('npts', 0):
                h = _median_perp_offset(ot, oc)
            else:
                h = _median_perp_offset(oc, ot)
            if h is not None and h > 0.01:
                metrics['outer_hv'] = h / v
                metrics['outer_hv_source'] = 'crest-to-toe'

    return metrics


def find_extreme_ground_perimeter_points(ring_coords, terrain_layer,
                                          n_samples=72):
    """Sample terrain elevation at n_samples evenly-spaced chainages around
    ring_coords. Return (high_chainage, high_z, low_chainage, low_z), or
    None if terrain sampling fails.
    """
    if not ring_coords or terrain_layer is None:
        return None
    try:
        dp = terrain_layer.dataProvider()
    except Exception:
        return None
    if not dp:
        return None
    ll = llen(ring_coords)
    if ll < 1.0:
        return None
    best_high = (-1.0, -float('inf'))
    best_low = (-1.0, float('inf'))
    for j in range(n_samples):
        ch = ll * j / n_samples
        pt = interp_ch(ring_coords, ch)
        try:
            res = dp.sample(QgsPointXY(pt[0], pt[1]), 1)
            if res is None:
                continue
            val, ok = res
            if not ok or val is None:
                continue
            if val > best_high[1]:
                best_high = (ch, val)
            if val < best_low[1]:
                best_low = (ch, val)
        except Exception:
            continue
    if best_high[1] == -float('inf') or best_low[1] == float('inf'):
        return None
    return (best_high[0], best_high[1], best_low[0], best_low[1])


def sample_terrain_perpendicular(ring_coords, chainage, terrain_layer,
                                  width=40.0, n=80):
    """Sample terrain elevation along a perpendicular line through ring_coords
    at the given chainage. Returns (offsets[], z_terrain[]) in metres - offset
    is signed distance perpendicular to the local ring tangent, positive
    pointing outward (away from centroid).
    """
    pt = interp_ch(ring_coords, chainage)
    ll = llen(ring_coords)
    delta = min(5.0, ll * 0.02)
    p0 = interp_ch(ring_coords, max(0, chainage - delta))
    p1 = interp_ch(ring_coords, min(ll, chainage + delta))
    tx, ty = p1[0] - p0[0], p1[1] - p0[1]
    tm = math.sqrt(tx*tx + ty*ty)
    if tm < 1e-9:
        return [], []
    # Outward perpendicular: rotate tangent 90 deg, flip to point AWAY from
    # the centroid of the ring (a rough proxy for "outward")
    cx = sum(c[0] for c in ring_coords) / len(ring_coords)
    cy = sum(c[1] for c in ring_coords) / len(ring_coords)
    px, py = -ty/tm, tx/tm
    if (px*(cx - pt[0]) + py*(cy - pt[1])) > 0:
        px, py = -px, -py  # was pointing inward, flip

    dp = terrain_layer.dataProvider() if terrain_layer is not None else None
    offsets, zs = [], []
    half = width / 2.0
    step = width / n
    o = -half
    while o <= half:
        x = pt[0] + px * o
        y = pt[1] + py * o
        z = None
        if dp:
            try:
                res = dp.sample(QgsPointXY(x, y), 1)
                if res:
                    val, ok = res
                    if ok and val is not None:
                        z = float(val)
            except Exception:
                pass
        offsets.append(o)
        zs.append(z)
        o += step
    return offsets, zs


# =============================================================================
# STEP 5: GENERATE POINTS (4 key lines only)
# =============================================================================

def ring_pts(ring, src, sp=None, zov=None):
    sp = sp or CFG['point_spacing']
    coords = list(ring['coords'])
    # Ensure closure before densifying. Ring dicts produced by step3 or
    # _ring_dict_from_xy strip the duplicated closing vertex for
    # consistency, but densify walks v0..v(N-1) treating the input as
    # an open polyline. Without re-adding the closing vertex, the
    # segment from v(N-1) back to v0 is never densified -> visible gap
    # in the elevation points file at the ring's first vertex.
    if coords and (
        (coords[0][0], coords[0][1]) != (coords[-1][0], coords[-1][1])):
        # Pad to match the dimensionality of existing coords
        if len(coords[0]) >= 3:
            coords.append((coords[0][0], coords[0][1], coords[0][2]))
        else:
            coords.append((coords[0][0], coords[0][1]))
    d = densify(coords, sp)
    if zov is not None:
        return [(c[0], c[1], zov, src) for c in d]
    return [(c[0], c[1], c[2], src) for c in d]


def step5_points(kl):
    """Generate the TIN-input point cloud from the 4 key design rings.

    All four rings are CONSTANT-Z by design:
      - inner_toe at invert
      - inner_crest at crest
      - outer_crest at crest
      - outer_toe at toe_low (artificially deep, e.g. 15 m below
        terrain minimum)

    Constant-Z outer toe is essential: any variable Z at the outer toe
    would create wonky TIN triangles between adjacent vertices with
    different Z values, producing visible artifacts on the outer
    batter. With const-Z outer toe, the TIN interpolates linearly from
    outer_crest (CRE) down to outer_toe (CFG['toe_low']) at the design
    slope, every single triangle following the same plane.

    The 'mask to actual dam footprint' step happens AFTER TIN: turn on
    'Drape DEM to terrain' on the DEM & Output tab. That samples
    terrain at each cell of the rendered DEM and masks cells where
    dam_z < terrain_z (i.e. cells below natural ground). The boundary
    of valid cells IS the variable-elevation outer toe - geometrically
    perfect on the inside, clipped exactly at where the dam meets
    natural ground.

    Workflow: 4 const-Z rings -> points -> TIN interpolate -> drape
    clip to terrain -> done.
    """
    LOG.start_step("Generating elevation points (all 4 rings const-Z for clean TIN)")

    INV, CRE = CFG['invert'], CFG['crest']
    sp = CFG['point_spacing']
    pts = []

    # inner_toe, inner_crest, outer_crest - forced to their nominal
    # design Z values via zov. These rings are flat by design.
    for name, ring, z in [("inner_toe", kl['inner_toe'], INV),
                           ("inner_crest", kl['inner_crest'], CRE),
                           ("outer_crest", kl['outer_crest'], CRE)]:
        p = ring_pts(ring, name, zov=z)
        LOG.info(f"{name}: {len(p)} pts at {z:.2f} m (spacing={sp} m)")
        pts.extend(p)

    # outer_toe at CONST-Z = CFG['toe_low']. The XY trace comes from
    # whichever ring is the "perfect geometry" source:
    #   - DXF auto / DXF+anchor / polygon AFTER step4c or Cut-to-terrain:
    #     use the saved nominal_const_coords (the original artificial
    #     deep ring before the variable-Z promotion).
    #   - Otherwise: use kl['outer_toe']['coords'] directly (still
    #     const-Z because no variable-Z step has run).
    # Z forced to CFG['toe_low'] via zov to guarantee the const-Z
    # invariant the downstream drape step needs.
    # outer_toe TIN input. Priority order:
    #   1. artificial_const_coords (from step4d) - parallel offset of
    #      outer_crest at design slope, at Z=CFG['toe_low'] (well below
    #      natural ground). Geometrically perfect; matches what the
    #      constant-slope post-processor expects.
    #   2. nominal_const_coords (legacy fallback) - DXF's outer toe XY,
    #      forced to CFG['toe_low'].
    #   3. The variable-Z 'coords' directly (no const-Z step ran).
    # Z always forced to CFG['toe_low'] via zov so the TIN sees a
    # const-Z outer toe with no per-vertex variation.
    ot = kl['outer_toe']
    if ot.get('artificial_const_coords'):
        const_ring = {'coords': ot['artificial_const_coords'],
                       'z_mean': CFG['toe_low']}
        p = ring_pts(const_ring, "outer_toe", zov=CFG['toe_low'])
        LOG.info(f"outer_toe: {len(p)} pts at Z={CFG['toe_low']:.2f} m "
                 f"(artificial_const_coords - parallel offset of "
                 f"outer_crest at design slope)")
    elif ot.get('nominal_const_coords'):
        const_ring = {'coords': ot['nominal_const_coords'],
                       'z_mean': ot.get('nominal_const_z', CFG['toe_low'])}
        p = ring_pts(const_ring, "outer_toe", zov=CFG['toe_low'])
        LOG.info(f"outer_toe: {len(p)} pts at Z={CFG['toe_low']:.2f} m "
                 f"(nominal_const_coords fallback - step4d didn't run)")
    else:
        p = ring_pts(ot, "outer_toe", zov=CFG['toe_low'])
        LOG.info(f"outer_toe: {len(p)} pts at Z={CFG['toe_low']:.2f} m")
    pts.extend(p)

    # ---- Interior sumps (deeper basin pockets) --------------------------
    # Model each sump as TWO rings: its invert ring at the sump Z, plus a
    # rim ring at the basin invert (INV) offset slightly OUTBOARD of the
    # sump. The rim is the critical piece - it pins the basin floor flat at
    # INV right up to the sump edge, so the TIN drops only the short sump
    # wall down to the invert instead of running the inner batter/basin all
    # the way down to it as a cone. The inner toe stays the basin floor, so
    # the inner batter still terminates at INV.
    n_sumps = 0
    if CFG.get('include_sump', True):
        for si, sump in enumerate(kl.get('sumps', []) or []):
            sc = sump.get('coords')
            sz = float(sump.get('z_mean', INV))
            if not sc or len(sc) < 3 or sz >= INV - 1e-3:
                continue
            # Rim outboard offset = wall run = pocket depth * wall batter.
            wall_hv = float(CFG.get('sump_wall_hv', 1.5))
            wall_run = max(0.3, (INV - sz) * wall_hv)
            cx = sum(c[0] for c in sc) / len(sc)
            cy = sum(c[1] for c in sc) / len(sc)
            try:
                rim = _offset_ring_xy(
                    sc, QgsGeometry.fromPointXY(QgsPointXY(cx, cy)),
                    wall_run, sp)
            except Exception:
                rim = None
            pts.extend(ring_pts(sump, "sump_invert", zov=sz))
            n_sumps += 1
            if rim:
                # _offset_ring_xy returns 2-tuples; densify (via ring_pts)
                # needs 3-tuples, so pad with the rim Z.
                rim3 = [(x, y, INV) for (x, y) in rim]
                pts.extend(ring_pts({'coords': rim3}, "sump_rim", zov=INV))
                LOG.info(f"sump {si + 1}: invert ring at {sz:.2f} m + rim at "
                         f"{INV:.2f} m ({wall_run:.1f} m outboard, "
                         f"{wall_hv:.1f}:1 wall)")
            else:
                LOG.warn(f"sump {si + 1}: rim offset failed; added invert "
                         f"ring only (basin may funnel to the sump).")

    LOG.success(f"Total: {len(pts)} points (4 const-Z rings"
                + (f" + {n_sumps} sump" if n_sumps else "") + ")")
    LOG.info("Next: TIN interpolate -> constant-slope post-process -> "
             "clip to the active variable-Z outer toe polygon (Method 1 "
             "from DXF, or Method 2 from terrain intersection).")
    return pts


# =============================================================================
# STEP 6: SPILLWAY (cross-lines + arcs + transition batters)
# =============================================================================
#
# Geometry in plan view (looking down):
#
#                    inner_arc (spillway Z)
#                   /                       \
#     transition  /  flat_start   flat_end    \  transition
#     (batter)  /    (spillway Z cross-line)    \  (batter)
#             /                                   \
#   batter_start ======= CREST ======== batter_end
#   (crest Z)    \                     /  (crest Z)
#     transition  \                   /  transition
#     (batter)     \               /    (batter)
#                   \             /
#                    outer_arc (spillway Z)
#
# All cross-lines are PARALLEL (same perpendicular direction from centre).
# 4 transition lines connect crest corners to spillway corners.
# 2 arcs connect spillway corners along the offset crest curves.

def _nearest_on_geom(geom, x, y):
    pt = QgsGeometry.fromPointXY(QgsPointXY(x, y))
    return QgsPointXY(geom.nearestPoint(pt).asPoint())


def _estimate_batter_hv(crest_coords, toe_coords, crest_geom, toe_geom,
                         crest_elev, sample_ch):
    """Estimate H:V batter ratio using actual toe Z at spillway location."""
    pt_crest = interp_ch(crest_coords, sample_ch)
    pt_toe_xy = _nearest_on_geom(toe_geom, pt_crest[0], pt_crest[1])
    toe_ch, _ = ch_nearest(toe_coords, pt_toe_xy.x(), pt_toe_xy.y())
    pt_toe_3d = interp_ch(toe_coords, toe_ch)
    toe_z = pt_toe_3d[2]
    h_dist = math.sqrt((pt_crest[0]-pt_toe_xy.x())**2 +
                        (pt_crest[1]-pt_toe_xy.y())**2)
    v_dist = abs(crest_elev - toe_z)
    if v_dist < 0.01:
        return 3.0
    hv = h_dist / v_dist
    LOG.detail(f"  Batter: H={h_dist:.1f}m, V={v_dist:.2f}m "
               f"(toe Z={toe_z:.2f}), H:V={hv:.1f}:1")
    return hv


def _line_pts(p0, p1, z, src, sp):
    """Points from (x,y) p0 to (x,y) p1 at elevation z."""
    dx, dy = p1[0]-p0[0], p1[1]-p0[1]
    d = math.sqrt(dx**2 + dy**2)
    if d < 0.01:
        return []
    n = max(int(d / sp), 2)
    return [(p0[0]+j/n*dx, p0[1]+j/n*dy, z, src) for j in range(n+1)]


def _transition_pts(p_crest, p_spill, cre_z, sp_z, src, sp):
    """Points along a batter transition from crest corner to spillway corner.
    Elevation interpolates linearly."""
    dx, dy = p_spill[0]-p_crest[0], p_spill[1]-p_crest[1]
    d = math.sqrt(dx**2 + dy**2)
    if d < 0.01:
        return []
    n = max(int(d / sp), 2)
    pts = []
    for j in range(n+1):
        f = j / n
        z = cre_z + f * (sp_z - cre_z)
        pts.append((p_crest[0]+f*dx, p_crest[1]+f*dy, z, src))
    return pts


def step6_spillway(kl, dam_pts):
    LOG.start_step("Spillway geometry")

    if not CFG['spillway_enabled']:
        LOG.info("Spillway disabled - skipping")
        return dam_pts, [], [], None, None

    CRE = CFG['crest']
    dep = CFG['spill_depth']
    wid = CFG['spill_width']
    bat = CFG['spill_batter']
    sp = CFG['point_spacing']

    sz = CRE - dep
    bh = bat * dep
    hf = wid / 2.0
    ht = hf + bh

    LOG.info(f"Spillway Z: {sz:.2f} m")
    LOG.info(f"Flat width: {wid:.1f} m, batter: {bh:.1f} m ({bat}:1 H:V)")

    ic = kl['inner_crest']['coords']
    oc = kl['outer_crest']['coords']
    it_c = kl['inner_toe']['coords']

    # For spillway batter calcs, use the outermost CONSTANT-Z ring
    # (design geometry) not the variable-Z outer toe (topography)
    outer_batter_rings = kl.get('outer_batter', [])
    if outer_batter_rings:
        const_ot = outer_batter_rings[-1]  # outermost constant-Z ring
        ot_c = const_ot['coords']
        LOG.detail(f"Using constant-Z outer toe for spillway: "
                   f"Z={const_ot['z_mean']:.2f}, area={const_ot['area']:.0f}")
    else:
        ot_c = kl['outer_toe']['coords']
        LOG.warn("No constant-Z outer ring found, using variable-Z outer toe")

    ic_g = QgsGeometry.fromPolylineXY([QgsPointXY(c[0], c[1]) for c in ic])
    oc_g = QgsGeometry.fromPolylineXY([QgsPointXY(c[0], c[1]) for c in oc])
    it_g = QgsGeometry.fromPolylineXY([QgsPointXY(c[0], c[1]) for c in it_c])
    ot_g = QgsGeometry.fromPolylineXY([QgsPointXY(c[0], c[1]) for c in ot_c])

    # Spillway centre on inner crest
    ich, id_ = ch_nearest(ic, CFG['spill_e'], CFG['spill_n'])
    och, od_ = ch_nearest(oc, CFG['spill_e'], CFG['spill_n'])

    avg_dist = (id_ + od_) / 2
    if avg_dist > 50:
        LOG.warn(f"Spillway ref point is {avg_dist:.1f} m from crest.")
    if avg_dist > 200:
        raise ValueError(
            f"Spillway ref is {avg_dist:.0f} m from crest - too far.\n"
            f"Reference: ({CFG['spill_e']:.1f}, {CFG['spill_n']:.1f})")

    LOG.info(f"Inner crest ch: {ich:.1f} m, Outer crest ch: {och:.1f} m")

    il, ol = llen(ic), llen(oc)

    # Batter H:V for the spillway. Use the CONTOUR-DERIVED design slope
    # (CFG['inner_hv']/['outer_hv'] from step4b - the median H:V between
    # consecutive contour rings), NOT a crest-to-toe estimate. The toe
    # position can be distorted (e.g. a sump-chopped basin floor), and basing
    # the spillway batter on it warps inner_ext/outer_ext. We still compute the
    # crest-to-toe estimate as a CROSS-CHECK and warn if it diverges from the
    # contour slope - a divergence means the toe is probably mis-identified.
    inner_hv = CFG.get('inner_hv')
    outer_hv = CFG.get('outer_hv')
    inner_hv_ct = _estimate_batter_hv(ic, it_c, ic_g, it_g, CRE, ich)
    outer_hv_ct = _estimate_batter_hv(oc, ot_c, oc_g, ot_g, CRE, och)
    if not inner_hv or inner_hv <= 0:
        inner_hv = inner_hv_ct
    if not outer_hv or outer_hv <= 0:
        outer_hv = outer_hv_ct
    for nm, slope, ct in (("inner", inner_hv, inner_hv_ct),
                          ("outer", outer_hv, outer_hv_ct)):
        if (slope and ct and slope > 0
                and abs(ct - slope) / slope > 0.3):
            LOG.warn(f"{nm} batter: crest-to-toe slope {ct:.1f}:1 differs from "
                     f"the contour slope {slope:.1f}:1 by >30% - the {nm} toe "
                     f"is probably mis-identified. Using the contour slope.")
    LOG.info(f"Spillway batter H:V (from contours): inner {inner_hv:.2f}:1, "
             f"outer {outer_hv:.2f}:1 "
             f"(crest-to-toe was inner {inner_hv_ct:.2f}:1, "
             f"outer {outer_hv_ct:.2f}:1)")

    inner_ext = dep * inner_hv
    outer_ext = dep * outer_hv
    LOG.info(f"Inner ext: {inner_ext:.1f} m, Outer ext: {outer_ext:.1f} m")

    # -------------------------------------------------------------------
    # Local perpendicular direction at each chainage
    # Uses a WIDE tangent sampling window to smooth out vertex noise
    # -------------------------------------------------------------------

    def local_perp(coords, ch, total_len, outward_ref_geom):
        """Get outward-pointing unit perpendicular to crest at chainage.
        Uses a wide sampling window (10m each side) to get smooth tangent
        direction unaffected by individual vertex positions."""
        delta = min(10.0, total_len * 0.05)  # 10m or 5% of length
        ch0 = max(0, ch - delta)
        ch1 = min(total_len, ch + delta)
        p0 = interp_ch(coords, ch0)
        p1 = interp_ch(coords, ch1)
        tx = p1[0] - p0[0]
        ty = p1[1] - p0[1]
        tm = math.sqrt(tx**2 + ty**2)
        if tm < 1e-10:
            return (1, 0)
        # Perpendicular: rotate tangent 90 deg
        px, py = -ty/tm, tx/tm
        # Check direction: should point outward
        pt_here = interp_ch(coords, ch)
        ref_pt = _nearest_on_geom(outward_ref_geom, pt_here[0], pt_here[1])
        dot = px*(ref_pt.x()-pt_here[0]) + py*(ref_pt.y()-pt_here[1])
        if dot < 0:
            px, py = -px, -py
        return (px, py)

    # Measure crest width at spillway centre
    pi_cen = interp_ch(ic, ich)
    po_cen = _nearest_on_geom(oc_g, pi_cen[0], pi_cen[1])
    d_crest = math.sqrt((po_cen.x()-pi_cen[0])**2 + (po_cen.y()-pi_cen[1])**2)
    LOG.detail(f"Crest width at spillway: {d_crest:.1f} m")

    def project_perp(pi, perp, target_geom):
        """Find where a perpendicular ray from inner crest intersects
        the outer crest. Uses actual line intersection, not nearest-point."""
        ray_len = d_crest * 5  # long enough to definitely cross
        far_x = pi[0] + perp[0] * ray_len
        far_y = pi[1] + perp[1] * ray_len
        # Create ray geometry and intersect with outer crest
        ray_geom = QgsGeometry.fromPolylineXY([
            QgsPointXY(pi[0], pi[1]),
            QgsPointXY(far_x, far_y)])
        ix = ray_geom.intersection(target_geom)
        if ix and not ix.isEmpty():
            # May return point or multipoint - take the nearest one
            if ix.isMultipart():
                best_d = float('inf')
                best_pt = None
                for pt in ix.asMultiPoint():
                    d = math.sqrt((pt.x()-pi[0])**2 + (pt.y()-pi[1])**2)
                    if d < best_d:
                        best_d = d
                        best_pt = (pt.x(), pt.y())
                if best_pt:
                    return best_pt
            else:
                pt = ix.asPoint()
                return (pt.x(), pt.y())
        # Fallback: nearest point on outer crest (shouldn't normally get here)
        LOG.warn(f"Ray intersection failed at ({pi[0]:.1f}, {pi[1]:.1f}), "
                 f"using nearest point fallback")
        po = _nearest_on_geom(target_geom, pi[0], pi[1])
        return (po.x(), po.y())

    # Key chainages along inner crest
    ch_bs = max(0, ich - ht)        # batter start
    ch_fs = max(0, ich - hf)        # flat start
    ch_fe = min(il, ich + hf)       # flat end
    ch_be = min(il, ich + ht)       # batter end

    # Inner crest points at key chainages
    pi_bs = interp_ch(ic, ch_bs)
    pi_fs = interp_ch(ic, ch_fs)
    pi_fe = interp_ch(ic, ch_fe)
    pi_be = interp_ch(ic, ch_be)

    # Compute local perpendicular and crest width at each key chainage
    perp_bs = local_perp(ic, ch_bs, il, oc_g)
    perp_fs = local_perp(ic, ch_fs, il, oc_g)
    perp_fe = local_perp(ic, ch_fe, il, oc_g)
    perp_be = local_perp(ic, ch_be, il, oc_g)
    perp_cen = local_perp(ic, ich, il, oc_g)

    # Outer crest points: project along LOCAL perpendicular
    po_bs = project_perp(pi_bs, perp_bs, oc_g)
    po_fs = project_perp(pi_fs, perp_fs, oc_g)
    po_fe = project_perp(pi_fe, perp_fe, oc_g)
    po_be = project_perp(pi_be, perp_be, oc_g)

    LOG.detail(f"Perp at centre: ({perp_cen[0]:.4f}, {perp_cen[1]:.4f})")

    # Log perpendicularity check for each cross-line
    for label, pi, po, perp, ch_val in [
        ("batter_start", pi_bs, po_bs, perp_bs, ch_bs),
        ("flat_start", pi_fs, po_fs, perp_fs, ch_fs),
        ("flat_end", pi_fe, po_fe, perp_fe, ch_fe),
        ("batter_end", pi_be, po_be, perp_be, ch_be),
    ]:
        # Cross-line direction
        cdx = po[0] - pi[0]
        cdy = po[1] - pi[1]
        cm = math.sqrt(cdx**2 + cdy**2)
        if cm > 0.01:
            # Tangent at this chainage
            delta = min(10.0, il * 0.05)
            c0 = max(0, ch_val - delta)
            c1 = min(il, ch_val + delta)
            t0 = interp_ch(ic, c0)
            t1 = interp_ch(ic, c1)
            tdx = t1[0] - t0[0]
            tdy = t1[1] - t0[1]
            tm = math.sqrt(tdx**2 + tdy**2)
            if tm > 0.01:
                # Angle between cross-line and tangent
                dot = abs(cdx*tdx + cdy*tdy) / (cm * tm)
                dot = min(1.0, dot)  # clamp for acos
                angle = math.degrees(math.acos(dot))
                LOG.detail(f"  {label}: cross-line angle to crest = {angle:.1f} deg "
                           f"({'OK' if angle > 85 else 'WARNING - not perpendicular'})")

    # -------------------------------------------------------------------
    # Compute 8 corner points of the spillway notch
    # -------------------------------------------------------------------
    # Crest-level corners:
    c_bs_i = (pi_bs[0], pi_bs[1])
    c_bs_o = po_bs
    c_be_i = (pi_be[0], pi_be[1])
    c_be_o = po_be

    # Spillway-level corners (extended into batters along LOCAL perp):
    s_fs_i = (pi_fs[0] - perp_fs[0]*inner_ext,
              pi_fs[1] - perp_fs[1]*inner_ext)
    s_fs_o = (po_fs[0] + perp_fs[0]*outer_ext,
              po_fs[1] + perp_fs[1]*outer_ext)
    s_fe_i = (pi_fe[0] - perp_fe[0]*inner_ext,
              pi_fe[1] - perp_fe[1]*inner_ext)
    s_fe_o = (po_fe[0] + perp_fe[0]*outer_ext,
              po_fe[1] + perp_fe[1]*outer_ext)

    # -------------------------------------------------------------------
    # Generate all spillway lines
    # -------------------------------------------------------------------
    spill_pts = []
    bls = []

    def add_line(pts, bl_name):
        if pts:
            spill_pts.extend(pts)
            bls.append([(p[0], p[1], p[2]) for p in pts])
            LOG.detail(f"{bl_name}: {len(pts)} pts")

    # 1-2: Crest-level cross-lines (batter boundaries)
    add_line(_line_pts(c_bs_i, c_bs_o, CRE, "spill_batter_start", sp),
             "Batter start (crest Z)")
    add_line(_line_pts(c_be_i, c_be_o, CRE, "spill_batter_end", sp),
             "Batter end (crest Z)")

    # 3-4: Spillway-level cross-lines (extended)
    add_line(_line_pts(s_fs_i, s_fs_o, sz, "spill_flat_start", sp),
             "Flat start (spillway Z)")
    add_line(_line_pts(s_fe_i, s_fe_o, sz, "spill_flat_end", sp),
             "Flat end (spillway Z)")

    # 5-8: Transition batter lines (crest corner -> spillway corner)
    # These form the truncated pyramid sides
    add_line(_transition_pts(c_bs_i, s_fs_i, CRE, sz, "spill_trans_start_i", sp),
             "Transition start inner")
    add_line(_transition_pts(c_bs_o, s_fs_o, CRE, sz, "spill_trans_start_o", sp),
             "Transition start outer")
    add_line(_transition_pts(c_be_i, s_fe_i, CRE, sz, "spill_trans_end_i", sp),
             "Transition end inner")
    add_line(_transition_pts(c_be_o, s_fe_o, CRE, sz, "spill_trans_end_o", sp),
             "Transition end outer")

    # 9-10: Connecting arcs at spillway level
    # Inner arc: follows inner crest, offset inward by local perpendicular
    inner_arc = []
    ch = ch_fs
    while ch <= ch_fe:
        pt = interp_ch(ic, ch)
        px, py = local_perp(ic, ch, il, oc_g)
        inner_arc.append((pt[0] - px*inner_ext,
                          pt[1] - py*inner_ext,
                          sz, "spill_inner_arc"))
        ch += sp
    add_line(inner_arc, "Inner arc (spillway Z)")

    # Outer arc: follows outer crest, offset outward
    och_fs = ch_nearest(oc, po_fs[0], po_fs[1])[0]
    och_fe = ch_nearest(oc, po_fe[0], po_fe[1])[0]
    if och_fs > och_fe:
        och_fs, och_fe = och_fe, och_fs

    outer_arc = []
    ch = och_fs
    while ch <= och_fe:
        pt = interp_ch(oc, ch)
        # Get local perpendicular on outer crest
        px, py = local_perp(oc, ch, ol, ot_g)
        outer_arc.append((pt[0] + px*outer_ext,
                          pt[1] + py*outer_ext,
                          sz, "spill_outer_arc"))
        ch += sp
    add_line(outer_arc, "Outer arc (spillway Z)")

    LOG.info(f"Total: {len(spill_pts)} spillway pts, {len(bls)} breaklines")

    # -------------------------------------------------------------------
    # Break crest rings in spillway zone
    # -------------------------------------------------------------------
    och_bs = ch_nearest(oc, po_bs[0], po_bs[1])[0]
    och_be = ch_nearest(oc, po_be[0], po_be[1])[0]
    if och_bs > och_be:
        och_bs, och_be = och_be, och_bs

    filtered = []
    rm_i, rm_o = 0, 0
    for x, y, z, s in dam_pts:
        if s == "inner_crest":
            ch, _ = ch_nearest(ic, x, y)
            if ch_bs <= ch <= ch_be:
                rm_i += 1
                continue
        elif s == "outer_crest":
            ch, _ = ch_nearest(oc, x, y)
            if och_bs <= ch <= och_be:
                rm_o += 1
                continue
        filtered.append((x, y, z, s))

    LOG.info(f"Removed {rm_i} inner + {rm_o} outer crest pts")
    all_pts = filtered + spill_pts

    # -------------------------------------------------------------------
    # Build spillway outline as a single closed polygon for rings CSV
    # Traces the full perimeter of the notch with correct elevations
    # -------------------------------------------------------------------
    spill_outline = []

    # Build legs once, reuse for outline + inner/outer traces
    leg1 = _transition_pts(c_bs_i, s_fs_i, CRE, sz, "spillway", sp)  # in down
    leg2 = list(inner_arc)                                            # inner arc
    leg3 = _transition_pts(s_fe_i, c_be_i, sz, CRE, "spillway", sp)  # in up
    leg4 = _line_pts(c_be_i, c_be_o, CRE, "spillway", sp)            # cross end
    leg5 = _transition_pts(c_be_o, s_fe_o, CRE, sz, "spillway", sp)  # out down
    leg6 = list(reversed(outer_arc))                                  # outer arc rev
    leg7 = _transition_pts(s_fs_o, c_bs_o, sz, CRE, "spillway", sp)  # out up
    leg8 = _line_pts(c_bs_o, c_bs_i, CRE, "spillway", sp)            # cross start

    spill_outline.extend(leg1)
    spill_outline.extend(leg2)
    spill_outline.extend(leg3)
    spill_outline.extend(leg4)
    spill_outline.extend(leg5)
    spill_outline.extend(leg6)
    spill_outline.extend(leg7)
    spill_outline.extend(leg8)

    LOG.info(f"Spillway outline: {len(spill_outline)} pts (closed polygon)")

    # Inner trace (legs 1-3): the upstream/inner perimeter of the spillway
    # c_bs_i -> s_fs_i -> [inner arc] -> s_fe_i -> c_be_i
    inner_trace = []
    for leg in (leg1, leg2, leg3):
        inner_trace.extend((p[0], p[1], p[2]) for p in leg)

    # Outer trace (legs 5-7): the downstream/outer perimeter of the spillway
    # c_be_o -> s_fe_o -> [outer arc reversed] -> s_fs_o -> c_bs_o
    # This is the "Spillway" line nearest the outer toe
    outer_trace = []
    for leg in (leg5, leg6, leg7):
        outer_trace.extend((p[0], p[1], p[2]) for p in leg)

    # Lateral cross-lines that close off each end of the notch in plan view.
    # Two at each lateral end: one at crest Z (batter shoulder) and one at
    # spillway Z (flat edge). Same geometry as the spill_batter_*/spill_flat_*
    # entities in the elevation points cloud.
    crosslines = []
    for part, p_in, p_out, z_const in (
        ("batter_start", c_bs_i, c_bs_o, CRE),
        ("batter_end",   c_be_i, c_be_o, CRE),
        ("flat_start",   s_fs_i, s_fs_o, sz),
        ("flat_end",     s_fe_i, s_fe_o, sz),
    ):
        seg = _line_pts(p_in, p_out, z_const, "spillway", sp)
        if seg:
            crosslines.append((part, [(p[0], p[1], p[2]) for p in seg]))

    spill_lines = {
        'inner_trace': inner_trace,
        'outer_trace': outer_trace,
        'crosslines': crosslines,
    }
    gap_info = {
        'inner': (ch_bs, ch_be),
        'outer': (och_bs, och_be),
    }
    LOG.success(f"Combined: {len(all_pts)} points")
    return all_pts, bls, spill_outline, spill_lines, gap_info


# =============================================================================
# STEP 7: OUTPUTS
# =============================================================================

def _layer_name(suffix):
    """Build a project layer name tied to the user's Dam Name input, so
    multiple dams' outputs in one QGIS project are distinguishable
    instead of all being generic ('Dam DEM', 'Dam Key Lines', ...).

    The Dam Name field (CFG['dam_name'], e.g. "Proposed Farm 12 Dam")
    becomes the prefix:
        "Proposed Farm 12 Dam" + "DEM" -> "Proposed Farm 12 Dam DEM"
        "Proposed Farm 12 Dam" + "Key Lines" -> "... Dam Key Lines"

    `suffix` is the bare descriptor without a leading "Dam " (e.g. "DEM",
    "Key Lines", "FSL", "Spillway", "Elevation Points", "Outer Toe
    Footprint"). If the dam name is blank or the placeholder default, we
    fall back to the old generic "Dam <suffix>" naming so nothing breaks
    when the user hasn't named the dam.
    """
    nm = (CFG.get('dam_name') or "").strip()
    if not nm or nm.lower() == "proposed dam":
        # Keep the historic generic name when unnamed / default
        return f"Dam {suffix}"
    return f"{nm} {suffix}"


def _make_pt_layer(name, points):
    lyr = QgsVectorLayer(f"PointZ?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([
        QgsField("id", QVariant.Int),
        QgsField("easting", QVariant.Double),
        QgsField("northing", QVariant.Double),
        QgsField("elevation", QVariant.Double),
        QgsField("source", QVariant.String),
    ])
    lyr.updateFields()
    feats = []
    for i, (x, y, z, s) in enumerate(points):
        f = QgsFeature()
        f.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
        f.setAttributes([i, x, y, z, s])
        feats.append(f)
    pr.addFeatures(feats)
    lyr.updateExtents()
    return lyr


def _make_line_layer(name, kl, gap_info=None):
    """4-feature line layer: inner_toe, outer_toe, inner_crest, outer_crest.

    If gap_info is provided (dict with 'inner' and 'outer' chainage tuples),
    inner_crest and outer_crest are emitted as OPEN polylines with the
    spillway zone removed - producing a clean visible gap in figures.

    Schema (matches the dam_spillway layer convention):
      - part:       feature identifier (inner_toe / inner_crest / ...)
      - elevation:  constant Z, or -1 for the variable-Z outer toe
      - Name:       labelable display name; populated only on outer_toe
                    (carries CFG['dam_name'] for the curved perimeter label)
    """
    lyr = QgsVectorLayer(f"LineString?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([QgsField("part", QVariant.String),
                      QgsField("elevation", QVariant.Double),
                      QgsField("Name", QVariant.String)])
    lyr.updateFields()

    inner_gap = (gap_info or {}).get('inner')
    outer_gap = (gap_info or {}).get('outer')
    dam_label = CFG.get('dam_name') or "Proposed Dam"

    specs = [
        ("inner_toe",   kl['inner_toe'],   CFG['invert'], None,      ""),
        ("inner_crest", kl['inner_crest'], CFG['crest'],  inner_gap, ""),
        ("outer_crest", kl['outer_crest'], CFG['crest'],  outer_gap, ""),
        ("outer_toe",   kl['outer_toe'],   -1,            None,      dam_label),
    ]
    for part, ring, el, gap, label in specs:
        coords = ring['coords']
        if gap is not None:
            arc = _ring_arc_with_gap(coords, gap[0], gap[1])
        else:
            arc = list(coords)
        if not arc or len(arc) < 2:
            continue
        # The outer_toe carries the dam-name label, set to "below line"
        # placement so it traces the OUTSIDE of the dam perimeter. "Below
        # line" is relative to the line's digitising direction, so the
        # label only lands outside if the ring is wound CLOCKWISE in map
        # coordinates. Different sources (DXF contours, buffer offsets,
        # terrain-cut walks) can produce either winding, so normalise the
        # outer_toe to clockwise here. Signed area > 0 = counter-clockwise
        # -> reverse it. Only the outer_toe needs this (it's the only
        # labelled ring).
        if part == "outer_toe" and len(arc) >= 3:
            sa = 0.0
            for i in range(len(arc)):
                x1, y1 = arc[i][0], arc[i][1]
                x2, y2 = arc[(i + 1) % len(arc)][0], arc[(i + 1) % len(arc)][1]
                sa += x1 * y2 - x2 * y1
            if sa > 0:  # counter-clockwise -> reverse to clockwise
                arc = list(reversed(arc))
        f = QgsFeature()
        f.setGeometry(QgsGeometry.fromPolylineXY(
            [QgsPointXY(c[0], c[1]) for c in arc]))
        f.setAttributes([part, el, label])
        pr.addFeatures([f])
    lyr.updateExtents()
    return lyr


def _make_bl_layer(name, crest_bls, spill_bls):
    lyr = QgsVectorLayer(f"LineString?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([QgsField("name", QVariant.String),
                      QgsField("elevation", QVariant.Double)])
    lyr.updateFields()
    feats = []
    for label, coords, elev in crest_bls:
        if len(coords) < 2: continue
        f = QgsFeature()
        f.setGeometry(QgsGeometry.fromPolylineXY(
            [QgsPointXY(c[0], c[1]) for c in coords]))
        f.setAttributes([label, elev])
        feats.append(f)
    for i, bl in enumerate(spill_bls):
        if len(bl) < 2: continue
        f = QgsFeature()
        f.setGeometry(QgsGeometry.fromPolylineXY(
            [QgsPointXY(c[0], c[1]) for c in bl]))
        f.setAttributes([f"spillway_bl_{i}", -1])
        feats.append(f)
    pr.addFeatures(feats)
    lyr.updateExtents()
    return lyr


def _make_poly_layer(name, coords):
    lyr = QgsVectorLayer(f"Polygon?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([QgsField("name", QVariant.String)])
    lyr.updateFields()
    pts = list(coords)
    if not is_closed(pts, 2.0): pts.append(pts[0])
    f = QgsFeature()
    f.setGeometry(QgsGeometry.fromPolygonXY(
        [[QgsPointXY(c[0], c[1]) for c in pts]]))
    f.setAttributes(["outer_toe"])
    pr.addFeatures([f])
    lyr.updateExtents()
    return lyr


def _offset_ring_xy(source_ring, ref_geom, offset_dist, sp):
    """Generate a closed XY ring parallel to source_ring, offset perpendicular
    AWAY from ref_geom by offset_dist.

    Implementation: QgsGeometry.buffer applied to the polygon formed by
    source_ring. This is the same operation as the QGIS Vector Geometry
    > Offset Lines algorithm on a closed boundary, but operating on the
    POLYGON (not the open polyline) ensures the boundary is treated as
    truly closed - every corner gets the same join style, including the
    start/end vertex of the original ring. (offsetCurve on a closed
    polyline leaves a diagonal closure at the start/end vertex because
    GEOS treats it as the endpoint of an open line.)

    Direction:
        - If ref_geom lies INSIDE source_ring, "away from ref" = outward.
          Use positive buffer distance.
        - If ref_geom lies OUTSIDE source_ring, "away from ref" = inward
          (toward centroid). Use negative buffer distance.

    Used for analytical parallel offsets:
      - construct_dam_rings_from_anchor (offsets between the 4 design rings)
      - step4d artificial deep outer toe (offset of outer_crest)
      - FSL ring (offset of inner_crest inward to spillway crest elev)

    Returns a closed XY ring (list of (x, y) tuples) or None if it can't
    be built.
    """
    if not source_ring or offset_dist <= 0:
        return None
    if len(source_ring) < 3:
        return None
    ll = llen(source_ring)
    if ll < 1.0:
        return None

    # Build the source polygon
    try:
        pts = [QgsPointXY(c[0], c[1]) for c in source_ring]
        if (pts[0].x() != pts[-1].x() or pts[0].y() != pts[-1].y()):
            pts.append(pts[0])
        src_poly = QgsGeometry.fromPolygonXY([pts])
        if src_poly is None or src_poly.isEmpty():
            return None
    except Exception:
        return None

    # Determine outward / inward by sampling ref_geom against src_poly.
    # ref_geom may be a single point (e.g. anchor centroid) or a line
    # (e.g. another ring).
    ref_is_inside = False
    try:
        samples_inside = 0
        samples_total = 0
        try:
            rlen = ref_geom.length()
        except Exception:
            rlen = 0.0
        if rlen and rlen > 0:
            for frac in (0.0, 0.25, 0.5, 0.75):
                pt_geom = ref_geom.interpolate(frac * rlen)
                if pt_geom is None:
                    continue
                p = pt_geom.asPoint()
                samples_total += 1
                if src_poly.contains(QgsGeometry.fromPointXY(p)):
                    samples_inside += 1
        else:
            try:
                p = ref_geom.asPoint()
                samples_total = 1
                if src_poly.contains(QgsGeometry.fromPointXY(p)):
                    samples_inside = 1
            except Exception:
                pass
        ref_is_inside = (samples_total > 0
                         and samples_inside > samples_total / 2)
    except Exception:
        ref_is_inside = False

    # Buffer sign: positive grows polygon outward, negative shrinks
    # inward. Buffer applies the cap/join styles consistently at every
    # corner because the polygon boundary is treated as closed.
    buf_dist = +float(offset_dist) if ref_is_inside else -float(offset_dist)

    # buffer(distance, segments) - segments = number of line segments
    # per quarter circle. 16 segments gives ~5.6 degree resolution on
    # the rounded corners, plenty smooth for design figures. Round
    # joins are the QGIS default; for explicit control we'd use the
    # 5-arg overload (distance, segments, cap, join, mitre) but the
    # default suffices here.
    try:
        offset_geom = src_poly.buffer(buf_dist, 16)
    except Exception:
        offset_geom = None
    if offset_geom is None or offset_geom.isEmpty():
        return None

    # buffer returns a polygon (or multipolygon if the inward offset
    # was large enough to split the source into pieces). Take the
    # exterior ring of the largest piece.
    try:
        if offset_geom.isMultipart():
            polys = offset_geom.asMultiPolygon()
            if not polys:
                return None
            if len(polys) > 1:
                LOG.warn(
                    f"Offset by {offset_dist:.1f} m split the ring into "
                    f"{len(polys)} pieces - the dam is narrower than the "
                    f"design batters + crest width allow somewhere along "
                    f"its length. Keeping the largest piece; the inner "
                    f"rings / reservoir floor may be incomplete. Reduce the "
                    f"batter slope, crest width or depth if the DEM looks "
                    f"wrong there.")
            def _poly_area(p):
                xy = p[0]
                if len(xy) < 3:
                    return 0.0
                return abs(shoelace([(pt.x(), pt.y()) for pt in xy]))
            biggest = max(polys, key=_poly_area)
            outer = biggest[0]
        else:
            poly_data = offset_geom.asPolygon()
            if not poly_data:
                return None
            outer = poly_data[0]
        if not outer or len(outer) < 3:
            return None
        coords = [(p.x(), p.y()) for p in outer]
    except Exception:
        return None

    if len(coords) < 3:
        return None
    if coords[0] != coords[-1]:
        coords.append(coords[0])
    return coords


def _build_fsl_ring_coords(kl):
    """Build FSL ring coords (offset inward from inner crest by
    depth * inner_HV). Returns a closed XY ring, or None if spillway is
    disabled or the offset can't be built.
    """
    if not CFG.get('spillway_enabled', False):
        return None

    ic = kl['inner_crest']['coords']
    oc_g = QgsGeometry.fromPolylineXY(
        [QgsPointXY(c[0], c[1]) for c in kl['outer_crest']['coords']])

    inner_hv = CFG.get('inner_hv', 3.0)
    fsl_offset = CFG['spill_depth'] * inner_hv
    return _offset_ring_xy(ic, oc_g, fsl_offset, CFG['point_spacing'])


# =============================================================================
# PHASE 2 - ANCHOR-BASED CONSTRUCTION + SUMP FILTER
# =============================================================================

def _offset_ring_inward(source_ring, center_pt, offset_dist, sp):
    """Offset source_ring inward toward center_pt by offset_dist.

    Implementation: delegates to _offset_ring_xy with center_pt wrapped
    as a point QgsGeometry. _offset_ring_xy's direction logic checks
    whether ref_geom (the centre point) lies INSIDE source_ring; since
    center_pt IS inside source_ring by construction (it's the centroid
    or similar interior point), ref_is_inside = True, which makes
    _offset_ring_xy buffer OUTWARD by the offset distance - the opposite
    of what we want here.

    Fix: pass a point that lies OUTSIDE source_ring as the reference,
    so ref_is_inside = False and _offset_ring_xy buffers INWARD.

    Returns a closed XY ring (list of (x, y) tuples) or None.
    """
    if not source_ring or offset_dist <= 0:
        return None
    if len(source_ring) < 3:
        return None
    # Build an "outside" reference point. Use a point far outside the
    # source ring's bounding box so it's reliably classified as outside.
    xs = [c[0] for c in source_ring]
    ys = [c[1] for c in source_ring]
    far_x = max(xs) + (max(xs) - min(xs)) + 1000.0
    far_y = max(ys) + (max(ys) - min(ys)) + 1000.0
    try:
        outside_ref = QgsGeometry.fromPointXY(QgsPointXY(far_x, far_y))
    except Exception:
        outside_ref = None
    if outside_ref is None:
        return None
    # Now _offset_ring_xy will see ref_is_inside = False and buffer
    # negatively (inward) by offset_dist.
    return _offset_ring_xy(source_ring, outside_ref, offset_dist, sp)


def _pad_to_3d(coords, z=0.0):
    """Pad 2-tuple coords to 3-tuple by appending the given Z. Pass-through
    if already 3-tuple."""
    if not coords or len(coords[0]) >= 3:
        return coords
    return [(c[0], c[1], z) for c in coords]


def _ring_dict_from_xy(coords_xy, z_value, layer_name):
    """Build a ring dict (matching the format step3_classify produces) from
    a closed XY ring and a constant Z. Used to wrap constructed rings so
    they slot into the existing pipeline. Tolerant of either 2-tuple
    (x, y) or 3-tuple (x, y, z) input coords - the input Z is discarded
    in favour of z_value."""
    if not coords_xy:
        return None
    # Drop the duplicated closing vertex for consistency with step3 output
    first, last = coords_xy[0], coords_xy[-1]
    if (first[0], first[1]) == (last[0], last[1]):
        pts = coords_xy[:-1]
    else:
        pts = coords_xy[:]
    if len(pts) < 3:
        return None
    coords_xyz = [(p[0], p[1], z_value) for p in pts]
    n = len(coords_xyz)
    area = abs(sum(coords_xyz[i][0]*coords_xyz[(i+1)%n][1] -
                    coords_xyz[(i+1)%n][0]*coords_xyz[i][1]
                    for i in range(n))) / 2.0
    return {
        'coords': coords_xyz,
        'z_mean': z_value, 'z_min': z_value, 'z_max': z_value, 'z_std': 0.0,
        'area': area, 'npts': n, 'layer': layer_name,
    }


def _repair_ring(coords, label="ring"):
    """Return a simple (non-self-intersecting) closed ring for `coords`.

    A self-intersecting ring - e.g. an outer toe that zig-zagged across
    itself at a concave corner in cut_outer_toe_to_terrain - silently
    corrupts everything that consumes it as a polygon. Used as the DEM
    clip mask it punches a NoData HOLE (matplotlib/GDAL apply the even-odd
    fill rule, so the doubly-enclosed lobe is treated as OUTSIDE), and
    written as a footprint it is an invalid polygon. This repairs it with
    GEOS MakeValid (buffer(0) fallback) and returns the exterior of the
    largest resulting part. Z (3rd ordinate, if present) is preserved by
    copying it from the nearest original vertex. Already-simple rings are
    returned unchanged, so this is a cheap no-op in the common case.
    """
    if not coords or len(coords) < 4:
        return coords
    has_z = len(coords[0]) >= 3
    try:
        pts = [QgsPointXY(c[0], c[1]) for c in coords]
        if pts[0] != pts[-1]:
            pts.append(pts[0])
        poly = QgsGeometry.fromPolygonXY([pts])
    except Exception:
        return coords
    try:
        if poly is None or poly.isEmpty() or poly.isGeosValid():
            return coords  # already simple/valid - nothing to do
    except Exception:
        return coords

    rep = None
    for how in ('makeValid', 'buffer0'):
        try:
            g = poly.makeValid() if how == 'makeValid' else poly.buffer(0.0, 1)
            if g and not g.isEmpty():
                rep = g
                break
        except Exception:
            rep = None
    if rep is None:
        LOG.warn(f"{label}: self-intersecting ring could not be repaired - "
                 f"using as-is; the DEM may show a hole or spur here.")
        return coords

    try:
        if rep.isMultipart():
            parts = [p for p in rep.asMultiPolygon() if p and p[0]]
            if not parts:
                return coords
            outer = max(parts, key=lambda p: abs(
                shoelace([(q.x(), q.y()) for q in p[0]])))[0]
        else:
            pg = rep.asPolygon()
            outer = pg[0] if pg else None
        if not outer or len(outer) < 4:
            return coords
    except Exception:
        return coords

    clean_xy = [(p.x(), p.y()) for p in outer]
    if has_z:
        clean = []
        for (x, y) in clean_xy:
            bz = coords[0][2]
            bd = float('inf')
            for c in coords:
                d = (c[0] - x) ** 2 + (c[1] - y) ** 2
                if d < bd:
                    bd = d
                    bz = c[2]
            clean.append((x, y, bz))
    else:
        clean = clean_xy
    LOG.warn(f"{label}: repaired a self-intersecting ring "
             f"({len(coords)} -> {len(clean)} vertices) - it would "
             f"otherwise punch a hole in the DEM / footprint at the "
             f"crossing.")
    return clean


def construct_dam_rings_from_anchor(anchor_ring, anchor_role, params, sp=1.0):
    """Build the 4 design rings (inner_toe, inner_crest, outer_crest,
    outer_toe) analytically from one anchor ring and design parameters.

    Args:
      anchor_ring: ring dict (with 'coords' list of (x, y, z))
      anchor_role: one of 'inner_toe', 'inner_crest', 'outer_crest',
                   'outer_toe' - which role the anchor fills
      params: dict with crest_z, invert_z, outer_toe_z, crest_width,
              inner_hv, outer_hv
      sp: sampling spacing for the constructed rings (m)

    Returns:
      dict mapping each role name to a ring dict, or raises ValueError if
      the parameters are inconsistent or any offset fails.

    The anchor's XY shape is preserved and used directly (with the override
    Z). The other 3 rings are perpendicular offsets, walking outward from
    the anchor where possible, and inward where the anchor is on the
    outside of a target ring.
    """
    crest_z       = float(params['crest_z'])
    invert_z      = float(params['invert_z'])
    outer_toe_z   = float(params['outer_toe_z'])
    crest_width   = float(params['crest_width'])
    inner_hv      = float(params['inner_hv'])
    outer_hv      = float(params['outer_hv'])

    if crest_width <= 0:
        raise ValueError("crest_width must be > 0")
    if crest_z <= invert_z:
        raise ValueError(
            f"crest_z ({crest_z:.2f}) must be > invert_z ({invert_z:.2f})")
    if crest_z <= outer_toe_z:
        raise ValueError(
            f"crest_z ({crest_z:.2f}) must be > outer_toe_z "
            f"({outer_toe_z:.2f})")
    if inner_hv <= 0 or outer_hv <= 0:
        raise ValueError("inner_hv and outer_hv must be > 0")

    inner_h = inner_hv * (crest_z - invert_z)
    outer_h = outer_hv * (crest_z - outer_toe_z)

    # Diagnostic: log the exact parameters and computed offset distances
    # so unexpected output sizes can be traced back to bad inputs.
    LOG.info(f"construct_dam_rings_from_anchor: role={anchor_role}, "
             f"crest_z={crest_z:.2f}, invert_z={invert_z:.2f}, "
             f"outer_toe_z={outer_toe_z:.2f}, crest_width={crest_width:.2f}, "
             f"inner_hv={inner_hv:.2f}:1, outer_hv={outer_hv:.2f}:1")
    LOG.info(f"  computed offsets: inner_h={inner_h:.2f} m "
             f"(= {inner_hv:.2f} x ({crest_z:.2f} - {invert_z:.2f})), "
             f"outer_h={outer_h:.2f} m "
             f"(= {outer_hv:.2f} x ({crest_z:.2f} - {outer_toe_z:.2f}))")
    if inner_h > 200 or outer_h > 200:
        LOG.warn(f"  Large offset detected. If the resulting rings look "
                 f"wildly oversized, check that crest_z / invert_z / "
                 f"outer_toe_z make sense - they're often the cause of "
                 f"huge offsets when no manual override is set.")

    # Anchor XY (closed) - kept as 3-tuple with anchor's z_mean as a
    # placeholder Z so _offset_ring_xy's interp_ch (which expects 3-tuple
    # coords) works. The placeholder Z is discarded by _ring_dict_from_xy
    # which uses the design Z passed in. Outputs of _offset_ring_xy are
    # 2-tuple so we pad them via _pad_to_3d before re-feeding into another
    # _offset_ring_xy call.
    az = anchor_ring.get('z_mean', 0.0)
    anchor_xy = [(c[0], c[1], az) for c in anchor_ring['coords']]
    if (anchor_xy[0][0], anchor_xy[0][1]) != (anchor_xy[-1][0], anchor_xy[-1][1]):
        anchor_xy.append(anchor_xy[0])
    # Centroid of anchor (used as inside reference for outward offsets and
    # as the centre for inward offsets)
    cx = sum(c[0] for c in anchor_xy[:-1]) / (len(anchor_xy) - 1)
    cy = sum(c[1] for c in anchor_xy[:-1]) / (len(anchor_xy) - 1)
    centroid_geom = QgsGeometry.fromPointXY(QgsPointXY(cx, cy))
    center_pt = (cx, cy)

    out = {}

    def _check(xy, what):
        if not xy or len(xy) < 4:
            raise ValueError(f"Failed to construct {what} (offset returned "
                             f"empty/degenerate ring)")
        return xy

    if anchor_role == 'inner_toe':
        # All offsets OUTWARD from the anchor, each one with a cumulative
        # distance (no chained corner-cut: every offset starts from the
        # sharp original anchor and preserves its corner geometry).
        out['inner_toe'] = _ring_dict_from_xy(
            anchor_xy, invert_z, 'constructed_inner_toe')
        ic_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom, inner_h, sp),
            'inner_crest')
        out['inner_crest'] = _ring_dict_from_xy(
            ic_xy, crest_z, 'constructed_inner_crest')
        oc_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom,
                             inner_h + crest_width, sp),
            'outer_crest')
        out['outer_crest'] = _ring_dict_from_xy(
            oc_xy, crest_z, 'constructed_outer_crest')
        ot_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom,
                             inner_h + crest_width + outer_h, sp),
            'outer_toe')
        out['outer_toe'] = _ring_dict_from_xy(
            ot_xy, outer_toe_z, 'constructed_outer_toe')

    elif anchor_role == 'inner_crest':
        # Outward offsets from anchor by single cumulative distances;
        # inner_toe is a single inward offset from anchor.
        out['inner_crest'] = _ring_dict_from_xy(
            anchor_xy, crest_z, 'constructed_inner_crest')
        oc_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom, crest_width, sp),
            'outer_crest')
        out['outer_crest'] = _ring_dict_from_xy(
            oc_xy, crest_z, 'constructed_outer_crest')
        ot_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom,
                             crest_width + outer_h, sp),
            'outer_toe')
        out['outer_toe'] = _ring_dict_from_xy(
            ot_xy, outer_toe_z, 'constructed_outer_toe')
        it_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt, inner_h, sp),
            'inner_toe')
        out['inner_toe'] = _ring_dict_from_xy(
            it_xy, invert_z, 'constructed_inner_toe')

    elif anchor_role == 'outer_crest':
        # One outward offset (outer_toe); two inward offsets at single
        # cumulative distances from the anchor (no chaining).
        out['outer_crest'] = _ring_dict_from_xy(
            anchor_xy, crest_z, 'constructed_outer_crest')
        ot_xy = _check(
            _offset_ring_xy(anchor_xy, centroid_geom, outer_h, sp),
            'outer_toe')
        out['outer_toe'] = _ring_dict_from_xy(
            ot_xy, outer_toe_z, 'constructed_outer_toe')
        ic_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt, crest_width, sp),
            'inner_crest')
        out['inner_crest'] = _ring_dict_from_xy(
            ic_xy, crest_z, 'constructed_inner_crest')
        it_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt,
                                 crest_width + inner_h, sp),
            'inner_toe')
        out['inner_toe'] = _ring_dict_from_xy(
            it_xy, invert_z, 'constructed_inner_toe')

    elif anchor_role == 'outer_toe':
        # All inward offsets from anchor by single cumulative distances.
        out['outer_toe'] = _ring_dict_from_xy(
            anchor_xy, outer_toe_z, 'constructed_outer_toe')
        oc_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt, outer_h, sp),
            'outer_crest')
        out['outer_crest'] = _ring_dict_from_xy(
            oc_xy, crest_z, 'constructed_outer_crest')
        ic_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt,
                                 outer_h + crest_width, sp),
            'inner_crest')
        out['inner_crest'] = _ring_dict_from_xy(
            ic_xy, crest_z, 'constructed_inner_crest')
        it_xy = _check(
            _offset_ring_inward(anchor_xy, center_pt,
                                 outer_h + crest_width + inner_h, sp),
            'inner_toe')
        out['inner_toe'] = _ring_dict_from_xy(
            it_xy, invert_z, 'constructed_inner_toe')

    else:
        raise ValueError(f"Unknown anchor_role: {anchor_role}")

    # Empty batter lists for downstream compatibility (no intermediate
    # contours in constructed mode - slopes come from CFG overrides)
    out['outer_batter'] = []
    out['inner_batter'] = []

    return out


def _filter_sumps_from_const_z(cr, area_ratio_threshold=0.25,
                                bbox_inside_factor=0.9):
    """Filter interior sump rings from const-Z rings (sorted by area asc).

    The inner toe is the BASIN FLOOR = the largest-area ring in the lowest
    elevation band. A sump is a separate deeper pocket: a ring in that low
    band that is much smaller than the basin floor AND whose centroid sits
    inside the dam footprint.

    This is robust to two cases the old heuristic missed:
      - OFF-CENTRE sumps. The old test required the sump centroid inside the
        NEXT ring's shrunk bbox; a sump at the basin edge (e.g. Schouten
        Dam 03) failed it and was wrongly taken as the inner toe.
      - Mid-size rings wedged between the sump and the basin floor (e.g.
        mixed-in DTM contours), which defeated the old 'compare to the
        immediately-next ring' area test.

    Returns (filtered_cr_sorted_asc, sumps).
    """
    if len(cr) < 2:
        return list(cr), []
    z_vals = [r.get('z_mean', 0.0) for r in cr]
    z_lo, z_hi = min(z_vals), max(z_vals)
    # Low band: the sump + basin floor sit near the bottom; the crest rings
    # are well above. Generous enough to span a sump-to-basin drop.
    band = max(2.5, 0.4 * (z_hi - z_lo))
    low = [r for r in cr if r.get('z_mean', 0.0) <= z_lo + band]
    if len(low) < 2:
        return list(cr), []
    # Basin floor (the inner toe) = the largest-area ring in the low band.
    basin = max(low, key=lambda r: r.get('area', 0.0))
    # Dam footprint bbox = the largest ring overall (outer crest / toe).
    biggest = max(cr, key=lambda r: r.get('area', 0.0))
    bxs = [c[0] for c in biggest['coords']]
    bys = [c[1] for c in biggest['coords']]
    bx0, bx1 = min(bxs), max(bxs)
    by0, by1 = min(bys), max(bys)
    pad_x = (bx1 - bx0) * 0.02
    pad_y = (by1 - by0) * 0.02
    sumps_out = []
    for r in low:
        if r is basin:
            continue
        if r.get('area', 0.0) >= area_ratio_threshold * basin.get('area', 1.0):
            continue  # not much smaller than the basin -> not a sump
        sxs = [c[0] for c in r['coords']]
        sys = [c[1] for c in r['coords']]
        scx = sum(sxs) / len(sxs)
        scy = sum(sys) / len(sys)
        if (bx0 - pad_x <= scx <= bx1 + pad_x
                and by0 - pad_y <= scy <= by1 + pad_y):
            sumps_out.append(r)
    if not sumps_out:
        return list(cr), []
    sump_ids = {id(s) for s in sumps_out}
    keep = [r for r in cr if id(r) not in sump_ids]
    return keep, sumps_out


def _make_fsl_layer(name, fsl_coords, fsl_z):
    """Single closed PolygonZ feature at FSL elevation."""
    lyr = QgsVectorLayer(f"PolygonZ?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([
        QgsField("name", QVariant.String),
        QgsField("elevation", QVariant.Double),
    ])
    lyr.updateFields()

    ring = QgsLineString([QgsPoint(c[0], c[1], fsl_z) for c in fsl_coords])
    poly = QgsPolygon()
    poly.setExteriorRing(ring)

    f = QgsFeature()
    f.setGeometry(QgsGeometry(poly))
    f.setAttributes(["FSL", fsl_z])
    pr.addFeatures([f])
    lyr.updateExtents()
    return lyr


def _make_spillway_layer(name, spill_lines):
    """Spillway-layer LineStringZ. Up to 6 features:
      - outer trace (legs 5-7), Name='Spillway', part='outer'
      - inner trace (legs 1-3), Name='',         part='inner'
      - 4 lateral cross-lines that close the notch ends in plan view:
          part='batter_start' / 'batter_end' (at crest Z)
          part='flat_start'   / 'flat_end'   (at spillway flat Z)
        all with Name=''
    """
    lyr = QgsVectorLayer(f"LineStringZ?crs=EPSG:{CRS_EPSG}", name, "memory")
    pr = lyr.dataProvider()
    pr.addAttributes([
        QgsField("Name", QVariant.String),
        QgsField("part", QVariant.String),
    ])
    lyr.updateFields()

    if not spill_lines:
        return lyr

    inner_trace = spill_lines.get('inner_trace') or []
    outer_trace = spill_lines.get('outer_trace') or []
    crosslines = spill_lines.get('crosslines') or []

    def _add(feats, trace, name_attr, part):
        if not trace or len(trace) < 2:
            return
        pts3d = [QgsPoint(p[0], p[1], p[2]) for p in trace]
        ls = QgsLineString(pts3d)
        f = QgsFeature()
        f.setGeometry(QgsGeometry(ls))
        f.setAttributes([name_attr, part])
        feats.append(f)

    feats = []
    # Main perimeter traces - outer carries the "Spillway" label
    _add(feats, outer_trace, "Spillway", "outer")
    _add(feats, inner_trace, "",         "inner")
    # Lateral cross-lines closing each end of the notch
    for part, trace in crosslines:
        _add(feats, trace, "", part)

    pr.addFeatures(feats)
    lyr.updateExtents()
    return lyr


def _apply_solid_line_style(layer, color="black", width_mm=0.4):
    """Render a vector line layer as a single solid colored line."""
    try:
        sym = QgsLineSymbol.createSimple({
            'color': color,
            'width': str(width_mm),
            'capstyle': 'round',
            'joinstyle': 'round',
        })
        layer.setRenderer(QgsSingleSymbolRenderer(sym))
        layer.triggerRepaint()
    except Exception as e:
        LOG.warn(f"Line style failed for {layer.name()}: {e}")


def _apply_fill_style(layer, fill_rgba, outline_rgba, outline_width_mm=0.3):
    """Render a polygon layer as a single solid fill with an outline.
    Colors are 'r,g,b,a' strings (a in 0-255)."""
    try:
        sym = QgsFillSymbol.createSimple({
            'color': fill_rgba,
            'outline_color': outline_rgba,
            'outline_width': str(outline_width_mm),
            'style': 'solid',
        })
        layer.setRenderer(QgsSingleSymbolRenderer(sym))
        layer.triggerRepaint()
    except Exception as e:
        LOG.warn(f"Fill style failed for {layer.name()}: {e}")


def _apply_curved_label(layer, field="Name", size_pt=14,
                        text_color="black", buffer_color="white",
                        buffer_size=1.0, line_placement="below"):
    """Enable curved labels along line features, using `field`. Features
    with empty/NULL values are not labeled (handled by a Show data-defined
    expression).

    line_placement controls which side of the line the label sits on:
      'below' - below the line (relative to the line's digitising
                direction). For a closed ring digitised clockwise, this
                puts the label on the OUTSIDE of the dam; for a counter-
                clockwise ring it's the inside. The dam name should trace
                the perimeter on the outside, so we also set the
                'on line' fallback flag off and let QGIS pick the below
                side. If the ring winds the other way the label lands
                inside - acceptable, and avoids per-ring winding logic.
      'on'    - centred on the line (the previous behaviour).
      'above' - above the line.
    """
    try:
        text_format = QgsTextFormat()
        text_format.setFont(QFont("Arial"))
        text_format.setSize(size_pt)
        text_format.setColor(QColor(text_color))

        buf = QgsTextBufferSettings()
        buf.setEnabled(True)
        buf.setSize(buffer_size)
        buf.setColor(QColor(buffer_color))
        text_format.setBuffer(buf)

        settings = QgsPalLayerSettings()
        settings.fieldName = field
        # Curved placement along line geometries (works for QGIS 3.x)
        try:
            settings.placement = QgsPalLayerSettings.Curved
        except AttributeError:
            try:
                settings.placement = QgsPalLayerSettings.Placement.Curved
            except AttributeError:
                pass

        # Line-placement side: above / on / below the line. For curved
        # labels QGIS uses QgsLabeling.LinePlacementFlags via the line
        # settings object. "Below line" traces the label on one side of
        # the perimeter (outside the dam for a clockwise ring), which
        # reads better on report figures than an on-line label that the
        # line cuts through.
        try:
            from qgis.core import QgsLabeling
            flag_map = {
                'below': QgsLabeling.LinePlacementFlag.BelowLine,
                'above': QgsLabeling.LinePlacementFlag.AboveLine,
                'on':    QgsLabeling.LinePlacementFlag.OnLine,
            }
            flag = flag_map.get(line_placement,
                                 QgsLabeling.LinePlacementFlag.BelowLine)
            # MapOrientation keeps "below" meaning below in map space
            # (consistent side) rather than flipping with text direction.
            flag = flag | QgsLabeling.LinePlacementFlag.MapOrientation
            ls = settings.lineSettings()
            ls.setPlacementFlags(flag)
            settings.setLineSettings(ls)
        except Exception as e:
            # Older QGIS: enum path differs; try the legacy flat enums.
            try:
                from qgis.core import QgsLabeling as _QL
                ls = settings.lineSettings()
                legacy = {
                    'below': _QL.LinePlacementFlags(_QL.BelowLine),
                    'above': _QL.LinePlacementFlags(_QL.AboveLine),
                    'on':    _QL.LinePlacementFlags(_QL.OnLine),
                }.get(line_placement)
                if legacy is not None:
                    ls.setPlacementFlags(legacy)
                    settings.setLineSettings(ls)
            except Exception:
                pass  # fall back to default on-line placement

        settings.setFormat(text_format)

        # Only label features whose `field` has a non-empty value
        try:
            settings.dataDefinedProperties().setProperty(
                QgsPalLayerSettings.Show,
                QgsProperty.fromExpression(
                    f'"{field}" IS NOT NULL AND "{field}" != \'\''))
        except Exception:
            pass  # if Show enum unavailable, fall back to default behaviour

        layer.setLabeling(QgsVectorLayerSimpleLabeling(settings))
        layer.setLabelsEnabled(True)
        layer.triggerRepaint()
    except Exception as e:
        LOG.warn(f"Label setup failed for {layer.name()}: {e}")


def _save_layer_style(layer, filename):
    """Persist the layer's style to a sidecar QML file next to the GPKG so
    the styling reloads automatically when QGIS opens the project later."""
    try:
        qml_path = os.path.join(
            CFG['output_dir'],
            os.path.splitext(filename)[0] + ".qml")
        layer.saveNamedStyle(qml_path)
        LOG.detail(f"Style saved: {qml_path}")
    except Exception as e:
        LOG.warn(f"QML style save failed for {filename}: {e}")


def _save_gpkg(layer, filename):
    """Save to GeoPackage and return the file-based layer."""
    fp = os.path.join(CFG['output_dir'], filename)
    opts = QgsVectorFileWriter.SaveVectorOptions()
    opts.driverName = "GPKG"
    err = QgsVectorFileWriter.writeAsVectorFormatV3(
        layer, fp, QgsProject.instance().transformContext(), opts)
    if err[0] != QgsVectorFileWriter.NoError:
        raise IOError(f"Failed to save {filename}: {err[1]}")
    LOG.detail(f"Saved: {fp}")

    # Reload as file-based layer (persists across sessions)
    file_layer = QgsVectorLayer(fp, layer.name(), "ogr")
    if not file_layer.isValid():
        LOG.warn(f"Could not reload {filename} as file layer. "
                 f"Using memory layer instead.")
        return layer
    return file_layer


def _save_csv(points, filename):
    fp = os.path.join(CFG['output_dir'], filename)
    with open(fp, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(["point_id", "easting_nztm", "northing_nztm",
                     "elevation_nzvd2016", "source"])
        for i, (x, y, z, s) in enumerate(points):
            w.writerow([i, f"{x:.4f}", f"{y:.4f}", f"{z:.4f}", s])
    LOG.detail(f"Saved: {fp}")
    return fp


def _save_rings_csv(points, filename):
    """Save rings CSV with blank line separators between each ring."""
    fp = os.path.join(CFG['output_dir'], filename)
    with open(fp, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(["point_id", "easting_nztm", "northing_nztm",
                     "elevation_nzvd2016", "ring"])
        prev_src = None
        pid = 0
        for x, y, z, s in points:
            if prev_src is not None and s != prev_src:
                w.writerow([])  # blank separator between rings
            w.writerow([pid, f"{x:.4f}", f"{y:.4f}", f"{z:.4f}", s])
            prev_src = s
            pid += 1
    LOG.detail(f"Saved: {fp}")
    return fp


def cut_outer_toe_to_terrain(kl, terrain_layer, params=None,
                              step=None, max_walk=None,
                              ring_to_terrain_offset=0.0):
    """Replace kl['outer_toe'] with a variable-Z polyline that traces
    where the outer batter intersects natural terrain. Used by the
    "Cut to terrain" button in DXF + anchor and Polygon modes (where
    the constructed outer toe is const-Z by design - artificially deep
    in polygon mode, or a const-Z parallel offset in DXF + anchor).

    DATUM HANDLING: rings and terrain may live in different vertical
    datums. The kl rings may be in DXF datum (preview-time, before
    z_offset is applied), while the terrain raster is in NZVD2016.
    `ring_to_terrain_offset` is the value to ADD to a ring-datum Z to
    convert it to terrain-datum Z (i.e. ring_z + offset = terrain_z).
    For preview-time DXF+anchor cut against NZVD2016 terrain, this is
    CFG['z_offset']. After Run has shifted everything to NZVD2016, it
    is 0 (the default).

    Algorithm (vertex-wise ray-cast, no raster build needed):
        For each vertex V on the outer_crest ring:
            Find outward perpendicular direction at V (away from inner
            crest, using V's local crest tangent)
            Walk outward in steps of `step` metres
            At step k, compute design batter Z = crest_z - k*step / outer_HV
            (all in RING datum)
            Sample terrain Z at the walked XY (in terrain datum)
            Convert terrain Z to ring datum: tz - ring_to_terrain_offset
            When tz_ring >= batter_z, intersection found
            Use linear interp between previous and current step for exact Z
        Connect intersections into a closed polyline - the var-Z outer toe.

    The stored Z values are in RING datum, so downstream code (the long
    section that adds z_offset for display, _apply_z_offset_to_kl, etc)
    behaves consistently.

    Modifies kl in place: replaces kl['outer_toe']['coords'] with the
    new (x, y, z) tuples, updates z_min/z_max/z_mean/z_std/npts, sets
    is_variable_z = True, and records ['nominal_const_z'] = the old
    z_mean so the long section can still draw the design ring as a
    dashed reference if desired.

    Returns the modified kl (also modifies in place).
    """
    if terrain_layer is None:
        LOG.warn("cut_outer_toe_to_terrain: no terrain raster provided.")
        return kl
    oc = kl.get('outer_crest')
    if oc is None or not oc.get('coords'):
        LOG.warn("cut_outer_toe_to_terrain: no outer_crest in kl.")
        return kl
    ot = kl.get('outer_toe')
    if ot is None:
        LOG.warn("cut_outer_toe_to_terrain: no outer_toe in kl.")
        return kl
    ic = kl.get('inner_crest')

    params = params or {}
    outer_hv = float(params.get('outer_hv', CFG.get('outer_hv', 3.0)))
    crest_z = float(params.get('crest_z', oc['z_mean']))
    if outer_hv <= 0:
        LOG.warn(f"cut_outer_toe_to_terrain: outer_hv = {outer_hv} not "
                 f"positive; cannot walk batter.")
        return kl

    step = float(step) if step else max(0.2, CFG.get('point_spacing', 1.0))
    # Maximum distance to walk before declaring no intersection
    if max_walk is None:
        # Cover crest-to-toe drop plus a generous skirt for low ground
        height = crest_z - float(ot.get('z_mean', crest_z))
        max_walk = max(50.0, abs(height) * outer_hv * 1.5)

    try:
        dp = terrain_layer.dataProvider()
    except Exception:
        LOG.warn("cut_outer_toe_to_terrain: terrain layer has no data "
                 "provider.")
        return kl

    oc_coords = oc['coords']
    n_oc = len(oc_coords)

    # Compute centroid of outer_crest. This is the SOURCE OF TRUTH for
    # "outward" - walking outward = away from this centroid. Using the
    # outer_crest's own centroid (not inner_crest) avoids edge cases
    # where the inner_crest is degenerate or weirdly positioned relative
    # to outer_crest (which we've seen in some DXF + anchor constructions
    # where the inner_crest is built by inward offset and ends up very
    # close to outer_crest).
    ccx = sum(c[0] for c in oc_coords) / n_oc
    ccy = sum(c[1] for c in oc_coords) / n_oc

    LOG.start_step("Cutting outer toe to terrain")
    LOG.info(f"outer_crest: {n_oc} vertices, "
             f"centroid=({ccx:.2f}, {ccy:.2f})")
    LOG.info(f"crest_z={crest_z:.3f} (ring datum), outer_hv={outer_hv:.2f}, "
             f"step={step:.2f} m, max_walk={max_walk:.0f} m, "
             f"ring_to_terrain_offset={ring_to_terrain_offset:.3f} m")
    # Sample terrain at the centroid as a sanity check
    try:
        res_c = dp.sample(QgsPointXY(ccx, ccy), 1)
        if res_c is not None:
            gz_c, ok_c = res_c
            if ok_c and gz_c is not None:
                tz_c_ring = float(gz_c) - ring_to_terrain_offset
                LOG.info(f"  terrain at centroid: {float(gz_c):.2f} m "
                         f"(terrain datum) = {tz_c_ring:.2f} m (ring datum)")
                if tz_c_ring >= crest_z:
                    LOG.warn(f"  WARNING: terrain at centroid ({tz_c_ring:.2f}) "
                             f"is >= crest_z ({crest_z:.2f}). Cut will find "
                             f"intersection immediately at outer_crest. Check "
                             f"that crest_z is correct in ring datum and that "
                             f"the terrain raster is what you expect (not a "
                             f"DSM that includes the existing dam).")
    except Exception:
        pass

    # Track diagnostics across all vertices to summarise at the end
    diag_walks = []  # list of distances walked at intersection
    new_toe = []
    n_hits = 0
    n_misses = 0
    for k in range(n_oc):
        x, y = oc_coords[k][0], oc_coords[k][1]
        # Local tangent: midpoint of adjacent segments
        prev_idx = (k - 1) % n_oc
        next_idx = (k + 1) % n_oc
        tx = oc_coords[next_idx][0] - oc_coords[prev_idx][0]
        ty = oc_coords[next_idx][1] - oc_coords[prev_idx][1]
        tlen = math.hypot(tx, ty)
        if tlen < 1e-6:
            # Degenerate - skip this vertex
            continue
        # Perpendicular candidates
        n1x, n1y = -ty / tlen,  tx / tlen
        n2x, n2y =  ty / tlen, -tx / tlen
        # Choose the one pointing AWAY from OUTER_CREST centroid. The
        # outer_crest is a closed ring around the dam, so its own
        # centroid is reliably "inside" the dam, and "outward" = away
        # from this centroid. Previous logic used inner_crest as the
        # reference, which can be unreliable when inner_crest is built
        # by inward offset from outer_crest (it ends up very close to
        # outer_crest in DXF+anchor mode with outer_crest as anchor).
        dot1 = (ccx - x) * n1x + (ccy - y) * n1y
        if dot1 < 0:
            nx, ny = n1x, n1y
        else:
            nx, ny = n2x, n2y
        # Walk outward
        prev_dz = None  # batter_z - terrain_z_in_ring_datum, previous step
        prev_walk = 0.0
        hit = None
        walked = step
        # Initial check at walked=0: is crest already underwater (i.e.
        # terrain at outer_crest is at or above design crest)? If yes,
        # the design dam is fictional at this vertex - the algorithm
        # would hit at walked=0 and we'd put the toe directly under the
        # crest. That's the user's complaint. Detect explicitly.
        try:
            res0 = dp.sample(QgsPointXY(x, y), 1)
            if res0 is not None:
                gz0, ok0 = res0
                if ok0 and gz0 is not None:
                    tz0 = float(gz0) - ring_to_terrain_offset
                    if tz0 >= crest_z - 1e-6:
                        # Crest is at or below terrain at this vertex.
                        # The dam doesn't physically project above
                        # terrain here, so there's no batter to cut.
                        # Leave this vertex as a "no hit" so the polyline
                        # falls back to the original outer toe vertex.
                        n_misses += 1
                        old_ot = ot['coords']
                        if old_ot:
                            best_d2 = float('inf'); fx, fy, fz = x, y, ot.get('z_mean', 0)
                            for c in old_ot:
                                d2 = (c[0]-x)**2 + (c[1]-y)**2
                                if d2 < best_d2:
                                    best_d2 = d2; fx, fy = c[0], c[1]
                                    fz = c[2] if len(c) >= 3 else ot.get('z_mean', 0)
                            new_toe.append((fx, fy, fz))
                        else:
                            new_toe.append((x, y, ot.get('z_mean', 0)))
                        continue
        except Exception:
            pass

        while walked <= max_walk:
            wx = x + nx * walked
            wy = y + ny * walked
            batter_z = crest_z - walked / outer_hv  # ring datum
            try:
                res = dp.sample(QgsPointXY(wx, wy), 1)
                if res is None:
                    walked += step; continue
                gz, ok = res
                if not ok or gz is None:
                    walked += step; continue
                # Convert terrain sample from terrain datum to ring datum
                tz = float(gz) - ring_to_terrain_offset
            except Exception:
                walked += step; continue
            dz = batter_z - tz
            if dz <= 0:
                # Intersection found between prev_walk and walked
                if prev_dz is not None and prev_dz > 0:
                    # Linear interp to dz = 0
                    frac = prev_dz / (prev_dz - dz)
                    int_walk = prev_walk + frac * (walked - prev_walk)
                else:
                    # First step already negative - cut is right at the
                    # crest. Means the crest is essentially at terrain
                    # level. Use walked=0 so the toe sits at the crest's
                    # XY (which is the physical truth).
                    int_walk = 0.0
                int_x = x + nx * int_walk
                int_y = y + ny * int_walk
                int_z = crest_z - int_walk / outer_hv  # ring datum
                # The Z should equal terrain Z (in ring datum); resample
                # for accuracy.
                try:
                    res2 = dp.sample(QgsPointXY(int_x, int_y), 1)
                    if res2 is not None:
                        gz2, ok2 = res2
                        if ok2 and gz2 is not None:
                            int_z = float(gz2) - ring_to_terrain_offset
                except Exception:
                    pass
                hit = (int_x, int_y, int_z)
                diag_walks.append(int_walk)
                break
            prev_dz = dz
            prev_walk = walked
            walked += step

        if hit is None:
            n_misses += 1
            # Fall back to the original outer toe vertex (artificial deep)
            # so the polyline still closes
            old_ot = ot['coords']
            # Try to find the closest old outer toe vertex
            if old_ot:
                best_d2 = float('inf'); fx, fy, fz = x, y, ot['z_mean']
                for c in old_ot:
                    d2 = (c[0]-x)**2 + (c[1]-y)**2
                    if d2 < best_d2:
                        best_d2 = d2; fx, fy = c[0], c[1]
                        fz = c[2] if len(c) >= 3 else ot['z_mean']
                new_toe.append((fx, fy, fz))
            else:
                new_toe.append((x, y, ot['z_mean']))
        else:
            n_hits += 1
            new_toe.append(hit)

    if n_hits == 0:
        LOG.warn(f"cut_outer_toe_to_terrain: no intersections found "
                 f"({n_misses} misses). Outer toe unchanged.")
        return kl

    # Close the ring
    if new_toe[0] != new_toe[-1]:
        new_toe.append(new_toe[0])

    # The vertex-wise ray-cast above walks each outer_crest vertex outward
    # independently; at concave corners (or where some vertices hit near
    # the crest while neighbours miss and snap back to the artificial-deep
    # toe) adjacent toe points cross, leaving a self-intersecting "bowtie".
    # Repair it here at the source so the footprint, long section and DEM
    # clip all get a simple ring. Z is preserved by nearest-vertex remap.
    new_toe = _repair_ring(new_toe, "outer toe (cut to terrain)")

    zs_new = [c[2] for c in new_toe]
    z_min_new, z_max_new = min(zs_new), max(zs_new)
    z_mean_new = sum(zs_new) / len(zs_new)
    z_std_new = (sum((z - z_mean_new) ** 2 for z in zs_new)
                 / len(zs_new)) ** 0.5
    # Mutate in place. Aliasing risk with outer_batter[-1] is handled
    # at the source (step4_identify shallow-copies that reference).
    # Stash const-Z reference on first promotion only.
    if 'nominal_const_z' not in ot or not ot.get('nominal_const_coords'):
        ot['nominal_const_z'] = ot.get('z_mean')
        ot['nominal_const_coords'] = [(c[0], c[1], c[2])
                                       for c in (ot.get('coords') or [])
                                       if len(c) >= 3]
    ot['coords'] = new_toe
    ot['z_min'] = z_min_new
    ot['z_max'] = z_max_new
    ot['z_mean'] = z_mean_new
    ot['z_std'] = z_std_new
    ot['npts'] = len(new_toe)
    ot['is_variable_z'] = True
    ot['cut_to_terrain'] = True
    LOG.success(f"Outer toe cut to terrain: {n_hits} intersections, "
                f"{n_misses} misses. Z range "
                f"{z_min_new:.2f} - {z_max_new:.2f} m.")
    # Walk-distance diagnostics. If most walks were ~0 m, the cut put
    # the toe right under the crest - usually because the terrain at
    # the outer crest is already AT or ABOVE the design crest level.
    # Common causes: wrong crest_z, wrong z_offset / datum, or a
    # terrain raster that includes the existing built dam (so LiDAR
    # samples land on the dam surface rather than virgin ground).
    if diag_walks:
        mean_walk = sum(diag_walks) / len(diag_walks)
        max_walk_seen = max(diag_walks)
        n_tiny = sum(1 for w in diag_walks if w < 0.5)
        LOG.info(f"Walk distances: mean {mean_walk:.2f} m, "
                 f"max {max_walk_seen:.2f} m. {n_tiny}/{len(diag_walks)} "
                 f"hits were < 0.5 m outward.")
        if mean_walk < 1.0 and n_hits > 0:
            LOG.warn("DEGENERATE CUT: most intersections were found <1 m "
                     "outward from the outer_crest. The variable-Z outer "
                     "toe will sit nearly directly under the outer crest "
                     "(near-vertical batter). Likely causes:")
            LOG.warn("  1. The terrain raster includes the existing dam "
                     "(LiDAR DSM, not bare-earth). LiDAR samples the dam "
                     "surface, which already follows the design batter, "
                     "so the cut hits at walked=0.")
            LOG.warn("  2. crest_z is wrong in ring datum. Check the "
                     "build-up panel's crest_z value matches the constructed "
                     "outer_crest ring elevation.")
            LOG.warn("  3. The z_offset is wrong, so ring-datum batter Z "
                     "is being compared to mis-converted terrain Z.")
            LOG.warn("Workarounds: use DXF auto mode (Method 1) which "
                     "derives variable-Z toe from partial contour endpoints; "
                     "or load a bare-earth DEM that excludes the existing "
                     "dam structure.")
    return kl


def _generate_rings_csv(kl, spill_outline=None, gap_info=None):
    """Generate the clean DESIGN rings for dam_rings.csv:
      - outer_toe (constant-Z; the artificially low ring in polygon mode,
        or a parallel offset of outer_crest at CFG['toe_low'] in DXF /
        anchor mode)
      - outer_crest (full closed ring at crest_z, NO spillway gap)
      - inner_crest (full closed ring at crest_z, NO spillway gap)
      - inner_toe (closed ring at invert_z)

    The as-built / spillway-cut / variable-Z view of the same geometry
    is captured in dam_elevation_points.csv (the full point cloud with
    spillway notch points and breaklines). This rings CSV is a clean
    four-ring representation suitable for a downstream dam-design tool
    that wants a parallel-offset description of the embankment.

    In polygon mode kl['outer_toe'] is already the const-Z artificial
    deep ring built by construct_dam_rings_from_anchor, so we use it
    directly. In DXF / anchor mode kl['outer_toe'] is typically a
    variable-Z polyline; we synthesise a constant-Z outer_toe by
    parallel offset of outer_crest at offset = outer_HV * (crest - toe_low).

    The spill_outline and gap_info arguments are accepted for signature
    compatibility but ignored - this CSV deliberately does NOT include
    the spillway cut or FSL ring.
    """
    CRE = CFG['crest']
    INV = CFG['invert']
    sp = CFG['point_spacing']
    pts = []

    # ---- outer_toe (constant-Z) -----------------------------------
    polygon_mode = bool(CFG.get('polygon_mode'))
    if polygon_mode:
        # construct_dam_rings_from_anchor already produced the artificial
        # const-Z ring. If cut-to-terrain has subsequently replaced
        # kl['outer_toe'] with a variable-Z polyline, the saved nominal
        # const-Z reference is still available - use it so the rings
        # file remains a clean const-Z "perfect geometry" file. The
        # variable-Z toe lives in the points CSV via step5_points.
        if kl['outer_toe'].get('nominal_const_coords'):
            ot_coords = kl['outer_toe']['nominal_const_coords']
            ot_z = kl['outer_toe'].get('nominal_const_z',
                                       kl['outer_toe']['z_mean'])
            LOG.detail("design outer_toe (polygon mode, using saved "
                       "nominal_const_coords - cut-to-terrain has run)")
        else:
            ot_coords = kl['outer_toe']['coords']
            ot_z = kl['outer_toe']['z_mean']
        d = densify(ot_coords, sp)
        # densify preserves the input Z; force to z_mean for cleanliness
        pts.extend([(c[0], c[1], ot_z, "outer_toe") for c in d])
        LOG.detail(f"design outer_toe (polygon mode, const-Z artificial): "
                   f"Z={ot_z:.2f}, {len(d)} pts")
    else:
        oc_coords = kl['outer_crest']['coords']
        ic_coords = kl['inner_crest']['coords']
        outer_hv = CFG.get('outer_hv', 3.0)
        toe_z = CFG['toe_low']
        height = CRE - toe_z
        if height > 0 and outer_hv > 0:
            ic_g = QgsGeometry.fromPolylineXY(
                [QgsPointXY(c[0], c[1]) for c in ic_coords])
            outer_offset = outer_hv * height
            ot_xy = _offset_ring_xy(oc_coords, ic_g, outer_offset, sp)
            if ot_xy:
                ring_xy = (ot_xy[:-1] if len(ot_xy) > 1
                                       and ot_xy[0] == ot_xy[-1]
                           else ot_xy)
                pts.extend([(x, y, toe_z, "outer_toe") for (x, y) in ring_xy])
                LOG.detail(f"design outer_toe (DXF mode, const-Z parallel "
                           f"offset): Z={toe_z:.2f}, "
                           f"offset={outer_offset:.2f} m, "
                           f"{len(ring_xy)} pts")
            else:
                LOG.warn("design outer_toe: parallel-offset construction "
                         "failed; falling back to as-built outer_toe")
                d = densify(kl['outer_toe']['coords'], sp)
                pts.extend([(c[0], c[1], c[2], "outer_toe") for c in d])
        else:
            LOG.warn(f"design outer_toe: skipped (height = {height:.2f} m, "
                     f"outer_hv = {outer_hv})")

    # ---- outer_crest (full closed, NO spillway gap) ---------------
    d = densify(kl['outer_crest']['coords'], sp)
    pts.extend([(c[0], c[1], CRE, "outer_crest") for c in d])

    # ---- inner_crest (full closed, NO spillway gap) ---------------
    d = densify(kl['inner_crest']['coords'], sp)
    pts.extend([(c[0], c[1], CRE, "inner_crest") for c in d])

    # ---- inner_toe (closed at invert) -----------------------------
    d = densify(kl['inner_toe']['coords'], sp)
    pts.extend([(c[0], c[1], INV, "inner_toe") for c in d])

    # ---- FSL ring (closed, at Full Supply Level = crest - spill_depth) ---
    # FSL is the reservoir water surface at full supply level - by
    # convention always equal to the spillway crest elevation. The
    # ring is offset inward from inner_crest by spill_depth * inner_HV
    # (same construction as the inner-batter contour at that Z). Only
    # included when a spillway is defined; without one there's no FSL.
    if CFG.get('spillway_enabled', False):
        try:
            fsl_coords = _build_fsl_ring_coords(kl)
            if fsl_coords:
                fsl_z = CRE - CFG['spill_depth']
                # _build_fsl_ring_coords returns (x, y) pairs; the ring
                # may or may not be closed at the last vertex.
                ring_xy = (fsl_coords[:-1]
                           if len(fsl_coords) > 1
                              and fsl_coords[0] == fsl_coords[-1]
                           else fsl_coords)
                d = densify([(x, y, fsl_z) for x, y in ring_xy], sp)
                pts.extend([(c[0], c[1], fsl_z, "fsl") for c in d])
                LOG.detail(f"FSL ring: Z={fsl_z:.2f}, {len(d)} pts")
            else:
                LOG.detail("FSL ring: skipped (could not build)")
        except Exception as e:
            LOG.warn(f"FSL ring CSV export failed: {e}")

    return pts


def step7_outputs(kl, all_pts, spill_bls, spill_outline,
                  spill_lines=None, gap_info=None):
    LOG.start_step("Writing outputs")

    out = CFG['output_dir']

    # AUTO-APPLY METHOD 2 if the outer toe is still in its as-constructed
    # const-Z state (Method 2 never run manually). Without this, the
    # outputs (dam_key_lines.gpkg outer_toe ring, outer_toe_footprint.gpkg,
    # DEM clip mask) all use the artificial deep polygon - a parallel
    # offset of outer_crest at design slope that sits 15+ m below
    # natural ground and extends well beyond where the dam actually meets
    # ground. The user sees a "wacked out" outer toe footprint in their
    # QGIS project that doesn't match the visible dam shape at all.
    # Running cut_outer_toe_to_terrain here clips back to the actual
    # dam-meets-ground line so the outputs are sensible. Preview state
    # in the dialog is unaffected.
    ot = kl.get('outer_toe', {}) or {}
    is_artificial = (
        not ot.get('is_variable_z')
        and not ot.get('cut_to_terrain')
        and (ot.get('z_std') or 0.0) < 0.01)
    tid = CFG.get('terrain_layer_id') or CFG.get('drape_terrain_id')
    if is_artificial and tid:
        terrain_layer = QgsProject.instance().mapLayer(tid)
        if terrain_layer is not None:
            try:
                LOG.info("Outer toe is still const-Z (Method 2 not run "
                         "manually). Auto-running cut-to-terrain so the "
                         "outputs reflect the actual dam-meets-ground "
                         "line, not the artificial deep design polygon.")
                cut_outer_toe_to_terrain(
                    kl, terrain_layer,
                    params={
                        'crest_z': float(kl['outer_crest']['z_mean']),
                        'outer_hv': float(CFG.get('outer_hv', 3.0)),
                    },
                    ring_to_terrain_offset=0.0)
                LOG.success(
                    f"Auto Method 2: outer toe now variable-Z "
                    f"({kl['outer_toe'].get('npts', 0)} pts, "
                    f"Z {kl['outer_toe'].get('z_min', 0):.2f}\u2013"
                    f"{kl['outer_toe'].get('z_max', 0):.2f} m).")
            except Exception as e:
                LOG.warn(f"Auto Method 2 cut-to-terrain failed: {e}. "
                         f"Outputs will use the artificial deep polygon.")
                import traceback as _tb
                _tb.print_exc()
    elif is_artificial and not tid:
        LOG.warn("Outer toe is still const-Z (artificial deep) and no "
                 "terrain raster is loaded. The outer_toe_footprint and "
                 "DEM clip will use the artificial deep polygon, which "
                 "extends well beyond the actual dam-meets-ground line. "
                 "Load a terrain raster and re-run for a proper clip.")

    # Key lines (4 features: inner_toe, outer_toe, inner_crest, outer_crest;
    # crests are gapped at the spillway when spillway is enabled)
    # Styled black; outer_toe carries CFG['dam_name'] and gets a curved label.
    try:
        ll = _make_line_layer(_layer_name("Key Lines"), kl, gap_info=gap_info)
        ll_file = _save_gpkg(ll, "dam_key_lines.gpkg")
        _apply_solid_line_style(ll_file, color="black", width_mm=0.4)
        _apply_curved_label(ll_file, field="Name", size_pt=14,
                             line_placement="below")
        _save_layer_style(ll_file, "dam_key_lines.gpkg")
        QgsProject.instance().addMapLayer(ll_file)
        LOG.info(f"Dam Key Lines -> project (label: \"{CFG.get('dam_name')}\")")
    except Exception as e:
        LOG.error(f"Key lines output failed: {e}")

    # FSL polygon (closed PolygonZ at FSL elevation)
    # Styled fill #41b9ff @ 50% opacity (RGBA 65,185,255,128)
    if CFG.get('spillway_enabled', False):
        try:
            fsl_coords = _build_fsl_ring_coords(kl)
            if fsl_coords:
                fsl_z = CFG['crest'] - CFG['spill_depth']
                fl = _make_fsl_layer(_layer_name("FSL"), fsl_coords, fsl_z)
                fl_file = _save_gpkg(fl, "dam_fsl.gpkg")
                _apply_fill_style(
                    fl_file,
                    fill_rgba="65,185,255,128",     # #41b9ff @ 50%
                    outline_rgba="65,185,255,255",  # #41b9ff solid
                    outline_width_mm=0.3)
                _save_layer_style(fl_file, "dam_fsl.gpkg")
                QgsProject.instance().addMapLayer(fl_file)
                LOG.info(f"Dam FSL polygon -> project (Z={fsl_z:.2f})")
            else:
                LOG.warn("FSL polygon skipped (could not build ring)")
        except Exception as e:
            LOG.error(f"FSL polygon output failed: {e}")

    # Spillway lines: outer perimeter (Name="Spillway"), inner perimeter,
    # and 4 lateral cross-lines closing the notch ends.
    # Styled black; outer trace gets a curved "Spillway" label.
    if CFG.get('spillway_enabled', False) and spill_lines:
        try:
            sp_lyr = _make_spillway_layer(_layer_name("Spillway"), spill_lines)
            sp_file = _save_gpkg(sp_lyr, "dam_spillway.gpkg")
            _apply_solid_line_style(sp_file, color="black", width_mm=0.4)
            _apply_curved_label(sp_file, field="Name", size_pt=14)
            _save_layer_style(sp_file, "dam_spillway.gpkg")
            QgsProject.instance().addMapLayer(sp_file)
            LOG.info(f"Dam Spillway lines -> project "
                     f"({sp_lyr.featureCount()} features)")
        except Exception as e:
            LOG.error(f"Spillway lines output failed: {e}")

    # Points (GPKG)
    try:
        pl = _make_pt_layer(_layer_name("Elevation Points"), all_pts)
        pl_file = _save_gpkg(pl, "dam_elevation_points.gpkg")
        QgsProject.instance().addMapLayer(pl_file)
        LOG.info(f"Elevation Points -> project ({len(all_pts)} pts)")
    except Exception as e:
        LOG.error(f"Points GPKG output failed: {e}")

    # Points (CSV) - all elevation points. The CSV gets the
    # VARIABLE-Z outer toe (the actual dam-meets-ground line, for the
    # downstream design app which uses per-vertex Z for per-chainage
    # embankment height). The TIN (built below) keeps the CONST-Z
    # outer toe from all_pts to avoid TIN artifacts. So we build a
    # CSV-specific copy here.
    if CFG['export_csv']:
        try:
            # Start with the const-Z points but strip the const-Z
            # outer_toe rows; re-append from kl['outer_toe']['coords']
            # which carries per-vertex variable Z if step4c
            # (partial contours) or cut_outer_toe_to_terrain has run.
            ot = kl.get('outer_toe', {})
            if ot.get('is_variable_z') and ot.get('coords'):
                csv_pts = [p for p in all_pts if p[3] != "outer_toe"]
                # Densify the variable-Z outer toe at the same point
                # spacing as the rest of the points.
                sp = CFG.get('point_spacing', 1.0)
                d = densify(ot['coords'], sp)
                csv_pts.extend([(c[0], c[1], c[2], "outer_toe") for c in d])
                LOG.info(f"CSV outer_toe replaced with variable-Z polyline: "
                         f"{len(d)} pts, Z range "
                         f"{ot.get('z_min', 0):.2f}-"
                         f"{ot.get('z_max', 0):.2f} m")
            else:
                csv_pts = list(all_pts)
                LOG.info("CSV outer_toe kept const-Z (no variable-Z source "
                         "available: step4c found no partial contours, and "
                         "cut-to-terrain not run)")
            csv_path = _save_csv(csv_pts, "dam_elevation_points.csv")
            LOG.info(f"CSV exported: {os.path.basename(csv_path)}")
        except Exception as e:
            LOG.error(f"CSV export failed: {e}")
            import traceback as tb_mod; tb_mod.print_exc()

        # Rings CSV - the 4 clean DESIGN rings: const-Z outer_toe at
        # CFG['toe_low'] = min(z) on the variable outer toe (set by
        # step4 auto-elev), plus the 3 other rings closed, no spillway
        # gap. The as-built / spillway-cut view of the same data lives
        # in dam_elevation_points.csv.
        try:
            rings_pts = _generate_rings_csv(kl)
            csv_path2 = _save_rings_csv(rings_pts, "dam_rings.csv")
            LOG.info(f"Rings CSV exported: "
                     f"{os.path.basename(csv_path2)} ({len(rings_pts)} pts)")
        except Exception as e:
            LOG.error(f"Rings CSV export failed: {e}")
            import traceback as tb_mod
            tb_mod.print_exc()

    # Footprint polygon
    try:
        fl = _make_poly_layer(_layer_name("Outer Toe Footprint"), kl['outer_toe']['coords'])
        fl_file = _save_gpkg(fl, "outer_toe_footprint.gpkg")
        QgsProject.instance().addMapLayer(fl_file)
        LOG.info("Outer Toe Footprint -> project")
    except Exception as e:
        LOG.error(f"Footprint output failed: {e}")

    # DEM
    if CFG['dem_enabled']:
        try:
            _build_dem(all_pts, kl, spill_bls, spill_outline)
        except Exception as e:
            LOG.error(f"DEM generation failed: {e}\n{traceback.format_exc()}")
    else:
        LOG.info("DEM generation disabled")

    LOG.success("Outputs complete")


def _apply_constant_slope_batter(raw_path, smooth_path, kl, spill_outline):
    """Replace TIN-derived external batter with a constant-slope surface.

    External batter zone = cells OUTSIDE (outer_crest_poly UNION
    spill_outline_poly). For these cells:
        Z = crest_z - perp_distance_to_outer_crest * (1 / outer_HV)
        Z >= toe_z (clamped)

    Inside the union, the TIN values are preserved (handles the dam top,
    inner batter, and the spillway notch including its flat extending
    beyond outer crest).

    Returns True on success, False if it falls back (raw is copied to
    smooth in that case so downstream pipeline still works).
    """
    import shutil

    if not HAS_NUMPY:
        LOG.warn("numpy unavailable - constant-slope batter skipped")
        shutil.copy(raw_path, smooth_path)
        return False

    try:
        from osgeo import gdal
        from matplotlib.path import Path as MplPath
    except ImportError as e:
        LOG.warn(f"Constant-slope batter needs gdal+matplotlib ({e}) - skipped")
        shutil.copy(raw_path, smooth_path)
        return False

    # Need a constant-Z outer toe ring to anchor the slope
    obr = kl.get('outer_batter', [])
    if not obr:
        LOG.warn("No const-Z outer toe ring - constant-slope batter skipped")
        shutil.copy(raw_path, smooth_path)
        return False

    const_ot = obr[-1]
    toe_z = const_ot['z_mean']
    crest_z = CFG['crest']
    oc_coords = kl['outer_crest']['coords']
    ot_const_coords = const_ot['coords']

    # Estimate outer batter H:V at multiple chainages, take median
    oc_g = QgsGeometry.fromPolylineXY(
        [QgsPointXY(c[0], c[1]) for c in oc_coords])
    ot_g = QgsGeometry.fromPolylineXY(
        [QgsPointXY(c[0], c[1]) for c in ot_const_coords])
    ol = llen(oc_coords)
    samples = []
    for f in (0.1, 0.25, 0.4, 0.5, 0.6, 0.75, 0.9):
        try:
            hv = _estimate_batter_hv(oc_coords, ot_const_coords,
                                     oc_g, ot_g, crest_z, ol * f)
            if hv > 0:
                samples.append(hv)
        except Exception:
            pass
    if not samples:
        LOG.warn("Could not estimate outer batter H:V - skipped")
        shutil.copy(raw_path, smooth_path)
        return False

    outer_hv = float(np.median(samples))
    inv_slope = 1.0 / outer_hv
    LOG.info(f"Constant-slope batter: H:V = {outer_hv:.2f}:1 "
             f"(median of {len(samples)}), crest={crest_z:.2f}, "
             f"toe={toe_z:.2f}")

    # ---- Read raw raster ----
    ds = gdal.Open(raw_path, gdal.GA_ReadOnly)
    if ds is None:
        LOG.warn(f"Could not open {raw_path} - skipped")
        shutil.copy(raw_path, smooth_path)
        return False
    band = ds.GetRasterBand(1)
    arr = band.ReadAsArray().astype(np.float64)
    nodata = band.GetNoDataValue()
    if nodata is None:
        nodata = -9999.0
    gt = ds.GetGeoTransform()
    nx, ny = ds.RasterXSize, ds.RasterYSize
    proj = ds.GetProjection()
    ds = None

    # ---- Cell-centre grid ----
    x0, dx, _, y0, _, dy = gt  # dy is negative
    gx = x0 + (np.arange(nx) + 0.5) * dx
    gy = y0 + (np.arange(ny) + 0.5) * dy
    GX, GY = np.meshgrid(gx, gy)
    pts_flat = np.column_stack([GX.ravel(), GY.ravel()])

    # ---- Preserve mask = inside (outer_crest UNION spill_outline) ----
    oc_xy = [(c[0], c[1]) for c in oc_coords]
    if oc_xy[0] != oc_xy[-1]:
        oc_xy.append(oc_xy[0])
    oc_path = MplPath(oc_xy)
    preserve = oc_path.contains_points(pts_flat).reshape(GX.shape)
    n_crest = int(preserve.sum())

    n_spill = 0
    if spill_outline:
        so_xy = [(p[0], p[1]) for p in spill_outline]
        if so_xy[0] != so_xy[-1]:
            so_xy.append(so_xy[0])
        so_path = MplPath(so_xy)
        spill_mask = so_path.contains_points(pts_flat).reshape(GX.shape)
        n_spill = int(spill_mask.sum())
        preserve |= spill_mask
    LOG.detail(f"Preserve mask: {int(preserve.sum())} cells "
               f"(crest={n_crest}, +spill={n_spill})")

    # ---- Vectorised perp distance from grid to outer-crest polyline ----
    pts = np.array(oc_xy, dtype=np.float64)
    starts = pts[:-1]
    ends = pts[1:]
    dist = np.full(GX.shape, np.inf, dtype=np.float64)
    for s, e in zip(starts, ends):
        ex = e[0] - s[0]
        ey = e[1] - s[1]
        L2 = ex * ex + ey * ey
        if L2 < 1e-12:
            d = np.hypot(GX - s[0], GY - s[1])
        else:
            t = ((GX - s[0]) * ex + (GY - s[1]) * ey) / L2
            np.clip(t, 0.0, 1.0, out=t)
            px = s[0] + t * ex
            py = s[1] + t * ey
            d = np.hypot(GX - px, GY - py)
        np.minimum(dist, d, out=dist)

    # ---- Constant-slope Z (clamped at toe_z) ----
    batter_z = crest_z - dist * inv_slope
    np.maximum(batter_z, toe_z, out=batter_z)

    # ---- Composite ----
    out_arr = np.where(preserve, arr, batter_z).astype(np.float32)
    # Where TIN was NoData inside preserve zone, keep NoData
    out_arr = np.where(np.logical_and(preserve, arr == nodata),
                       np.float32(nodata), out_arr)

    # ---- Write ----
    drv = gdal.GetDriverByName('GTiff')
    ds_out = drv.Create(smooth_path, nx, ny, 1, gdal.GDT_Float32)
    ds_out.SetGeoTransform(gt)
    ds_out.SetProjection(proj)
    bo = ds_out.GetRasterBand(1)
    bo.SetNoDataValue(float(nodata))
    bo.WriteArray(out_arr)
    bo.FlushCache()
    ds_out = None

    n_replaced = int((~preserve).sum())
    valid = out_arr[out_arr != np.float32(nodata)]
    if valid.size:
        LOG.info(f"Constant-slope batter applied: {n_replaced} cells "
                 f"(Z range {valid.min():.2f}-{valid.max():.2f})")
    return True


def _build_dem(all_pts, kl, spill_bls, spill_outline=None):
    res = CFG['dem_res']
    # Repair any self-intersection before the toe is used as the clip mask.
    # A bowtied toe (common after cut-to-terrain on a concave footprint)
    # otherwise punches a NoData hole through the DEM via the even-odd fill
    # rule. No-op when the toe is already simple. This single call feeds
    # both the GDAL mask-clip and the scipy fallback clip below.
    toe = _repair_ring(kl['outer_toe']['coords'], "outer toe (DEM clip)")

    pt_lyr = _make_pt_layer("_tmp_pts", all_pts)
    QgsProject.instance().addMapLayer(pt_lyr, False)
    clip_lyr = _make_poly_layer("_tmp_clip", toe)
    QgsProject.instance().addMapLayer(clip_lyr, False)

    xs = [c[0] for c in toe]
    ys = [c[1] for c in toe]
    buf = res * 3
    xn, xx = min(xs)-buf, max(xs)+buf
    yn, yx = min(ys)-buf, max(ys)+buf

    raw = os.path.join(CFG['output_dir'], "dam_dem_raw.tif")
    smooth = os.path.join(CFG['output_dir'], "dam_dem_smooth.tif")
    clip = os.path.join(CFG['output_dir'], "dam_dem.tif")

    # Interpolation data
    interp_parts = [f"{pt_lyr.id()},elevation,0,{INTERP_SOURCE_POINTS}"]

    bl_lyr = None
    if CFG.get('use_breaklines', True):
        crest_bls = [
            ("inner_crest", kl['inner_crest']['coords'], CFG['crest']),
            ("outer_crest", kl['outer_crest']['coords'], CFG['crest']),
        ]
        bl_lyr = _make_bl_layer("_tmp_bls", crest_bls, spill_bls)
        QgsProject.instance().addMapLayer(bl_lyr, False)
        interp_parts.append(
            f"{bl_lyr.id()},elevation,0,{INTERP_SOURCE_BREAKLINES}")
        LOG.detail(f"Breaklines: {bl_lyr.featureCount()} features")

    interp_data = "::".join(interp_parts)

    try:
        LOG.info("TIN interpolation...")
        processing.run("qgis:tininterpolation", {
            'INTERPOLATION_DATA': interp_data,
            'METHOD': 0,
            'EXTENT': f"{xn},{xx},{yn},{yx} [EPSG:{CRS_EPSG}]",
            'PIXEL_SIZE': res,
            'OUTPUT': raw,
        })

        # Replace TIN-derived external batter with constant-slope surface
        LOG.info("Applying constant-slope external batter...")
        applied = _apply_constant_slope_batter(raw, smooth, kl, spill_outline)
        intermediate = smooth if applied else raw

        LOG.info("Clipping to outer toe (variable Z)...")
        processing.run("gdal:cliprasterbymasklayer", {
            'INPUT': intermediate,
            'MASK': clip_lyr,
            'SOURCE_CRS': f'EPSG:{CRS_EPSG}',
            'TARGET_CRS': f'EPSG:{CRS_EPSG}',
            'NODATA': -9999,
            'CROP_TO_CUTLINE': True,
            'KEEP_RESOLUTION': True,
            'OUTPUT': clip,
        })
        LOG.detail(f"DEM: {clip}")

        dem = QgsRasterLayer(clip, _layer_name("DEM"))
        if dem.isValid():
            QgsProject.instance().addMapLayer(dem)
            LOG.info(f"{_layer_name('DEM')} -> project")
        else:
            LOG.warn("DEM file created but could not be loaded as layer")

    except Exception as e:
        LOG.warn(f"QGIS TIN interpolation failed: {e}")
        LOG.info("Attempting scipy fallback (no breaklines)...")
        _dem_scipy(all_pts, toe, xn, xx, yn, yx, res, clip)

    # Cleanup temp layers
    for lyr in [pt_lyr, clip_lyr, bl_lyr]:
        if lyr:
            try:
                QgsProject.instance().removeMapLayer(lyr.id())
            except:
                pass


def _dem_scipy(pts, toe, xn, xx, yn, yx, res, out):
    try:
        from scipy.interpolate import griddata
    except ImportError:
        raise ImportError(
            "scipy is not installed. Cannot use fallback DEM method.\n\n"
            "Install scipy in your QGIS Python environment, or fix the\n"
            "QGIS TIN interpolation error above.")
    try:
        from osgeo import gdal, osr
    except ImportError:
        raise ImportError(
            "GDAL Python bindings not available. Cannot write GeoTIFF.")

    xs = np.array([p[0] for p in pts])
    ys = np.array([p[1] for p in pts])
    zs = np.array([p[2] for p in pts])
    nx = int(math.ceil((xx-xn)/res))
    ny = int(math.ceil((yx-yn)/res))
    gx, gy = np.linspace(xn, xx, nx), np.linspace(yn, yx, ny)
    gX, gY = np.meshgrid(gx, gy)
    gZ = griddata((xs, ys), zs, (gX, gY), method='linear', fill_value=-9999)

    # Clip to the outer-toe polygon. The previous implementation called
    # QgsGeometry.contains() once per grid cell in a Python double loop -
    # at 0.1 m resolution that's 10M+ contains() calls (~2-9 minutes,
    # low CPU because it's QGIS-call overhead, not compute). Vectorise
    # with matplotlib.path.Path.contains_points, which tests ALL cells in
    # one C call (sub-second for the same grid). Fall back to the slow
    # per-cell loop only if matplotlib isn't available.
    tc = [(c[0], c[1]) for c in toe]
    if tc[0] != tc[-1]:
        tc.append(tc[0])
    clipped = False
    try:
        from matplotlib.path import Path as _MplPath
        poly_path = _MplPath(tc)
        # gX, gY are (ny, nx). Flatten, test, reshape. radius=0 keeps the
        # boundary crisp (cells whose centre is inside the polygon).
        flat_xy = np.column_stack((gX.ravel(), gY.ravel()))
        inside = poly_path.contains_points(flat_xy).reshape(gZ.shape)
        gZ[~inside] = -9999
        clipped = True
    except Exception as e:
        LOG.warn(f"Vectorised clip failed ({e}); falling back to the "
                 f"per-cell test (this can be slow at fine resolution).")
    if not clipped:
        poly = QgsGeometry.fromPolygonXY([[QgsPointXY(*p) for p in tc]])
        for iy in range(ny):
            for ix in range(nx):
                if not poly.contains(QgsGeometry.fromPointXY(
                        QgsPointXY(gx[ix], gy[iy]))):
                    gZ[iy, ix] = -9999

    drv = gdal.GetDriverByName('GTiff')
    ds = drv.Create(out, nx, ny, 1, gdal.GDT_Float32)
    ds.SetGeoTransform([xn, res, 0, yx, 0, -res])
    srs = osr.SpatialReference()
    srs.ImportFromEPSG(CRS_EPSG)
    ds.SetProjection(srs.ExportToWkt())
    b = ds.GetRasterBand(1)
    b.SetNoDataValue(-9999)
    b.WriteArray(np.flipud(gZ))
    b.FlushCache()
    ds = None

    dem = QgsRasterLayer(out, _layer_name("DEM"))
    if dem.isValid():
        QgsProject.instance().addMapLayer(dem)
        LOG.info(f"{_layer_name('DEM')} (scipy) -> project")
    LOG.detail(f"scipy DEM: {out}")


# =============================================================================
# MAIN
# =============================================================================

def _apply_z_offset_to_classified(classified, z_offset):
    """Apply a constant vertical shift to every const-Z and var-Z ring in
    the classified output. Modifies the Z component of every coord and the
    aggregate z_mean/z_min/z_max fields. Used to bring DXF Z values into
    the LiDAR datum (NZVD2016) before any downstream processing."""
    if abs(z_offset) < 1e-9:
        return
    for key in ('const_z', 'var_z'):
        for r in classified.get(key, []):
            r['coords'] = [(x, y, z + z_offset) for x, y, z in r['coords']]
            r['z_mean'] = r.get('z_mean', 0) + z_offset
            r['z_min'] = r.get('z_min', 0) + z_offset
            r['z_max'] = r.get('z_max', 0) + z_offset
    # Partial contour open polylines need the offset too, otherwise
    # step4c_var_z_outer_toe compares DXF-datum Zs to NZVD2016-datum
    # ranges and silently rejects everything. These have 'z' (the
    # contour elevation) rather than 'z_mean', and 2D 'start_xy' /
    # 'end_xy' tuples that don't carry Z.
    for p in classified.get('partial_contours', []):
        p['coords'] = [(x, y, z + z_offset) for x, y, z in p['coords']]
        p['z'] = p.get('z', 0) + z_offset


def _apply_z_offset_to_kl(kl, z_offset):
    """Apply z_offset to every ring in a kl dict (used when a constructed
    kl is supplied - its Z values are in DXF datum and need shifting)."""
    if abs(z_offset) < 1e-9:
        return
    for role, val in kl.items():
        if val is None:
            continue
        if role == 'partial_contours':
            # Special-cased: each item has 'z' (contour elevation) and
            # 2D 'start_xy' / 'end_xy' rather than 'z_mean' / 'z_min' /
            # 'z_max'. The generic ring loop would corrupt these.
            if isinstance(val, list):
                for p in val:
                    p['coords'] = [(x, y, z + z_offset) for x, y, z in p['coords']]
                    p['z'] = p.get('z', 0) + z_offset
            continue
        if isinstance(val, list):
            for r in val:
                r['coords'] = [(x, y, z + z_offset) for x, y, z in r['coords']]
                r['z_mean'] = r.get('z_mean', 0) + z_offset
                r['z_min'] = r.get('z_min', 0) + z_offset
                r['z_max'] = r.get('z_max', 0) + z_offset
        elif isinstance(val, dict):
            val['coords'] = [(x, y, z + z_offset) for x, y, z in val['coords']]
            val['z_mean'] = val.get('z_mean', 0) + z_offset
            val['z_min'] = val.get('z_min', 0) + z_offset
            val['z_max'] = val.get('z_max', 0) + z_offset


# =============================================================================
# PHASE 3: POLYGON MODE + TERRAIN DRAPE
# =============================================================================
#
# Polygon mode is the "last-resort" entry point for building a dam DEM
# from minimal input: a SINGLE closed polygon (any QGIS line or polygon
# layer) representing one of the 3 constant-elevation design rings
# (inner_toe, inner_crest, or outer_crest) plus all the design parameters.
#
# Pipeline:
#   1) step1c_polygon_validate     : pull polygon coords + reproject to NZTM2000
#   2) step3c_build_rings_from_polygon : construct 4 rings analytically,
#                                         deliberately overshooting the outer
#                                         toe to a depth below terrain
#   3) step5 / step6 / step7        : (reused unchanged) produce points,
#                                         spillway, DEM
#   4) step7c_drape_to_terrain      : clip the dam DEM to where it sits
#                                         above natural ground; the boundary
#                                         of valid cells IS the variable-Z
#                                         outer toe
#
# step7c is also useful as a clean-up step in DXF mode, so it's exposed
# under the "Drape DEM to terrain" checkbox in the DEM & Output tab and
# runs in either mode.

def _terrain_min_in_bbox(terrain_layer, coords, samples_per_axis=21):
    """Return the minimum terrain elevation sampled on a regular grid
    covering the XY bbox of `coords`. None if no valid samples."""
    if not coords or terrain_layer is None:
        return None
    xs = [c[0] for c in coords]
    ys = [c[1] for c in coords]
    xn, xx = min(xs), max(xs)
    yn, yx = min(ys), max(ys)
    dp = terrain_layer.dataProvider()
    if dp is None:
        return None
    tmin = float('inf')
    n = max(2, int(samples_per_axis))
    for j in range(n):
        y = yn + (yx - yn) * j / (n - 1)
        for i in range(n):
            x = xn + (xx - xn) * i / (n - 1)
            try:
                res = dp.sample(QgsPointXY(x, y), 1)
            except Exception:
                continue
            if res is None:
                continue
            try:
                val, ok = res
            except (TypeError, ValueError):
                continue
            if ok and val is not None and val < tmin:
                tmin = float(val)
    return tmin if tmin < float('inf') else None


def step1c_polygon_validate():
    """Phase 3 entry: validate the polygon-mode inputs and pull the
    polygon coordinates into NZTM2000 with the assigned Z."""
    LOG.start_step("Polygon mode: validating input")

    # Output dir
    out = CFG['output_dir']
    if not os.path.exists(out):
        os.makedirs(out)
        LOG.info(f"Created output directory: {out}")

    layer_id = CFG.get('polygon_layer_id')
    if not layer_id:
        raise ValueError("Polygon mode requires a polygon source layer "
                         "(select one on the Polygon Mode tab).")
    layer = QgsProject.instance().mapLayer(layer_id)
    if layer is None:
        raise ValueError(f"Polygon source layer not found "
                         f"(id={layer_id}). Was it removed from the "
                         f"project?")

    # Pick the feature (specified FID or first feature)
    fid = CFG.get('polygon_feature_fid')
    feature = None
    for f in layer.getFeatures():
        if fid is None or f.id() == fid:
            feature = f
            break
    if feature is None:
        raise ValueError(
            f"No matching feature in polygon layer '{layer.name()}'."
            + (f" Requested FID={fid}." if fid is not None else
               " Layer is empty."))

    geom = feature.geometry()
    if geom is None or geom.isEmpty():
        raise ValueError("Selected polygon feature has empty geometry.")

    # Extract exterior ring as XY (works for line OR polygon geometry)
    coords_xy = []
    gtype = geom.type()  # 1=Line, 2=Polygon
    try:
        if gtype == 1:  # Line/polyline
            if geom.isMultipart():
                # Use the first part
                pl = geom.asMultiPolyline()
                if pl and pl[0]:
                    coords_xy = [(p.x(), p.y()) for p in pl[0]]
            else:
                pl = geom.asPolyline()
                coords_xy = [(p.x(), p.y()) for p in pl]
        elif gtype == 2:  # Polygon
            if geom.isMultipart():
                mp = geom.asMultiPolygon()
                if mp and mp[0] and mp[0][0]:
                    coords_xy = [(p.x(), p.y()) for p in mp[0][0]]
            else:
                pg = geom.asPolygon()
                if pg and pg[0]:
                    coords_xy = [(p.x(), p.y()) for p in pg[0]]
        else:
            raise ValueError(
                f"Polygon source must be a line or polygon geometry "
                f"(got type {gtype}).")
    except Exception as e:
        raise ValueError(f"Failed to read polygon coordinates: {e}")

    if len(coords_xy) < 4:
        raise ValueError(
            f"Polygon has only {len(coords_xy)} vertices "
            f"(need at least 4 to define a closed ring).")

    # Ensure closure
    if coords_xy[0] != coords_xy[-1]:
        coords_xy.append(coords_xy[0])

    # Reproject to NZTM2000 if needed
    layer_crs = layer.crs()
    target_crs = QgsCoordinateReferenceSystem(f"EPSG:{CRS_EPSG}")
    if layer_crs.isValid() and layer_crs != target_crs:
        LOG.info(f"Reprojecting polygon from {layer_crs.authid()} to "
                 f"EPSG:{CRS_EPSG} (NZTM2000)...")
        xform = QgsCoordinateTransform(layer_crs, target_crs,
                                       QgsProject.instance())
        reprojected = []
        for (x, y) in coords_xy:
            pt = xform.transform(QgsPointXY(x, y))
            reprojected.append((pt.x(), pt.y()))
        coords_xy = reprojected
        # Re-check closure after reprojection (FP drift can break it)
        if coords_xy[0] != coords_xy[-1]:
            coords_xy.append(coords_xy[0])

    # Stamp the elevation onto every vertex
    p_z = float(CFG.get('polygon_z', 0.0))
    coords3d = [(x, y, p_z) for (x, y) in coords_xy]

    area = shoelace(coords3d)
    role = CFG.get('polygon_role', 'inner_crest')
    if role not in ('inner_toe', 'inner_crest', 'outer_crest'):
        raise ValueError(
            f"polygon_role must be inner_toe, inner_crest, or outer_crest "
            f"(got '{role}'). outer_toe is excluded because it is "
            f"constructed artificially in polygon mode.")

    # Auto-couple: the polygon IS its role's design elevation. If the
    # user separately set crest_z / invert_z to something inconsistent
    # with the polygon elevation, override and log it - the polygon is
    # the source of truth for "this ring sits at this elevation".
    if role == 'inner_crest' or role == 'outer_crest':
        cur_cz = float(CFG.get('polygon_crest_z', p_z))
        if abs(cur_cz - p_z) > 0.01:
            LOG.info(f"Overriding crest_z {cur_cz:.2f} -> {p_z:.2f} m "
                     f"to match polygon elevation (polygon defines the "
                     f"'{role}' ring)")
            CFG['polygon_crest_z'] = p_z
    elif role == 'inner_toe':
        cur_iz = float(CFG.get('polygon_invert_z', p_z))
        if abs(cur_iz - p_z) > 0.01:
            LOG.info(f"Overriding invert_z {cur_iz:.2f} -> {p_z:.2f} m "
                     f"to match polygon elevation (polygon defines the "
                     f"'{role}' ring)")
            CFG['polygon_invert_z'] = p_z

    LOG.info(f"Polygon: role='{role}', z={p_z:.2f} m, "
             f"{len(coords3d)} verts, area={area:.0f} m2")
    LOG.success("Polygon validated")

    return {
        'coords': coords3d,
        'z_mean': p_z, 'z_min': p_z, 'z_max': p_z, 'z_std': 0.0,
        'area': area, 'npts': len(coords3d),
    }


def step3c_build_rings_from_polygon(polygon_ring):
    """Construct the 4 design rings from a single polygon + parameters.
    The outer_toe is set to an artificial deep elevation so the resulting
    DEM overshoots into below-natural-ground. step7c then clips the DEM
    back to where it sits above terrain."""
    LOG.start_step("Polygon mode: constructing 4 design rings from "
                   "polygon + parameters")

    role = CFG.get('polygon_role', 'inner_crest')
    crest_z = float(CFG['polygon_crest_z'])
    invert_z = float(CFG['polygon_invert_z'])
    crest_width = float(CFG.get('polygon_crest_width', 6.0))
    inner_hv = float(CFG.get('polygon_inner_hv', 2.5))
    outer_hv = float(CFG.get('polygon_outer_hv', 2.5))
    overshoot = float(CFG.get('terrain_overshoot', 15.0))

    # Pick a sensibly-deep artificial outer_toe_z. Prefer terrain_min -
    # overshoot (guarantees the outer batter projects below ground all
    # around) but fall back to invert_z - overshoot when terrain isn't
    # available.
    terrain_layer = None
    tid = CFG.get('terrain_layer_id')
    if tid:
        terrain_layer = QgsProject.instance().mapLayer(tid)

    tmin = _terrain_min_in_bbox(terrain_layer,
                                polygon_ring['coords']) if terrain_layer else None
    if tmin is not None:
        artificial_otz = tmin - overshoot
        LOG.info(f"Terrain min near polygon: {tmin:.2f} m -> "
                 f"artificial outer_toe_z = {artificial_otz:.2f} m "
                 f"({overshoot:.1f} m below terrain)")
    else:
        artificial_otz = invert_z - overshoot
        LOG.warn(f"No terrain layer available; using invert_z - "
                 f"overshoot = {artificial_otz:.2f} m as artificial "
                 f"outer_toe_z. The drape step may not clip properly "
                 f"if natural ground is above this elevation.")

    params = {
        'crest_z': crest_z,
        'invert_z': invert_z,
        'outer_toe_z': artificial_otz,
        'crest_width': crest_width,
        'inner_hv': inner_hv,
        'outer_hv': outer_hv,
    }
    sp = float(CFG.get('point_spacing', 1.0))

    try:
        kl = construct_dam_rings_from_anchor(
            polygon_ring, role, params, sp=sp)
    except Exception as e:
        raise ValueError(
            f"Failed to construct rings from polygon: {e}\n\n"
            f"Common causes:\n"
            f"  - polygon is too small (inner toe collapses to nothing)\n"
            f"  - parameters are inconsistent (e.g. crest_z <= invert_z)\n"
            f"  - polygon has self-intersections")

    LOG.info(f"Built 4 rings analytically:")
    for nm in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
        r = kl.get(nm)
        if r:
            LOG.detail(f"  {nm}: z={r['z_mean']:.2f} m, "
                       f"{r['npts']} pts, area={r['area']:.0f} m2")

    # Validate each constructed ring is geometrically valid (no self-
    # intersection). A bowtie ring crashes the TIN / DEM build later in
    # the pipeline. Surface the failure HERE with a clear message so the
    # user gets a recoverable error instead of a partial-output crash.
    for nm in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
        r = kl.get(nm)
        if r is None:
            raise ValueError(
                f"Construction failed to produce a {nm} ring. "
                f"Check that the polygon and parameters are consistent "
                f"(crest_z > invert_z, crest_z > outer_toe_z, sensible "
                f"H:V slopes, non-zero crest width).")
        try:
            ring_pts_q = [QgsPointXY(c[0], c[1]) for c in r['coords']]
            poly_g = QgsGeometry.fromPolygonXY([ring_pts_q])
            if poly_g is None or poly_g.isEmpty():
                raise ValueError("empty geometry")
            # QgsGeometry.isGeosValid() returns False on self-intersection
            if hasattr(poly_g, 'isGeosValid'):
                if not poly_g.isGeosValid():
                    raise ValueError("self-intersection (bowtie loop)")
            # Last-resort area check - degenerate rings have ~0 area
            if abs(shoelace([(c[0], c[1])
                              for c in r['coords']])) < 1.0:
                raise ValueError("degenerate (area < 1 m\u00b2)")
        except Exception as e:
            raise ValueError(
                f"Construction produced an invalid {nm} ring: {e}. "
                f"Common cause: polygon has very tight inside corners, "
                f"and the inward offset (depth x H:V) caused the ring "
                f"to fold over itself. Try: enlarge the polygon, reduce "
                f"depth, or use a less curved polygon outline.")

    LOG.success(f"Rings ready (outer toe is ARTIFICIAL at "
                f"z={artificial_otz:.2f} m; will be clipped to terrain "
                f"by drape step)")
    # CRITICAL: step5_points reads CFG['toe_low'] directly to set the
    # Z of every outer_toe point fed into the TIN. _collect_run_settings
    # populates CFG['toe_low'] from the Input-tab "Outer toe lowest"
    # spinbox (which is meaningless in polygon mode - it's part of the
    # DXF auto-elev flow). Without overwriting it here, the TIN gets
    # outer_toe points at the spinbox value (often = invert_z or 336.0
    # default), not at the artificial deep elevation we just computed.
    # Result: outer batter slope is wrong by the difference, DEM is
    # visibly broken.
    # Also push invert/crest into CFG so step6 and others get the right
    # values regardless of the spinbox state on the Input tab.
    CFG['toe_low'] = artificial_otz
    CFG['invert'] = invert_z
    CFG['crest'] = crest_z
    return kl


def _points_in_polygon_grid(cx, cy, poly_x, poly_y):
    """Vectorised point-in-polygon test using the even-odd ray-casting rule.
    cx, cy: 2D numpy arrays of cell centre X/Y (same shape).
    poly_x, poly_y: 1D arrays of polygon vertex X/Y, in order (open or
        closed - the wrap from last to first is handled automatically).
    Returns: boolean 2D array of the same shape as cx/cy. True = inside.

    The algorithm casts a horizontal ray from each cell to the right and
    counts polygon-edge crossings. Edges from (xj, yj) to (xi, yi) cross
    the ray at y=cy iff (yi > cy) != (yj > cy). For the cell to be inside,
    cx must be less than the x-intercept.
    """
    n = len(poly_x)
    if n < 3:
        return np.zeros(cx.shape, dtype=bool)
    inside = np.zeros(cx.shape, dtype=bool)
    j = n - 1
    for i in range(n):
        xi, yi = float(poly_x[i]), float(poly_y[i])
        xj, yj = float(poly_x[j]), float(poly_y[j])
        if abs(yj - yi) < 1e-12:
            j = i
            continue
        cond = (yi > cy) != (yj > cy)
        # x-intercept of edge with the horizontal ray at y=cy
        xint = (xj - xi) * (cy - yi) / (yj - yi) + xi
        inside ^= (cond & (cx < xint))
        j = i
    return inside


def step7c_drape_to_terrain(dem_path, terrain_layer, output_dir,
                            dam_name="dam", outer_crest_coords=None,
                            inner_toe_coords=None):
    """Clip a dam DEM to where it sits above natural ground - but only
    on the OUTER BATTER (between outer_crest and outer_toe in plan view).

    Reads the dam DEM raster, samples terrain at each cell, and replaces
    cells where dam_z < terrain_z with nodata - but ONLY for cells that
    sit OUTSIDE the outer_crest ring. Cells inside outer_crest are dam
    structure (crest, inner batter) and stay regardless of natural
    ground, because parts of the dam invert can legitimately sit below
    local terrain (e.g. at abutment knolls, in excavated foundations,
    or where the inner-toe ring drapes into a reservoir basin).

    The boundary of the resulting valid cells IS the variable-Z outer
    toe in the new draped DEM.

    Works as a clean-up step in either polygon mode (where the outer
    toe was constructed artificially deep) or DXF mode (where the
    conservative outer toe may overshoot natural ground).

    Args:
        dem_path: path to dam DEM (input)
        terrain_layer: QgsRasterLayer for natural terrain
        output_dir: where to write the draped DEM
        dam_name: prefix for the output filename
        outer_crest_coords: list of (x, y[, z]) tuples for the outer
            crest ring. Cells inside this polygon are KEPT regardless of
            terrain. If None, all valid cells are subject to the clip
            (legacy behaviour; warns the user).
        inner_toe_coords: reserved for a future enhancement (currently
            unused; would let us mask out the reservoir interior).

    Returns: path to the draped DEM, or None on failure.
    """
    if terrain_layer is None:
        LOG.warn("Drape step skipped: no terrain raster selected.")
        return None
    if not os.path.isfile(dem_path):
        LOG.warn(f"Drape step skipped: dam DEM not found at {dem_path}")
        return None
    if not HAS_NUMPY:
        LOG.warn("Drape step skipped: numpy not available.")
        return None

    LOG.start_step("Draping dam DEM onto natural terrain")

    try:
        from osgeo import gdal, osr
    except ImportError:
        LOG.error("GDAL Python bindings not available; cannot drape DEM.")
        return None

    # Read the dam DEM
    ds = gdal.Open(dem_path, gdal.GA_ReadOnly)
    if ds is None:
        LOG.error(f"Failed to open dam DEM: {dem_path}")
        return None
    band = ds.GetRasterBand(1)
    dam_arr = band.ReadAsArray().astype('float32')
    nodata = band.GetNoDataValue()
    if nodata is None:
        nodata = -9999.0
    nodata = float(nodata)
    gt = ds.GetGeoTransform()  # (ox, dx, rot, oy, rot, dy)
    proj = ds.GetProjection()
    cols, rows = ds.RasterXSize, ds.RasterYSize
    ds = None

    # Build a copy we'll mutate
    drape_arr = dam_arr.copy()
    valid_mask = (np.abs(drape_arr - nodata) > 1e-3) & np.isfinite(drape_arr)

    n_total = int(valid_mask.sum())
    if n_total == 0:
        LOG.warn("Dam DEM has no valid cells; nothing to drape.")
        return None
    LOG.info(f"Dam DEM has {n_total:,} valid cells "
             f"(grid {cols} x {rows})")

    # Build the "inside outer crest" mask. Cells inside this polygon are
    # dam structure (crest + inner batter + reservoir-side fill) and stay
    # regardless of terrain elevation - terrain clip applies only to the
    # OUTER BATTER (cells between outer_crest and outer_toe in plan view).
    inside_oc = None
    if outer_crest_coords:
        try:
            poly_x = np.array([float(c[0]) for c in outer_crest_coords],
                              dtype='float64')
            poly_y = np.array([float(c[1]) for c in outer_crest_coords],
                              dtype='float64')
            # Cell-centre grid in world coords
            ii = np.arange(cols, dtype='float64')
            jj = np.arange(rows, dtype='float64')
            cx_row = gt[0] + (ii + 0.5) * gt[1]      # 1D
            cy_col = gt[3] + (jj + 0.5) * gt[5]      # 1D
            cx = np.broadcast_to(cx_row, (rows, cols))
            cy = np.broadcast_to(cy_col[:, None], (rows, cols))
            inside_oc = _points_in_polygon_grid(cx, cy, poly_x, poly_y)
            n_inside = int((inside_oc & valid_mask).sum())
            LOG.info(f"Inside outer-crest polygon: {n_inside:,} valid "
                     f"cells (dam interior - exempt from terrain clip)")
        except Exception as e:
            LOG.warn(f"Failed to build outer-crest mask ({e}); falling "
                     f"back to clipping all valid cells. Inner-toe / "
                     f"crest cells below terrain may be wrongly removed.")
            inside_oc = None
    else:
        LOG.warn("No outer_crest_coords supplied; drape will clip ALL "
                 "cells below terrain, including dam-structure cells. "
                 "Pass outer_crest_coords for the correct behaviour.")

    # Sample terrain at every valid cell that is OUTSIDE outer crest
    terrain_dp = terrain_layer.dataProvider()
    if terrain_dp is None:
        LOG.error("Terrain layer has no data provider.")
        return None

    n_clipped = 0
    n_kept_outer = 0
    n_kept_interior = 0
    n_terrain_miss = 0
    for j in range(rows):
        # Pixel row j -> world y at cell centre
        y = gt[3] + (j + 0.5) * gt[5]
        for i in range(cols):
            if not valid_mask[j, i]:
                continue
            # Interior cells (inside outer crest) are dam structure - keep
            if inside_oc is not None and inside_oc[j, i]:
                n_kept_interior += 1
                continue
            dam_z = float(drape_arr[j, i])
            x = gt[0] + (i + 0.5) * gt[1]
            try:
                res = terrain_dp.sample(QgsPointXY(x, y), 1)
            except Exception:
                n_terrain_miss += 1
                continue
            if res is None:
                n_terrain_miss += 1
                continue
            try:
                t_val, ok = res
            except (TypeError, ValueError):
                n_terrain_miss += 1
                continue
            if not ok or t_val is None:
                n_terrain_miss += 1
                continue
            if dam_z < float(t_val):
                # Below natural ground on the OUTER BATTER - clip
                drape_arr[j, i] = nodata
                n_clipped += 1
            else:
                n_kept_outer += 1

    LOG.info(f"Clipping summary: "
             f"{n_kept_interior:,} kept (dam interior, inside outer crest), "
             f"{n_kept_outer:,} kept (outer batter, above ground), "
             f"{n_clipped:,} clipped (outer batter, below ground), "
             f"{n_terrain_miss:,} terrain misses")

    if n_terrain_miss > 0.1 * n_total:
        LOG.warn(f"More than 10% of cells had no terrain coverage. The "
                 f"terrain raster may not extend over the full dam "
                 f"footprint - check that '{terrain_layer.name()}' covers "
                 f"the whole dam area.")

    # Write the draped DEM
    drape_path = os.path.join(output_dir,
                              f"{dam_name}_dam_dem_draped.tif")
    drv = gdal.GetDriverByName("GTiff")
    out_ds = drv.Create(drape_path, cols, rows, 1, gdal.GDT_Float32)
    out_ds.SetGeoTransform(gt)
    if proj:
        out_ds.SetProjection(proj)
    else:
        srs = osr.SpatialReference()
        srs.ImportFromEPSG(CRS_EPSG)
        out_ds.SetProjection(srs.ExportToWkt())
    out_band = out_ds.GetRasterBand(1)
    out_band.SetNoDataValue(nodata)
    out_band.WriteArray(drape_arr)
    out_band.FlushCache()
    out_ds = None

    LOG.detail(f"Draped DEM: {drape_path}")

    # ------------------------------------------------------------------
    # Extract variable-Z outer toe: cells on the boundary of the draped
    # mask. These are where the outer batter cuts into natural terrain,
    # so Z at each boundary point is the terrain elevation. Returned in
    # the result dict so run() can append them to the elevation_points
    # CSV with source="outer_toe_drape".
    # ------------------------------------------------------------------
    outer_toe_drape_pts = []
    outer_toe_drape_polyline = []
    try:
        # Updated valid_mask after clipping
        valid_after = ((np.abs(drape_arr - nodata) > 1e-3)
                       & np.isfinite(drape_arr))
        # Pad with False so edge cells are correctly flagged as boundary
        padded = np.pad(valid_after, 1, constant_values=False)
        all_neighbors_valid = (
            padded[1:-1, :-2]    # left
            & padded[1:-1, 2:]   # right
            & padded[:-2, 1:-1]  # up
            & padded[2:, 1:-1]   # down
        )
        # Boundary = valid cell with at least one invalid 4-neighbor OR
        # at grid edge. Exclude cells inside outer crest (those are dam
        # interior and form an inside-boundary that isn't the outer toe)
        boundary_mask = valid_after & ~all_neighbors_valid
        if inside_oc is not None:
            boundary_mask = boundary_mask & ~inside_oc

        js, is_ = np.where(boundary_mask)
        n_boundary = len(js)
        LOG.info(f"Outer-toe-drape extraction: {n_boundary:,} boundary "
                 f"cells identified")

        if n_boundary > 0:
            n_terrain_miss_b = 0
            # Order points by 8-connected walk starting from top-left.
            # If the boundary isn't simply connected this still produces
            # a reasonable single-loop walk; any orphan loops are dropped.
            # For just CSV scatter, ordering doesn't matter; but the
            # polyline GeoPackage benefits.
            cells = set(zip(js.tolist(), is_.tolist()))
            unwalked = set(cells)
            # Start at lexicographically smallest cell
            start = min(cells)
            walked_order = [start]
            unwalked.discard(start)
            cur = start
            # 8-connected neighbour offsets in CCW order
            nb = [(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1),(1,0),(1,1)]
            safety = 4 * n_boundary
            while safety > 0:
                safety -= 1
                j, i = cur
                found = None
                for dj, di in nb:
                    cand = (j+dj, i+di)
                    if cand in unwalked:
                        found = cand
                        break
                if found is None:
                    break
                walked_order.append(found)
                unwalked.discard(found)
                cur = found

            # Always sample EVERY boundary cell for the CSV (so all
            # var-Z points get into elevation_points.csv); walked_order
            # is only used to build the polyline.
            walked_set = set(walked_order)
            scatter_order = walked_order + [c for c in cells
                                            if c not in walked_set]

            for j, i in scatter_order:
                x = gt[0] + (i + 0.5) * gt[1]
                y = gt[3] + (j + 0.5) * gt[5]
                # Sample terrain (the dam Z at the boundary equals the
                # terrain Z to within one cell, so terrain is the right
                # choice for the var-Z outer toe)
                try:
                    res = terrain_dp.sample(QgsPointXY(x, y), 1)
                    if res is None:
                        n_terrain_miss_b += 1
                        continue
                    t_val, ok = res
                    if not ok or t_val is None:
                        n_terrain_miss_b += 1
                        continue
                    z = float(t_val)
                    outer_toe_drape_pts.append((x, y, z))
                    if (j, i) in walked_set:
                        outer_toe_drape_polyline.append((x, y, z))
                except Exception:
                    n_terrain_miss_b += 1
                    continue
            LOG.info(f"Outer-toe-drape: sampled {len(outer_toe_drape_pts):,} "
                     f"var-Z points (terrain misses: {n_terrain_miss_b})")
            if outer_toe_drape_pts:
                z_vals = [p[2] for p in outer_toe_drape_pts]
                LOG.detail(f"Outer-toe-drape Z range: "
                           f"{min(z_vals):.2f} to {max(z_vals):.2f} m")
    except Exception as e:
        LOG.warn(f"Outer-toe-drape extraction failed ({e}); the "
                 f"elevation_points CSV will not include drape-boundary "
                 f"points. The draped DEM is still correct.")
        outer_toe_drape_pts = []
        outer_toe_drape_polyline = []

    # Write the drape outer toe as a polyline GeoPackage for QGIS
    # visualisation (so the user can SEE the var-Z toe on the map)
    if len(outer_toe_drape_polyline) >= 2:
        try:
            tl_name = f"{dam_name} - Outer Toe (drape)"
            tl_lyr = QgsVectorLayer(
                f"LineStringZ?crs=EPSG:{CRS_EPSG}", tl_name, "memory")
            tl_pr = tl_lyr.dataProvider()
            tl_pr.addAttributes([QgsField("name", QVariant.String)])
            tl_lyr.updateFields()
            tl_f = QgsFeature()
            tl_f.setGeometry(QgsGeometry.fromPolyline(
                [QgsPoint(p[0], p[1], p[2])
                 for p in outer_toe_drape_polyline]))
            tl_f.setAttributes(["outer_toe_drape"])
            tl_pr.addFeatures([tl_f])
            tl_lyr.updateExtents()
            tl_file = _save_gpkg(tl_lyr, "outer_toe_drape.gpkg")
            try:
                _apply_solid_line_style(
                    tl_file, color="orange", width_mm=0.5)
            except Exception:
                pass
            QgsProject.instance().addMapLayer(tl_file)
            LOG.info(f"Outer toe (drape) polyline -> project "
                     f"({len(outer_toe_drape_polyline)} pts)")
        except Exception as e:
            LOG.warn(f"Failed to write outer_toe_drape polyline: {e}")

    # Load draped DEM into project
    drape_lyr = QgsRasterLayer(drape_path, f"{dam_name} - Draped DEM")
    if drape_lyr.isValid():
        QgsProject.instance().addMapLayer(drape_lyr)
        LOG.info("Draped DEM -> project")
    else:
        LOG.warn("Draped DEM file written but could not be loaded as "
                 "layer (check path / GDAL).")

    LOG.success("Drape to terrain complete")
    return {
        'drape_path': drape_path,
        'outer_toe_drape_points': outer_toe_drape_pts,
    }


def run(params):
    global CFG, LOG
    CFG = params
    LOG = StepLogger()

    print("\n" + "=" * 60)
    print(f"  {TOOL_NAME} v{VERSION}")
    print(f"  Goldie Geotechnics")
    print("=" * 60)

    # ------------------------------------------------------------------
    # PHASE 3: Polygon mode bypasses step1-4 entirely. The polygon plus
    # design parameters fully determines the 4 rings analytically.
    # ------------------------------------------------------------------
    if CFG.get('polygon_mode'):
        LOG.info("Polygon Mode: bypassing DXF/layer extraction and "
                 "ring classification.")
        polygon_ring = step1c_polygon_validate()
        kl = step3c_build_rings_from_polygon(polygon_ring)
        # Polygon-mode design elevations feed directly into step5/6/7.
        # CRITICAL: step3c_build_rings_from_polygon already sets
        # CFG['toe_low'] to the artificial-deep elevation. DO NOT
        # overwrite it with invert_z - step5 reads CFG['toe_low'] to
        # set the Z of every outer_toe TIN input point, and using the
        # invert here puts those points 15-30 m too high (collapsing
        # the outer batter). The previous version of this block had
        # 'CFG[toe_low] = polygon_invert_z' which caused step 3 to log
        # "outer_toe: N pts at Z=invert" instead of the artificial deep
        # elevation, producing visibly broken DEM output.
        CFG['invert']  = float(CFG['polygon_invert_z'])
        CFG['crest']   = float(CFG['polygon_crest_z'])
        # toe_low was set correctly by step3c; verify it's the deep
        # value, not the invert, before continuing.
        try:
            current_toe_low = float(CFG.get('toe_low', 0))
            if abs(current_toe_low - CFG['invert']) < 0.01:
                # step3c didn't set it; fall back to artificial deep
                # computed from the constructed outer_toe ring.
                CFG['toe_low'] = float(kl['outer_toe']['z_mean'])
                LOG.warn(f"toe_low was set to invert; restoring to "
                         f"artificial deep {CFG['toe_low']:.2f} m")
        except Exception:
            pass
        CFG['inner_hv'] = float(CFG.get('polygon_inner_hv', 2.5))
        CFG['outer_hv'] = float(CFG.get('polygon_outer_hv', 2.5))
        # AUTO-APPLY METHOD 2 (cut to terrain) so the DEM clips to the
        # actual dam-meets-ground line, not the artificial-deep apron.
        # Users build the dam in polygon mode to see the artificial
        # deep state in the GUI, but at Run time they expect the DEM
        # to be the actual dam clipped to natural ground. Without this
        # auto-apply, the pipeline produces a DEM extending 15+ m past
        # the real outer toe (visible as the "huge gap in points"
        # complaint - the orange outer toe sits well outside the
        # actual dam).
        terrain_lid = CFG.get('terrain_layer_id')
        if terrain_lid:
            terrain_layer = QgsProject.instance().mapLayer(terrain_lid)
            if terrain_layer is not None:
                # Only auto-run if the outer toe is still const-Z (i.e.
                # the artificial-deep design state). If user already
                # ran Method 2 manually, kl['outer_toe']['is_variable_z']
                # would be True and we should keep their result.
                ot = kl.get('outer_toe', {})
                if not ot.get('is_variable_z'):
                    LOG.info("Auto-applying Method 2 (cut to terrain) "
                             "to clip the artificial deep outer toe "
                             "back to natural ground...")
                    try:
                        cut_outer_toe_to_terrain(
                            kl, terrain_layer,
                            params={'crest_z': CFG['crest'],
                                    'outer_hv': CFG['outer_hv']},
                            ring_to_terrain_offset=0.0)
                        new_ot = kl.get('outer_toe', {})
                        LOG.success(
                            f"Outer toe cut to terrain: "
                            f"Z {new_ot.get('z_min', 0):.2f}-"
                            f"{new_ot.get('z_max', 0):.2f} m, "
                            f"{new_ot.get('npts', 0)} vertices. DEM "
                            f"will be clipped to this polygon.")
                    except Exception as e:
                        LOG.warn(f"Auto-Method-2 failed: {e}. DEM will "
                                 f"be clipped to the artificial deep "
                                 f"polygon (extends past natural ground).")
            else:
                LOG.warn("Terrain layer ID set but layer not found in "
                         "project. DEM will be clipped to artificial "
                         "deep polygon.")
        else:
            LOG.warn("No terrain raster selected. DEM will be clipped "
                     "to the artificial deep polygon (extends past "
                     "natural ground). Load a terrain raster on the "
                     "Input tab and re-run for a properly clipped DEM.")
        # Skip DXF datum offset in polygon mode (user inputs already in
        # NZVD2016)
    else:
        # Step 1: Validate
        input_layers = step1_validate()

        # Step 2: Extract
        all_lines = step2_extract(input_layers)

        # Step 3: Classify
        classified = step3_classify(all_lines)

        # Apply datum-correction Z offset (DXF -> NZVD2016) if requested.
        # All downstream rings carry the shifted Z, so the output points / DEM
        # land in NZVD2016 ready for HEC-RAS.
        z_offset = float(CFG.get('z_offset') or 0.0)
        if abs(z_offset) > 1e-9:
            LOG.info(f"Applying vertical offset of {z_offset:+.3f} m to all "
                     f"DXF rings (DXF -> NZVD2016 datum correction)")
            _apply_z_offset_to_classified(classified, z_offset)

        # Step 4: Identify (or use constructed kl from the Geometry tab)
        constructed_kl = CFG.get('constructed_kl')
        if constructed_kl is not None:
            LOG.start_step("Using constructed rings (anchor + parameters build-up)")
            kl = dict(constructed_kl)  # shallow copy so we can mutate
            # Constructed rings come from the dialog in DXF datum - apply offset
            _apply_z_offset_to_kl(kl, z_offset)
            # Force CFG slopes from the build-up overrides, otherwise step4b
            # would search for contour pairs (there are none in constructed mode)
            inner_hv = CFG.get('constructed_inner_hv')
            outer_hv = CFG.get('constructed_outer_hv')
            if inner_hv is not None: CFG['inner_hv'] = float(inner_hv)
            if outer_hv is not None: CFG['outer_hv'] = float(outer_hv)
            # Auto-elevations from the constructed kl (so step5/6/7 don't
            # re-derive them from the now-replaced rings)
            if CFG.get('auto_elev'):
                CFG['invert']  = round(kl['inner_toe']['z_mean'], 2)
                CFG['crest']   = round(kl['inner_crest']['z_mean'], 2)
                CFG['toe_low'] = round(kl['outer_toe']['z_min'], 2)
            LOG.info(f"Inner toe   Z={kl['inner_toe']['z_mean']:.2f} m, "
                     f"{kl['inner_toe']['npts']} pts")
            LOG.info(f"Inner crest Z={kl['inner_crest']['z_mean']:.2f} m, "
                     f"{kl['inner_crest']['npts']} pts")
            LOG.info(f"Outer crest Z={kl['outer_crest']['z_mean']:.2f} m, "
                     f"{kl['outer_crest']['npts']} pts")
            LOG.info(f"Outer toe   Z={kl['outer_toe']['z_mean']:.2f} m, "
                     f"{kl['outer_toe']['npts']} pts")
            LOG.info(f"Design slopes: inner H:V = {CFG['inner_hv']:.2f}:1, "
                     f"outer H:V = {CFG['outer_hv']:.2f}:1 (from overrides)")
            LOG.success("Constructed rings ready (step4 + step4b skipped)")
        else:
            kl = step4_identify(classified)
            # Apply manual role overrides from the dialog picker BEFORE step4b.
            # The user may have picked a different ring (typically the actual
            # variable-Z outer-toe polyline draped on natural ground) than
            # what step4_identify auto-selected. We get INDICES from the
            # dialog (not ring objects) so the z_offset stays applied
            # consistently across all kl rings - the lookup hits classified's
            # already-offset rings.
            ro_idx = CFG.get('role_override_indices')
            n_const_dlg = CFG.get('n_const_in_preview')
            if ro_idx:
                # Combined list in the same order the dialog's preview saw:
                # const-Z first, then var-Z. step3_classify is deterministic so
                # this matches the dialog's all_rings indexing.
                combined = (list(classified['const_z'])
                            + list(classified['var_z']))
                n_const_run = len(classified['const_z'])
                if (n_const_dlg is not None
                        and n_const_dlg != n_const_run):
                    LOG.warn(f"Ring count drift between preview "
                             f"({n_const_dlg} const-Z) and run "
                             f"({n_const_run} const-Z) - role overrides may "
                             f"be applied to wrong rings. Check classify "
                             f"parameters haven't changed.")
                swaps = []
                for role in ('inner_toe', 'inner_crest', 'outer_crest', 'outer_toe'):
                    idx = ro_idx.get(role)
                    if idx is None or idx < 0 or idx >= len(combined):
                        continue
                    new_r = combined[idx]
                    old_r = kl.get(role)
                    if old_r is None or old_r is not new_r:
                        kl[role] = new_r
                        is_var = idx >= n_const_run
                        tag = (f"V{idx - n_const_run + 1}" if is_var
                               else f"#{idx + 1}")
                        z_desc = (f"Z=[{new_r['z_min']:.2f},{new_r['z_max']:.2f}]"
                                  if is_var else f"Z={new_r['z_mean']:.2f}")
                        swaps.append(f"{role}<-{tag} ({z_desc})")
                if swaps:
                    LOG.info("Applied manual role override(s) from picker:")
                    for s in swaps:
                        LOG.detail(f"  {s}")
            # Step 4b: Detect design batter slopes from contour rings
            step4b_detect_slopes(kl)
            # Step 4c: Promote outer toe to variable-Z using partial
            # contour endpoints, if any are present in the DXF.
            try:
                step4c_var_z_outer_toe(kl)
            except Exception as e:
                LOG.warn(f"step4c_var_z_outer_toe failed ({e}); outer toe "
                         f"stays at the DXF's nominal Z.")
            # Step 4d: Build the artificial-deep, geometrically-perfect
            # outer toe ring (parallel offset of outer_crest at design
            # slope, going down to terrain_min - 5 m). This is what
            # feeds the TIN and the constant-slope post-processor - so
            # the rendered DEM has clean design slopes everywhere. The
            # active variable-Z outer toe in kl['outer_toe']['coords']
            # is the mask polygon for the final DEM clip.
            try:
                _tid = CFG.get('terrain_layer_id')
                _terrain = (QgsProject.instance().mapLayer(_tid)
                            if _tid else None)
                step4d_build_artificial_deep_outer_toe(kl, _terrain)
            except Exception as e:
                LOG.warn(f"step4d_build_artificial_deep_outer_toe failed "
                         f"({e}); using fallback outer toe geometry.")

    # Force Method 2 (terrain intersection) when the dam was moved off
    # the DXF datum by a non-ground snap. The DXF's baked-in outer toe
    # (Method 1, set by step4c from partial contours) reflects where the
    # dam sat in the ORIGINAL DXF. Once the user applies the cut/fill
    # snap, the max-embankment-height snap, or drags the lift/drop slider,
    # the dam no longer sits there - so Method 1 is stale and would write
    # a toe that doesn't match the height-limited dam the user designed.
    # Re-derive the toe from the terrain intersection at the dam's new
    # position. step7_outputs only auto-cuts when the toe is still
    # const-Z; here the toe is already variable-Z (Method 1), so we must
    # force the re-cut explicitly.
    if (not CFG.get('polygon_mode')
            and CFG.get('dam_moved_off_dxf_toe')):
        _tid = CFG.get('terrain_layer_id')
        _terrain = (QgsProject.instance().mapLayer(_tid) if _tid else None)
        if _terrain is not None:
            ot = kl.get('outer_toe', {})
            already_m2 = (ot.get('method') == 'method2'
                          or ot.get('cut_to_terrain'))
            if not already_m2:
                LOG.start_step("Forcing Method 2 (dam moved off DXF toe)")
                LOG.info("A non-ground snap (cut/fill, max-height, or "
                         "manual lift/drop) moved the dam off the DXF "
                         "datum. The DXF's outer toe (Method 1) is now "
                         "stale; re-deriving the toe from the terrain "
                         "intersection so the output matches the dam you "
                         "designed.")
                try:
                    cut_outer_toe_to_terrain(
                        kl, _terrain,
                        params={'crest_z': float(kl['outer_crest']['z_mean']),
                                'outer_hv': float(CFG.get('outer_hv', 3.0))},
                        ring_to_terrain_offset=0.0)
                    ot2 = kl.get('outer_toe', {})
                    LOG.success(
                        f"Method 2 forced: outer toe Z "
                        f"{ot2.get('z_min', 0):.2f}-{ot2.get('z_max', 0):.2f} "
                        f"m, {ot2.get('npts', 0)} vertices.")
                    if CFG.get('auto_elev'):
                        CFG['toe_low'] = round(ot2.get('z_min', CFG['toe_low']), 2)
                except Exception as e:
                    LOG.warn(f"Forced Method 2 cut failed: {e}. Output "
                             f"will use the (stale) DXF Method 1 toe.")
        else:
            LOG.warn("Dam was moved off the DXF toe by a snap, but no "
                     "terrain raster is loaded - cannot re-derive the "
                     "outer toe. Output uses the stale DXF Method 1 toe. "
                     "Load a terrain raster and re-run.")

    # Step 5: Points
    dam_pts = step5_points(kl)

    # Step 6: Spillway
    all_pts, spill_bls, spill_outline, spill_lines, gap_info = \
        step6_spillway(kl, dam_pts)

    # Step 7: Outputs
    step7_outputs(kl, all_pts, spill_bls, spill_outline,
                  spill_lines, gap_info)

    # The DEM build in step7_outputs already clips to the active
    # variable-Z outer toe polygon (kl['outer_toe']['coords']) - which
    # carries Method 1 (DXF partial contours) or Method 2 (terrain
    # intersection) per the user's choice on the Geometry tab. The
    # legacy cell-level "drape" step is dropped: it was redundant with
    # the polygon clip and produced an identical output.

    # Summary
    print("\n" + "=" * 60)
    print(f"  {TOOL_NAME} - COMPLETE")
    print("=" * 60)
    summary = LOG.summary()
    print(summary)

    # Embankment height for the summary = crest down to the LOWEST point
    # on the ACTUAL outer toe (where the batter meets natural ground).
    # CFG['toe_low'] is the ARTIFICIAL-DEEP design elevation (~15 m below
    # terrain) used only for clean TIN interpolation - reporting
    # crest - toe_low gives a meaningless ~9 m "height" that has nothing
    # to do with the real dam. After Run, kl['outer_toe'] has been cut to
    # terrain (Method 2, auto-applied in step7_outputs), so its z_min is
    # the lowest natural ground at the toe = the true max embankment
    # height reference. Fall back to CFG['toe_low'] only if the cut never
    # ran (no terrain raster), and flag it.
    emb_height = None
    emb_note = ""
    try:
        try:
            ot_final = kl.get('outer_toe', {})
        except NameError:
            ot_final = {}
        ot_zmin = ot_final.get('z_min')
        is_cut = (ot_final.get('is_variable_z')
                  or ot_final.get('cut_to_terrain'))
        if ot_zmin is not None and is_cut:
            emb_height = CFG['crest'] - float(ot_zmin)
        else:
            # Toe still artificial-deep - crest - toe_low is meaningless.
            emb_height = CFG['crest'] - CFG['toe_low']
            emb_note = " (artificial-deep toe; load terrain + re-run)"
    except Exception:
        emb_height = CFG['crest'] - CFG['toe_low']

    # Result dialog
    msg = (
        f"Invert: {CFG['invert']:.2f} m NZVD2016\n"
        f"Crest: {CFG['crest']:.2f} m NZVD2016\n"
        f"Max embankment height: {emb_height:.2f} m{emb_note}\n"
        f"  (crest to lowest natural ground at outer toe)\n"
        f"Points: {len(all_pts)}\n\n"
        f"Output: {CFG['output_dir']}"
    )
    if CFG.get('polygon_mode'):
        msg = "POLYGON MODE\n\n" + msg
    if LOG.warnings:
        msg += f"\n\n{len(LOG.warnings)} warning(s) - check console"
    if LOG.errors:
        msg += f"\n\n{len(LOG.errors)} error(s) - check console"
        QMessageBox.warning(None, TOOL_NAME, msg)
    else:
        QMessageBox.information(None, TOOL_NAME, msg)


# =============================================================================
# LAUNCH
# =============================================================================

print(f"\n[{TOOL_NAME}] Script loaded successfully.")

# Check iface is available
try:
    _test = iface.mainWindow()
except NameError:
    print(f"[{TOOL_NAME}] ERROR: 'iface' not found. "
          f"This script must be run from the QGIS Python Console.")
    raise RuntimeError("Run this script from QGIS Python Console, not standalone.")


def _on_accepted():
    """Called when user clicks Run."""
    global _dam_dlg
    dlg = _dam_dlg
    if dlg is None or dlg.result_params is None:
        print(f"[{TOOL_NAME}] No parameters - aborting.")
        return
    print(f"[{TOOL_NAME}] Parameters accepted. Running...")
    try:
        run(dlg.result_params)
    except Exception as e:
        tb = traceback.format_exc()
        print(f"\n{'='*60}")
        print(f"  FATAL ERROR during execution")
        print(f"{'='*60}")
        print(tb)
        QMessageBox.critical(
            None, f"{TOOL_NAME} - Fatal Error",
            f"The tool failed with an unrecoverable error.\n\n"
            f"Step: [{LOG.current_step}/{LOG.total_steps}] {LOG.step_name}\n\n"
            f"Error: {e}\n\n"
            f"Full traceback has been printed to the Python console.\n"
            f"Copy it if reporting this issue.")


def _on_rejected():
    """Called when user clicks Cancel."""
    print(f"[{TOOL_NAME}] Cancelled by user.")


# Keep a global reference so the dialog isn't garbage collected
_dam_dlg = None

try:
    print(f"[{TOOL_NAME}] Opening dialog...")
    _dam_dlg = TransformerDialog(iface, iface.mainWindow())

    # Non-modal: show() instead of exec_()
    # This allows the map canvas to receive clicks while dialog is hidden
    _dam_dlg.accepted.connect(_on_accepted)
    _dam_dlg.rejected.connect(_on_rejected)

    print(f"[{TOOL_NAME}] Dialog created. Showing (non-modal)...")
    _dam_dlg.show()
    _dam_dlg.raise_()
    _dam_dlg.activateWindow()

except Exception as e:
    tb = traceback.format_exc()
    print(f"\n{'='*60}")
    print(f"  FATAL ERROR during dialog/startup")
    print(f"{'='*60}")
    print(tb)
    try:
        QMessageBox.critical(
            None, f"{TOOL_NAME} - Startup Error",
            f"Failed to launch the tool.\n\n"
            f"Error: {e}\n\n"
            f"Full traceback printed to Python console.")
    except:
        pass
