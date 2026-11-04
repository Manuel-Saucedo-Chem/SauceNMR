"""
SauceNMR 1.0
------------
A desktop tool for processing and analyzing NMR (nuclear magnetic
resonance) data: open a raw FID (free induction decay), Fourier-transform
it into a frequency-domain spectrum, and work it up interactively.

Features
    - Fourier transform with zero-filling, line broadening, and digital
      filter (group delay) correction
    - Manual and automatic phase correction
    - Solvent referencing against literature chemical shifts, with
      manual fine-positioning of the reference tag
    - Peak integration with draggable windows and relative H-counts
    - Multiplicity assignment (manual or automatic) with J values
    - Baseline correction from user-picked points
    - Residual solvent / impurity detection against a built-in table
    - SI-style NMR report text generated from the assigned peaks
    - Multiple spectra open at once as pages, with overlay and stacked
      comparison views
    - A compound library: a shared folder of reference spectra that can
      be searched, loaded, and compared against the current spectrum
    - Publication-quality figure export

Input format
    The default assumption is a raw binary file with no header containing
    interleaved 32-bit signed little-endian integers as (real, imaginary)
    pairs - the layout written by Bruker spectrometers, where the file is
    typically named "fid" with no extension. If your data uses a
    different type or byte order, change it in the Data Format panel
    before loading.

Requires: customtkinter, numpy, matplotlib
    pip install customtkinter numpy matplotlib
Optional (peak finding and auto-multiplicity): scipy
    pip install scipy
Optional (drag-and-drop to open a file): tkinterdnd2
    pip install tkinterdnd2
"""

import os
import re
import time
import json
import queue
import base64
import tempfile
import threading
import tkinter as tk
from tkinter import filedialog, messagebox

import numpy as np
import matplotlib
import matplotlib.transforms as mtransforms

try:
    from scipy.signal import find_peaks
    _SCIPY_AVAILABLE = True
except ImportError:
    _SCIPY_AVAILABLE = False


def _trapz(y, x):
    """np.trapz was removed in numpy 2.0 (renamed to np.trapezoid). Support
    both, since we don't control which numpy version is installed."""
    if hasattr(np, "trapezoid"):
        return np.trapezoid(y, x)
    return np.trapz(y, x)

matplotlib.use("TkAgg")
# Free up 'f' (fullscreen) and 'h'/'home' so our own F/H hotkeys don't
# collide with matplotlib's built-in canvas shortcuts.
matplotlib.rcParams["keymap.fullscreen"] = []
matplotlib.rcParams["keymap.home"] = []
# A wide-sweep spectrum (or heavy zero-fill) can put hundreds of thousands
# of points on the spectrum line. Every redraw - including just changing
# y-limits when scrolling to zoom - has to process the WHOLE line, not just
# what's visible, unless path simplification is on. This is the standard
# matplotlib fix for "big line plot feels laggy" and doesn't change how
# anything looks; it collapses points that fall on top of each other at
# the rendered resolution before drawing.
matplotlib.rcParams["path.simplify"] = True
matplotlib.rcParams["path.simplify_threshold"] = 1.0
matplotlib.rcParams["agg.path.chunksize"] = 20000
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.figure import Figure
from matplotlib.widgets import RectangleSelector, SpanSelector

import customtkinter as ctk

try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    _DND_AVAILABLE = True
except ImportError:
    _DND_AVAILABLE = False

APP_TITLE = "SauceNMR 1.0"

PROCESSED_FILE_EXT = ".saucenmr"
PROCESSED_FILE_MAGIC = "saucenmr_processed_v1"     # legacy: a single spectrum
PROCESSED_FILE_MAGIC_V2 = "saucenmr_processed_v2"  # current: any number of pages

AUTOSAVE_INTERVAL_MS = 30000  # how often the active page is autosaved
AUTOSAVE_MAX_FILES = 2        # per source folder - oldest gets reused once at the cap
AUTOSAVE_NAME_RE = re.compile(r"^sauceNMR_autosave_(\d+)\.saucenmr$")

# --------------------------------------------------------------- library --
# A compound library: a shared root folder (e.g. a lab Dropbox), one
# sub-folder per compound, containing exactly one .saucenmr file - the
# single best NMR ever made for that compound. Saving a new one over an
# existing one replaces it (after confirming). Routine/every-day NMRs
# live wherever they already did before this feature existed (manual
# save folders, autosave) - this library is purely the gold-star shelf.
APP_CONFIG_DIR = os.path.join(os.path.expanduser("~"), ".saucenmr")
APP_CONFIG_PATH = os.path.join(APP_CONFIG_DIR, "config.json")
LIBRARY_GOLD_STAR_DIR = "gold_star"  # legacy sub-folder name, read for backward compatibility only
# XX-n-mmm: 2-3 letter initials, a lab notebook number, an entry 1-155
NOTEBOOK_ID_RE = re.compile(r"^([A-Za-z]{2,3})-(\d+)-(\d{1,3})$")

# ---------------------------------------------------------------- theme --
ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

BG_COLOR = "#101114"
PANEL_COLOR = "#181a1f"
ACCENT = "#3ea6ff"
TEXT_MUTED = "#8b8f98"
PLOT_LINE_COLOR = "#3ea6ff"
PLOT_GRID_COLOR = "#2a2d34"
TAG_COLOR = "#ff5c5c"  # deliberately different from the spectrum's accent
                        # blue, so impurity tags don't visually blend with the
                        # peak and make it look taller than it actually is
INTEGRATION_COLOR = "#4caf50"  # green, distinct from zoom (blue) and tags (red)
INTEGRATION_HANDLE_COLOR = "#a5d6a7"  # lighter green, the draggable edge handles

MULTIPLICITY_LABELS = {1: "s", 2: "d", 3: "t", 4: "q", 5: "quint", 6: "sext", 7: "hept"}
MULTIPLICITY_COLOR = "#ab47bc"  # purple, distinct from integration's green

# Fixed axes-fraction Y positions (0=bottom, 1=top of the CURRENT view) for the
# integration bar and its labels. Using axes-fraction rather than data
# coordinates means these stay pinned to the same visual spot as the user
# scrolls/zooms, and every region's row aligns with every other region's.
INTEGRATION_BAR_YMAX = 0.045
INTEGRATION_H_LABEL_Y = 0.05   # H-tag: rotated vertical text growing UPWARD from here
INTEGRATION_M_LABEL_Y = 0.02   # multiplicity tag: rotated vertical text growing DOWNWARD from here
SOLVENT_TAG_COLOR = "#ffd54a"  # gold, marks the solvent reference peak specifically

# Same idea, but for the solvent-reference/impurity tags at the top of the
# plot: pinned to the top 10% of the axes regardless of peak height or zoom,
# just like the integration row is pinned to the bottom.
TAG_BAND_YMIN = 0.90   # bottom of the fixed tag band (axes-fraction)
TAG_STUB_YMAX = 0.93   # the flagpole line only extends this far - a short tick, not the whole band
TAG_LABEL_Y = 0.935    # rotated label baseline, growing UPWARD (va="bottom") above the stub - no overlap
BASELINE_COLOR = "#ffa726"  # orange, distinct from every other marker/tag color in use

# Plot appearance themes - selectable from the Export tab. Only affects the
# plot itself (trace/labels/background), not the surrounding app UI.
PLOT_THEMES = {
    "Neon": {
        "bg": BG_COLOR, "text": "#d7d9de", "trace": PLOT_LINE_COLOR, "grid": PLOT_GRID_COLOR,
        "integration": INTEGRATION_COLOR, "integration_handle": INTEGRATION_HANDLE_COLOR,
        "multiplicity": MULTIPLICITY_COLOR, "tag": TAG_COLOR,
        "solvent_tag": SOLVENT_TAG_COLOR, "baseline": BASELINE_COLOR,
        "overlay_palette": ["#3ea6ff", "#ff6b6b", "#66d9a0", "#ffd54a", "#c77dff", "#ff9f4a", "#5fd4d4", "#e07bd0"],
    },
    "Hacker": {
        "bg": "#000000", "text": "#33ff66", "trace": "#39ff14", "grid": "#0d3319",
        "integration": "#39ff14", "integration_handle": "#a8ffb0",
        "multiplicity": "#00e5a0", "tag": "#39ff14",
        "solvent_tag": "#ccff00", "baseline": "#39ff14",
        # every trace in the green family, just distinguishable shades -
        # keeps the monochrome CRT look even with multiple spectra on screen
        "overlay_palette": ["#39ff14", "#00e676", "#76ff03", "#1de9b6", "#66ff99", "#00c853", "#aeea00", "#00e5a0"],
    },
    "Professional": {
        "bg": "#ffffff", "text": "#000000", "trace": "#000000", "grid": "#d0d0d0",
        "integration": "#1565c0", "integration_handle": "#64b5f6",
        "multiplicity": "#1565c0", "tag": "#1565c0",
        "solvent_tag": "#1565c0", "baseline": "#1565c0",
        "overlay_palette": ["#3ea6ff", "#ff6b6b", "#66d9a0", "#ffd54a", "#c77dff", "#ff9f4a", "#5fd4d4", "#e07bd0"],
    },
}

DTYPE_OPTIONS = {
    "32-bit integer (Bruker default)": "i4",
    "64-bit integer": "i8",
    "16-bit integer": "i2",
    "32-bit float": "f4",
    "64-bit float": "f8",
}

BYTE_ORDER_OPTIONS = {
    "Little-endian (default)": "<",
    "Big-endian": ">",
}

ZERO_FILL_OPTIONS = ["1x (none)", "2x", "4x", "8x"]

# 1H NMR residual solvent peaks (ppm), from Fulmer et al., Organometallics
# 2010, 29, 2176-2179, Table 1 "solvent residual signals" row (including
# wrapped continuation values for solvents with more than one residual
# peak). Used for referencing the spectrum to a known internal standard.
SOLVENT_RESIDUAL_PEAKS = [
    ("CDCl3", [7.26]),
    ("C6D6", [7.16]),
    ("CD2Cl2", [5.32]),
    ("(CD3)2CO", [2.05]),
    ("(CD3)2SO", [2.50]),
    ("CD3CN", [1.94]),
    ("CD3OD", [3.31]),
    ("D2O", [4.79]),
    ("THF-d8", [1.72, 3.58]),
    ("toluene-d8", [2.08, 6.97, 7.01, 7.09]),
    ("C6D5Cl", [6.96, 6.99, 7.14]),
    ("TFE-d3", [5.02, 3.88]),
]

# 1H NMR impurity/organics data, transcribed from Fulmer et al., Organometallics
# 2010, 29, 2176-2179, Table 1. Column order matches the paper exactly.
# `None` marks values not reported/not observed for that solvent.
IMPURITY_SOLVENT_COLUMNS = [
    "THF-d8", "CD2Cl2", "CDCl3", "toluene-d8", "C6D6", "C6D5Cl",
    "(CD3)2CO", "(CD3)2SO", "CD3CN", "TFE-d3", "CD3OD", "D2O",
]

IMPURITY_RAW_ROWS = [
    ("water", [2.46, 1.52, 1.56, 0.43, 0.40, 1.03, 2.84, 3.33, 2.13, 3.66, 4.87, None]),
    ("acetic acid", [1.89, 2.06, 2.10, 1.57, 1.52, 1.76, 1.96, 1.91, 1.96, 2.06, 1.99, 2.08]),
    ("acetone", [2.05, 2.12, 2.17, 1.57, 1.55, 1.77, 2.09, 2.09, 2.08, 2.19, 2.15, 2.22]),
    ("acetonitrile", [1.95, 1.97, 2.10, 0.69, 0.58, 1.21, 2.05, 2.07, 1.96, 1.95, 2.03, 2.06]),
    ("benzene", [7.31, 7.35, 7.36, 7.12, 7.15, 7.20, 7.36, 7.37, 7.37, 7.36, 7.33, None]),
    ("tert-butyl alcohol (CH3)", [1.15, 1.24, 1.28, 1.03, 1.05, 1.12, 1.18, 1.11, 1.16, 1.28, 1.40, 1.24]),
    ("chloroform", [7.89, 7.32, 7.26, 6.10, 6.15, 6.74, 8.02, 8.32, 7.58, 7.33, 7.90, None]),
    ("18-crown-6", [3.57, 3.59, 3.67, 3.36, 3.39, 3.41, 3.59, 3.51, 3.51, 3.64, 3.64, 3.80]),
    ("cyclohexane", [1.44, 1.44, 1.43, 1.40, 1.40, 1.37, 1.43, 1.40, 1.44, 1.47, 1.45, None]),
    ("1,2-dichloroethane", [3.77, 3.76, 3.73, 2.91, 2.90, 3.26, 3.87, 3.90, 3.81, 3.71, 3.78, None]),
    ("dichloromethane", [5.51, 5.33, 5.30, 4.32, 4.27, 4.77, 5.63, 5.76, 5.44, 5.24, 5.49, None]),
    ("diethyl ether (CH3)", [1.12, 1.15, 1.21, 1.10, 1.11, 1.10, 1.11, 1.09, 1.12, 1.20, 1.18, 1.17]),
    ("diethyl ether (CH2)", [3.38, 3.43, 3.48, 3.25, 3.26, 3.31, 3.41, 3.38, 3.42, 3.58, 3.49, 3.56]),
    ("diglyme (CH2 a)", [3.43, 3.57, 3.65, 3.43, 3.46, 3.49, 3.56, 3.51, 3.53, 3.67, 3.61, 3.67]),
    ("diglyme (CH2 b)", [3.53, 3.50, 3.57, 3.31, 3.34, 3.37, 3.47, 3.38, 3.45, 3.62, 3.58, 3.61]),
    ("diglyme (OCH3)", [3.28, 3.33, 3.39, 3.12, 3.11, 3.16, 3.28, 3.24, 3.29, 3.41, 3.35, 3.37]),
    ("dimethylformamide (CH)", [7.91, 7.96, 8.02, 7.57, 7.63, 7.73, 7.96, 7.95, 7.92, 7.86, 7.97, 7.92]),
    ("dimethylformamide (CH3 a)", [2.88, 2.91, 2.96, 2.37, 2.36, 2.51, 2.94, 2.89, 2.89, 2.98, 2.99, 3.01]),
    ("dimethylformamide (CH3 b)", [2.76, 2.82, 2.88, 1.96, 1.86, 2.30, 2.78, 2.73, 2.77, 2.88, 2.86, 2.85]),
    ("1,4-dioxane", [3.56, 3.65, 3.71, 3.33, 3.35, 3.45, 3.59, 3.57, 3.60, 3.76, 3.66, 3.75]),
    ("DME (CH3)", [3.28, 3.34, 3.40, 3.12, 3.12, 3.17, 3.28, 3.24, 3.28, 3.40, 3.35, 3.37]),
    ("DME (CH2)", [3.43, 3.49, 3.55, 3.31, 3.33, 3.37, 3.46, 3.43, 3.45, 3.61, 3.52, 3.60]),
    ("ethane", [0.85, 0.85, 0.87, 0.81, 0.80, 0.79, 0.83, 0.82, 0.85, 0.85, 0.85, 0.82]),
    ("ethanol (CH3)", [1.10, 1.19, 1.25, 0.97, 0.96, 1.06, 1.12, 1.06, 1.12, 1.22, 1.19, 1.17]),
    ("ethanol (CH2)", [3.51, 3.66, 3.72, 3.36, 3.34, 3.51, 3.57, 3.44, 3.54, 3.71, 3.60, 3.65]),
    ("ethyl acetate (CH3CO)", [1.94, 2.00, 2.05, 1.69, 1.65, 1.78, 1.97, 1.99, 1.97, 2.03, 2.01, 2.07]),
    ("ethyl acetate (OCH2)", [4.04, 4.08, 4.12, 3.87, 3.89, 3.96, 4.05, 4.03, 4.06, 4.14, 4.09, 4.14]),
    ("ethyl acetate (CH3, ethyl)", [1.19, 1.23, 1.26, 0.94, 0.92, 1.04, 1.20, 1.17, 1.20, 1.26, 1.24, 1.24]),
    ("ethylene", [5.36, 5.40, 5.40, 5.25, 5.25, 5.29, 5.38, 5.41, 5.41, 5.40, 5.39, 5.44]),
    ("ethylene glycol", [3.48, 3.66, 3.76, 3.36, 3.41, 3.58, 3.28, 3.34, 3.51, 3.72, 3.59, 3.65]),
    ("H grease (CH3)", [0.88, 0.87, 0.855, 0.925, 0.94, 0.89, 0.90, 0.85, None, 0.91, 0.895, None]),
    ("H grease (CH2)", [1.29, 1.27, 1.25, 1.33, 1.32, 1.30, 1.29, 1.24, None, 1.33, 1.29, None]),
    ("hexamethylbenzene", [2.18, 2.20, 2.24, 2.10, 2.13, 2.10, 2.17, 2.14, 2.19, 2.24, 2.19, None]),
    ("n-hexane (CH3)", [0.89, 0.89, 0.88, 0.88, 0.89, 0.85, 0.88, 0.86, 0.89, 0.91, 0.90, None]),
    ("n-hexane (CH2)", [1.29, 1.27, 1.26, 1.22, 1.24, 1.19, 1.28, 1.25, 1.28, 1.31, 1.29, None]),
    ("hexamethyldisiloxane", [0.07, 0.07, 0.07, 0.10, 0.12, 0.10, 0.07, 0.06, 0.07, 0.08, 0.07, 0.28]),
    ("HMPA", [2.58, 2.60, 2.65, 2.42, 2.40, 2.47, 2.59, 2.53, 2.57, 2.63, 2.64, 2.61]),
    ("hydrogen", [4.55, 4.59, 4.62, 4.50, 4.47, 4.49, 4.54, 4.61, 4.57, 4.53, 4.56, None]),
    ("imidazole (CH2)", [7.48, 7.63, 7.67, 7.30, 7.33, 7.53, 7.62, 7.63, 7.57, 7.61, 7.67, 7.78]),
    ("imidazole (CH4,5)", [6.94, 7.07, 7.10, 6.86, 6.90, 7.01, 7.04, 7.01, 7.01, 7.03, 7.05, 7.14]),
    ("methane", [0.19, 0.21, 0.22, 0.17, 0.16, 0.15, 0.17, 0.20, 0.20, 0.18, 0.20, 0.18]),
    ("methanol (CH3)", [3.27, 3.42, 3.49, 3.03, 3.07, 3.25, 3.31, 3.16, 3.28, 3.44, 3.34, 3.34]),
    ("nitromethane", [4.31, 4.31, 4.33, 3.01, 2.94, 3.59, 4.43, 4.42, 4.31, 4.28, 4.34, 4.40]),
    ("n-pentane (CH3)", [0.89, 0.89, 0.88, 0.87, 0.87, 0.84, 0.88, 0.86, 0.89, 0.90, 0.90, None]),
    ("n-pentane (CH2)", [1.31, 1.30, 1.27, 1.25, 1.23, 1.23, 1.27, 1.27, 1.29, 1.33, 1.29, None]),
    ("propane (CH3)", [0.90, 0.90, 0.90, 0.89, 0.86, 0.84, 0.88, 0.87, 0.90, 0.90, 0.91, 0.88]),
    ("propane (CH2)", [1.33, 1.32, 1.32, 1.32, 1.26, 1.26, 1.31, 1.29, 1.33, 1.33, 1.34, 1.30]),
    ("2-propanol (CH3)", [1.08, 1.17, 1.22, 0.95, 0.95, 1.04, 1.10, 1.04, 1.09, 1.20, 1.15, 1.17]),
    ("2-propanol (CH)", [3.82, 3.97, 4.04, 3.65, 3.67, 3.82, 3.90, 3.78, 3.87, 4.05, 3.92, 4.02]),
    ("propylene (CH3)", [1.69, 1.71, 1.73, 1.55, 1.55, 1.58, 1.68, 1.68, 1.70, 1.70, 1.70, 1.70]),
    ("propylene (CH2, 1)", [4.89, 4.93, 4.94, 4.92, 4.95, 4.91, 4.90, 4.94, 4.93, 4.93, 4.91, 4.95]),
    ("propylene (CH2, 2)", [4.99, 5.03, 5.03, 4.98, 5.01, 4.98, 5.00, 5.03, 5.04, 5.03, 5.01, 5.06]),
    ("propylene (CH)", [5.79, 5.84, 5.83, 5.70, 5.72, 5.72, 5.81, 5.80, 5.85, 5.87, 5.82, 5.90]),
    ("pyridine (CH2,6)", [8.54, 8.59, 8.62, 8.47, 8.53, 8.51, 8.58, 8.58, 8.57, 8.45, 8.53, 8.52]),
    ("pyridine (CH3,5)", [7.25, 7.28, 7.29, 6.67, 6.66, 6.90, 7.35, 7.39, 7.33, 7.40, 7.44, 7.45]),
    ("pyridine (CH4)", [7.65, 7.68, 7.68, 6.99, 6.98, 7.25, 7.76, 7.79, 7.73, 7.82, 7.85, 7.87]),
    ("pyrrole (CH2,5)", [6.66, 6.79, 6.83, 6.43, 6.48, 6.62, 6.77, 6.73, 6.75, 6.84, 6.72, 6.93]),
    ("pyrrole (CH3,4)", [6.02, 6.19, 6.26, 6.27, 6.37, 6.27, 6.07, 6.01, 6.10, 6.24, 6.08, 6.26]),
    ("pyrrolidine (CH2,5)", [2.75, 2.82, 2.87, 2.54, 2.54, 2.64, None, 2.67, 2.75, 3.11, 2.80, 3.07]),
    ("pyrrolidine (CH3,4)", [1.59, 1.67, 1.68, 1.36, 1.33, 1.43, None, 1.55, 1.61, 1.93, 1.72, 1.87]),
    ("silicone grease", [0.11, 0.09, 0.07, 0.26, 0.29, 0.14, 0.13, -0.06, 0.08, 0.16, 0.10, None]),
    ("tetrahydrofuran (CH2,5)", [3.62, 3.69, 3.76, 3.54, 3.57, 3.59, 3.63, 3.60, 3.64, 3.78, 3.71, 3.74]),
    ("tetrahydrofuran (CH3,4)", [1.79, 1.82, 1.85, 1.43, 1.40, 1.55, 1.79, 1.76, 1.80, 1.91, 1.87, 1.88]),
    ("toluene (CH3)", [2.31, 2.34, 2.36, 2.11, 2.11, 2.16, 2.32, 2.30, 2.33, 2.33, 2.32, None]),
    ("toluene (CH2,4,6)", [7.10, 7.15, 7.17, 6.985, 7.02, 7.045, 7.15, 7.18, 7.20, 7.20, 7.16, None]),
    ("toluene (CH3,5)", [7.19, 7.24, 7.25, 7.09, 7.13, 7.135, 7.15, 7.25, 7.20, 7.20, 7.16, None]),
    ("triethylamine (CH3)", [0.97, 0.99, 1.03, 0.95, 0.96, 0.93, 0.96, 0.93, 0.96, 1.31, 1.05, 0.99]),
    ("triethylamine (CH2)", [2.46, 2.48, 2.53, 2.39, 2.40, 2.39, 2.45, 2.43, 2.45, 3.12, 2.58, 2.57]),
]

IMPURITY_ROWS = [
    (name, dict(zip(IMPURITY_SOLVENT_COLUMNS, values)))
    for name, values in IMPURITY_RAW_ROWS
]

# Maps each deuterated NMR solvent to the name of its own protio compound in
# IMPURITY_ROWS, so the solvent itself never shows up as a "detected
# impurity" of its own spectrum (e.g. CDCl3 shouldn't flag "chloroform").
SOLVENT_SELF_COMPOUND = {
    "CDCl3": "chloroform",
    "C6D6": "benzene",
    "CD2Cl2": "dichloromethane",
    "(CD3)2CO": "acetone",
    "CD3CN": "acetonitrile",
    "CD3OD": "methanol",
    "D2O": "water",
    "THF-d8": "tetrahydrofuran",
    "toluene-d8": "toluene",
}

# How each internal solvent identifier is conventionally written in an SI/
# experimental section - most match already; a few (parenthetical formulas)
# are normally spelled out instead.
SOLVENT_REPORT_NAMES = {
    "C6D6": "benzene-d6",
    "(CD3)2CO": "acetone-d6",
    "(CD3)2SO": "DMSO-d6",
}

# For rendering chemical formulas correctly in report text - e.g. CDCl3 -> CDCl₃
_SUBSCRIPT_DIGITS = str.maketrans("0123456789", "\u2080\u2081\u2082\u2083\u2084\u2085\u2086\u2087\u2088\u2089")


_AppBases = (ctk.CTk, TkinterDnD.DnDWrapper) if _DND_AVAILABLE else (ctk.CTk,)


class SauceNMRApp(*_AppBases):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1200x780")
        self.minsize(900, 600)
        self.configure(fg_color=BG_COLOR)

        if _DND_AVAILABLE:
            self.TkdndVersion = TkinterDnD._require(self)
            self.drop_target_register(DND_FILES)
            self.dnd_bind("<<Drop>>", self._on_file_drop)

        self.current_path = None
        self._raw_fid = None  # uncorrected, exactly as read from disk
        self.complex_data = None
        self.spectrum_data = None

        # --- multi-spectrum pages ---
        self.pages = []  # [{"name": str, "state": dict_or_None}, ...]
        self.current_page_index = None  # index into self.pages of the page currently shown
        self.overlay_selected = set()  # page indices shift-clicked for the next overlay
        self._overlay_lines = []  # Line2D objects currently shown, matching the overlay page's series order
        self._page_drag = None  # {"start_index":, "dragging":, "target_index":} while drag-reordering pages
        self._page_drag_indicator = None  # thin accent-colored frame shown at the drop position while dragging
        self._page_preview_timer = None  # after() id for the pending 3s hover-preview
        self._page_preview_popup = None  # the small preview Toplevel, if one is currently shown
        self._page_preview_figure = None  # its matplotlib Figure, so it can be closed cleanly
        self.freq_axis = None
        self.freq_unit = "index"
        self.view_mode = "spectrum"  # "fid" or "spectrum"

        self.dtype_name = tk.StringVar(value="32-bit integer (Bruker default)")
        self.byte_order_name = tk.StringVar(value="Little-endian (default)")

        self.zero_fill_name = tk.StringVar(value=ZERO_FILL_OPTIONS[0])
        self.line_broadening = tk.StringVar(value="0")
        self.spectral_width = tk.StringVar(value="")
        self.transmitter_offset = tk.StringVar(value="")
        self.spectrometer_freq = tk.StringVar(value="")
        self.grpdly = tk.StringVar(value="")
        self.phase_deg = tk.StringVar(value="0")
        self.reverse_axis = tk.BooleanVar(value=True)
        self.plot_style_name = tk.StringVar(value="Neon")  # placeholder for future styles

        # View tab display toggles - apply everywhere, all the time
        self.plot_show_title = tk.BooleanVar(value=False)
        self.plot_title_text = tk.StringVar(value="Spectrum")
        self.plot_show_ylabel = tk.BooleanVar(value=False)
        self.plot_show_grid = tk.BooleanVar(value=False)
        self.plot_show_box = tk.BooleanVar(value=True)

        # Export tab preview toggles - only affect the plot while the
        # Export tab itself is the active tab; switching to any other tab
        # always shows everything normally regardless of these.
        self.export_show_integration_highlight = tk.BooleanVar(value=True)  # the shaded bar
        self.export_show_integration_numbers = tk.BooleanVar(value=True)    # the "4.0" label
        self.export_show_multiplicity = tk.BooleanVar(value=True)           # the "d"/"dd" tag only
        self.export_show_peak_position = tk.BooleanVar(value=True)          # the ppm number under a peak
        self.export_show_impurities = tk.BooleanVar(value=True)             # residual-solvent tags
        self.export_show_legend = tk.BooleanVar(value=True)                 # FID/overlay legend
        # Y position (axes-fraction, 0-100%) of each annotation type's text -
        # defaults match the fixed values used everywhere else in the app.
        self.export_integration_number_y = tk.DoubleVar(value=INTEGRATION_H_LABEL_Y * 100)
        self.export_multiplicity_y = tk.DoubleVar(value=INTEGRATION_M_LABEL_Y * 100)
        self.export_peak_position_y = tk.DoubleVar(value=TAG_LABEL_Y * 100)
        self.export_impurity_y = tk.DoubleVar(value=TAG_LABEL_Y * 100)
        self.export_solvent_reference_y = tk.DoubleVar(value=TAG_LABEL_Y * 100)  # the "CDCl3"/reference peak tag
        self.export_show_position_ticks = tk.BooleanVar(value=True)  # the little stub/flagpole lines
        self.export_position_ticks_y = tk.DoubleVar(value=TAG_STUB_YMAX * 100)  # independent of the text position

        # Library (compound inventory) state
        self.library_root = tk.StringVar(value=self._load_app_config().get("library_root", ""))
        self.library_search_var = tk.StringVar(value="")
        self._library_check_vars = {}  # path -> BooleanVar, for the Overlay/Stack-checked feature
        # The folder walk in _scan_library_folder is the slow part on a
        # cloud-synced (e.g. Dropbox) library - it runs on a background
        # thread (see _refresh_library_list) so it never blocks the window
        # from opening or freezes the UI. These track that scan.
        self._library_scan_cache = None  # (root_path, [(name, gold_path_or_None), ...]) from the last completed scan
        self._library_scan_token = 0  # bumped per scan so a stale (superseded) one can be discarded on arrival
        self._library_scan_queue = queue.Queue()  # worker -> UI handoff; polled only while a scan is in flight
        self.export_dpi = tk.StringVar(value="300")
        self.export_baseline_margin = tk.DoubleVar(value=7.5)  # % of view height below y=0
        self._pre_export_ylim = None  # view remembered when entering the Export tab

        # --- zoom state ---
        self.zoom_modes = ["Horizontal", "Vertical", "Both"]
        self.zoom_mode = "Horizontal"
        self.zoom_active = False  # zoom selectors are off until Z is pressed
        self.zoom_click_count = 0
        self.span_h_selector = None
        self.span_v_selector = None
        self.rect_selector = None
        self.full_xlim = None
        self.full_ylim = None
        self.default_ylim = None  # the "nice" baseline-margined view (like after scrolling once)

        # --- solvent-peak referencing state ---
        self.pick_mode = False
        self.ppm_reference_offset = 0.0
        self.pick_popup = None
        self.pick_coord_text = None
        self.pick_hover_line = None

        # --- impurity/residual solvent detection state ---
        self.detection_solvent = tk.StringVar(value="Select solvent...")
        self.detection_popup = None
        self.detection_hover_artists = []
        self.impurity_tags = []  # list of {"line","text","ppm","name"} for persistent tags
        self.solvent_tag = None  # (line_artist, text_artist) for the gold solvent-reference tag
        self.reference_info = None  # (literature_ppm, solvent_name), re-applied after every reprocess
        self.impurity_drag = None  # {"tag":..., "start_ppm":...} while manually fitting a residual-solvent tag
        self.solvent_drag = None  # {"start_ppm":...} while manually fitting the solvent reference tag

        # --- integration state ---
        self.integrate_mode = False
        self.integration_selector = None
        self.integration_regions = []  # list of dicts: xmin, xmax, value, span, text
        self.integration_reference_area = None  # raw area of the "1H" reference integration
        self.integration_undo_stack = []  # reversible add/delete/delete_all actions
        self._undo_seq = 0  # shared counter so Ctrl+Z can tell which of several
                             # undo-able action types (integration edits, page
                             # closes, ...) happened most recently
        self.page_close_undo_stack = []  # reversible page closes
        self.zoom_undo_stack = []  # reversible zoom actions: {"seq","xlim","ylim"} = the view BEFORE the zoom
        self._zoom_undo_last_push_time = 0.0  # throttles scroll-zoom so one flick = one undo step
        self.edit_integration_popup = None
        self.integration_drag = None  # {"region":..., "side": "left"/"right"} while dragging a handle
        self.active_drag_highlight = None  # temporary full-height highlight shown only while dragging

        # --- multiplicity state ---
        self.multiplicity_mode = False
        self.multiplicity_selector = None

        # --- baseline correction state ---
        self.baseline_mode = False
        self.baseline_points = []  # in-progress picks: [{"ppm","y","marker"}], not yet applied
        self.baseline_correction_points = []  # [(ppm, y), ...] actually applied - reapplied on every replot
        self.baseline_preview_line = None  # live dashed preview of the fitted curve while picking
        self.baseline_drag = None  # {"point":, "start_ppm":, "start_y":} while dragging a picked point

        # --- phase correction state ---
        self._cached_spectrum_raw = None  # unphased spectrum, reused for live slider updates
        self.spectrum_line = None
        self._updating_phase = False
        # Set while _restore_state bulk-populates the processing fields:
        # each .set() fires a trace that would otherwise run a full
        # FFT + replot, so a page switch did that ~8 times over instead
        # of once. _restore_state reprocesses explicitly at the end.
        self._suspend_live_reprocess = False

        self._autosave_seconds_remaining = AUTOSAVE_INTERVAL_MS // 1000

        self._build_layout()
        self.autosave_countdown_label.configure(text=f"Autosave in {self._autosave_seconds_remaining}s")
        self.after(1000, self._schedule_autosave)

    # ---------------------------------------------------------------- UI --
    def _build_layout(self):
        self.grid_columnconfigure(0, weight=0)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_main_area()

    def _build_sidebar(self):
        outer = ctk.CTkFrame(self, width=320, fg_color=PANEL_COLOR, corner_radius=0)
        outer.grid(row=0, column=0, sticky="nsw")
        outer.grid_propagate(False)
        outer.grid_rowconfigure(1, weight=1)
        outer.grid_columnconfigure(0, weight=1)

        # --- Title (fixed, non-scrolling), with Open FID / Save right next to it ---
        title_frame = ctk.CTkFrame(outer, fg_color="transparent")
        title_frame.grid(row=0, column=0, sticky="ew", padx=18, pady=(20, 4))
        title_frame.grid_columnconfigure(0, weight=1)

        title_text_col = ctk.CTkFrame(title_frame, fg_color="transparent")
        title_text_col.grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(
            title_text_col, text="SauceNMR", font=ctk.CTkFont(size=22, weight="bold")
        ).pack(anchor="w")
        ctk.CTkLabel(
            title_text_col, text=APP_TITLE.replace("SauceNMR ", "version "), font=ctk.CTkFont(size=12),
            text_color=TEXT_MUTED,
        ).pack(anchor="w")

        title_btn_col = ctk.CTkFrame(title_frame, fg_color="transparent")
        title_btn_col.grid(row=0, column=1, sticky="e")
        open_fid_btn = ctk.CTkButton(
            title_btn_col, text="Open FID", command=self.browse_file,
            height=30, width=100, corner_radius=8, font=ctk.CTkFont(size=12),
        )
        open_fid_btn.pack(pady=(0, 4))
        save_btn = ctk.CTkButton(
            title_btn_col, text="Save", command=self.save_processed_file,
            height=30, width=100, corner_radius=8, font=ctk.CTkFont(size=12),
            fg_color=PANEL_COLOR, hover_color="#22252b", text_color="#d7d9de",
            border_width=1, border_color=PLOT_GRID_COLOR,
        )
        save_btn.pack()
        open_fid_btn.bind(
            "<Enter>", lambda event, w=open_fid_btn: self._show_tooltip(w, self.current_path or "No file loaded", event)
        )
        open_fid_btn.bind("<Leave>", self._hide_tooltip)
        save_hint = f"Saves ALL open pages ({PROCESSED_FILE_EXT}) - drag it back on to reopen"
        save_btn.bind("<Enter>", lambda event, w=save_btn, t=save_hint: self._show_tooltip(w, t, event))
        save_btn.bind("<Leave>", self._hide_tooltip)

        # --- Scrollable body for all the controls ---
        sidebar = ctk.CTkScrollableFrame(outer, fg_color=PANEL_COLOR)
        sidebar.grid(row=1, column=0, sticky="nsew")

        # --- Pages (multiple loaded spectra) ---
        ctk.CTkLabel(sidebar, text="PAGES", font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).pack(anchor="w", padx=18, pady=(6, 4))
        self.pages_list_frame = ctk.CTkFrame(sidebar, fg_color="transparent")
        self.pages_list_frame.pack(fill="x", padx=18, pady=(0, 8))
        self._refresh_pages_list()

        # --- Overlay (compare multiple loaded spectra on one plot) ---
        overlay_btn_row = ctk.CTkFrame(sidebar, fg_color="transparent")
        overlay_btn_row.pack(fill="x", padx=18, pady=(10, 10))
        overlay_hint = "Shift-click 2+ page names above to select them, then show"
        show_overlay_btn = ctk.CTkButton(
            overlay_btn_row, text="Overlay", command=self._show_overlay,
            height=32, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        )
        show_overlay_btn.pack(side="left", fill="x", expand=True, padx=(0, 6))
        show_stacked_btn = ctk.CTkButton(
            overlay_btn_row, text="Stack", command=self._show_stacked,
            height=32, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        )
        show_stacked_btn.pack(side="left", fill="x", expand=True)
        for btn in (show_overlay_btn, show_stacked_btn):
            btn.bind("<Enter>", lambda event, w=btn, t=overlay_hint: self._show_tooltip(w, t, event))
            btn.bind("<Leave>", self._hide_tooltip)

        # --- File status: kept as widgets (still updated everywhere they
        # always were) but not shown permanently - path shows as a tooltip
        # on "Open FID" above, and the solvent reference shows as a
        # tooltip on the "Impurities" tab (only while none is set yet).
        # "Adjust intensities" moved to the A hotkey - see Hotkeys popup.
        self.path_label = ctk.CTkLabel(sidebar, text="No file loaded")
        self.reference_label = ctk.CTkLabel(sidebar, text="No solvent reference yet (press L to pick one)")

        # --- Compact tool tabs (View / Processing / Detect Impurities /
        # Baseline / Report / Advanced) - only one panel shown at a time,
        # instead of every section stacked and always visible.
        self._build_tool_tabs(sidebar)

        ctk.CTkLabel(sidebar, text="", height=1).pack(pady=6)  # bottom breathing room

        # --- Status bar, fixed at the very bottom of the sidebar column ---
        self.status = ctk.CTkLabel(
            outer, text="Ready", text_color=TEXT_MUTED,
            font=ctk.CTkFont(size=11), wraplength=280, justify="left", anchor="w",
        )
        self.status.grid(row=2, column=0, sticky="ew", padx=18, pady=(6, 14))

    # Tab names, in display order. "Detect Impurities" is deliberately not a
    # real content tab - clicking it just runs the detection directly.
    _TOOL_TAB_NAMES = ["View", "Library", "Processing", "Detect Impurities", "Baseline", "Report", "Export", "Advanced"]
    _TOOL_TAB_CONTENT_NAMES = ["View", "Library", "Processing", "Baseline", "Report", "Export", "Advanced"]

    def _build_tool_tabs(self, sidebar):
        tabs_container = ctk.CTkFrame(sidebar, fg_color="transparent")
        tabs_container.pack(fill="both", expand=True, padx=0, pady=(6, 0))

        # A narrow strip of genuinely rotated ("sideways") text labels,
        # right at the edge of the sidebar - a real vertical-tab look,
        # rather than a column of normal wide buttons. CTkButton can't
        # rotate its own text, so these are plain tk.Canvas items instead.
        TAB_STRIP_WIDTH = 38
        tab_strip = tk.Canvas(
            tabs_container, width=TAB_STRIP_WIDTH, bg=PANEL_COLOR,
            highlightthickness=0, bd=0,
        )
        tab_strip.pack(side="left", fill="y", padx=(0, 6))

        tab_labels = {
            "View": "View", "Library": "Library", "Processing": "Processing", "Detect Impurities": "Impurities",
            "Baseline": "Baseline", "Report": "Report", "Export": "Export", "Advanced": "Advanced",
        }
        self._tool_tab_canvas = tab_strip
        self._tool_tab_items = {}  # name -> (text_item_id, bg_rect_id)
        y = 14
        row_height = 128
        for name in self._TOOL_TAB_NAMES:
            rect_id = tab_strip.create_rectangle(
                0, y, TAB_STRIP_WIDTH, y + row_height, fill=PANEL_COLOR, outline="",
            )
            text_id = tab_strip.create_text(
                TAB_STRIP_WIDTH / 2, y + row_height / 2, text=tab_labels[name],
                angle=90, fill=TEXT_MUTED, font=("Segoe UI", 14, "bold"), anchor="center",
            )
            for item_id in (rect_id, text_id):
                tab_strip.tag_bind(item_id, "<Button-1>", lambda e, n=name: self._on_tool_tab_click(n))
                tab_strip.tag_bind(item_id, "<Enter>", lambda e, n=name: self._on_tab_strip_hover(n, True, e))
                tab_strip.tag_bind(item_id, "<Leave>", lambda e, n=name: self._on_tab_strip_hover(n, False, e))
            self._tool_tab_items[name] = (text_id, rect_id)
            y += row_height
        tab_strip.configure(height=y + 10)
        self._tool_tab_disabled = {"Detect Impurities"}

        self._tool_tab_content_area = ctk.CTkFrame(tabs_container, fg_color="transparent")
        self._tool_tab_content_area.pack(side="left", fill="both", expand=True, padx=(0, 8))

        # Tabs are built on first use rather than all at once up front:
        # constructing all seven means hundreds of CTk widgets, and you
        # only ever look at one at a time. "Processing" (the default) is
        # the only one built during startup - the rest cost nothing until
        # actually opened. Anything outside this method that touches a
        # tab's widgets must tolerate that tab not existing yet (see
        # _ensure_tool_tab_built and the hasattr guards at those sites).
        self._tool_tab_builders = {
            "View": self._build_view_tab,
            "Library": self._build_library_tab,
            "Processing": self._build_processing_tab,
            "Baseline": self._build_baseline_tab,
            "Report": self._build_report_tab,
            "Export": self._build_export_tab,
            "Advanced": self._build_advanced_tab,
        }
        self._tool_tab_frames = {}
        self._select_tool_tab("Processing")  # the first thing you touch after loading a FID

    def _ensure_tool_tab_built(self, name):
        """Build a tool tab's widgets if they don't exist yet, and return
        its frame (None for a name with no builder, e.g. the pseudo-tab
        'Detect Impurities', which is an action rather than a panel)."""
        frame = self._tool_tab_frames.get(name)
        if frame is not None:
            return frame
        builder = self._tool_tab_builders.get(name)
        if builder is None:
            return None
        frame = builder(self._tool_tab_content_area)
        self._tool_tab_frames[name] = frame
        return frame

    def _set_view_switch(self, value):
        """Update the View tab's Spectrum/FID toggle if that tab has been
        built. It's created on first open, so callers that run earlier
        (loading a file, resetting) must not assume it exists - the tab
        reads self.view_mode when it is eventually built."""
        if hasattr(self, "view_switch"):
            self.view_switch.set(value)

    def _on_tab_strip_hover(self, name, entered, event=None):
        if name == "Detect Impurities" and name in self._tool_tab_disabled:
            if entered:
                self._show_tooltip(
                    self._tool_tab_canvas, "No solvent reference yet (press L to pick one)", event,
                )
            else:
                self._hide_tooltip()
        if name in self._tool_tab_disabled or name == self._active_tool_tab:
            return
        text_id, rect_id = self._tool_tab_items[name]
        self._tool_tab_canvas.itemconfigure(rect_id, fill="#22252b" if entered else PANEL_COLOR)

    def _set_tool_tab_enabled(self, name, enabled):
        if enabled:
            self._tool_tab_disabled.discard(name)
        else:
            self._tool_tab_disabled.add(name)
        text_id, rect_id = self._tool_tab_items[name]
        if name == self._active_tool_tab:
            return
        self._tool_tab_canvas.itemconfigure(text_id, fill=TEXT_MUTED if enabled else "#494c54")

    def _on_tool_tab_click(self, name):
        if name in self._tool_tab_disabled:
            return
        if name == "Detect Impurities":
            self.detect_residual_solvents()
            return
        self._select_tool_tab(name)

    def _select_tool_tab(self, name):
        self._active_tool_tab = name
        self._ensure_tool_tab_built(name)  # lazily built on first open
        for tab_name, frame in self._tool_tab_frames.items():
            if tab_name == name:
                frame.pack(fill="both", expand=True, padx=0, pady=(2, 6))
            else:
                frame.pack_forget()
        for tab_name, (text_id, rect_id) in self._tool_tab_items.items():
            is_active = (tab_name == name)
            disabled = tab_name in self._tool_tab_disabled
            self._tool_tab_canvas.itemconfigure(
                rect_id, fill=ACCENT if is_active else PANEL_COLOR,
            )
            self._tool_tab_canvas.itemconfigure(
                text_id,
                fill="white" if is_active else ("#494c54" if disabled else TEXT_MUTED),
            )
        if name == "Report":
            self._refresh_report_preview()
        if name == "Export":
            self._apply_export_preview()
        else:
            self._revert_export_preview()

    def _build_view_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        ctk.CTkLabel(frame, text="Which data to plot", font=ctk.CTkFont(size=12),
                     text_color="#c7c9cf").pack(anchor="w", pady=(0, 4))
        self.view_switch = ctk.CTkSegmentedButton(
            frame, values=["Spectrum", "FID"], command=self._on_view_change,
        )
        # Reflect whatever the current view actually is - this tab may be
        # built long after a file was loaded (it's built on first open).
        self.view_switch.set("FID" if self.view_mode == "fid" else "Spectrum")
        self.view_switch.pack(fill="x", pady=(0, 16))

        ctk.CTkLabel(frame, text="DISPLAY", font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).pack(anchor="w", pady=(0, 4))
        ctk.CTkCheckBox(
            frame, text="Show title", variable=self.plot_show_title, font=ctk.CTkFont(size=12),
            checkbox_width=16, checkbox_height=16, command=self._on_plot_style_change,
        ).pack(anchor="w", pady=3)
        title_entry = ctk.CTkEntry(frame, textvariable=self.plot_title_text, height=30, corner_radius=8)
        title_entry.pack(fill="x", pady=(0, 3), padx=(24, 0))
        self.plot_title_text.trace_add("write", lambda *a: self._on_plot_style_change())
        for text, var in (
            ("Show Y-axis label and values", self.plot_show_ylabel),
            ("Show grid", self.plot_show_grid),
            ("Show box (top/left/right border)", self.plot_show_box),
        ):
            ctk.CTkCheckBox(
                frame, text=text, variable=var, font=ctk.CTkFont(size=12),
                checkbox_width=16, checkbox_height=16,
                command=self._on_plot_style_change,
            ).pack(anchor="w", pady=3)
        return frame

    def _build_processing_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")

        self._labeled_entry(frame, "Line broadening (Hz)", self.line_broadening, padx=0)
        self.line_broadening.trace_add("write", lambda *a: self._live_reprocess())

        # Phase row: manual entry + auto-phase button side by side
        ctk.CTkLabel(frame, text="Phase (deg)", font=ctk.CTkFont(size=12),
                     text_color="#c7c9cf").pack(anchor="w", pady=(6, 2))
        phase_row = ctk.CTkFrame(frame, fg_color="transparent")
        phase_row.pack(fill="x")
        ctk.CTkEntry(phase_row, textvariable=self.phase_deg, height=32, corner_radius=8).pack(
            side="left", fill="x", expand=True, padx=(0, 6)
        )
        ctk.CTkButton(
            phase_row, text="Auto", width=60, height=32, corner_radius=8,
            command=self.auto_phase_correction, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(side="left")

        self.phase_slider = ctk.CTkSlider(
            frame, from_=-180, to=180, number_of_steps=720,
            command=self._on_phase_slider_drag,
        )
        self.phase_slider.set(0)
        self.phase_slider.pack(fill="x", pady=(8, 0))

        slider_labels = ctk.CTkFrame(frame, fg_color="transparent")
        slider_labels.pack(fill="x")
        ctk.CTkLabel(slider_labels, text="-180", text_color=TEXT_MUTED, font=ctk.CTkFont(size=10)).pack(side="left")
        ctk.CTkLabel(slider_labels, text="+180", text_color=TEXT_MUTED, font=ctk.CTkFont(size=10)).pack(side="right")

        # Manual edits to the text field should also drive the slider + live preview
        self.phase_deg.trace_add("write", self._on_phase_text_change)
        return frame

    def _build_baseline_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        ctk.CTkLabel(
            frame, text="Pick 2+ flat, peak-free points (B) - drag a point to adjust it - then apply",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=260,
            justify="left", anchor="w",
        ).pack(fill="x", pady=(0, 6))

        ctk.CTkButton(
            frame, text="Pick baseline points", command=self._toggle_baseline_mode,
            height=36, corner_radius=10, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(fill="x", pady=(0, 4))

        self.baseline_count_label = ctk.CTkLabel(
            frame, text="0 point(s) picked", font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
        )
        self.baseline_count_label.pack(anchor="w", pady=(0, 6))

        baseline_btn_row = ctk.CTkFrame(frame, fg_color="transparent")
        baseline_btn_row.pack(fill="x")
        self.apply_baseline_button = ctk.CTkButton(
            baseline_btn_row, text="Apply correction", command=self._apply_baseline_correction,
            height=32, corner_radius=8, state="disabled",
            fg_color=ACCENT, hover_color="#2f8fe0",
        )
        self.apply_baseline_button.pack(side="left", fill="x", expand=True, padx=(0, 6))
        ctk.CTkButton(
            baseline_btn_row, text="Reset", command=self._reset_baseline,
            height=32, corner_radius=8, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(side="left")
        # Points may already have been picked via the B hotkey before this
        # tab was ever opened (and so before these widgets existed).
        self._update_baseline_controls()
        return frame

    def _build_report_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        ctk.CTkLabel(
            frame, text="Formats every integrated peak into an SI-style NMR line",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=260,
            justify="left", anchor="w",
        ).pack(fill="x", pady=(0, 6))
        ctk.CTkButton(
            frame, text="Copy NMR text", command=self.copy_nmr_report,
            height=36, corner_radius=10, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(fill="x", pady=(0, 8))

        self.report_textbox = ctk.CTkTextbox(
            frame, height=160, corner_radius=8, font=ctk.CTkFont(size=12), wrap="word",
        )
        self.report_textbox.pack(fill="both", expand=True, pady=(4, 0))
        return frame

    def _refresh_report_preview(self):
        if not hasattr(self, "report_textbox"):
            return
        text = self._build_nmr_report_text()
        self.report_textbox.delete("1.0", "end")
        if text:
            self.report_textbox.insert("1.0", text)
        else:
            self.report_textbox.insert("1.0", "(Integrate at least one peak first - I hotkey.)")

    def _build_export_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        ctk.CTkLabel(
            frame, text="Exports the current page's plot next to its source FID",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=260,
            justify="left", anchor="w",
        ).pack(fill="x", pady=(0, 8))

        export_btn_row = ctk.CTkFrame(frame, fg_color="transparent")
        export_btn_row.pack(fill="x", pady=(0, 4))
        ctk.CTkButton(
            export_btn_row, text="PNG", command=lambda: self._export_current_plot("png"),
            height=34, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        ).pack(side="left", fill="x", expand=True, padx=(0, 6))
        ctk.CTkButton(
            export_btn_row, text="TIFF", command=lambda: self._export_current_plot("tiff"),
            height=34, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        ).pack(side="left", fill="x", expand=True)

        self._labeled_entry(frame, "Resolution (DPI)", self.export_dpi, padx=0)

        ctk.CTkLabel(
            frame, text="Baseline margin (space below the spectrum)",
            font=ctk.CTkFont(size=12), text_color="#c7c9cf",
        ).pack(anchor="w", pady=(12, 2))
        ctk.CTkSlider(
            frame, from_=0, to=25, number_of_steps=100, variable=self.export_baseline_margin,
            command=lambda v: self._update_export_baseline_margin(),
        ).pack(fill="x")

        self.export_legend_frame = ctk.CTkFrame(frame, fg_color="transparent")
        self.export_legend_frame.pack(fill="x")
        ctk.CTkCheckBox(
            self.export_legend_frame, text="Show legend", variable=self.export_show_legend,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_legend_visibility,
        ).pack(anchor="w", pady=(12, 0))

        # Integration/multiplicity/impurity preview - not applicable to
        # overlay/stacked pages (they have none of these), so this whole
        # section is hidden while viewing one of those.
        self.export_single_preview_frame = ctk.CTkFrame(frame, fg_color="transparent")
        self.export_single_preview_frame.pack(fill="x")
        preview = self.export_single_preview_frame

        ctk.CTkLabel(preview, text="PREVIEW (only while this tab is open)",
                     font=ctk.CTkFont(size=11, weight="bold"), text_color=TEXT_MUTED,
                     ).pack(anchor="w", pady=(16, 4))
        ctk.CTkCheckBox(
            preview, text="Show integration highlight", variable=self.export_show_integration_highlight,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=3)
        ctk.CTkCheckBox(
            preview, text="Show integration numbers", variable=self.export_show_integration_numbers,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=3)
        ctk.CTkCheckBox(
            preview, text="Show multiplicity", variable=self.export_show_multiplicity,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=3)
        ctk.CTkCheckBox(
            preview, text="Show peak position", variable=self.export_show_peak_position,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=3)
        ctk.CTkCheckBox(
            preview, text="Show impurities", variable=self.export_show_impurities,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=3)
        ctk.CTkCheckBox(
            preview, text="Show position ticks", variable=self.export_show_position_ticks,
            font=ctk.CTkFont(size=12), checkbox_width=16, checkbox_height=16,
            command=self._update_export_integration_visibility,
        ).pack(anchor="w", pady=(3, 12))

        for label, var in (
            ("Integration numbers - Y position", self.export_integration_number_y),
            ("Multiplicity - Y position", self.export_multiplicity_y),
            ("Peak position - Y position", self.export_peak_position_y),
            ("Solvent impurities - Y position", self.export_impurity_y),
            ("Solvent (reference) - Y position", self.export_solvent_reference_y),
            ("Position ticks - Y position", self.export_position_ticks_y),
        ):
            ctk.CTkLabel(preview, text=label, font=ctk.CTkFont(size=12),
                         text_color="#c7c9cf").pack(anchor="w", pady=(6, 2))
            ctk.CTkSlider(
                preview, from_=0, to=100, number_of_steps=200, variable=var,
                command=lambda v: self._update_export_label_positions(),
            ).pack(fill="x")
        return frame

    def _apply_export_preview(self):
        """Called once when the Export tab becomes the active tab -
        remembers the current view exactly as it is, so it can be put
        back when leaving, then applies the integration/multiplicity and
        baseline-margin preview on top of it."""
        if not hasattr(self, "ax"):
            return
        is_overlay_page = False
        if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
            is_overlay_page = self.pages[self.current_page_index].get("type") == "overlay"
        if is_overlay_page:
            self.export_single_preview_frame.pack_forget()
            self.export_legend_frame.pack(fill="x")
        else:
            self.export_single_preview_frame.pack(fill="x")
            self.export_legend_frame.pack_forget()

        self._pre_export_ylim = self.ax.get_ylim()
        self._update_export_integration_visibility()
        self._update_export_baseline_margin()
        self._update_export_label_positions()
        self._update_export_legend_visibility()

    def _revert_export_preview(self):
        """Called whenever any OTHER tab becomes active - these settings
        only ever affect the plot while Export itself is open."""
        if not hasattr(self, "ax"):
            return
        for r in self.integration_regions:
            for key in ("bar", "handle_left", "handle_right", "text",
                        "mult_text", "ppm_tag_line", "ppm_tag_text"):
                artist = r.get(key)
                if artist is not None:
                    artist.set_visible(True)
            text = r.get("text")
            if text is not None:
                x, _ = text.get_position()
                text.set_position((x, INTEGRATION_H_LABEL_Y))
            mult_text = r.get("mult_text")
            if mult_text is not None:
                x, _ = mult_text.get_position()
                mult_text.set_position((x, INTEGRATION_M_LABEL_Y))
            ppm_tag_text = r.get("ppm_tag_text")
            if ppm_tag_text is not None:
                x, _ = ppm_tag_text.get_position()
                ppm_tag_text.set_position((x, TAG_LABEL_Y))
            ppm_tag_line = r.get("ppm_tag_line")
            if ppm_tag_line is not None:
                ppm_tag_line.set_ydata([TAG_BAND_YMIN, TAG_STUB_YMAX])
        for tag in self.impurity_tags:
            for key in ("line", "text"):
                artist = tag.get(key)
                if artist is not None:
                    artist.set_visible(True)
            text = tag.get("text")
            if text is not None:
                x, _ = text.get_position()
                text.set_position((x, TAG_LABEL_Y))
            line = tag.get("line")
            if line is not None:
                line.set_ydata([TAG_BAND_YMIN, TAG_STUB_YMAX])
        if self.solvent_tag is not None:
            line, text = self.solvent_tag
            line.set_visible(True)
            x, _ = text.get_position()
            text.set_position((x, TAG_LABEL_Y))
            line.set_ydata([TAG_BAND_YMIN, TAG_STUB_YMAX])
        legend = self.ax.get_legend()
        if legend is not None:
            legend.set_visible(True)
        if getattr(self, "_pre_export_ylim", None) is not None:
            self.ax.set_ylim(*self._pre_export_ylim)
            self._pre_export_ylim = None
        self.canvas.draw_idle()

    def _update_export_integration_visibility(self):
        if not hasattr(self, "canvas"):
            return
        show_highlight = self.export_show_integration_highlight.get()
        show_numbers = self.export_show_integration_numbers.get()
        show_mult = self.export_show_multiplicity.get()
        show_peak_pos = self.export_show_peak_position.get()
        show_impurities = self.export_show_impurities.get()
        show_ticks = self.export_show_position_ticks.get()
        for r in self.integration_regions:
            for key in ("bar", "handle_left", "handle_right"):
                artist = r.get(key)
                if artist is not None:
                    artist.set_visible(show_highlight)
            text_artist = r.get("text")
            if text_artist is not None:
                text_artist.set_visible(show_numbers)
            mult_artist = r.get("mult_text")
            if mult_artist is not None:
                mult_artist.set_visible(show_mult)
            ppm_tag_text = r.get("ppm_tag_text")
            if ppm_tag_text is not None:
                ppm_tag_text.set_visible(show_peak_pos)
            ppm_tag_line = r.get("ppm_tag_line")
            if ppm_tag_line is not None:
                ppm_tag_line.set_visible(show_peak_pos and show_ticks)
        for tag in self.impurity_tags:
            text = tag.get("text")
            if text is not None:
                text.set_visible(show_impurities)
            line = tag.get("line")
            if line is not None:
                line.set_visible(show_impurities and show_ticks)
        if self.solvent_tag is not None:
            line, text = self.solvent_tag
            line.set_visible(show_ticks)
        self.canvas.draw_idle()

    def _update_export_label_positions(self):
        """Live-move each annotation type's text to the Y position set by
        its Export-tab slider, and the stub/tick lines (peak position,
        impurities, solvent reference) to their own independent Y
        position - preview only, reverted on leaving Export."""
        if not hasattr(self, "canvas"):
            return
        int_y = self.export_integration_number_y.get() / 100.0
        mult_y = self.export_multiplicity_y.get() / 100.0
        peak_y = self.export_peak_position_y.get() / 100.0
        imp_y = self.export_impurity_y.get() / 100.0
        solvent_y = self.export_solvent_reference_y.get() / 100.0
        ticks_y = self.export_position_ticks_y.get() / 100.0

        for r in self.integration_regions:
            text = r.get("text")
            if text is not None:
                x, _ = text.get_position()
                text.set_position((x, int_y))
            mult_text = r.get("mult_text")
            if mult_text is not None:
                x, _ = mult_text.get_position()
                mult_text.set_position((x, mult_y))
            ppm_tag_text = r.get("ppm_tag_text")
            if ppm_tag_text is not None:
                x, _ = ppm_tag_text.get_position()
                ppm_tag_text.set_position((x, peak_y))
            ppm_tag_line = r.get("ppm_tag_line")
            if ppm_tag_line is not None:
                ppm_tag_line.set_ydata([TAG_BAND_YMIN, ticks_y])
        for tag in self.impurity_tags:
            text = tag.get("text")
            if text is not None:
                x, _ = text.get_position()
                text.set_position((x, imp_y))
            line = tag.get("line")
            if line is not None:
                line.set_ydata([TAG_BAND_YMIN, ticks_y])
        if self.solvent_tag is not None:
            line, text = self.solvent_tag
            x, _ = text.get_position()
            text.set_position((x, solvent_y))
            line.set_ydata([TAG_BAND_YMIN, ticks_y])
        self.canvas.draw_idle()

    def _update_export_legend_visibility(self):
        if not hasattr(self, "canvas"):
            return
        legend = self.ax.get_legend()
        if legend is not None:
            legend.set_visible(self.export_show_legend.get())
        self.canvas.draw_idle()

    def _update_export_baseline_margin(self):
        if getattr(self, "_pre_export_ylim", None) is None:
            return
        _, cur_top = self._pre_export_ylim
        if cur_top > 0:
            margin_fraction = self.export_baseline_margin.get() / 100.0
            new_bottom, new_top = self._margined_ylim(cur_top, margin_fraction)
            self.ax.set_ylim(new_bottom, new_top)
        self.canvas.draw_idle()

    def _export_current_plot(self, fmt):
        if self.spectrum_data is None and self.complex_data is None:
            messagebox.showinfo("Nothing to export", "Load and process a spectrum first.")
            return

        ext = "png" if fmt == "png" else "tiff"
        if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
            page_name = self.pages[self.current_page_index]["name"]
        else:
            page_name = "spectrum"
        safe_name = re.sub(r'[\\/*?:"<>|]', "_", page_name).strip() or "spectrum"

        folder = os.path.dirname(self.current_path) if self.current_path else None
        if folder and os.path.isdir(folder):
            path = os.path.join(folder, f"{safe_name}.{ext}")
        else:
            path = filedialog.asksaveasfilename(
                title=f"Export as {ext.upper()}",
                defaultextension=f".{ext}",
                initialfile=f"{safe_name}.{ext}",
                filetypes=[(f"{ext.upper()} image", f"*.{ext}")],
            )
            if not path:
                return

        try:
            dpi = int(float(self.export_dpi.get()))
        except (TypeError, ValueError):
            dpi = 300

        try:
            self.figure.savefig(path, format=ext, facecolor=self._theme_colors()["bg"], dpi=dpi)
        except Exception as exc:
            messagebox.showerror("Error exporting", str(exc))
            return
        self.status.configure(text=f"Exported to {os.path.basename(path)}")

    def _build_advanced_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        self._labeled_combo(frame, "Zero-fill", self.zero_fill_name, ZERO_FILL_OPTIONS, padx=0)
        self.zero_fill_name.trace_add("write", lambda *a: self._live_reprocess())

        ctk.CTkLabel(frame, text="CALIBRATION (optional)", font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).pack(anchor="w", pady=(16, 4))
        self._labeled_entry(frame, "Spectral width SW (Hz)", self.spectral_width, padx=0)
        self._labeled_entry(frame, "Transmitter offset O1 (Hz)", self.transmitter_offset, padx=0)
        self._labeled_entry(frame, "Spectrometer freq SF (MHz)", self.spectrometer_freq, padx=0)
        self._labeled_entry(frame, "Digital filter delay GRPDLY (pts)", self.grpdly, padx=0)
        for var in (self.spectral_width, self.transmitter_offset, self.spectrometer_freq, self.grpdly):
            var.trace_add("write", lambda *a: self._live_reprocess())

        ctk.CTkLabel(frame, text="DATA FORMAT", font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).pack(anchor="w", pady=(16, 4))
        self._labeled_combo(frame, "Data type", self.dtype_name, list(DTYPE_OPTIONS.keys()), padx=0)
        self._labeled_combo(frame, "Byte order", self.byte_order_name, list(BYTE_ORDER_OPTIONS.keys()), padx=0)
        return frame

    def _labeled_entry(self, parent, label, var, padx=18):
        ctk.CTkLabel(parent, text=label, font=ctk.CTkFont(size=12),
                     text_color="#c7c9cf").pack(anchor="w", padx=padx, pady=(6, 2))
        ctk.CTkEntry(parent, textvariable=var, height=32, corner_radius=8).pack(
            fill="x", padx=padx
        )

    def _labeled_combo(self, parent, label, var, values, padx=18):
        ctk.CTkLabel(parent, text=label, font=ctk.CTkFont(size=12),
                     text_color="#c7c9cf").pack(anchor="w", padx=padx, pady=(6, 2))
        ctk.CTkComboBox(
            parent, values=values, variable=var, height=32, corner_radius=8,
            state="readonly", button_color=ACCENT,
        ).pack(fill="x", padx=padx)

    def _build_main_area(self):
        main = ctk.CTkFrame(self, fg_color=BG_COLOR, corner_radius=0)
        main.grid(row=0, column=1, sticky="nsew")
        main.grid_rowconfigure(0, weight=1)
        main.grid_columnconfigure(0, weight=1)

        self.figure = Figure(figsize=(8, 6), dpi=100, facecolor=BG_COLOR)
        self.ax = self.figure.add_subplot(111)
        self._style_axis(self.ax)
        self._apply_figure_layout()

        self.canvas = FigureCanvasTkAgg(self.figure, master=main)
        self.canvas.get_tk_widget().configure(bg=BG_COLOR, highlightthickness=0)
        self.canvas.get_tk_widget().grid(row=0, column=0, sticky="nsew", padx=16, pady=(16, 0))
        if _DND_AVAILABLE:
            self.canvas.get_tk_widget().drop_target_register(DND_FILES)
            self.canvas.get_tk_widget().dnd_bind("<<Drop>>", self._on_file_drop)
        self.canvas.mpl_connect("button_press_event", self._on_pick_click)
        self.canvas.mpl_connect("motion_notify_event", self._on_pick_motion)
        self.canvas.mpl_connect("button_press_event", self._on_canvas_right_click)
        self.canvas.mpl_connect("button_press_event", self._on_handle_press)
        self.canvas.mpl_connect("motion_notify_event", self._on_handle_motion)
        self.canvas.mpl_connect("button_release_event", self._on_handle_release)
        self.canvas.mpl_connect("motion_notify_event", self._on_impurity_drag_motion)
        self.canvas.mpl_connect("button_release_event", self._on_impurity_drag_release)
        self.canvas.mpl_connect("motion_notify_event", self._on_solvent_tag_drag_motion)
        self.canvas.mpl_connect("button_release_event", self._on_solvent_tag_drag_release)
        self.canvas.mpl_connect("button_press_event", self._on_baseline_click)
        self.canvas.mpl_connect("motion_notify_event", self._on_baseline_point_drag_motion)
        self.canvas.mpl_connect("button_release_event", self._on_baseline_point_drag_release)

        self._build_zoom_hint(main)
        self._draw_placeholder()
        self._register_hotkeys()
        self._register_scroll_zoom()
        self._update_cursor()

    def _register_scroll_zoom(self):
        widget = self.canvas.get_tk_widget()
        # Windows / macOS (trackpad two-finger scroll generates the same event)
        widget.bind("<MouseWheel>", self._on_scroll_zoom)
        # Linux / X11 scroll wheel (harmless to include for portability)
        widget.bind("<Button-4>", self._on_scroll_zoom)
        widget.bind("<Button-5>", self._on_scroll_zoom)

    def _on_scroll_zoom(self, event):
        if self.complex_data is None or self.full_ylim is None:
            return

        # Windows/macOS: event.delta is +/-120 per notch (can be a larger
        # multiple of 120 for a fast flick). Linux: event.num is 4 (up) or 5
        # (down), one notch at a time.
        delta = getattr(event, "delta", 0)
        if delta != 0:
            notches = abs(delta) / 120.0
            scrolled_up = delta > 0
        elif getattr(event, "num", None) in (4, 5):
            notches = 1.0
            scrolled_up = event.num == 4
        else:
            return

        # Stacked-overlay pages have several different baselines (each
        # spectrum's vertical offset) sharing one axis - a normal ylim zoom
        # (below) rescales around y=0 and inevitably pushes the higher
        # baselines out of view. Instead, scale each spectrum's own height
        # around its own fixed baseline and leave the axis limits alone.
        if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
            page = self.pages[self.current_page_index]
            if page.get("type") == "overlay" and page["state"] is not None and page["state"].get("stacked"):
                self._stacked_scroll_zoom(page["state"], notches, scrolled_up)
                return

        self._push_scroll_zoom_undo()

        # A much gentler step per notch than before (was 0.85, an ~18% jump
        # per tick - felt like discrete "steps" rather than a smooth zoom).
        # ~1.5% per notch reads as continuous; scaling by `notches` means a
        # fast flick (which reports a bigger delta) still zooms faster.
        STEP = 0.985
        factor = STEP ** notches if scrolled_up else (1.0 / STEP) ** notches

        # Anchor to zero - the true baseline/noise-floor level for a phased
        # absorption spectrum - NOT self.full_ylim[0], which is just the
        # global minimum and can be dominated by a deep negative dip on a
        # peak with residual dispersion. That would drag the "baseline"
        # reference far below where the real noise floor sits.
        cur_top = self.ax.get_ylim()[1]
        new_top = cur_top * factor

        # Guard against collapsing the range to nothing after many scrolls
        full_range = abs(self.full_ylim[1] - self.full_ylim[0])
        if abs(new_top) < full_range * 1e-4:
            return

        new_bottom, new_top = self._margined_ylim(new_top)

        self.ax.set_ylim(new_bottom, new_top)
        self.canvas.draw_idle()

    def _stacked_scroll_zoom(self, state, notches, scrolled_up):
        """Scroll-to-zoom for a stacked page: grow/shrink every spectrum's
        height around its own fixed baseline (offset), so smaller peaks
        become easier to see without any spectrum drifting out of view.
        Reset via "Adjust intensities... > Reset all to 1.0x"."""
        STEP = 0.985
        # Scrolling up should reveal smaller peaks, same feel as the normal
        # zoom - here that means making them relatively taller.
        factor = (1.0 / STEP) ** notches if scrolled_up else STEP ** notches

        for i, s in enumerate(state["series"]):
            new_scale = s.get("scale", 1.0) * factor
            s["scale"] = min(max(new_scale, 1e-3), 1e3)  # sane bounds
            self._update_overlay_line(state, i)

    # All hotkeys/mouse actions, shown in the popup opened by the
    # "Hotkeys" button rather than taking up permanent screen space.
    HOTKEY_REFERENCE = [
        ("Z", "Cycle zoom mode (drag to zoom into a region)"),
        ("F", "Reset to the full view (X and Y)"),
        ("H", "Reset height only (Y)"),
        ("A", "Open the intensity-adjustment sliders (overlay/stacked pages)"),
        ("D", "Detect residual solvents (needs a solvent reference first)"),
        ("Scroll", "Zoom in/out to reveal smaller peaks"),
        ("L", "Pick/move the solvent reference peak"),
        ("I", "Toggle integration mode"),
        ("M", "Toggle multiplicity assignment mode"),
        ("B", "Toggle baseline point picking"),
        ("Esc", "Cancel the current action / clear overlay selection"),
        ("Ctrl+Z", "Undo (zoom, integration edit, or closed page)"),
        ("Shift+click a page name", "Select it for the next overlay/stacked view"),
        ("Drag a page name", "Reorder the open pages"),
        ("Hover a page name", "Preview that spectrum after a moment"),
        ("Right-click an integration", "Open its options menu"),
        ("Right-click a residual-solvent tag", "Erase it or manually fit its position"),
        ("Right-click the solvent reference tag", "Delete it or manually fit its position"),
    ]

    def _show_hotkeys_popup(self):
        win = ctk.CTkToplevel(self)
        win.title("Hotkeys")
        win.configure(fg_color=PANEL_COLOR)
        win.geometry("460x480")
        # transient, not "-topmost": topmost pins the window above every
        # other application on the desktop even after you alt-tab away.
        win.transient(self)
        win.lift()

        ctk.CTkLabel(
            win, text="Hotkeys & mouse actions", font=ctk.CTkFont(size=15, weight="bold"),
        ).pack(anchor="w", padx=18, pady=(16, 10))

        scroll = ctk.CTkScrollableFrame(win, fg_color=PANEL_COLOR)
        scroll.pack(fill="both", expand=True, padx=18, pady=(0, 16))

        for key, description in self.HOTKEY_REFERENCE:
            row = ctk.CTkFrame(scroll, fg_color="transparent")
            row.pack(fill="x", pady=4)
            ctk.CTkLabel(
                row, text=key, font=ctk.CTkFont(size=12, weight="bold"),
                text_color=ACCENT, width=170, anchor="w", justify="left",
            ).pack(side="left", anchor="n")
            ctk.CTkLabel(
                row, text=description, font=ctk.CTkFont(size=12), text_color="#d7d9de",
                anchor="w", justify="left", wraplength=230,
            ).pack(side="left", fill="x", expand=True)

    def _build_zoom_hint(self, parent):
        row = ctk.CTkFrame(parent, fg_color=BG_COLOR, corner_radius=0)
        row.grid(row=1, column=0, sticky="ew", padx=16, pady=(4, 10))

        ctk.CTkButton(
            row, text="Hotkeys", command=self._show_hotkeys_popup,
            height=26, width=90, corner_radius=8, font=ctk.CTkFont(size=12),
            fg_color=PANEL_COLOR, hover_color="#22252b", text_color="#d7d9de",
            border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(side="left")

        self.style_combo = ctk.CTkComboBox(
            row, values=list(PLOT_THEMES.keys()), variable=self.plot_style_name,
            height=26, width=130, corner_radius=8, font=ctk.CTkFont(size=12),
            state="readonly", button_color=ACCENT,
        )
        self.style_combo.pack(side="left", padx=(10, 0))
        self.plot_style_name.trace_add("write", lambda *a: self._on_plot_style_change())

        self.zoom_mode_label = ctk.CTkLabel(
            row, text="Current mode: Off (press Z to zoom)", text_color=TEXT_MUTED,
            font=ctk.CTkFont(size=12, weight="bold"),
        )
        self.zoom_mode_label.pack(side="left", padx=(16, 0))

        self.autosave_countdown_label = ctk.CTkLabel(
            row, text="", text_color=TEXT_MUTED, font=ctk.CTkFont(size=12),
        )
        self.autosave_countdown_label.pack(side="left", padx=(16, 0))

    def _on_plot_style_change(self):
        """Re-render whatever's currently on screen with the newly chosen
        theme's colors - works for a normal spectrum, the FID view, or an
        overlay/stacked page, without needing to reprocess any data."""
        try:
            if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
                page = self.pages[self.current_page_index]
                if page.get("type") == "overlay" and page["state"] is not None:
                    self._restore_overlay_view(page["state"])
                    return
            if self.complex_data is None:
                return
            if self.view_mode == "fid":
                self._plot_fid()
            else:
                self._plot_spectrum()
            self.canvas.draw_idle()
        except Exception as exc:
            # A display-setting redraw should never be able to freeze the
            # rest of the app - report it and keep going.
            self.status.configure(text=f"Display update failed: {exc}")

    # Letter hotkeys that should be suppressed while typing in a text field.
    # Maps key letter -> the (no-arg) method it triggers.
    _LETTER_HOTKEYS = {
        "z": "_cycle_zoom_mode",
        "f": "reset_full",
        "h": "reset_height",
        "a": "_open_intensity_normalizer",
        "d": "detect_residual_solvents",
        "l": "_toggle_pick_mode",
        "i": "_toggle_integrate_mode",
        "m": "_toggle_multiplicity_mode",
        "b": "_toggle_baseline_mode",
    }

    def _register_hotkeys(self):
        for letter in self._LETTER_HOTKEYS:
            self.bind_all(f"<KeyPress-{letter}>", self._make_letter_hotkey(letter))
            self.bind_all(f"<KeyPress-{letter.upper()}>", self._make_letter_hotkey(letter))
        self.bind_all("<Escape>", self._hotkey_escape)
        self.bind_all("<Control-z>", self._hotkey_undo)
        self.bind_all("<Control-Z>", self._hotkey_undo)

    def _make_letter_hotkey(self, letter):
        method_name = self._LETTER_HOTKEYS[letter]

        def handler(event=None):
            if self._typing_in_entry():
                return
            # Don't let Ctrl+<letter> (Ctrl+A, Ctrl+F, Ctrl+I ... common
            # muscle memory) fire the plain-letter hotkey. Tk matches
            # <KeyPress-f> even while Control is held unless a specific
            # <Control-f> binding exists, so it has to be checked here.
            if event is not None and getattr(event, "state", 0) & 0x0004:
                return
            getattr(self, method_name)()

        return handler

    def _typing_in_entry(self):
        # Don't hijack Z/F/H/L/I/M while the user is typing in a text
        # field. Both widget kinds matter: CTkEntry wraps a tk.Entry, and
        # CTkTextbox (the editable Report preview) wraps a tk.Text.
        focused = self.focus_get()
        return isinstance(focused, (tk.Entry, tk.Text))

    def _hotkey_escape(self, event=None):
        # Escape cancels any active cursor mode - safe to run even while a
        # text field has focus, since it doesn't type a character.
        had_overlay_selection = bool(self.overlay_selected)
        if had_overlay_selection:
            self.overlay_selected = set()
            self._refresh_pages_list()

        changed = (
            self.pick_mode or self.integrate_mode or self.multiplicity_mode
            or self.zoom_active or self.baseline_mode or had_overlay_selection
        )
        self._exit_exclusive_modes()
        if self.zoom_active:
            self.zoom_active = False
        if self.impurity_drag is not None:
            tag, start_ppm = self.impurity_drag["tag"], self.impurity_drag["start_ppm"]
            tag["ppm"] = start_ppm
            self._position_impurity_tag(tag)
            self.impurity_drag = None
            self._apply_active_selector()
            self._update_cursor()
            self.status.configure(text="Cancelled")
            return
        if self.solvent_drag is not None:
            self.solvent_drag = None
            if self.reference_info is not None:
                self._tag_solvent_peak(*self.reference_info)  # snap back to the literature position
            self._apply_active_selector()
            self._update_cursor()
            self.status.configure(text="Cancelled")
            return
        if self.baseline_drag is not None:
            point = self.baseline_drag["point"]
            point["ppm"] = self.baseline_drag["start_ppm"]
            point["y"] = self.baseline_drag["start_y"]
            point["marker"].set_data([point["ppm"]], [point["y"]])
            self.baseline_drag = None
            self.baseline_points.sort(key=lambda p: p["ppm"])
            self._update_baseline_preview()
            self._apply_active_selector()
            self._update_cursor()
            self.status.configure(text="Cancelled")
            return
        if changed:
            self._apply_active_selector()
            self._update_cursor()
            self.status.configure(text="Cancelled")

    def _next_undo_seq(self):
        self._undo_seq += 1
        return self._undo_seq

    def _hotkey_undo(self, event=None):
        if self._typing_in_entry():
            return

        top_integration_seq = self.integration_undo_stack[-1]["seq"] if self.integration_undo_stack else -1
        top_page_seq = self.page_close_undo_stack[-1]["seq"] if self.page_close_undo_stack else -1
        top_zoom_seq = self.zoom_undo_stack[-1]["seq"] if self.zoom_undo_stack else -1

        if top_integration_seq < 0 and top_page_seq < 0 and top_zoom_seq < 0:
            self.status.configure(text="Nothing to undo")
            return

        if top_zoom_seq > top_page_seq and top_zoom_seq > top_integration_seq:
            self._undo_zoom()
            return

        if top_page_seq > top_integration_seq:
            self._undo_page_close()
            return

        action = self.integration_undo_stack.pop()

        if action["type"] == "add":
            d = action["data"]
            target = None
            for r in reversed(self.integration_regions):
                if r["xmin"] == d["xmin"] and r["xmax"] == d["xmax"] and r["value"] == d["value"]:
                    target = r
                    break
            if target is not None:
                self._remove_integration_region(target, record_undo=False)
            self.status.configure(text="Last integration undone")

        elif action["type"] == "delete":
            d = action["data"]
            self._restore_integration_region(d)
            self.status.configure(text="Deleted integration restored")

        elif action["type"] == "delete_all":
            for d in action["data"]:
                self._restore_integration_region(d)
            self.status.configure(text="All deleted integrations restored")

    def _undo_page_close(self):
        if not self.page_close_undo_stack:
            return
        entry = self.page_close_undo_stack.pop()
        # Sync away whatever's currently live BEFORE inserting - insertion
        # shifts indices, so current_page_index would otherwise end up
        # pointing at the wrong (just-reinserted) page and corrupt it with
        # stale live data.
        self._sync_current_page_state()
        index = min(entry["index"], len(self.pages))
        self.pages.insert(index, entry["page"])
        self.current_page_index = index
        self._show_page(entry["page"])
        self._refresh_pages_list()
        self.status.configure(text=f"Restored closed page: {entry['page']['name']}")

    def _push_zoom_undo(self, prev_xlim, prev_ylim):
        """Record the view as it was BEFORE a zoom action, so Ctrl+Z can
        put it back. Capped so a long session of zooming doesn't grow
        this unboundedly."""
        self.zoom_undo_stack.append({
            "seq": self._next_undo_seq(), "xlim": prev_xlim, "ylim": prev_ylim,
        })
        if len(self.zoom_undo_stack) > 50:
            self.zoom_undo_stack.pop(0)

    def _push_scroll_zoom_undo(self):
        """Same idea as _push_zoom_undo, but for continuous scroll-wheel
        zooming: a fast flick fires many scroll events, and pushing one
        undo step per event would make a single Ctrl+Z barely move the
        view. Instead, only start a new undo step if it's been a little
        while (400ms) since the last one, so one scroll gesture = one
        undo step."""
        now = time.monotonic()
        if not self.zoom_undo_stack or (now - self._zoom_undo_last_push_time) > 0.4:
            self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
        self._zoom_undo_last_push_time = now

    def _undo_zoom(self):
        if not self.zoom_undo_stack:
            return
        entry = self.zoom_undo_stack.pop()
        self.ax.set_xlim(*entry["xlim"])
        self.ax.set_ylim(*entry["ylim"])
        self.canvas.draw_idle()
        self.status.configure(text="Zoom undone")

    def _theme_colors(self):
        return PLOT_THEMES.get(self.plot_style_name.get(), PLOT_THEMES["Neon"])

    def _style_axis(self, ax):
        colors = self._theme_colors()
        ax.set_facecolor(colors["bg"])
        self.figure.set_facecolor(colors["bg"])
        ax.tick_params(colors=colors["text"], labelsize=9)

        show_box = self.plot_show_box.get()
        for name, spine in ax.spines.items():
            spine.set_color(colors["text"])
            spine.set_visible(True if name == "bottom" else show_box)
        # Hiding the box previously only hid the border line - the tick
        # marks themselves stayed on. Tie them to the same toggle (top/
        # right tick marks are never wanted here regardless).
        ax.tick_params(left=show_box, right=False, top=False, bottom=True)

        if self.plot_show_grid.get():
            ax.grid(True, color=colors.get("grid", colors["text"]), linewidth=0.6, alpha=0.6)
        else:
            ax.grid(False)

        # NOTE: title/xlabel/ylabel color is NOT set here - set_title() /
        # set_xlabel() / set_ylabel() (called later, after this) each
        # create a brand-new Text object with matplotlib's default color,
        # silently discarding whatever we set on the old one here. That
        # was a real bug: on a dark theme, the default title color came
        # out black-on-black - "invisible" even though plot_show_title
        # was on and the text genuinely was being drawn. Colors are set
        # in _set_plot_title_and_ylabel() instead, after those exist.

    def _apply_figure_layout(self):
        """Fixed margins instead of figure.tight_layout(). tight_layout()'s
        auto-margin algorithm estimates padding from the rendered size of
        the title/labels/ticks - when the View-tab toggles hide all of
        them at once, that estimation can degenerate to NaN and crash the
        next render entirely (a real bug hit in testing). Adapting the
        margins to what's actually visible is robust and never crashes -
        and kept as tight as still comfortably fits each element."""
        left = 0.065 if self.plot_show_ylabel.get() else 0.015
        top = 0.92 if self.plot_show_title.get() else 0.985
        self.figure.subplots_adjust(left=left, right=0.985, top=top, bottom=0.09)

    def _set_plot_title_and_ylabel(self, title_text, ylabel_text):
        """Centralizes the View-tab title/y-label/y-tick-values toggles so
        every plotting function (spectrum, FID, overlay) behaves the same
        way instead of each hardcoding ax.set_title/set_ylabel directly.

        The title is NOT set via ax.set_title() - matplotlib's own title
        mechanism has its own internal auto-positioning pass
        (_update_title_position, which tries to dodge the Y-axis's
        scientific-notation offset text) that has caused two real bugs
        here: a NaN crash when everything else was hidden, and the title
        going invisible/clipped in some cases even with plenty of margin
        reserved for it. A plain text object at a fixed spot relative to
        the axes sidesteps that whole mechanism."""
        colors = self._theme_colors()
        self.ax.set_title("")
        if self.plot_show_title.get() and title_text:
            self.ax.text(
                0.5, 1.02, title_text, transform=self.ax.transAxes,
                ha="center", va="bottom", fontsize=13, color=colors["text"],
            )
        self.ax.set_ylabel(ylabel_text if self.plot_show_ylabel.get() else "")
        self.ax.tick_params(labelleft=self.plot_show_ylabel.get())
        # Set AFTER creating them - see the note in _style_axis.
        self.ax.xaxis.label.set_color(colors["text"])
        self.ax.yaxis.label.set_color(colors["text"])

    def _draw_placeholder(self):
        self.ax.clear()
        self._style_axis(self.ax)
        self.ax.text(
            0.5, 0.5, "Load a FID file to get started",
            ha="center", va="center", transform=self.ax.transAxes,
            color=TEXT_MUTED, fontsize=13,
        )
        self.ax.set_xticks([])
        self.ax.set_yticks([])
        self._apply_figure_layout()
        self.canvas.draw()

    # -------------------------------------------------------------- zoom --
    def _exit_exclusive_modes(self, keep=None):
        """Turn off pick/integrate/multiplicity/baseline mode, except `keep`
        (one of "pick", "integrate", "multiplicity", "baseline", or None to
        turn off all four). Only one of Zoom/Pick/Integrate/Multiplicity/
        Baseline is ever active at once."""
        if keep != "pick" and self.pick_mode:
            self.pick_mode = False
            self._clear_pick_annotation()
        if keep != "integrate" and self.integrate_mode:
            self.integrate_mode = False
        if keep != "multiplicity" and self.multiplicity_mode:
            self.multiplicity_mode = False
        if keep != "baseline" and self.baseline_mode:
            self.baseline_mode = False

    def _cycle_zoom_mode(self):
        # Z explicitly asks for zoom - exit any other exclusive mode first.
        self._exit_exclusive_modes()

        if not self.zoom_active:
            # First press just turns zoom on, starting at Horizontal - zoom
            # is off by default so a plain click-drag doesn't accidentally
            # zoom before the user has asked for it.
            self.zoom_active = True
            self.zoom_click_count = 1
            self.zoom_mode = self.zoom_modes[0]
        else:
            self.zoom_click_count += 1
            index = (self.zoom_click_count - 1) % len(self.zoom_modes)
            self.zoom_mode = self.zoom_modes[index]

        self._apply_active_selector()
        self._update_cursor()

    _CURSOR_CACHE = {}  # (letter, style) -> Tk cursor spec string, built once per run

    def _get_mode_cursor(self, letter, style):
        """Builds (and caches) a genuinely custom cursor - a letter plus a
        directional glyph - instead of relying on generic system cursor
        shapes that some modes had to share (integration and zoom's
        Horizontal mode both drag left-right, and looked identical).
        Returns a Tk cursor spec string, or None if it couldn't be built
        (falls back to a plain named cursor in that case)."""
        key = (letter, style)
        if key in self._CURSOR_CACHE:
            return self._CURSOR_CACHE[key]
        try:
            from PIL import Image, ImageDraw, ImageFont
            size = 32

            def render(inflate=0):
                img = Image.new("1", (size, size), 0)
                d = ImageDraw.Draw(img)
                try:
                    font = ImageFont.load_default(size=19)
                except TypeError:
                    font = ImageFont.load_default()
                d.text((1, 0), letter, fill=1, font=font)
                lw = 2 + inflate
                if style == "h":
                    y = size - 7
                    d.line((3, y, size - 3, y), fill=1, width=lw)
                    d.line((3, y, 8, y - 4), fill=1, width=lw)
                    d.line((3, y, 8, y + 4), fill=1, width=lw)
                    d.line((size - 3, y, size - 8, y - 4), fill=1, width=lw)
                    d.line((size - 3, y, size - 8, y + 4), fill=1, width=lw)
                elif style == "v":
                    x = size - 7
                    d.line((x, 12, x, size - 2), fill=1, width=lw)
                    d.line((x, 12, x - 4, 17), fill=1, width=lw)
                    d.line((x, 12, x + 4, 17), fill=1, width=lw)
                    d.line((x, size - 2, x - 4, size - 7), fill=1, width=lw)
                    d.line((x, size - 2, x + 4, size - 7), fill=1, width=lw)
                elif style == "square":
                    d.rectangle((size - 15, size - 15, size - 2, size - 2), outline=1, width=lw)
                elif style == "x":
                    d.line((size - 13, size - 13, size - 2, size - 2), fill=1, width=lw)
                    d.line((size - 13, size - 2, size - 2, size - 13), fill=1, width=lw)
                elif style == "cross":
                    d.line((size - 12, size - 2, size - 2, size - 2), fill=1, width=lw)
                    d.line((size - 7, size - 9, size - 7, size - 1), fill=1, width=lw)
                return img

            shape = render(inflate=0)
            mask = render(inflate=2)  # slightly thicker -> a visible halo so it reads on any background

            cache_dir = os.path.join(tempfile.gettempdir(), "saucenmr_cursors")
            os.makedirs(cache_dir, exist_ok=True)
            shape_path = os.path.join(cache_dir, f"{letter}_{style}_shape.xbm")
            mask_path = os.path.join(cache_dir, f"{letter}_{style}_mask.xbm")
            shape.save(shape_path, format="XBM")
            mask.save(mask_path, format="XBM")
            for path in (shape_path, mask_path):
                with open(path) as f:
                    content = f.read()
                content = content.replace(
                    "#define im_height 32", "#define im_height 32\n#define im_x_hot 1\n#define im_y_hot 1"
                )
                with open(path, "w") as f:
                    f.write(content)

            spec = f"@{shape_path} {mask_path} black white"
            self._CURSOR_CACHE[key] = spec
            return spec
        except Exception:
            self._CURSOR_CACHE[key] = None
            return None

    def _update_cursor(self):
        fallback = "arrow"
        letter = style = None
        if self.pick_mode:
            fallback, letter, style = "tcross", "L", "cross"
        elif self.integrate_mode:
            fallback, letter, style = "sb_h_double_arrow", "I", "h"
        elif self.multiplicity_mode:
            fallback, letter, style = "question_arrow", "M", "h"
        elif self.baseline_mode:
            fallback, letter, style = "crosshair", "B", "x"
        elif self.zoom_active:
            fallback = {
                "Horizontal": "sb_h_double_arrow",
                "Vertical": "sb_v_double_arrow",
                "Both": "dotbox",
            }.get(self.zoom_mode, "arrow")
            style = {"Horizontal": "h", "Vertical": "v", "Both": "square"}.get(self.zoom_mode)
            letter = "Z"

        cursor = self._get_mode_cursor(letter, style) if letter else None
        try:
            self.canvas.get_tk_widget().configure(cursor=cursor or fallback)
        except Exception:
            try:
                self.canvas.get_tk_widget().configure(cursor=fallback)
            except Exception:
                pass
        self._update_mode_label()

    def _update_mode_label(self):
        """The 'Current mode' indicator - several modes share a cursor
        shape (integration and zoom's Horizontal both drag left-right),
        so each gets its own icon-style prefix to stay unambiguous at a
        glance: an italic I with a double arrow for integration, a Z with
        a square and arrows for zoom, etc."""
        if self.pick_mode:
            text = "Current mode: L \u2014 pick solvent reference"
        elif self.integrate_mode:
            text = "Current mode: \U0001D43C \u2194  Integrate"
        elif self.multiplicity_mode:
            text = "Current mode: M \u2194  Multiplicity"
        elif self.baseline_mode:
            text = "Current mode: B \u00d7  Baseline points"
        elif self.zoom_active:
            icon = {"Horizontal": "\u2194", "Vertical": "\u2195", "Both": "\u25a2 \u2194\u2195"}.get(self.zoom_mode, "")
            text = f"Current mode: Z {icon}  {self.zoom_mode}"
        else:
            text = "Current mode: Off (press Z to zoom)"
        color = TEXT_MUTED if text.startswith("Current mode: Off") else ACCENT
        self.zoom_mode_label.configure(text=text, text_color=color)

    def _toggle_pick_mode(self):
        self.pick_mode = not self.pick_mode
        if self.pick_mode:
            self._exit_exclusive_modes(keep="pick")
            # Suspend the zoom selectors while picking a reference peak
            for sel in (self.span_h_selector, self.span_v_selector, self.rect_selector):
                if sel is not None:
                    sel.set_active(False)
            self.status.configure(text="Pick a peak on the spectrum to reference it (L to cancel)")
        else:
            self._apply_active_selector()
            self._clear_pick_annotation()
            self.status.configure(text="Peak-pick mode cancelled")
        self._update_cursor()

    def _toggle_integrate_mode(self):
        self.integrate_mode = not self.integrate_mode
        if self.integrate_mode:
            self._exit_exclusive_modes(keep="integrate")
        self._apply_active_selector()
        self._update_cursor()
        if self.integrate_mode:
            self.status.configure(text="Drag across a peak to integrate it (I to stop)")
        else:
            self.status.configure(text="Integration mode off")

    def _toggle_multiplicity_mode(self):
        self.multiplicity_mode = not self.multiplicity_mode
        if self.multiplicity_mode:
            self._exit_exclusive_modes(keep="multiplicity")
        self._apply_active_selector()
        self._update_cursor()
        if self.multiplicity_mode:
            self.status.configure(
                text="Drag across a peak to assign its multiplicity (M to stop)"
            )
        else:
            self.status.configure(text="Multiplicity mode off")

    def _toggle_baseline_mode(self):
        self.baseline_mode = not self.baseline_mode
        if self.baseline_mode:
            self._exit_exclusive_modes(keep="baseline")
        self._apply_active_selector()
        self._update_cursor()
        if self.baseline_mode:
            self.status.configure(
                text="Click 2+ flat, peak-free points to define the baseline (B to stop)"
            )
        else:
            self.status.configure(text="Baseline point picking off")

    def _clear_pick_annotation(self):
        changed = False
        if self.pick_coord_text is not None:
            try:
                self.pick_coord_text.remove()
            except Exception:
                pass
            self.pick_coord_text = None
            changed = True
        if self.pick_hover_line is not None:
            try:
                self.pick_hover_line.remove()
            except Exception:
                pass
            self.pick_hover_line = None
            changed = True
        if changed:
            self.canvas.draw_idle()

    def _on_pick_motion(self, event):
        if not self.pick_mode:
            return
        if event.xdata is None or event.ydata is None:
            self._clear_pick_annotation()
            return

        if self.pick_coord_text is not None:
            try:
                self.pick_coord_text.remove()
            except Exception:
                pass

        # Vertical guide line showing exactly which peak is under the cursor
        if self.pick_hover_line is None:
            self.pick_hover_line = self.ax.axvline(
                event.xdata, color=ACCENT, linewidth=1, linestyle="--", alpha=0.6, zorder=5,
            )
        else:
            self.pick_hover_line.set_xdata([event.xdata, event.xdata])

        unit_label = {"ppm": "ppm", "Hz": "Hz", "index": ""}.get(self.freq_unit, "")
        text = f"{event.xdata:.3f} {unit_label}".strip()
        self.pick_coord_text = self.ax.annotate(
            text, xy=(event.xdata, event.ydata), xytext=(18, 18),
            textcoords="offset points", color=ACCENT, fontsize=15, fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.4", fc=PANEL_COLOR, ec=PLOT_GRID_COLOR, alpha=0.95),
            zorder=10,
        )
        self.canvas.draw_idle()

    def _on_pick_click(self, event):
        if not self.pick_mode:
            return
        if self.view_mode != "spectrum" or self.spectrum_data is None:
            return
        if event.xdata is None:
            return

        # Snap to the actual peak apex near the click, within a small window
        # relative to the current visible range, rather than requiring a
        # pixel-perfect click on the exact peak maximum.
        x = self.freq_axis
        mag = np.abs(self.spectrum_data)
        xlim = self.ax.get_xlim()
        window = abs(xlim[1] - xlim[0]) * 0.01
        mask = (x >= event.xdata - window) & (x <= event.xdata + window)
        if not np.any(mask):
            return
        local_idx = np.argmax(mag[mask])
        clicked_ppm = float(x[mask][local_idx])

        self.pick_mode = False
        self._apply_active_selector()
        self._clear_pick_annotation()
        self._update_cursor()
        self._open_solvent_pick_popup(clicked_ppm)

    def _open_solvent_pick_popup(self, clicked_ppm):
        if self.pick_popup is not None:
            try:
                self.pick_popup.destroy()
            except Exception:
                pass

        popup = ctk.CTkToplevel(self)
        popup.title("Reference to solvent peak")
        popup.geometry("320x420")
        popup.configure(fg_color=PANEL_COLOR)
        # transient, not "-topmost": topmost pins the window above every
        # other application on the desktop even after you alt-tab away.
        popup.transient(self)
        popup.lift()
        self.pick_popup = popup

        ctk.CTkLabel(
            popup, text=f"Picked peak at {clicked_ppm:.4f} ppm",
            font=ctk.CTkFont(size=13, weight="bold"),
        ).pack(padx=14, pady=(14, 2), anchor="w")
        ctk.CTkLabel(
            popup, text="Select which solvent residual peak this is:",
            font=ctk.CTkFont(size=12), text_color=TEXT_MUTED,
        ).pack(padx=14, pady=(0, 10), anchor="w")

        scroll = ctk.CTkScrollableFrame(popup, fg_color=PANEL_COLOR)
        scroll.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        # Find the single closest literature peak across every solvent
        best_solvent, best_shift, best_diff = None, None, None
        for solvent_name, shifts in SOLVENT_RESIDUAL_PEAKS:
            for shift in shifts:
                diff = abs(shift - clicked_ppm)
                if best_diff is None or diff < best_diff:
                    best_diff = diff
                    best_solvent, best_shift = solvent_name, shift

        if best_solvent is not None:
            ctk.CTkLabel(
                scroll, text="SUGGESTED", font=ctk.CTkFont(size=11, weight="bold"),
                text_color=ACCENT,
            ).pack(anchor="w", padx=6, pady=(4, 2))
            ctk.CTkButton(
                scroll, text=f"{best_solvent} - \u03b4 {best_shift:.2f} ppm",
                height=32, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
                text_color="white",
                command=lambda s=best_shift, n=best_solvent: self._apply_solvent_reference(clicked_ppm, s, n),
            ).pack(fill="x", padx=6, pady=(0, 6))
            ctk.CTkFrame(scroll, height=1, fg_color=PLOT_GRID_COLOR).pack(fill="x", padx=6, pady=(2, 10))

        for solvent_name, shifts in sorted(SOLVENT_RESIDUAL_PEAKS, key=lambda item: item[0].lower()):
            ctk.CTkLabel(
                scroll, text=solvent_name, font=ctk.CTkFont(size=12, weight="bold"),
                text_color="#d7d9de",
            ).pack(anchor="w", padx=6, pady=(8, 2))
            for shift in shifts:
                ctk.CTkButton(
                    scroll, text=f"\u03b4 {shift:.2f} ppm", height=28, corner_radius=8,
                    fg_color=BG_COLOR, hover_color="#20232a", text_color="#d7d9de",
                    border_width=1, border_color=PLOT_GRID_COLOR,
                    command=lambda s=shift, n=solvent_name: self._apply_solvent_reference(clicked_ppm, s, n),
                ).pack(fill="x", padx=6, pady=2)

        ctk.CTkButton(
            popup, text="Cancel", height=32, corner_radius=8,
            fg_color=PANEL_COLOR, hover_color="#20232a", text_color=TEXT_MUTED,
            border_width=1, border_color=PLOT_GRID_COLOR,
            command=popup.destroy,
        ).pack(fill="x", padx=14, pady=(0, 14))

    def _apply_solvent_reference(self, clicked_ppm, literature_ppm, solvent_name):
        delta = literature_ppm - clicked_ppm
        self.ppm_reference_offset += delta

        # Referencing shifts the whole ppm axis by `delta` - shift every
        # existing integration/impurity annotation by the same amount so
        # they stay lined up with their peaks instead of getting stranded
        # (or wiped) when the spectrum is replotted below.
        if delta and self.freq_unit == "ppm":
            for region in self.integration_regions:
                region["xmin"] += delta
                region["xmax"] += delta
            for tag in self.impurity_tags:
                tag["ppm"] += delta
                tag["origin_ppm"] += delta

        if self.pick_popup is not None:
            try:
                self.pick_popup.destroy()
            except Exception:
                pass
            self.pick_popup = None

        # The app now "knows" which solvent this spectrum is in, straight from
        # the reference peak just picked - sync the detection dropdown and
        # enable the Detect button without requiring a separate manual pick.
        self.detection_solvent.set(solvent_name)
        self._on_detection_solvent_change(solvent_name)
        self.reference_label.configure(
            text=f"Reference: {solvent_name} ({literature_ppm:.2f} ppm)", text_color=ACCENT,
        )

        self.reference_info = (literature_ppm, solvent_name)
        self.run_fft()
        self.status.configure(
            text=f"Referenced to {solvent_name} ({literature_ppm:.2f} ppm) - shift {delta:+.4f} ppm applied"
        )

    def _tag_solvent_peak(self, ppm, solvent_name):
        """Place a distinctive gold tag on the solvent reference peak, so
        it's visually unmistakable from red impurity tags or green
        integration markers. Pinned to the top 10% of the axes (like the
        integration row is pinned to the bottom) so it stays put regardless
        of peak height or how far the user has zoomed vertically."""
        if self.solvent_tag is not None:
            for artist in self.solvent_tag:
                try:
                    artist.remove()
                except Exception:
                    pass
            self.solvent_tag = None

        if self.spectrum_data is None:
            return

        blended = mtransforms.blended_transform_factory(self.ax.transData, self.ax.transAxes)
        solvent_tag_color = self._theme_colors()["solvent_tag"]
        line = self.ax.axvline(
            ppm, ymin=TAG_BAND_YMIN, ymax=TAG_STUB_YMAX, color=solvent_tag_color, linewidth=1.5, zorder=7,
        )
        text = self.ax.text(
            ppm, TAG_LABEL_Y, solvent_name, transform=blended, rotation=90,
            va="bottom", ha="center", fontsize=13, color=solvent_tag_color,
            fontweight="bold", zorder=7,
        )
        self.solvent_tag = (line, text)
        self.canvas.draw_idle()

    # --------------------------------------------------- impurity detection --
    def _on_detection_solvent_change(self, value):
        if not hasattr(self, "_tool_tab_items"):
            return
        enabled = bool(value and value != "Select solvent...")
        self._set_tool_tab_enabled("Detect Impurities", enabled)

    def _integrate_window(self, lo, hi):
        """Integrate the real part of the spectrum over [lo, hi], returning
        (abs area, number of points in the window)."""
        x = self.freq_axis
        mask = (x >= lo) & (x <= hi)
        n_window = int(np.sum(mask))
        if n_window < 2:
            return 0.0, n_window
        area = abs(float(_trapz(self.spectrum_data.real[mask], x[mask])))
        return area, n_window

    @staticmethod
    def _compound_base_name(row_name):
        """Strip a trailing '(...)' proton qualifier so multi-peak rows like
        'toluene (CH3)' and 'toluene (CH2,4,6)' group under 'toluene'."""
        idx = row_name.find(" (")
        return row_name[:idx] if idx != -1 else row_name

    def detect_residual_solvents(self):
        solvent = self.detection_solvent.get()
        if not solvent or solvent == "Select solvent...":
            return
        if self.spectrum_data is None:
            messagebox.showinfo("No data", "Load a FID file and run the Fourier transform first.")
            return
        if self.freq_unit != "ppm":
            messagebox.showinfo(
                "ppm axis required",
                "Impurity detection needs a calibrated ppm axis. Set the spectral "
                "width / spectrometer frequency (Advanced settings) or load a file "
                "with a companion acqus, then try again.",
            )
            return

        x = self.freq_axis
        y = self.spectrum_data.real
        dppm = float(abs(x[1] - x[0])) if len(x) > 1 else 1.0

        # Robust noise floor (MAD-based) and the whole-spectrum integrated
        # intensity, used together to judge whether a literature peak
        # position actually has real signal or is just baseline noise.
        mad = np.median(np.abs(y - np.median(y)))
        noise_std = 1.4826 * mad if mad > 0 else (np.std(y) or 1.0)
        total_area = abs(float(_trapz(y, x)))

        tolerance = 0.03
        safety_factor = 6.0
        self_compound = SOLVENT_SELF_COMPOUND.get(solvent)

        # Group every literature peak by its parent compound, so a compound
        # like diethyl ether (which needs BOTH its CH3 and CH2 signals) only
        # counts as detected when every one of its peaks shows real,
        # above-noise integrated intensity - not just a nearby local max.
        groups = {}
        for name, d in IMPURITY_ROWS:
            lit_val = d.get(solvent)
            if lit_val is None:
                continue
            base = self._compound_base_name(name)
            if base == self_compound:
                continue  # this is the solvent itself, not an impurity
            groups.setdefault(base, []).append(lit_val)

        results = []
        for compound, lit_vals in groups.items():
            peak_details = []
            all_passed = True
            for lit_val in lit_vals:
                local_area, n_window = self._integrate_window(lit_val - tolerance, lit_val + tolerance)
                if n_window < 2:
                    all_passed = False
                    break
                expected_noise_area = noise_std * dppm * np.sqrt(n_window)
                # A tiny floor tied to the whole-spectrum intensity guards
                # against pathological near-zero-noise edge cases.
                threshold = max(safety_factor * expected_noise_area, total_area * 1e-5)
                snr = local_area / threshold if threshold > 0 else 0.0
                peak_details.append((lit_val, local_area, threshold, snr))
                if local_area <= threshold:
                    all_passed = False
                    break
            if all_passed and peak_details:
                mean_snr = float(np.mean([p[3] for p in peak_details]))
                results.append((compound, peak_details, mean_snr))

        results.sort(key=lambda r: r[2], reverse=True)
        self._show_detection_results(solvent, results)

    def _show_detection_results(self, solvent, results):
        if self.detection_popup is not None:
            try:
                self.detection_popup.destroy()
            except Exception:
                pass

        popup = ctk.CTkToplevel(self)
        popup.title("Detected residual solvents / impurities")
        popup.geometry("380x460")
        popup.configure(fg_color=PANEL_COLOR)
        # NOT "-topmost": that pins the window above every other application
        # on the desktop, even after alt-tabbing away from SauceNMR entirely.
        # `transient` ties its stacking to the main window instead - it
        # stays on top of SauceNMR (raises/lowers with it) but steps aside
        # like a normal window once you switch to something else.
        popup.transient(self)
        popup.lift()
        self.detection_popup = popup

        ctk.CTkLabel(
            popup, text=f"Impurity scan - solvent: {solvent}",
            font=ctk.CTkFont(size=13, weight="bold"),
        ).pack(padx=14, pady=(14, 2), anchor="w")

        if not results:
            ctk.CTkLabel(
                popup, text="No known impurities detected with intensity clearly above the "
                "noise floor (compounds with multiple signature peaks need ALL of them present).",
                font=ctk.CTkFont(size=12), text_color=TEXT_MUTED, wraplength=340,
            ).pack(padx=14, pady=(6, 14), anchor="w")
            return

        ctk.CTkLabel(
            popup, text=f"{len(results)} compound(s) found - every signature peak shows "
            "intensity clearly above the noise floor:",
            font=ctk.CTkFont(size=12), text_color=TEXT_MUTED, wraplength=340,
        ).pack(padx=14, pady=(0, 8), anchor="w")

        scroll = ctk.CTkScrollableFrame(popup, fg_color=PANEL_COLOR)
        scroll.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        for compound, peak_details, mean_snr in results:
            row = ctk.CTkFrame(scroll, fg_color=BG_COLOR, corner_radius=8)
            row.pack(fill="x", padx=4, pady=3)
            name_label = ctk.CTkLabel(
                row, text=compound, font=ctk.CTkFont(size=12, weight="bold"),
                text_color="#d7d9de",
            )
            name_label.pack(anchor="w", padx=10, pady=(6, 0))

            detail_text = "\n".join(
                f"\u03b4 {lv:.2f} ppm  -  {snr:.1f}\u00d7 above noise floor"
                for lv, area, thresh, snr in peak_details
            )
            detail_label = ctk.CTkLabel(
                row, text=detail_text, font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
                justify="left", anchor="w",
            )
            detail_label.pack(anchor="w", padx=10, pady=(0, 6))

            found_ppms = [p[0] for p in peak_details]
            for widget in (row, name_label, detail_label):
                widget.bind("<Enter>", lambda e, ps=found_ppms: self._highlight_peaks(ps))
                widget.bind("<Leave>", lambda e: self._unhighlight_peaks())
                widget.bind("<Button-1>", lambda e, ps=found_ppms, n=compound: self._tag_impurity(ps, n))

    # ----------------------------------------------- hover / tag interactions --
    def _find_peak_window(self, ppm, half_width_ppm=0.02):
        x = self.freq_axis
        mask = (x >= ppm - half_width_ppm) & (x <= ppm + half_width_ppm)
        return mask

    def _highlight_peaks(self, ppms):
        if self.spectrum_data is None:
            return
        self._unhighlight_peaks(redraw=False)
        for ppm in ppms:
            mask = self._find_peak_window(ppm)
            if not np.any(mask):
                continue
            x = self.freq_axis[mask]
            y = self.spectrum_data.real[mask]
            artist = self.ax.plot(x, y, color="#ffb454", linewidth=2.2, zorder=8)[0]
            self.detection_hover_artists.append(artist)
        self.canvas.draw_idle()

    def _unhighlight_peaks(self, redraw=True):
        if self.detection_hover_artists:
            for artist in self.detection_hover_artists:
                try:
                    artist.remove()
                except Exception:
                    pass
            self.detection_hover_artists = []
            if redraw:
                self.canvas.draw_idle()

    def _tag_impurity(self, ppms, name, origins=None):
        if self.spectrum_data is None:
            return
        blended = mtransforms.blended_transform_factory(self.ax.transData, self.ax.transAxes)
        tag_color = self._theme_colors()["tag"]

        for i, ppm in enumerate(ppms):
            line = self.ax.axvline(
                ppm, ymin=TAG_BAND_YMIN, ymax=TAG_STUB_YMAX, color=tag_color, linewidth=1.2, zorder=7,
            )
            text = self.ax.text(
                ppm, TAG_LABEL_Y, name, transform=blended, rotation=90,
                va="bottom", ha="center", fontsize=13, color=tag_color, zorder=7,
                fontweight="bold",
            )
            origin_ppm = origins[i] if origins is not None else ppm
            self.impurity_tags.append({
                "line": line, "text": text, "ppm": ppm, "name": name, "origin_ppm": origin_ppm,
            })
        self.canvas.draw_idle()

    def _clear_all_impurity_tags(self):
        for tag in self.impurity_tags:
            for artist in (tag["line"], tag["text"]):
                try:
                    artist.remove()
                except Exception:
                    pass
        self.impurity_tags = []

    # ------------------------------------------------------------ baseline --
    def _on_baseline_click(self, event):
        if not self.baseline_mode or event.button != 1 or event.x is None or event.y is None:
            return
        if self.spectrum_data is None:
            return

        # Clicking on top of an existing point starts a free drag instead of
        # adding a new one.
        hit = self._find_baseline_point_at(event)
        if hit is not None:
            self._start_baseline_point_drag(hit)
            return

        if event.xdata is None:
            return
        ppm = event.xdata
        x = self.freq_axis
        # Sample a small window around the click and take the median, so a
        # single noisy point doesn't throw the fitted baseline off.
        step = abs(float(x[1] - x[0])) if len(x) > 1 else 0.0
        half_width = step * 3
        mask = (x >= ppm - half_width) & (x <= ppm + half_width)
        if np.any(mask):
            y = float(np.median(self.spectrum_data.real[mask]))
        else:
            y = float(np.interp(ppm, x, self.spectrum_data.real))

        marker = self.ax.plot(
            [ppm], [y], marker="o", markersize=6, color=self._theme_colors()["baseline"],
            linestyle="none", zorder=8,
        )[0]
        self.baseline_points.append({"ppm": ppm, "y": y, "marker": marker})
        self.baseline_points.sort(key=lambda p: p["ppm"])
        self._update_baseline_preview()

        self._update_baseline_controls()
        self.status.configure(
            text=f"Baseline point at {ppm:.4f} ppm ({len(self.baseline_points)} total)"
        )

    def _update_baseline_controls(self):
        """Sync the Baseline tab's point counter / Apply button. Baseline
        mode is reachable by the B hotkey without ever opening that tab,
        which (now that tabs are built on first open) may not exist yet."""
        if hasattr(self, "baseline_count_label"):
            self.baseline_count_label.configure(text=f"{len(self.baseline_points)} point(s) picked")
        if hasattr(self, "apply_baseline_button"):
            self.apply_baseline_button.configure(
                state="normal" if len(self.baseline_points) >= 2 else "disabled"
            )

    def _find_baseline_point_at(self, event, tolerance_px=10):
        for p in self.baseline_points:
            try:
                disp_x, disp_y = self.ax.transData.transform((p["ppm"], p["y"]))
            except Exception:
                continue
            if (disp_x - event.x) ** 2 + (disp_y - event.y) ** 2 <= tolerance_px ** 2:
                return p
        return None

    def _start_baseline_point_drag(self, point):
        self.baseline_drag = {"point": point, "start_ppm": point["ppm"], "start_y": point["y"]}
        self._suspend_all_selectors()
        try:
            self.canvas.get_tk_widget().configure(cursor="fleur")
        except Exception:
            pass
        self.status.configure(text="Dragging baseline point - release to drop it, Esc to cancel")

    def _on_baseline_point_drag_motion(self, event):
        if self.baseline_drag is None or event.xdata is None or event.ydata is None:
            return
        point = self.baseline_drag["point"]
        point["ppm"] = event.xdata
        point["y"] = event.ydata
        point["marker"].set_data([event.xdata], [event.ydata])
        self._update_baseline_preview()
        self.canvas.draw_idle()

    def _on_baseline_point_drag_release(self, event):
        if self.baseline_drag is None:
            return
        self.baseline_drag = None
        self.baseline_points.sort(key=lambda p: p["ppm"])
        self._apply_active_selector()
        self._update_cursor()
        self._update_baseline_preview()
        self.status.configure(text=f"{len(self.baseline_points)} point(s) picked")

    def _update_baseline_preview(self):
        """Draw/refresh a dashed line showing what the fitted baseline
        would look like with the points picked so far, updated live as
        points are added, dragged, or cleared."""
        if len(self.baseline_points) < 2 or self.spectrum_data is None:
            if self.baseline_preview_line is not None:
                try:
                    self.baseline_preview_line.remove()
                except Exception:
                    pass
                self.baseline_preview_line = None
            self.canvas.draw_idle()
            return

        pts = sorted(self.baseline_points, key=lambda p: p["ppm"])
        ppms = [p["ppm"] for p in pts]
        ys = [p["y"] for p in pts]
        curve = np.interp(self.freq_axis, ppms, ys)

        if self.baseline_preview_line is None:
            self.baseline_preview_line, = self.ax.plot(
                self.freq_axis, curve, color=self._theme_colors()["baseline"], linewidth=1.2,
                linestyle="--", zorder=7,
            )
        else:
            self.baseline_preview_line.set_data(self.freq_axis, curve)
        self.canvas.draw_idle()

    def _baseline_curve(self, x):
        """The current baseline as a real-valued curve over `x`, or None if
        no correction has been applied. Piecewise-linear through whatever
        points were picked - simple, dependency-free, and exact at every
        picked point."""
        if not self.baseline_correction_points:
            return None
        ppms, ys = zip(*self.baseline_correction_points)
        return np.interp(x, ppms, ys)

    def _clear_baseline_markers(self):
        for p in self.baseline_points:
            try:
                p["marker"].remove()
            except Exception:
                pass
        self.baseline_points = []
        self.baseline_drag = None
        if self.baseline_preview_line is not None:
            try:
                self.baseline_preview_line.remove()
            except Exception:
                pass
            self.baseline_preview_line = None
        if hasattr(self, "baseline_count_label"):
            self.baseline_count_label.configure(text="0 point(s) picked")
        if hasattr(self, "apply_baseline_button"):
            self.apply_baseline_button.configure(state="disabled")
        self.canvas.draw_idle()

    def _apply_baseline_correction(self):
        if len(self.baseline_points) < 2 or self.spectrum_data is None:
            return
        self.baseline_correction_points = [
            (p["ppm"], p["y"]) for p in sorted(self.baseline_points, key=lambda p: p["ppm"])
        ]
        n_points = len(self.baseline_correction_points)
        self._clear_baseline_markers()
        if self.baseline_mode:
            self._toggle_baseline_mode()  # one-shot, like integration/multiplicity
        self.run_fft()  # replot re-derives the spectrum and re-applies the correction
        self.status.configure(text=f"Baseline correction applied using {n_points} point(s)")

    def _reset_baseline(self):
        had_correction = bool(self.baseline_correction_points)
        self._clear_baseline_markers()
        self.baseline_correction_points = []
        if had_correction and self.spectrum_data is not None:
            self.run_fft()
            self.status.configure(text="Baseline correction removed")
        else:
            self.status.configure(text="Baseline points cleared")

    # ------------------------------------------------------------ integration --
    def _on_canvas_right_click(self, event):
        if event.button != 3:  # only right-click
            return
        if event.x is None or event.y is None:
            return

        # Right-clicking the gold solvent-reference tag offers to manually
        # nudge it onto the true peak (referencing isn't always perfect).
        if self._find_solvent_tag_hit(event):
            self._show_solvent_tag_context_menu(event)
            return

        # Right-clicking a red residual-solvent/impurity tag offers to erase
        # it or manually nudge it onto the true peak (interactions with the
        # analyte can shift these signals slightly from their literature
        # value) - checked first since these tags sit on top of the plot.
        impurity_hit = self._find_impurity_tag_hit(event)
        if impurity_hit is not None:
            self._show_impurity_tag_context_menu(event, impurity_hit)
            return

        if not self.integration_regions:
            return

        region = None
        for candidate in self.integration_regions:
            tx, ty = candidate["text"].get_position()
            try:
                # Use the text's OWN transform, not transData - integration
                # labels use a blended transform (x=data, y=axes-fraction),
                # so transforming ty through transData alone would silently
                # compare against the wrong pixel row.
                disp_x, disp_y = candidate["text"].get_transform().transform((tx, ty))
            except Exception:
                continue
            if (disp_x - event.x) ** 2 + (disp_y - event.y) ** 2 <= 22 ** 2:
                region = candidate
                break

        self._show_integration_context_menu(event, region)

    def _show_integration_context_menu(self, event, region):
        menu = tk.Menu(
            self, tearoff=0, bg=PANEL_COLOR, fg="#d7d9de",
            activebackground=ACCENT, activeforeground="white", borderwidth=0,
        )
        if region is not None:
            label = f"Delete integration ({region['value']:.1f}H)"
            if region.get("is_reference"):
                label += " - resets 1H reference"
            menu.add_command(label=label, command=lambda: self._remove_integration_region(region))
            menu.add_separator()

        menu.add_command(label="Delete all integrations", command=self._delete_all_integrations)
        menu.add_command(label="Auto-assign multiplicity (all peaks)", command=self.compute_all_multiplicities)
        menu.add_command(label="Edit integration...", command=self.open_edit_integration_table)

        canvas_widget = self.canvas.get_tk_widget()
        y_from_top = canvas_widget.winfo_height() - event.y
        x_root = canvas_widget.winfo_rootx() + int(event.x)
        y_root = canvas_widget.winfo_rooty() + int(y_from_top)
        try:
            menu.tk_popup(x_root, y_root)
        finally:
            menu.grab_release()

    # ------------------------------------------------------ solvent reference tag --
    def _find_solvent_tag_hit(self, event, tolerance_px=22):
        if self.solvent_tag is None or event.x is None or event.y is None:
            return False
        _, text = self.solvent_tag
        try:
            tx, ty = text.get_position()
            disp_x, disp_y = text.get_transform().transform((tx, ty))
        except Exception:
            return False
        return (disp_x - event.x) ** 2 + (disp_y - event.y) ** 2 <= tolerance_px ** 2

    def _show_solvent_tag_context_menu(self, event):
        menu = tk.Menu(
            self, tearoff=0, bg=PANEL_COLOR, fg="#d7d9de",
            activebackground=ACCENT, activeforeground="white", borderwidth=0,
        )
        solvent_name = self.reference_info[1] if self.reference_info else "solvent"
        menu.add_command(
            label=f"Delete solvent reference ({solvent_name})",
            command=self._erase_solvent_reference_tag,
        )
        menu.add_command(
            label="Manually fit position (\u00b10.5 ppm)",
            command=self._start_solvent_tag_drag,
        )

        canvas_widget = self.canvas.get_tk_widget()
        y_from_top = canvas_widget.winfo_height() - event.y
        x_root = canvas_widget.winfo_rootx() + int(event.x)
        y_root = canvas_widget.winfo_rooty() + int(y_from_top)
        try:
            menu.tk_popup(x_root, y_root)
        finally:
            menu.grab_release()

    def _erase_solvent_reference_tag(self):
        """Remove the gold solvent-reference tag and forget which peak it
        was on - the ppm-axis shift already applied (self.ppm_reference_offset)
        is left in place, same as closing the detection popup does; this
        only clears the tag/label so a fresh one can be picked with L."""
        if self.solvent_tag is not None:
            for artist in self.solvent_tag:
                try:
                    artist.remove()
                except Exception:
                    pass
            self.solvent_tag = None
        self.reference_info = None
        self.reference_label.configure(
            text="No solvent reference yet (press L to pick one)", text_color=TEXT_MUTED,
        )
        self.canvas.draw_idle()
        self.status.configure(text="Solvent reference tag deleted")

    def _start_solvent_tag_drag(self):
        if self.reference_info is None or self.solvent_tag is None:
            return
        literature_ppm, _solvent_name = self.reference_info
        self.solvent_drag = {"start_ppm": literature_ppm}
        self._suspend_all_selectors()
        try:
            self.canvas.get_tk_widget().configure(cursor="sb_h_double_arrow")
        except Exception:
            pass
        self.status.configure(
            text="Drag the tag onto the true peak (within \u00b10.5 ppm), release to recalibrate (Esc to cancel)"
        )

    def _on_solvent_tag_drag_motion(self, event):
        if self.solvent_drag is None or self.solvent_tag is None or event.xdata is None:
            return
        origin = self.solvent_drag["start_ppm"]
        new_x = max(origin - 0.5, min(origin + 0.5, event.xdata))
        line, text = self.solvent_tag
        line.set_xdata([new_x, new_x])
        _, ty = text.get_position()
        text.set_position((new_x, ty))
        self.canvas.draw_idle()

    def _on_solvent_tag_drag_release(self, event):
        if self.solvent_drag is None:
            return
        self.solvent_drag = None
        self._apply_active_selector()
        self._update_cursor()

        if event.xdata is None or self.reference_info is None:
            if self.reference_info is not None:
                self._tag_solvent_peak(*self.reference_info)  # snap back
            return

        origin = self.reference_info[0]
        new_ppm = max(origin - 0.5, min(origin + 0.5, event.xdata))
        literature_ppm, solvent_name = self.reference_info
        # Reuse the same offset math as picking a fresh reference peak: the
        # user just told us the true peak is at new_ppm, so recalibrate the
        # axis (and shift existing integrations/tags along with it) so that
        # position becomes exactly literature_ppm again.
        self._apply_solvent_reference(new_ppm, literature_ppm, solvent_name)
        self.status.configure(text=f"Solvent tag manually fitted to {new_ppm:.4f} ppm")

    # --------------------------------------------- residual solvent tags --
    def _find_impurity_tag_hit(self, event, tolerance_px=22):
        if event.x is None or event.y is None:
            return None
        for tag in self.impurity_tags:
            try:
                tx, ty = tag["text"].get_position()
                disp_x, disp_y = tag["text"].get_transform().transform((tx, ty))
            except Exception:
                continue
            if (disp_x - event.x) ** 2 + (disp_y - event.y) ** 2 <= tolerance_px ** 2:
                return tag
        return None

    def _show_impurity_tag_context_menu(self, event, tag):
        menu = tk.Menu(
            self, tearoff=0, bg=PANEL_COLOR, fg="#d7d9de",
            activebackground=ACCENT, activeforeground="white", borderwidth=0,
        )
        menu.add_command(
            label=f"Erase residual solvent ({tag['name']})",
            command=lambda: self._erase_impurity_tag(tag),
        )
        menu.add_command(
            label="Manually fit position (\u00b10.5 ppm)",
            command=lambda: self._start_impurity_tag_drag(tag),
        )

        canvas_widget = self.canvas.get_tk_widget()
        y_from_top = canvas_widget.winfo_height() - event.y
        x_root = canvas_widget.winfo_rootx() + int(event.x)
        y_root = canvas_widget.winfo_rooty() + int(y_from_top)
        try:
            menu.tk_popup(x_root, y_root)
        finally:
            menu.grab_release()

    def _erase_impurity_tag(self, tag):
        for artist in (tag["line"], tag["text"]):
            try:
                artist.remove()
            except Exception:
                pass
        if tag in self.impurity_tags:
            self.impurity_tags.remove(tag)
        self.canvas.draw_idle()
        self.status.configure(text=f"Erased residual solvent tag ({tag['name']})")

    def _position_impurity_tag(self, tag):
        """Move a tag's artists to match its current tag['ppm'], keeping
        the same vertical placement they already had."""
        new_x = tag["ppm"]
        tag["line"].set_xdata([new_x, new_x])
        _, ty = tag["text"].get_position()
        tag["text"].set_position((new_x, ty))
        self.canvas.draw_idle()

    def _start_impurity_tag_drag(self, tag):
        self.impurity_drag = {"tag": tag, "start_ppm": tag["ppm"]}
        self._suspend_all_selectors()
        try:
            self.canvas.get_tk_widget().configure(cursor="sb_h_double_arrow")
        except Exception:
            pass
        self.status.configure(
            text=f"Drag {tag['name']} onto the true peak (within \u00b10.5 ppm), "
            "release to confirm - Esc to cancel"
        )

    def _on_impurity_drag_motion(self, event):
        if self.impurity_drag is None or event.xdata is None:
            return
        tag = self.impurity_drag["tag"]
        # Solvent-shifted peaks move a little, not a lot - clamp to +-0.5 ppm
        # of the tag's original (detected) position so a peak can't be
        # accidentally re-labeled onto some unrelated, far-away signal.
        origin = tag["origin_ppm"]
        new_x = max(origin - 0.5, min(origin + 0.5, event.xdata))
        tag["ppm"] = new_x
        self._position_impurity_tag(tag)

    def _on_impurity_drag_release(self, event):
        if self.impurity_drag is None:
            return
        tag = self.impurity_drag["tag"]
        self.impurity_drag = None
        self._apply_active_selector()
        self._update_cursor()
        self.status.configure(text=f"{tag['name']} tag fitted to {tag['ppm']:.4f} ppm")

    def _find_integration_handle_at(self, event, tolerance_px=7):
        if event.x is None:
            return None
        for region in self.integration_regions:
            for side, x_val in (("left", region["xmin"]), ("right", region["xmax"])):
                try:
                    disp_x = self.ax.transData.transform((x_val, 0))[0]
                except Exception:
                    continue
                if abs(disp_x - event.x) <= tolerance_px:
                    return region, side
        return None

    def _suspend_all_selectors(self):
        for sel in (self.span_h_selector, self.span_v_selector, self.rect_selector, self.integration_selector):
            if sel is not None:
                try:
                    sel.set_active(False)
                except Exception:
                    pass

    def _on_handle_press(self, event):
        if event.button != 1 or not self.integration_regions:
            return
        hit = self._find_integration_handle_at(event)
        if hit is None:
            return
        region, side = hit
        self.integration_drag = {"region": region, "side": side}
        self._suspend_all_selectors()

        # Show a temporary full-height highlight for easier fine-tuning while
        # actively dragging - removed again as soon as the drag ends.
        self.active_drag_highlight = self.ax.axvspan(
            region["xmin"], region["xmax"], color=self._theme_colors()["integration"], alpha=0.15, zorder=2,
        )

    def _on_handle_motion(self, event):
        if self.integration_drag is None:
            # Not dragging - just give hover feedback if the cursor is over a
            # handle, but only in the neutral state; pick/integrate/multiplicity/
            # baseline modes already own the cursor via _update_cursor.
            if (
                self.spectrum_data is not None
                and not self.pick_mode and not self.integrate_mode
                and not self.multiplicity_mode and not self.baseline_mode
            ):
                hit = self._find_integration_handle_at(event)
                try:
                    if hit:
                        cursor = "sb_h_double_arrow"
                    elif self.zoom_active:
                        cursor = {
                            "Horizontal": "sb_h_double_arrow",
                            "Vertical": "sb_v_double_arrow",
                            "Both": "dotbox",
                        }.get(self.zoom_mode, "arrow")
                    else:
                        cursor = "arrow"
                    self.canvas.get_tk_widget().configure(cursor=cursor)
                except Exception:
                    pass
            return

        if event.xdata is None:
            return
        region = self.integration_drag["region"]
        side = self.integration_drag["side"]
        new_x = event.xdata

        if side == "left":
            if new_x >= region["xmax"]:
                return
            region["xmin"] = new_x
            region["handle_left"].set_xdata([new_x, new_x])
        else:
            if new_x <= region["xmin"]:
                return
            region["xmax"] = new_x
            region["handle_right"].set_xdata([new_x, new_x])

        region["bar"].set_x(region["xmin"])
        region["bar"].set_width(region["xmax"] - region["xmin"])
        if self.active_drag_highlight is not None:
            self.active_drag_highlight.set_x(region["xmin"])
            self.active_drag_highlight.set_width(region["xmax"] - region["xmin"])

        new_center = (region["xmin"] + region["xmax"]) / 2
        region["text"].set_position((new_center, region["text"].get_position()[1]))
        if region.get("mult_text") is not None:
            region["mult_text"].set_position((new_center, region["mult_text"].get_position()[1]))

        x = self.freq_axis
        mask = (x >= region["xmin"]) & (x <= region["xmax"])
        if np.any(mask):
            raw_area = abs(float(_trapz(self.spectrum_data.real[mask], x[mask])))
            region["raw_area"] = raw_area

            if region["is_reference"]:
                self.integration_reference_area = raw_area if raw_area > 0 else 1.0
                region["value"] = 1.0
                # Resizing the reference region rescales every other integration live too
                for r in self.integration_regions:
                    if r is not region:
                        r["value"] = r["raw_area"] / self.integration_reference_area
                        r["text"].set_text(f"{r['value']:.1f}")
            else:
                ref = self.integration_reference_area or 1.0
                region["value"] = raw_area / ref

            region["text"].set_text(f"{region['value']:.1f}")

        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()

    def _on_handle_release(self, event):
        if self.integration_drag is None:
            return
        self.integration_drag = None
        if self.active_drag_highlight is not None:
            try:
                self.active_drag_highlight.remove()
            except Exception:
                pass
            self.active_drag_highlight = None
        self._apply_active_selector()
        self._update_cursor()
        self.status.configure(text="Integration boundary adjusted")
        self.canvas.draw_idle()

    def _on_integration_select(self, xmin, xmax):
        if not self.integrate_mode or self.spectrum_data is None:
            return
        lo, hi = (xmin, xmax) if xmin <= xmax else (xmax, xmin)

        x = self.freq_axis
        mask = (x >= lo) & (x <= hi)
        if not np.any(mask):
            return
        x_sub = x[mask]
        y_sub = self.spectrum_data.real[mask]
        raw_area = abs(float(_trapz(y_sub, x_sub)))

        is_reference = False
        if not self.integration_regions or self.integration_reference_area in (None, 0):
            # The first integration performed becomes the 1H reference - every
            # later integration is expressed relative to it.
            self.integration_reference_area = raw_area if raw_area > 0 else 1.0
            display_value = 1.0
            is_reference = True
        else:
            display_value = raw_area / self.integration_reference_area

        self._add_integration_region(lo, hi, display_value, raw_area, is_reference)

        # Integration is deliberately one-shot: drag once, then you're back to
        # your previous tool. Press I again to integrate another peak.
        self.integrate_mode = False
        self._apply_active_selector()
        self._update_cursor()
        self.status.configure(
            text=f"Integrated: {display_value:.1f}H (press I to integrate another peak)"
        )

    def _add_integration_region(self, lo, hi, value, raw_area, is_reference, record_undo=True):
        blended = mtransforms.blended_transform_factory(self.ax.transData, self.ax.transAxes)
        colors = self._theme_colors()

        # A thin permanent bar below the baseline (not a full-height overlay -
        # keeps the actual spectrum trace uncluttered). ymin/ymax here are in
        # axes-fraction, so it always sits in the same visual strip.
        bar = self.ax.axvspan(lo, hi, ymin=0.0, ymax=INTEGRATION_BAR_YMAX, color=colors["integration"], alpha=0.35, zorder=3)
        handle_left = self.ax.axvline(
            lo, ymin=0.0, ymax=INTEGRATION_BAR_YMAX,
            color=colors["integration_handle"], linewidth=2.2, alpha=0.85, zorder=4,
        )
        handle_right = self.ax.axvline(
            hi, ymin=0.0, ymax=INTEGRATION_BAR_YMAX,
            color=colors["integration_handle"], linewidth=2.2, alpha=0.85, zorder=4,
        )
        text = self.ax.text(
            (lo + hi) / 2, INTEGRATION_H_LABEL_Y, f"{value:.1f}", transform=blended,
            rotation=90, ha="center", va="bottom", color=colors["integration"],
            fontsize=13, fontweight="bold", zorder=6,
        )
        region = {
            "xmin": lo, "xmax": hi, "value": value, "raw_area": raw_area,
            "is_reference": is_reference, "bar": bar, "text": text,
            "handle_left": handle_left, "handle_right": handle_right,
            "multiplicity": None, "mult_text": None, "j_hz": None,
            "rep_ppm": None, "ppm_tag_line": None, "ppm_tag_text": None,
        }
        self.integration_regions.append(region)
        if record_undo:
            self.integration_undo_stack.append({
                "type": "add",
                "data": self._region_snapshot(region),
                "seq": self._next_undo_seq(),
            })
        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()
        return region

    @staticmethod
    def _integration_artists(region):
        return (
            region["bar"], region["text"], region.get("handle_left"),
            region.get("handle_right"), region.get("mult_text"),
            region.get("ppm_tag_line"), region.get("ppm_tag_text"),
        )

    @classmethod
    def _remove_region_artists(cls, region):
        for artist in cls._integration_artists(region):
            if artist is None:
                continue
            try:
                artist.remove()
            except Exception:
                pass

    @staticmethod
    def _region_snapshot(region):
        """The subset of a region's data needed to recreate it later (for
        undo, or for re-adding it after a delete-all / axis rebuild)."""
        return dict(
            xmin=region["xmin"], xmax=region["xmax"], value=region["value"],
            raw_area=region["raw_area"], is_reference=region["is_reference"],
            multiplicity=region.get("multiplicity"), j_hz=region.get("j_hz"),
            rep_ppm=region.get("rep_ppm"),
        )

    def _restore_integration_region(self, snapshot, record_undo=False):
        """Recreate a region (and its multiplicity label, if any) from a
        snapshot produced by _region_snapshot."""
        region = self._add_integration_region(
            snapshot["xmin"], snapshot["xmax"], snapshot["value"], snapshot["raw_area"],
            snapshot["is_reference"], record_undo=record_undo,
        )
        if snapshot["is_reference"]:
            value = snapshot["value"] or 1.0
            self.integration_reference_area = snapshot["raw_area"] / value
        if snapshot.get("multiplicity"):
            self._set_region_multiplicity(
                region, snapshot["multiplicity"], snapshot.get("j_hz"), snapshot.get("rep_ppm"),
            )
        return region

    def _remove_integration_region(self, region, record_undo=True):
        self._remove_region_artists(region)
        if region in self.integration_regions:
            self.integration_regions.remove(region)
        if record_undo:
            self.integration_undo_stack.append({
                "type": "delete",
                "data": self._region_snapshot(region),
                "seq": self._next_undo_seq(),
            })
        if region.get("is_reference"):
            # The 1H reference integration was removed - the next integration
            # performed (or the next region re-added via undo) establishes a
            # new reference from scratch.
            self.integration_reference_area = None
        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()

    def _delete_all_integrations(self):
        if not self.integration_regions:
            return
        all_data = [self._region_snapshot(r) for r in self.integration_regions]
        for region in list(self.integration_regions):
            self._remove_region_artists(region)
        self.integration_regions = []
        self.integration_reference_area = None
        self.integration_undo_stack.append({
            "type": "delete_all", "data": all_data, "seq": self._next_undo_seq(),
        })
        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()

    def _clear_all_integrations(self):
        # Like _delete_all_integrations, but doesn't record undo history -
        # used for hard resets (new file load, full reprocess).
        for region in list(self.integration_regions):
            self._remove_region_artists(region)
        self.integration_regions = []
        self.integration_reference_area = None
        self.integration_undo_stack = []
        self.integration_drag = None
        self.active_drag_highlight = None

    # ------------------------------------------------------------ multiplicity --
    @staticmethod
    def _format_j_hz(j_hz):
        """j_hz may be a single float, a list of floats (a compound
        multiplet like dd has one J per component, largest first), or None.
        Returns the comma-joined "8.0, 2.0" string, or None."""
        if j_hz is None:
            return None
        if isinstance(j_hz, (list, tuple)):
            if not j_hz:
                return None
            return ", ".join(f"{v:.1f}" for v in j_hz)
        return f"{j_hz:.1f}"

    @staticmethod
    def _decompose_multiplet(positions_hz, heights, max_components=3):
        """Try to explain a resolved-but-non-uniformly-spaced set of peaks
        as a first-order compound multiplet (dd, ddd, dt, td, qd, tt, ...)
        by recursively "peeling off" one splitting at a time: if the peaks
        can be grouped into adjacent pairs/triplets/quartets of the right
        spacing AND the right relative intensity (1:1, 1:2:1, or 1:3:3:1),
        each group collapses to one virtual peak (weighted center, summed
        height) and the same test is applied to what's left. Every
        distinct gap seen in the current peak set is tried as the
        candidate splitting (not just the smallest) - after one level is
        peeled, the next split isn't always the smallest remaining gap.

        This assumes a "first-order", well-separated-couplings pattern
        (the usual case chemists report by eye) - couplings similar in
        size, or overlapping multiplets, won't decompose cleanly and
        correctly fall through to "m".

        Returns a list of (letter, J_hz) in the order peeled (SMALLEST J
        first overall isn't guaranteed - just the order found) if the
        whole pattern collapses to a single line, else None.
        """
        positions_hz = np.asarray(positions_hz, dtype=float)
        heights = np.asarray(heights, dtype=float)
        n = len(positions_hz)

        if n == 1:
            return []
        if max_components <= 0 or n > 16:
            return None

        spacings = np.diff(positions_hz)
        if np.any(spacings <= 0):
            return None

        # Cluster near-equal gaps (within tolerance) into distinct candidate
        # J values, smallest first.
        candidates = []
        for g in sorted(spacings):
            if not candidates or abs(g - candidates[-1]) > max(candidates[-1] * 0.15, 0.4):
                candidates.append(float(g))

        for j_candidate in candidates:
            tol = max(j_candidate * 0.15, 0.4)

            attempts = []
            if n % 2 == 0:
                attempts.append(("d", 2, (1.0, 1.0)))
            if n % 3 == 0:
                attempts.append(("t", 3, (1.0, 2.0, 1.0)))
            if n % 4 == 0:
                attempts.append(("q", 4, (1.0, 3.0, 3.0, 1.0)))

            for letter, group_size, ideal_ratios in attempts:
                ok = True
                new_pos, new_ht = [], []
                for i in range(0, n, group_size):
                    group_pos = positions_hz[i:i + group_size]
                    group_ht = heights[i:i + group_size]
                    gaps = np.diff(group_pos)
                    if np.any(np.abs(gaps - j_candidate) > tol):
                        ok = False
                        break
                    # Compare relative intensities within the group to the
                    # ideal binomial ratio (loosely - real spectra are noisy).
                    scale = group_ht[0] / ideal_ratios[0] if ideal_ratios[0] else group_ht[0]
                    if scale <= 0:
                        ok = False
                        break
                    expected = np.array(ideal_ratios) * scale
                    if np.any(np.abs(group_ht - expected) > 0.6 * expected + 0.3 * scale):
                        ok = False
                        break
                    weight_total = float(np.sum(group_ht))
                    center = float(np.sum(group_pos * group_ht) / weight_total) if weight_total > 0 else float(np.mean(group_pos))
                    new_pos.append(center)
                    new_ht.append(weight_total)
                if not ok:
                    continue

                rest = SauceNMRApp._decompose_multiplet(
                    np.array(new_pos), np.array(new_ht), max_components - 1,
                )
                if rest is not None:
                    return [(letter, j_candidate)] + rest

        return None

    def _compute_multiplicity(self, lo, hi):
        """Count distinct real peaks within [lo, hi] using scipy's
        prominence-based peak finder, with a noise floor estimated robustly
        (via MAD) from the whole spectrum, so noisy baseline wiggle doesn't
        get counted as extra splitting. Identifies simple (s/d/t/q/quint/
        sext/hept) and common compound (dd, ddd, dt, td, qd, tt, ...)
        patterns, estimating J (Hz) from peak spacing if a spectrometer
        frequency is known, and a representative chemical shift to tag the
        peak with:
          - odd peak count (true center line, e.g. t, ddd with an odd
            total): the single tallest point
          - even peak count (no true center line, e.g. d, dd, q): the
            midpoint between the two tallest points
          - unresolved multiplets (m): the center of the integrated region
        Returns (label, count, j_hz, rep_ppm), where j_hz is a single float
        for a simple pattern, a list (largest first) for a compound one, or
        None."""
        y_full = self.spectrum_data.real
        x = self.freq_axis
        region_center = (lo + hi) / 2.0

        mad = np.median(np.abs(y_full - np.median(y_full)))
        noise_std = 1.4826 * mad if mad > 0 else (np.std(y_full) or 1.0)

        mask = (x >= lo) & (x <= hi)
        x_sub = x[mask]
        y_sub = y_full[mask]
        if len(y_sub) < 3:
            return None, 0, None, None

        if not _SCIPY_AVAILABLE:
            return "m", -1, None, region_center  # signal "unavailable" - caller shows a message

        min_distance = max(1, int(len(x_sub) * 0.02))
        thresh = noise_std * 6.0
        peaks, props = find_peaks(y_sub, height=thresh, prominence=thresh, distance=min_distance)
        count = len(peaks)

        if count <= 0:
            return None, 0, None, None

        peak_ppms = x_sub[peaks]
        heights = props["peak_heights"]
        order = np.argsort(peak_ppms)
        peak_ppms = peak_ppms[order]
        heights = heights[order]

        sf_mhz = None
        if self.freq_unit == "ppm":
            sf_mhz = self._parse_float(self.spectrometer_freq.get(), default=None)

        label = None
        j_hz = None

        if count == 1:
            label = "s"
        elif sf_mhz:
            spacings_hz = np.diff(peak_ppms) * sf_mhz
            mean_spacing = float(np.mean(spacings_hz))
            if count <= 7 and np.ptp(spacings_hz) <= max(0.15 * mean_spacing, 0.4):
                # Uniform spacing - a simple single-J pattern.
                label = MULTIPLICITY_LABELS.get(count, "m")
                j_hz = mean_spacing
            else:
                # Not uniform - try a compound (first-order) decomposition.
                components = self._decompose_multiplet(peak_ppms * sf_mhz, heights)
                if components:
                    components = sorted(components, key=lambda c: -c[1])  # largest J first
                    label = "".join(letter for letter, _ in components)
                    j_hz = [j for _, j in components]
        elif count <= 7:
            # No calibration to get Hz - can still name a uniformly-spaced
            # simple pattern (in ppm), just without a J value.
            if np.ptp(np.diff(peak_ppms)) <= max(0.15 * np.mean(np.diff(peak_ppms)), 1e-4):
                label = MULTIPLICITY_LABELS.get(count, "m")

        if label is None:
            label = "m"

        if label == "m":
            # No clean, trustworthy set of discrete lines - just use the
            # middle of what the user integrated.
            rep_ppm = region_center
        elif count % 2 == 1:
            # Odd number of lines has a true center line - the tallest one
            # (e.g. the middle line of a symmetric triplet).
            rep_ppm = float(peak_ppms[np.argmax(heights)])
        else:
            # Even number of lines has no single center line - use the
            # midpoint between the two most prominent (the two central
            # lines of a symmetric doublet/quartet/sextet).
            top2 = np.argsort(heights)[-2:]
            rep_ppm = float(np.mean(peak_ppms[top2]))

        return label, count, j_hz, rep_ppm

    def _find_integration_region_overlapping(self, lo, hi):
        best = None
        best_overlap = 0.0
        for r in self.integration_regions:
            overlap = min(hi, r["xmax"]) - max(lo, r["xmin"])
            if overlap > best_overlap:
                best_overlap = overlap
                best = r
        return best

    def compute_all_multiplicities(self):
        if self.spectrum_data is None or not self.integration_regions:
            messagebox.showinfo("No integrations", "Integrate at least one peak first.")
            return
        if not _SCIPY_AVAILABLE:
            messagebox.showinfo(
                "scipy required",
                "Multiplicity detection needs the 'scipy' package. Install it with:\n\n"
                "pip install scipy",
            )
            return

        assigned = 0
        skipped = 0
        for region in self.integration_regions:
            label, count, j_hz, rep_ppm = self._compute_multiplicity(region["xmin"], region["xmax"])
            if label is None:
                skipped += 1
                continue
            self._set_region_multiplicity(region, label, j_hz, rep_ppm)
            assigned += 1

        msg = f"Multiplicity assigned to {assigned} peak(s)"
        if skipped:
            msg += f", {skipped} skipped (no clear peak above the noise floor)"
        self.status.configure(text=msg)

    # ------------------------------------------------------------ SI report --
    def _report_solvent_name(self):
        if self.reference_info is not None:
            internal_name = self.reference_info[1]
        else:
            internal_name = self.detection_solvent.get()
        if not internal_name or internal_name == "Select solvent...":
            return None
        return SOLVENT_REPORT_NAMES.get(internal_name, internal_name)

    def _build_nmr_report_text(self):
        if not self.integration_regions:
            return None

        freq_mhz = self._parse_float(self.spectrometer_freq.get(), default=None)
        freq_str = f"{freq_mhz:.0f}" if freq_mhz else "??"
        solvent_str = (self._report_solvent_name() or "solvent").translate(_SUBSCRIPT_DIGITS)

        def sort_key(r):
            ppm = r.get("rep_ppm")
            if ppm is None:
                ppm = (r["xmin"] + r["xmax"]) / 2
            return -ppm

        entries = []
        for region in sorted(self.integration_regions, key=sort_key):
            label = region.get("multiplicity")
            h_str = f"{round(region['value'])}H"

            if label is None or label == "m":
                # No clean discrete peaks (or never assigned) - report as a
                # range across the integrated region, standard practice for
                # an unresolved multiplet.
                hi, lo = max(region["xmin"], region["xmax"]), min(region["xmin"], region["xmax"])
                entries.append(f"{hi:.2f} \u2013 {lo:.2f} (m, {h_str})")
                continue

            ppm = region.get("rep_ppm")
            if ppm is None:
                ppm = (region["xmin"] + region["xmax"]) / 2
            j_str = self._format_j_hz(region.get("j_hz"))
            if j_str is not None:
                entries.append(f"{ppm:.2f} ({label}, J = {j_str} Hz, {h_str})")
            else:
                entries.append(f"{ppm:.2f} ({label}, {h_str})")

        body = ", ".join(entries)
        # Assignments (ArylH, CHMe2, etc.) are left out for now - planned as
        # a future feature once structure-based (SMILES/ChemDraw) peak
        # assignment is added.
        return f"\u00b9H NMR ({freq_str} MHz, {solvent_str}) \u03b4 {body}."

    def copy_nmr_report(self):
        text = self._build_nmr_report_text()
        if text is None:
            messagebox.showinfo(
                "Nothing to report", "Integrate at least one peak first (I hotkey)."
            )
            return
        self.clipboard_clear()
        self.clipboard_append(text)
        self.status.configure(text="NMR report text copied to clipboard")

    def _on_multiplicity_select(self, xmin, xmax):
        if not self.multiplicity_mode or self.spectrum_data is None:
            return
        lo, hi = (xmin, xmax) if xmin <= xmax else (xmax, xmin)

        if not _SCIPY_AVAILABLE:
            messagebox.showinfo(
                "scipy required",
                "Multiplicity detection needs the 'scipy' package. Install it with:\n\n"
                "pip install scipy",
            )
        else:
            label, count, j_hz, rep_ppm = self._compute_multiplicity(lo, hi)
            region = self._find_integration_region_overlapping(lo, hi)
            if region is None:
                self.status.configure(
                    text="No integration here yet - integrate this peak first, then assign multiplicity"
                )
            elif label is None:
                self.status.configure(text="No distinguishable peak found above the noise floor")
            else:
                self._set_region_multiplicity(region, label, j_hz, rep_ppm)
                j_str = self._format_j_hz(j_hz)
                j_msg = f", J \u2248 {j_str} Hz" if j_str is not None else ""
                self.status.configure(text=f"Multiplicity assigned: {label} ({count} peak(s) detected{j_msg})")

        # One-shot, like integration mode
        self.multiplicity_mode = False
        self._apply_active_selector()
        self._update_cursor()

    _MULTIPLICITY_PEAK_COUNTS = {"s": 1, "d": 2, "t": 3, "q": 4, "quint": 5, "sext": 6, "hept": 7}

    def _estimate_j_for_manual_multiplicity(self, region, label):
        """When a multiplicity is manually typed/overridden in the edit
        table (e.g. correcting an auto-detected "m" to "d"), estimate J
        from the region's most intense peaks - the same idea as automatic
        detection, just told what pattern to expect instead of guessing
        it. Only handles simple, single-J patterns (s/d/t/q/quint/sext/
        hept); compound labels (dd, ddd, ...) are left for manual J entry.
        Returns (j_hz, rep_ppm), either of which may be None if it can't
        be determined (no calibration, not enough resolvable peaks, etc.)."""
        n = self._MULTIPLICITY_PEAK_COUNTS.get(label)
        if not n or n < 2:
            return None, None
        if self.spectrum_data is None or not _SCIPY_AVAILABLE:
            return None, None
        if self.freq_unit != "ppm":
            return None, None
        sf_mhz = self._parse_float(self.spectrometer_freq.get(), default=None)
        if not sf_mhz:
            return None, None

        x = self.freq_axis
        y_full = self.spectrum_data.real
        lo, hi = region["xmin"], region["xmax"]
        mask = (x >= lo) & (x <= hi)
        x_sub = x[mask]
        y_sub = y_full[mask]
        if len(y_sub) < n:
            return None, None

        mad = np.median(np.abs(y_full - np.median(y_full)))
        noise_std = 1.4826 * mad if mad > 0 else (np.std(y_full) or 1.0)
        min_distance = max(1, int(len(x_sub) * 0.02))

        peaks, props = find_peaks(y_sub, height=noise_std * 3.0, prominence=noise_std * 3.0, distance=min_distance)
        if len(peaks) < n:
            # Thresholds too strict for this region - fall back to plain
            # local-maxima detection (still spaced apart) before giving up.
            peaks, props = find_peaks(y_sub, distance=min_distance)
        if len(peaks) < n:
            return None, None

        heights = props["peak_heights"] if "peak_heights" in props else y_sub[peaks]
        top_idx = np.argsort(heights)[-n:]
        top_ppms = np.sort(x_sub[peaks][top_idx])

        spacings_hz = np.diff(top_ppms) * sf_mhz
        j_hz = float(np.mean(spacings_hz))

        if n % 2 == 1:
            rep_ppm = float(top_ppms[n // 2])
        else:
            mid = n // 2
            rep_ppm = float((top_ppms[mid - 1] + top_ppms[mid]) / 2.0)
        return j_hz, rep_ppm

    def _set_region_multiplicity(self, region, label, j_hz=None, rep_ppm=None):
        old_text = region.get("mult_text")
        if old_text is not None:
            try:
                old_text.remove()
            except Exception:
                pass
        for old_artist in (region.get("ppm_tag_line"), region.get("ppm_tag_text")):
            if old_artist is not None:
                try:
                    old_artist.remove()
                except Exception:
                    pass

        center_x = (region["xmin"] + region["xmax"]) / 2
        blended = mtransforms.blended_transform_factory(self.ax.transData, self.ax.transAxes)
        colors = self._theme_colors()
        mult_text = self.ax.text(
            center_x, INTEGRATION_M_LABEL_Y, label, transform=blended,
            rotation=90, ha="center", va="top", color=colors["integration"],
            fontsize=12, fontweight="bold", fontstyle="italic", zorder=6,
        )

        ppm_tag_line = ppm_tag_text = None
        if rep_ppm is not None:
            # Same fixed top-10% band the solvent/impurity tags live in, so
            # every peak's chemical shift is labeled at a consistent height.
            ppm_tag_line = self.ax.axvline(
                rep_ppm, ymin=TAG_BAND_YMIN, ymax=TAG_STUB_YMAX, color=colors["multiplicity"],
                linewidth=1.2, zorder=7,
            )
            ppm_tag_text = self.ax.text(
                rep_ppm, TAG_LABEL_Y, f"{rep_ppm:.2f}", transform=blended, rotation=90,
                va="bottom", ha="center", fontsize=11, color=colors["multiplicity"],
                fontweight="bold", zorder=7,
            )

        region["multiplicity"] = label
        region["mult_text"] = mult_text
        region["j_hz"] = j_hz
        region["rep_ppm"] = rep_ppm
        region["ppm_tag_line"] = ppm_tag_line
        region["ppm_tag_text"] = ppm_tag_text
        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()

    def _set_integration_reference(self, region, new_value):
        """Redefine the 1H reference so that `region` corresponds to
        `new_value` H - every integration's displayed value (including its
        on-canvas tag) is recalculated relative to this new reference."""
        if new_value <= 0 or region["raw_area"] <= 0:
            return
        self.integration_reference_area = region["raw_area"] / new_value
        for r in self.integration_regions:
            r["is_reference"] = (r is region)
            r["value"] = r["raw_area"] / self.integration_reference_area
            r["text"].set_text(f"{r['value']:.1f}")
        self.canvas.draw_idle()
        self._refresh_edit_table_if_open()

    def open_edit_integration_table(self):
        self._rebuild_edit_integration_table()

    def _refresh_edit_table_if_open(self):
        if self.edit_integration_popup is not None:
            self._rebuild_edit_integration_table()

    def _on_edit_table_close(self):
        if self.edit_integration_popup is not None:
            try:
                self.edit_integration_popup.destroy()
            except Exception:
                pass
            self.edit_integration_popup = None

    def _rebuild_edit_integration_table(self):
        if self.edit_integration_popup is not None:
            try:
                self.edit_integration_popup.destroy()
            except Exception:
                pass
            self.edit_integration_popup = None

        if not self.integration_regions:
            messagebox.showinfo("No integrations", "Integrate at least one peak first.")
            return

        popup = ctk.CTkToplevel(self)
        popup.title("Edit integrations")
        popup.geometry("540x460")
        popup.configure(fg_color=PANEL_COLOR)
        # transient, not "-topmost": topmost pins the window above every
        # other application on the desktop even after you alt-tab away.
        popup.transient(self)
        popup.lift()
        popup.protocol("WM_DELETE_WINDOW", self._on_edit_table_close)
        self.edit_integration_popup = popup

        ctk.CTkLabel(
            popup, text="Integrations (sorted by ppm)",
            font=ctk.CTkFont(size=13, weight="bold"),
        ).pack(padx=14, pady=(14, 2), anchor="w")
        ctk.CTkLabel(
            popup,
            text="Edit the Integration value to redefine the 1H reference - every "
            "other peak recalculates relative to it.\n(Note: 1-decimal precision is "
            "fixed for now - a control to change it will be added to the right-click "
            "menu later.)",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=400, justify="left",
        ).pack(padx=14, pady=(0, 8), anchor="w")

        header = ctk.CTkFrame(popup, fg_color="transparent")
        header.pack(fill="x", padx=18)
        ctk.CTkLabel(header, text="ppm", width=55, font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(header, text="Intensity", width=80, font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).grid(row=0, column=1, sticky="w")
        ctk.CTkLabel(header, text="Integ. (H)", width=80, font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).grid(row=0, column=2, sticky="w")
        ctk.CTkLabel(header, text="Mult.", width=50, font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).grid(row=0, column=3, sticky="w")
        ctk.CTkLabel(header, text="J (Hz)", width=65, font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).grid(row=0, column=4, sticky="w")

        scroll = ctk.CTkScrollableFrame(popup, fg_color=PANEL_COLOR)
        scroll.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        sorted_regions = sorted(self.integration_regions, key=lambda r: (r["xmin"] + r["xmax"]) / 2)
        for region in sorted_regions:
            row = ctk.CTkFrame(scroll, fg_color=BG_COLOR, corner_radius=8)
            row.pack(fill="x", padx=4, pady=3)
            center = (region["xmin"] + region["xmax"]) / 2

            ctk.CTkLabel(row, text=f"{center:.2f}", width=55, font=ctk.CTkFont(size=11)).grid(
                row=0, column=0, padx=6, pady=8
            )
            ctk.CTkLabel(row, text=f"{region['raw_area']:.0f}", width=80, font=ctk.CTkFont(size=11)).grid(
                row=0, column=1, padx=6, pady=8
            )

            var = tk.StringVar(value=f"{region['value']:.1f}")
            entry = ctk.CTkEntry(row, textvariable=var, width=65, height=28)
            entry.grid(row=0, column=2, padx=6, pady=8)

            def _commit(event=None, region=region, var=var):
                try:
                    new_val = float(var.get())
                except ValueError:
                    return
                self._set_integration_reference(region, new_val)

            entry.bind("<Return>", _commit)
            entry.bind("<FocusOut>", _commit)

            mult_var = tk.StringVar(value=region.get("multiplicity") or "")
            mult_entry = ctk.CTkEntry(row, textvariable=mult_var, width=50, height=28)
            mult_entry.grid(row=0, column=3, padx=6, pady=8)

            def _commit_mult(event=None, region=region, var=mult_var):
                label = var.get().strip()
                if label:
                    old_label = region.get("multiplicity")
                    if label != old_label:
                        j_hz, rep_ppm = self._estimate_j_for_manual_multiplicity(region, label)
                        self._set_region_multiplicity(region, label, j_hz=j_hz, rep_ppm=rep_ppm)
                        if j_hz is not None:
                            self.status.configure(
                                text=f"{label}: J = {self._format_j_hz(j_hz)} Hz "
                                     f"(estimated from the most intense peaks)"
                            )
                    else:
                        # Unchanged - just re-commit without touching J/rep_ppm
                        self._set_region_multiplicity(
                            region, label, j_hz=region.get("j_hz"), rep_ppm=region.get("rep_ppm"),
                        )
                    self._refresh_edit_table_if_open()
                else:
                    # Cleared by the user - remove the on-canvas multiplicity tag
                    old = region.get("mult_text")
                    if old is not None:
                        try:
                            old.remove()
                        except Exception:
                            pass
                    region["multiplicity"] = None
                    region["mult_text"] = None
                    self.canvas.draw_idle()

            mult_entry.bind("<Return>", _commit_mult)
            mult_entry.bind("<FocusOut>", _commit_mult)

            j_val = region.get("j_hz")
            j_var = tk.StringVar(value=self._format_j_hz(j_val) or "")
            j_entry = ctk.CTkEntry(row, textvariable=j_var, width=90, height=28)
            j_entry.grid(row=0, column=4, padx=6, pady=8)

            def _commit_j(event=None, region=region, var=j_var):
                text = var.get().strip()
                if not text:
                    region["j_hz"] = None
                    return
                try:
                    # Comma-separated for a compound multiplet (e.g. "8.0, 2.0"
                    # for a dd) - a single number still works as before.
                    parts = [float(p.strip()) for p in text.split(",") if p.strip()]
                    if not parts:
                        region["j_hz"] = None
                    elif len(parts) == 1:
                        region["j_hz"] = parts[0]
                    else:
                        region["j_hz"] = parts
                except ValueError:
                    pass

            j_entry.bind("<Return>", _commit_j)
            j_entry.bind("<FocusOut>", _commit_j)

    def _init_selectors(self):
        # Tear down any previous selectors (axes get cleared/redrawn on replot)
        for sel in (self.span_h_selector, self.span_v_selector, self.rect_selector,
                    self.integration_selector, self.multiplicity_selector):
            if sel is not None:
                try:
                    sel.set_active(False)
                    sel.disconnect_events()
                except Exception:
                    pass

        # Horizontal mode: a full-height vertical band, only x matters
        self.span_h_selector = SpanSelector(
            self.ax,
            self._on_hspan_select,
            direction="horizontal",
            useblit=True,
            button=[1],
            minspan=0,
            props=dict(facecolor=ACCENT, alpha=0.18),
            interactive=False,
        )

        # Vertical mode: a full-width horizontal band, only y matters
        self.span_v_selector = SpanSelector(
            self.ax,
            self._on_vspan_select,
            direction="vertical",
            useblit=True,
            button=[1],
            minspan=0,
            props=dict(facecolor=ACCENT, alpha=0.18),
            interactive=False,
        )

        # Both mode: a bounded rectangle
        self.rect_selector = RectangleSelector(
            self.ax,
            self._on_rect_select,
            useblit=True,
            button=[1],
            minspanx=5,
            minspany=5,
            spancoords="pixels",
            interactive=False,
            props=dict(facecolor=ACCENT, edgecolor=ACCENT, alpha=0.15, fill=True),
        )

        # Integration mode: a full-height band (like Horizontal zoom) but in a
        # distinct color, left in place (not just a live-drag preview) once released.
        self.integration_selector = SpanSelector(
            self.ax,
            self._on_integration_select,
            direction="horizontal",
            useblit=True,
            button=[1],
            minspan=0,
            props=dict(facecolor=INTEGRATION_COLOR, alpha=0.18),
            interactive=False,
        )

        # Multiplicity mode: same shape as integration, distinct purple color
        self.multiplicity_selector = SpanSelector(
            self.ax,
            self._on_multiplicity_select,
            direction="horizontal",
            useblit=True,
            button=[1],
            minspan=0,
            props=dict(facecolor=MULTIPLICITY_COLOR, alpha=0.18),
            interactive=False,
        )

        self._apply_active_selector()

    def _apply_active_selector(self):
        if self.integrate_mode:
            self.span_h_selector.set_active(False)
            self.span_v_selector.set_active(False)
            self.rect_selector.set_active(False)
            self.multiplicity_selector.set_active(False)
            self.integration_selector.set_active(True)
            return
        if self.multiplicity_mode:
            self.span_h_selector.set_active(False)
            self.span_v_selector.set_active(False)
            self.rect_selector.set_active(False)
            self.integration_selector.set_active(False)
            self.multiplicity_selector.set_active(True)
            return
        if self.baseline_mode:
            self.span_h_selector.set_active(False)
            self.span_v_selector.set_active(False)
            self.rect_selector.set_active(False)
            self.integration_selector.set_active(False)
            self.multiplicity_selector.set_active(False)
            return
        self.integration_selector.set_active(False)
        self.multiplicity_selector.set_active(False)
        self.span_h_selector.set_active(self.zoom_active and self.zoom_mode == "Horizontal")
        self.span_v_selector.set_active(self.zoom_active and self.zoom_mode == "Vertical")
        self.rect_selector.set_active(self.zoom_active and self.zoom_mode == "Both")

    def _on_hspan_select(self, xmin, xmax):
        self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
        cur_xlim = self.ax.get_xlim()
        if cur_xlim[0] > cur_xlim[1]:
            self.ax.set_xlim(xmax, xmin)
        else:
            self.ax.set_xlim(xmin, xmax)
        self.canvas.draw_idle()

    def _on_vspan_select(self, ymin, ymax):
        self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
        self.ax.set_ylim(ymin, ymax)
        self.canvas.draw_idle()

    def _on_rect_select(self, eclick, erelease):
        x1, y1 = eclick.xdata, eclick.ydata
        x2, y2 = erelease.xdata, erelease.ydata
        if x1 is None or x2 is None or y1 is None or y2 is None:
            return

        self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())

        xlo, xhi = (x1, x2) if x1 <= x2 else (x2, x1)
        ylo, yhi = (y1, y2) if y1 <= y2 else (y2, y1)

        cur_xlim = self.ax.get_xlim()
        if cur_xlim[0] > cur_xlim[1]:
            self.ax.set_xlim(xhi, xlo)
        else:
            self.ax.set_xlim(xlo, xhi)
        self.ax.set_ylim(ylo, yhi)

        self.canvas.draw_idle()

    @staticmethod
    def _margined_ylim(top, margin_fraction=0.075):
        """Given a desired ceiling, return (bottom, top) such that y=0 sits
        at `margin_fraction` from the bottom of the range - the same
        baseline-margin logic used by scroll-zoom."""
        margin_below = (margin_fraction / (1 - margin_fraction)) * top
        return (-margin_below, top)

    def _current_overlay_state(self):
        """The state dict of the current page, if (and only if) it's an
        overlay/stacked page - else None."""
        if self.current_page_index is None or not (0 <= self.current_page_index < len(self.pages)):
            return None
        page = self.pages[self.current_page_index]
        if page.get("type") == "overlay" and page["state"] is not None:
            return page["state"]
        return None

    def _reset_overlay_scales(self, state):
        """Undo any scroll-zoom (or manual slider) intensity scaling, back
        to 1.0x for every spectrum - this is what actually changes on a
        scroll for a stacked page (the axis view itself is deliberately
        left alone so baselines never move), so F/H need to reset this,
        not just the view, or they'd have nothing to undo."""
        for i in range(len(state["series"])):
            state["series"][i]["scale"] = 1.0
            self._update_overlay_line(state, i)

    def reset_full(self):
        overlay_state = self._current_overlay_state()
        if overlay_state is not None:
            if overlay_state.get("stacked"):
                self._reset_overlay_scales(overlay_state)
            xlim = overlay_state.get("original_xlim")
            ylim = overlay_state.get("original_ylim")
            if xlim is None or ylim is None:
                return
            self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
            self.ax.set_xlim(*xlim)
            self.ax.set_ylim(*ylim)
            overlay_state["ylim"] = ylim  # remember the reset, so switching away/back keeps it
            self.canvas.draw_idle()
            return

        if self.full_xlim is None or self.default_ylim is None:
            return
        # F is a view change like any other zoom - make it Ctrl+Z-able, so
        # accidentally hitting it doesn't throw away a careful zoom.
        self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
        self.ax.set_xlim(*self.full_xlim)
        self.ax.set_ylim(*self.default_ylim)
        self.canvas.draw_idle()

    def reset_height(self):
        overlay_state = self._current_overlay_state()
        if overlay_state is not None:
            if overlay_state.get("stacked"):
                self._reset_overlay_scales(overlay_state)
            ylim = overlay_state.get("original_ylim")
            if ylim is None:
                return
            self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
            self.ax.set_ylim(*ylim)
            overlay_state["ylim"] = ylim
            self.canvas.draw_idle()
            return

        if self.default_ylim is None:
            return
        self._push_zoom_undo(self.ax.get_xlim(), self.ax.get_ylim())
        self.ax.set_ylim(*self.default_ylim)
        self.canvas.draw_idle()

    # ------------------------------------------------------------ actions --
    def _on_view_change(self, value):
        self.view_mode = "fid" if value == "FID" else "spectrum"
        if self.complex_data is None:
            return
        if self.view_mode == "fid":
            self._plot_fid()
        else:
            self._plot_spectrum()

    # ------------------------------------------------------------ pages --
    @staticmethod
    def _page_name_for_path(path):
        if not path:
            return "Untitled"
        base = os.path.basename(path.rstrip("/\\"))
        stem, ext = os.path.splitext(base)
        if not ext or base.lower() == "fid":
            # Bruker layout is .../SAMPLE_NAME/EXPNO/fid - the immediate
            # parent is just a numbered experiment folder (EXPNO), not a
            # useful name. The real sample name is the folder above that -
            # keep the EXPNO in parentheses too, so e.g. loading multiple
            # experiments (1H, 13C, 19F, ...) from the same sample folder
            # still gives each page a distinct name.
            parent_dir = os.path.dirname(path.rstrip("/\\"))
            parent_name = os.path.basename(parent_dir)
            if parent_name.isdigit():
                grandparent = os.path.basename(os.path.dirname(parent_dir))
                return f"{grandparent} ({parent_name})" if grandparent else parent_name
            return parent_name or base
        return stem

    def _capture_current_state(self):
        """Everything needed to reconstruct the current spectrum and all
        its annotations later. Shared by on-disk save (base64-encoded
        separately) and in-memory page-switching.

        Also caches the final computed spectrum/axis (spectrum_data,
        freq_axis, freq_unit) purely for in-memory use (e.g. the overlay
        view) - these are NOT written to the .saucenmr file, since they're
        cheaply re-derivable from raw_fid + params."""
        if self._raw_fid is None:
            return None
        return {
            "current_path": self.current_path,
            "raw_fid": self._raw_fid.copy(),
            "params": {
                "zero_fill_name": self.zero_fill_name.get(),
                "line_broadening": self.line_broadening.get(),
                "spectral_width": self.spectral_width.get(),
                "transmitter_offset": self.transmitter_offset.get(),
                "spectrometer_freq": self.spectrometer_freq.get(),
                "grpdly": self.grpdly.get(),
                "phase_deg": self.phase_deg.get(),
                "reverse_axis": bool(self.reverse_axis.get()),
                "dtype_name": self.dtype_name.get(),
                "byte_order_name": self.byte_order_name.get(),
                "detection_solvent": self.detection_solvent.get(),
            },
            "ppm_reference_offset": self.ppm_reference_offset,
            "reference_info": tuple(self.reference_info) if self.reference_info else None,
            "baseline_correction_points": list(self.baseline_correction_points),
            "integration_regions": [self._region_snapshot(r) for r in self.integration_regions],
            "impurity_tags": [
                {"ppm": t["ppm"], "name": t["name"], "origin_ppm": t["origin_ppm"]}
                for t in self.impurity_tags
            ],
            "spectrum_data": self.spectrum_data.copy() if self.spectrum_data is not None else None,
            "freq_axis": self.freq_axis.copy() if self.freq_axis is not None else None,
            "freq_unit": self.freq_unit,
        }

    def _restore_state(self, state):
        """Apply a state dict (from _capture_current_state, or reconstructed
        from a .saucenmr file) as the live spectrum - shared by page-
        switching and load_processed_file."""
        self._clear_all_impurity_tags()
        self._clear_all_integrations()
        # A stored zoom belongs to the axis of the spectrum being replaced -
        # restoring it onto a different spectrum (different ppm range and
        # intensity scale) would jump the view somewhere meaningless.
        self.zoom_undo_stack = []
        self.reference_info = None
        self.solvent_tag = None
        self._clear_baseline_markers()
        self.baseline_correction_points = []

        self.current_path = state["current_path"]
        self._raw_fid = state["raw_fid"]
        self.ppm_reference_offset = state.get("ppm_reference_offset", 0.0)
        self.path_label.configure(text=self.current_path or "(original file path unknown)")

        params = state.get("params", {})
        # Each .set() below fires a write-trace that reprocesses the whole
        # spectrum. Suspend that for the bulk repopulation - run_fft() is
        # called explicitly once everything is in place (further down).
        self._suspend_live_reprocess = True
        try:
            self.zero_fill_name.set(params.get("zero_fill_name", ZERO_FILL_OPTIONS[0]))
            self.line_broadening.set(params.get("line_broadening", "0"))
            self.spectral_width.set(params.get("spectral_width", ""))
            self.transmitter_offset.set(params.get("transmitter_offset", ""))
            self.spectrometer_freq.set(params.get("spectrometer_freq", ""))
            self.grpdly.set(params.get("grpdly", ""))
            self.phase_deg.set(params.get("phase_deg", "0"))
            self.reverse_axis.set(True)  # always reversed (NMR convention) - the toggle is gone, nobody used the other way
            if params.get("dtype_name"):
                self.dtype_name.set(params["dtype_name"])
            if params.get("byte_order_name"):
                self.byte_order_name.set(params["byte_order_name"])
        finally:
            self._suspend_live_reprocess = False
        if params.get("detection_solvent"):
            self.detection_solvent.set(params["detection_solvent"])
            self._on_detection_solvent_change(params["detection_solvent"])
        else:
            self.detection_solvent.set("Select solvent...")
            self._on_detection_solvent_change("Select solvent...")

        ref_info = state.get("reference_info")
        self.reference_info = tuple(ref_info) if ref_info else None
        if self.reference_info:
            self.reference_label.configure(
                text=f"Reference: {self.reference_info[1]} ({self.reference_info[0]:.2f} ppm)",
                text_color=ACCENT,
            )
        else:
            self.reference_label.configure(
                text="No solvent reference yet (press L to pick one)", text_color=TEXT_MUTED,
            )

        self.baseline_correction_points = [
            tuple(p) for p in state.get("baseline_correction_points", [])
        ]

        self._set_view_switch("Spectrum")
        self.view_mode = "spectrum"
        self.run_fft()  # builds the spectrum + re-tags the solvent reference from reference_info

        for snap in state.get("integration_regions", []):
            self._restore_integration_region(snap, record_undo=False)
        for tag in state.get("impurity_tags", []):
            self._tag_impurity([tag["ppm"]], tag["name"], origins=[tag.get("origin_ppm", tag["ppm"])])

    def _sync_current_page_state(self):
        """Save the live spectrum's state back into its page slot, before
        switching away to a different page (or closing it). Overlay pages
        are static snapshots with nothing "live" to sync back, EXCEPT the
        current y-zoom level, which is remembered so returning to the page
        doesn't silently re-fit to a fresh (and possibly very different,
        if scroll-zoom has since grown the data) view."""
        if self.current_page_index is None or not (0 <= self.current_page_index < len(self.pages)):
            return
        page = self.pages[self.current_page_index]
        if page.get("type") == "overlay":
            if page["state"] is not None:
                page["state"]["ylim"] = self.ax.get_ylim()
            return
        state = self._capture_current_state()
        if state is not None:
            page["state"] = state

    def _add_new_page(self, name, page_type="single"):
        """Create a new, empty page slot and make it current. The caller
        is responsible for actually populating its state right after
        (this only handles the bookkeeping/switching)."""
        self._sync_current_page_state()
        self.pages.append({"name": name, "type": page_type, "state": None, "_autosave_path": None})
        self.current_page_index = len(self.pages) - 1
        self._refresh_pages_list()

    def _show_page(self, page):
        """Render whichever page dict is now current - a normal spectrum
        or a static overlay snapshot."""
        if page.get("type") == "overlay":
            if page["state"] is not None:
                self._restore_overlay_view(page["state"])
        else:
            if page["state"] is not None:
                self._restore_state(page["state"])

    def _switch_to_page(self, index):
        if not (0 <= index < len(self.pages)):
            return
        currently_overlay = (
            self.current_page_index is not None
            and 0 <= self.current_page_index < len(self.pages)
            and self.pages[self.current_page_index].get("type") == "overlay"
        )
        if index == self.current_page_index and not currently_overlay:
            return
        self._sync_current_page_state()
        self.current_page_index = index
        self._show_page(self.pages[index])
        self._refresh_pages_list()
        self.status.configure(text=f"Switched to {self.pages[index]['name']}")

    def _close_page(self, index):
        if not (0 <= index < len(self.pages)):
            return
        if index == self.current_page_index:
            self._sync_current_page_state()  # capture any edits before it's gone
        was_current = (index == self.current_page_index)
        closed_page = self.pages[index]
        closed_name = closed_page["name"]

        self.page_close_undo_stack.append({
            "seq": self._next_undo_seq(), "index": index, "page": closed_page,
        })
        del self.pages[index]

        if not self.pages:
            self.current_page_index = None
            self._reset_to_empty()
        elif was_current:
            new_index = min(index, len(self.pages) - 1)
            self.current_page_index = new_index
            self._show_page(self.pages[new_index])
        elif index < self.current_page_index:
            self.current_page_index -= 1

        self._refresh_pages_list()
        self.status.configure(text=f"Closed {closed_name} (Ctrl+Z to undo)")

    def _rename_page(self, index):
        if not (0 <= index < len(self.pages)):
            return
        dialog = ctk.CTkInputDialog(text="New name for this page:", title="Rename page")
        new_name = dialog.get_input()
        if new_name and new_name.strip():
            self.pages[index]["name"] = new_name.strip()
            self._refresh_pages_list()
            self.status.configure(text=f"Renamed page to {new_name.strip()}")

    def _reset_to_empty(self):
        """Clear the view entirely - used when the last page is closed."""
        self._clear_all_impurity_tags()
        self._clear_all_integrations()
        self.reference_info = None
        self.solvent_tag = None
        self._clear_baseline_markers()
        self.baseline_correction_points = []
        self._raw_fid = None
        self._cached_spectrum_raw = None
        self.spectrum_data = None
        self.current_path = None
        self.path_label.configure(text="No file loaded")
        self.reference_label.configure(
            text="No solvent reference yet (press L to pick one)", text_color=TEXT_MUTED,
        )
        self.detection_solvent.set("Select solvent...")
        self._on_detection_solvent_change("Select solvent...")
        self._draw_placeholder()

    def _show_tooltip(self, widget, text, event=None):
        self._hide_tooltip()
        try:
            if event is not None and hasattr(event, "x_root"):
                x = event.x_root + 14
                y = event.y_root + 12
            else:
                x = widget.winfo_rootx() + 12
                y = widget.winfo_rooty() + widget.winfo_height() + 4
            tw = tk.Toplevel(widget)
            tw.wm_overrideredirect(True)
            tw.wm_geometry(f"+{x}+{y}")
            tk.Label(
                tw, text=text, background="#1c1e24", foreground="#d7d9de",
                relief="solid", borderwidth=1, font=("Segoe UI", 10), padx=6, pady=3,
            ).pack()
            self._active_tooltip = tw
        except Exception:
            self._active_tooltip = None

    def _hide_tooltip(self, event=None):
        tw = getattr(self, "_active_tooltip", None)
        if tw is not None:
            try:
                tw.destroy()
            except Exception:
                pass
            self._active_tooltip = None

    @staticmethod
    def _truncate_page_name(name, max_chars=24):
        if len(name) <= max_chars:
            return name
        return name[:max_chars - 1].rstrip() + "\u2026"

    def _bind_page_name_tooltip(self, widget, name):
        # Only bother if the name is long enough that it's actually being
        # truncated in the button (see _truncate_page_name).
        if len(name) <= 24:
            return
        # add="+" so this can coexist with the hover-preview bindings
        # (_bind_page_preview_hover), which also use <Enter>/<Leave>.
        widget.bind("<Enter>", lambda event, n=name, w=widget: self._show_tooltip(w, n, event), add="+")
        widget.bind("<Leave>", self._hide_tooltip, add="+")

    def _on_page_click(self, event, index):
        # Shift-click selects for overlay WITHOUT switching pages; a plain
        # click switches to it, same as before.
        if event.state & 0x0001:
            self._toggle_overlay_selection(index)
        else:
            self._switch_to_page(index)

    # ------------------------------------------------- drag-to-reorder pages --
    def _on_page_press(self, event, index):
        self._page_drag = {
            "start_index": index, "dragging": False, "target_index": None,
            "start_x_root": event.x_root, "start_y_root": event.y_root,
        }

    def _on_page_drag_motion(self, event, index):
        drag = self._page_drag
        if drag is None or drag["start_index"] != index:
            return
        if not drag["dragging"]:
            # Small tolerance (in screen pixels moved since the press), so
            # this doesn't turn every plain click into a "drag".
            dx = abs(event.x_root - drag["start_x_root"])
            dy = abs(event.y_root - drag["start_y_root"])
            if dx < 4 and dy < 4:
                return
            drag["dragging"] = True
            self._cancel_page_preview_timer()
            self._hide_page_preview()
        target = self._page_index_at_y(event.y_root)
        if target is None:
            return
        drag["target_index"] = target
        self._show_drag_indicator(target)

    def _on_page_release(self, event, index):
        drag = self._page_drag
        self._page_drag = None
        self._clear_drag_indicator()
        if drag is None or drag["start_index"] != index:
            return
        if not drag["dragging"]:
            self._on_page_click(event, index)
            return
        target = drag.get("target_index")
        start = drag["start_index"]
        if target is None:
            return
        self._reorder_page(start, target)

    def _page_index_at_y(self, y_root):
        """Which row-slot (0..len(rows), insert-before semantics) the given
        root y-coordinate falls in, ignoring the drop indicator itself."""
        indicator = self._page_drag_indicator
        rows = [w for w in self.pages_list_frame.winfo_children() if w is not indicator]
        if not rows:
            return None
        for i, row in enumerate(rows):
            mid = row.winfo_rooty() + row.winfo_height() / 2
            if y_root < mid:
                return i
        return len(rows)

    def _ensure_drag_indicator(self):
        indicator = self._page_drag_indicator
        if indicator is not None and indicator.winfo_exists():
            return indicator
        indicator = ctk.CTkFrame(self.pages_list_frame, height=3, fg_color=ACCENT, corner_radius=2)
        self._page_drag_indicator = indicator
        return indicator

    def _show_drag_indicator(self, target_index):
        rows = [w for w in self.pages_list_frame.winfo_children() if w is not self._page_drag_indicator]
        if not rows:
            return
        indicator = self._ensure_drag_indicator()
        indicator.pack_forget()
        if target_index >= len(rows):
            indicator.pack(fill="x", pady=(2, 0), after=rows[-1])
        else:
            indicator.pack(fill="x", pady=(0, 2), before=rows[target_index])

    def _clear_drag_indicator(self):
        indicator = self._page_drag_indicator
        if indicator is not None:
            try:
                indicator.pack_forget()
            except Exception:
                pass

    def _reorder_page(self, start, target):
        if not (0 <= start < len(self.pages)):
            return
        target = max(0, min(target, len(self.pages)))
        insert_at = target - 1 if target > start else target

        current_page_obj = None
        if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
            current_page_obj = self.pages[self.current_page_index]

        page = self.pages.pop(start)
        insert_at = max(0, min(insert_at, len(self.pages)))  # valid range after the pop
        if insert_at == start:
            self.pages.insert(start, page)  # no-op move; put it back where it was
            return
        self.pages.insert(insert_at, page)

        if current_page_obj is not None:
            for k, p in enumerate(self.pages):
                if p is current_page_obj:
                    self.current_page_index = k
                    break

        self._refresh_pages_list()
        self.status.configure(text=f"Moved \"{page['name']}\"")

    # ------------------------------------------------- hover-preview on pages --
    def _bind_page_preview_hover(self, widget, index):
        widget.bind("<Enter>", lambda event, w=widget, idx=index: self._on_page_hover_enter(event, w, idx), add="+")
        widget.bind("<Leave>", lambda event, w=widget: self._on_page_hover_leave(event, w), add="+")

    def _on_page_hover_enter(self, event, widget, index):
        self._cancel_page_preview_timer()
        self._page_preview_timer = self.after(3000, lambda w=widget, idx=index: self._show_page_preview(w, idx))

    def _on_page_hover_leave(self, event, widget):
        self._cancel_page_preview_timer()
        self._hide_page_preview()

    def _cancel_page_preview_timer(self):
        timer_id = self._page_preview_timer
        if timer_id is not None:
            try:
                self.after_cancel(timer_id)
            except Exception:
                pass
            self._page_preview_timer = None

    def _hide_page_preview(self):
        popup = self._page_preview_popup
        if popup is not None:
            try:
                popup.destroy()
            except Exception:
                pass
            self._page_preview_popup = None
        # The preview's Figure() is created standalone (not via pyplot), so
        # it isn't tracked by any global figure registry - dropping the
        # reference here is all that's needed for it to be garbage collected.
        self._page_preview_figure = None

    def _get_page_preview_series(self, index):
        """List of (x, y) arrays to plot for a page's preview thumbnail, or
        None if there's nothing to show (e.g. an empty just-created page).
        The currently-open page's data lives in the live attributes, not
        page["state"] (that's only synced back on switch-away), so it's
        handled as a special case."""
        if not (0 <= index < len(self.pages)):
            return None
        page = self.pages[index]

        if page.get("type") == "overlay":
            state = page.get("state")
            if not state or not state.get("series"):
                return None
            return [
                (s["x"], s["y"] * s.get("scale", 1.0) + s.get("offset", 0.0))
                for s in state["series"]
            ]

        if index == self.current_page_index:
            spectrum_data, freq_axis = self.spectrum_data, self.freq_axis
        else:
            state = page.get("state")
            if not state:
                return None
            spectrum_data, freq_axis = state.get("spectrum_data"), state.get("freq_axis")

        if spectrum_data is None or freq_axis is None:
            return None
        return [(freq_axis, spectrum_data.real)]

    def _show_page_preview(self, widget, index):
        self._page_preview_timer = None
        if not widget.winfo_exists() or not (0 <= index < len(self.pages)):
            return
        series_list = self._get_page_preview_series(index)
        if not series_list:
            return
        self._hide_page_preview()

        popup = tk.Toplevel(self)
        popup.wm_overrideredirect(True)
        x = widget.winfo_rootx() + widget.winfo_width() + 10
        y = widget.winfo_rooty()
        popup.wm_geometry(f"+{x}+{y}")
        popup.configure(bg="#1c1e24")
        # Same reasoning as the detection popup: transient (not -topmost)
        # keeps this above SauceNMR without pinning it above other apps.
        popup.transient(self)

        tk.Label(
            popup, text=self._truncate_page_name(self.pages[index]["name"], max_chars=40),
            bg="#1c1e24", fg="#d7d9de", font=("Segoe UI", 10, "bold"), anchor="w",
        ).pack(fill="x", padx=6, pady=(4, 0))

        fig = Figure(figsize=(3.0, 1.8), dpi=100)
        fig.patch.set_facecolor("#1c1e24")
        ax = fig.add_subplot(111)
        ax.set_facecolor("#1c1e24")
        palette = ["#3ea6ff", "#ff6b6b", "#66d9a0", "#ffd54a", "#c77dff", "#ff9f4a"]
        x_mins, x_maxs = [], []
        for k, (x_vals, y_vals) in enumerate(series_list):
            if x_vals is None or y_vals is None or len(x_vals) == 0:
                continue
            ax.plot(x_vals, y_vals, color=palette[k % len(palette)], linewidth=0.8)
            x_mins.append(float(np.min(x_vals)))
            x_maxs.append(float(np.max(x_vals)))
        if x_mins and x_maxs:
            ax.set_xlim(max(x_maxs), min(x_mins))  # NMR convention: high ppm on the left
        for spine in ax.spines.values():
            spine.set_visible(False)
        ax.set_xticks([])
        ax.set_yticks([])
        fig.subplots_adjust(left=0.02, right=0.98, top=0.97, bottom=0.05)

        canvas = FigureCanvasTkAgg(fig, master=popup)
        canvas.draw()
        canvas.get_tk_widget().configure(bg="#1c1e24", highlightthickness=0)
        canvas.get_tk_widget().pack(padx=6, pady=(2, 6))

        self._page_preview_popup = popup
        self._page_preview_figure = fig

    def _refresh_pages_list(self):
        # A rebuild mid-hover would otherwise leave a stale preview/timer
        # pointing at a destroyed row.
        self._cancel_page_preview_timer()
        self._hide_page_preview()
        self._page_drag = None

        # Keep selections matched by name across a refresh, since indices
        # can shift when a page is closed/reordered.
        previously_selected_names = {
            self.pages[i]["name"] for i in self.overlay_selected if 0 <= i < len(self.pages)
        }

        for child in self.pages_list_frame.winfo_children():
            child.destroy()
        self._page_drag_indicator = None
        self.overlay_selected = set()

        if not self.pages:
            ctk.CTkLabel(
                self.pages_list_frame, text="No spectra loaded yet",
                font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
            ).pack(anchor="w", pady=2)
            return

        for i, page in enumerate(self.pages):
            if page["name"] in previously_selected_names:
                self.overlay_selected.add(i)

        for i, page in enumerate(self.pages):
            is_current = (i == self.current_page_index)
            is_overlay_selected = i in self.overlay_selected
            row = ctk.CTkFrame(self.pages_list_frame, fg_color="transparent")
            row.pack(fill="x", pady=1)
            page_btn = ctk.CTkButton(
                row, text=self._truncate_page_name(page["name"]), anchor="w",
                height=28, corner_radius=6, width=1,
                fg_color=ACCENT if is_current else "transparent",
                hover_color="#2f8fe0" if is_current else "#22252b",
                text_color="white" if is_current else "#d7d9de",
                border_width=2 if is_overlay_selected else 0,
                border_color=BASELINE_COLOR if is_overlay_selected else PANEL_COLOR,
            )
            page_btn.pack(side="left", fill="x", expand=True)
            # Press/motion/release (rather than a plain <Button-1>) so a
            # click-and-hold-and-move can be told apart from a plain click
            # and used to drag-reorder the page; a plain click still selects
            # it exactly as before (see _on_page_release).
            page_btn.bind("<ButtonPress-1>", lambda event, idx=i: self._on_page_press(event, idx))
            page_btn.bind("<B1-Motion>", lambda event, idx=i: self._on_page_drag_motion(event, idx))
            page_btn.bind("<ButtonRelease-1>", lambda event, idx=i: self._on_page_release(event, idx))
            page_btn.bind("<Button-3>", lambda event, idx=i: self._rename_page(idx))
            self._bind_page_name_tooltip(page_btn, page["name"])
            self._bind_page_preview_hover(page_btn, i)
            ctk.CTkButton(
                row, text="\u00d7", width=26, height=28, corner_radius=6,
                fg_color="transparent", hover_color="#4a2020", text_color="#d7d9de",
                command=lambda idx=i: self._close_page(idx),
            ).pack(side="left", padx=(4, 0))

    def _toggle_overlay_selection(self, index):
        if not (0 <= index < len(self.pages)):
            return
        if index in self.overlay_selected:
            self.overlay_selected.discard(index)
        else:
            self.overlay_selected.add(index)
        self._refresh_pages_list()

    def _collect_selected_series(self):
        """Validate the shift-selected pages and build a fresh (unstacked,
        scale=1.0) series list from their cached spectra. Returns
        (series, n_valid) or (None, 0) if the selection isn't usable (a
        message box has already been shown in that case)."""
        selected = sorted(self.overlay_selected)
        if len(selected) < 2:
            messagebox.showinfo(
                "Select spectra", "Shift-click 2 or more page names above to select them first."
            )
            return None, 0

        valid = [
            i for i in selected
            if self.pages[i]["state"] is not None
            and self.pages[i]["state"].get("spectrum_data") is not None
            and self.pages[i]["state"].get("freq_axis") is not None
        ]
        if len(valid) < 2:
            messagebox.showinfo(
                "Nothing to overlay", "The selected pages don't have a processed spectrum yet."
            )
            return None, 0

        # Always normalize each spectrum to its own peak height - makes
        # shape/shift comparison meaningful regardless of concentration,
        # which is what you want the overwhelming majority of the time.
        normalize = True
        series = []
        for i in valid:
            state = self.pages[i]["state"]
            x = state["freq_axis"].copy()
            y = state["spectrum_data"].real.copy()
            if normalize:
                peak = float(np.max(y))
                if peak > 0:
                    y = y / peak
            series.append({"name": self.pages[i]["name"], "x": x, "y": y, "scale": 1.0, "offset": 0.0})
        return series, len(valid)

    def _finish_creating_overlay_page(self, title_prefix, series, stacked):
        overlay_state = {
            "type": "overlay",
            "series": series,
            "normalize": True,
            "reverse_axis": bool(self.reverse_axis.get()),
            "stacked": stacked,
        }
        names = " + ".join(s["name"] for s in series)
        self._add_new_page(f"{title_prefix} ({names})", page_type="overlay")
        self.pages[self.current_page_index]["state"] = overlay_state
        self._restore_overlay_view(overlay_state)
        self.overlay_selected = set()
        self._refresh_pages_list()
        word = "stacked" if stacked else "overlay"
        self.status.configure(text=f"Created {word} page with {len(series)} spectra")

    def _toggle_current_overlay_stacked(self, target_stacked):
        """If the current page is already an overlay/stacked page, just
        re-style it in place instead of rebuilding from the shift-
        selected pages - so clicking Stack while looking at an overlay
        (or vice versa) transforms what's already there. Returns True if
        it handled it this way (nothing further to do), False if the
        current page isn't an overlay page at all."""
        if self.current_page_index is None:
            return False
        page = self.pages[self.current_page_index]
        if page.get("type") != "overlay" or page.get("state") is None:
            return False
        state = page["state"]
        series = state["series"]
        if target_stacked:
            typical_height = float(np.mean([float(np.max(s["y"])) for s in series])) if series else 0.0
            gap = typical_height * 1.15 if typical_height > 0 else 1.0
            for k, s in enumerate(series):
                s["offset"] = k * gap
        else:
            for s in series:
                s["offset"] = 0.0
        state["stacked"] = target_stacked
        self._restore_overlay_view(state)
        word = "stacked" if target_stacked else "overlay"
        self.status.configure(text=f"Switched to {word} view")
        return True

    def _show_overlay(self):
        self._sync_current_page_state()
        if self._toggle_current_overlay_stacked(target_stacked=False):
            return
        series, n = self._collect_selected_series()
        if series is None:
            return
        self._finish_creating_overlay_page("Overlay", series, stacked=False)

    def _show_stacked(self):
        self._sync_current_page_state()
        if self._toggle_current_overlay_stacked(target_stacked=True):
            return
        series, n = self._collect_selected_series()
        if series is None:
            return

        # Space each spectrum out vertically by a consistent gap based on
        # their typical peak height, so they read top-to-bottom without
        # overlapping.
        typical_height = float(np.mean([float(np.max(s["y"])) for s in series]))
        gap = typical_height * 1.15 if typical_height > 0 else 1.0
        for k, s in enumerate(series):
            s["offset"] = k * gap

        self._finish_creating_overlay_page("Stacked", series, stacked=True)

    def _restore_overlay_view(self, state):
        """Draw a static overlay snapshot (from _show_overlay, a page
        switch, or a reloaded .saucenmr) - shared by all three."""
        # A clean slate - no cursor mode makes sense while several spectra
        # share one axis.
        self._exit_exclusive_modes()
        if self.zoom_active:
            self.zoom_active = False
        self.zoom_undo_stack = []  # belongs to the previous page's axis
        self._apply_active_selector()
        self._update_cursor()

        self.ax.clear()
        self._style_axis(self.ax)

        colors = self._theme_colors()
        palette = colors.get(
            "overlay_palette", ["#3ea6ff", "#ff6b6b", "#66d9a0", "#ffd54a", "#c77dff", "#ff9f4a", "#5fd4d4", "#e07bd0"],
        )
        normalize = state.get("normalize", True)
        stacked = state.get("stacked", False)
        all_x, all_y = [], []
        self._overlay_lines = []
        for k, s in enumerate(state["series"]):
            y = s["y"] * s.get("scale", 1.0) + s.get("offset", 0.0)
            line, = self.ax.plot(s["x"], y, color=palette[k % len(palette)], linewidth=0.9, label=s["name"])
            self._overlay_lines.append(line)
            all_x.append(s["x"])
            all_y.append(y)

        self.ax.set_xlabel("Chemical shift (ppm)")
        self._set_plot_title_and_ylabel(
            "Stacked" if stacked else "Overlay",
            "Normalized intensity" if normalize else "Intensity",
        )
        legend = self.ax.legend(
            loc="upper right", fontsize=9, facecolor=colors["bg"], edgecolor=colors["text"],
        )
        for text in legend.get_texts():
            text.set_color(colors["text"])

        xmin = min(float(x.min()) for x in all_x)
        xmax = max(float(x.max()) for x in all_x)
        if state.get("reverse_axis", True):
            self.ax.set_xlim(xmax, xmin)
        else:
            self.ax.set_xlim(xmin, xmax)
        self.full_xlim = self.ax.get_xlim()

        # Needed for F (reset_full), H (reset_height), and scroll-to-zoom to
        # work on the overlay too - these were left stale before, which is
        # why they silently did nothing.
        ymax_all = max(float(np.max(y)) for y in all_y)
        ymin_all = min(float(np.min(y)) for y in all_y)
        self.full_ylim = (ymin_all, ymax_all)
        self.default_ylim = self._margined_ylim(ymax_all) if ymax_all > 0 else (ymin_all, ymax_all)

        # The TRUE original view, captured once (when scale/offset are
        # still whatever they were at creation) and never touched again -
        # this is what F/H return to, regardless of how much scroll-zoom
        # has since scaled the data. (self.full_xlim/default_ylim above
        # get recomputed from the CURRENT, possibly-scaled data on every
        # redraw, so they're the wrong thing for F/H to use here.)
        if state.get("original_xlim") is None:
            state["original_xlim"] = self.full_xlim
        if state.get("original_ylim") is None:
            state["original_ylim"] = self.default_ylim

        # Restore whatever y-view the user had scrolled to last time they
        # were on this page, rather than always re-fitting fresh - scroll-
        # zoom on a stacked page grows the data without touching the view,
        # so a fresh fit here would silently discard the crop they set up
        # and could balloon to a huge range if they'd zoomed in a lot.
        remembered_ylim = state.get("ylim")
        if remembered_ylim is not None:
            self.ax.set_ylim(*remembered_ylim)
        else:
            self.ax.set_ylim(*self.default_ylim)
            state["ylim"] = self.default_ylim

        self._apply_figure_layout()
        self.canvas.draw()

    def _open_intensity_normalizer(self):
        if self.current_page_index is None or not (0 <= self.current_page_index < len(self.pages)):
            messagebox.showinfo("No overlay", "Switch to an overlay page first.")
            return
        page = self.pages[self.current_page_index]
        if page.get("type") != "overlay" or page["state"] is None:
            messagebox.showinfo("No overlay", "Switch to an overlay page first.")
            return
        state = page["state"]

        win = ctk.CTkToplevel(self)
        win.title("Adjust intensities")
        win.configure(fg_color=PANEL_COLOR)
        win.geometry(f"420x{140 + 74 * len(state['series'])}")
        # transient, not "-topmost": topmost pins the window above every
        # other application on the desktop even after you alt-tab away.
        win.transient(self)
        win.lift()

        ctk.CTkLabel(
            win, text=f"Scale each spectrum's intensity in \u201c{page['name']}\u201d",
            font=ctk.CTkFont(size=12), text_color=TEXT_MUTED, wraplength=380,
        ).pack(anchor="w", padx=16, pady=(14, 4))

        sliders = []
        value_labels = []

        def make_handler(idx):
            def handler(v):
                v = float(v)
                state["series"][idx]["scale"] = v
                value_labels[idx].configure(text=f"{v:.2f}x")
                self._update_overlay_line(state, idx)
            return handler

        for i, s in enumerate(state["series"]):
            row = ctk.CTkFrame(win, fg_color="transparent")
            row.pack(fill="x", padx=16, pady=(10, 0))
            top_row = ctk.CTkFrame(row, fg_color="transparent")
            top_row.pack(fill="x")
            ctk.CTkLabel(
                top_row, text=s["name"], font=ctk.CTkFont(size=12), text_color="#d7d9de",
            ).pack(side="left")
            value_label = ctk.CTkLabel(
                top_row, text=f"{s.get('scale', 1.0):.2f}x",
                font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
            )
            value_label.pack(side="right")
            value_labels.append(value_label)

            slider = ctk.CTkSlider(row, from_=0.0, to=3.0, number_of_steps=300, command=make_handler(i))
            slider.set(s.get("scale", 1.0))
            slider.pack(fill="x", pady=(4, 0))
            sliders.append(slider)

        def reset_all():
            for i, s in enumerate(state["series"]):
                s["scale"] = 1.0
                sliders[i].set(1.0)
                value_labels[i].configure(text="1.00x")
                self._update_overlay_line(state, i)

        ctk.CTkButton(win, text="Reset all to 1.0x", command=reset_all).pack(
            fill="x", padx=16, pady=16,
        )

    def _update_overlay_line(self, state, series_index):
        """Cheaply update one overlay line's y-data in place, without a
        full axis rebuild - lets the intensity sliders feel responsive.
        Only touches the canvas if `state` is still the page actually on
        screen (the user may have switched pages while the dialog is open,
        in which case the scale value above is still saved correctly - it
        just won't be visible until they switch back)."""
        if self.current_page_index is None or not (0 <= self.current_page_index < len(self.pages)):
            return
        if self.pages[self.current_page_index].get("state") is not state:
            return
        if series_index >= len(state["series"]) or series_index >= len(self._overlay_lines):
            return
        s = state["series"][series_index]
        y = s["y"] * s.get("scale", 1.0) + s.get("offset", 0.0)
        self._overlay_lines[series_index].set_ydata(y)
        self.canvas.draw_idle()

    def browse_file(self):
        path = filedialog.askopenfilename(
            title="Select FID file or processed NMR",
            filetypes=[
                ("FID or processed NMR", "*.fid fid *" + PROCESSED_FILE_EXT),
                ("FID files", "*.fid fid"),
                ("SauceNMR processed file", "*" + PROCESSED_FILE_EXT),
                ("All files", "*.*"),
            ],
        )
        if not path:
            return
        self._open_any_file(path)

    def _open_any_file(self, path):
        if path.lower().endswith(PROCESSED_FILE_EXT):
            self.load_processed_file(path)
        else:
            self.load_and_plot(path)

    def _on_file_drop(self, event):
        # event.data is a Tcl list - each path may be brace-wrapped if it
        # contains spaces; tk.splitlist handles that correctly either way.
        paths = self.tk.splitlist(event.data)
        if not paths:
            return
        path = paths[0]
        if not os.path.isfile(path):
            messagebox.showerror("Error loading file", f"Not a file: {path}")
            return
        self._open_any_file(path)

    def load_and_plot(self, path):
        try:
            data = self._read_fid(path)
        except Exception as exc:
            messagebox.showerror("Error loading file", str(exc))
            self.status.configure(text="Failed to load " + os.path.basename(path))
            return

        # Every load opens as its own new page - switching pages later
        # brings back exactly this spectrum and all its annotations.
        self._add_new_page(self._page_name_for_path(path))

        self.current_path = path
        self._raw_fid = data  # uncorrected, exactly as read from disk
        self.ppm_reference_offset = 0.0
        self.path_label.configure(text=path)

        self.reference_label.configure(
            text="No solvent reference yet (press L to pick one)", text_color=TEXT_MUTED,
        )
        self.detection_solvent.set("Select solvent...")
        self._on_detection_solvent_change("Select solvent...")
        self._clear_all_impurity_tags()
        self._clear_all_integrations()
        self.reference_info = None
        self.solvent_tag = None
        self._clear_baseline_markers()
        self.baseline_correction_points = []

        n = len(data)
        status_msg = "Loaded " + os.path.basename(path) + " - " + str(n) + " complex points"

        # Try to auto-detect SW / O1 / SFO1 / GRPDLY from a companion Bruker
        # acqus file, so the spectrum axis can default to ppm and the raw
        # digital-filter delay can be stripped automatically.
        self.spectral_width.set("")
        self.transmitter_offset.set("")
        self.spectrometer_freq.set("")
        self.grpdly.set("")
        acqus_params = self._autodetect_acqus_params(path)
        if acqus_params:
            if "sw_hz" in acqus_params:
                self.spectral_width.set(f"{acqus_params['sw_hz']:.6g}")
                self.transmitter_offset.set(f"{acqus_params['o1_hz']:.6g}")
                self.spectrometer_freq.set(f"{acqus_params['sfo1_mhz']:.6g}")
                status_msg += " - acquisition parameters auto-detected (ppm axis)"
            if "grpdly" in acqus_params:
                self.grpdly.set(f"{acqus_params['grpdly']:.6g}")
                status_msg += " - digital filter delay auto-corrected"

        self._refresh_corrected_fid()
        self.status.configure(text=status_msg)

        self._set_view_switch("Spectrum")
        self.view_mode = "spectrum"
        self.phase_deg.set("0")
        self.run_fft()
        # Auto-phase immediately so the spectrum looks right from the start,
        # without needing to click "Auto" manually every time.
        self.auto_phase_correction()

    @staticmethod
    def _page_payload_from_state(name, state):
        """One page's worth of the save-file format - shared by every page
        when saving multiple at once. Handles both a normal single
        spectrum and a static overlay snapshot."""
        if state.get("type") == "overlay":
            return {
                "name": name,
                "type": "overlay",
                "normalize": state.get("normalize", True),
                "reverse_axis": state.get("reverse_axis", True),
                "stacked": state.get("stacked", False),
                "ylim": list(state["ylim"]) if state.get("ylim") is not None else None,
                "original_xlim": list(state["original_xlim"]) if state.get("original_xlim") is not None else None,
                "original_ylim": list(state["original_ylim"]) if state.get("original_ylim") is not None else None,
                "series": [
                    {
                        "name": s["name"],
                        "scale": s.get("scale", 1.0),
                        "offset": s.get("offset", 0.0),
                        "x_dtype": str(np.asarray(s["x"]).dtype),
                        "x_b64": base64.b64encode(np.asarray(s["x"]).tobytes()).decode("ascii"),
                        "y_dtype": str(np.asarray(s["y"]).dtype),
                        "y_b64": base64.b64encode(np.asarray(s["y"]).tobytes()).decode("ascii"),
                    }
                    for s in state["series"]
                ],
            }
        raw = state["raw_fid"]
        return {
            "name": name,
            "type": "single",
            "original_path": state["current_path"],
            "raw_fid_dtype": str(raw.dtype),
            "raw_fid_b64": base64.b64encode(raw.tobytes()).decode("ascii"),
            "params": state["params"],
            "ppm_reference_offset": state["ppm_reference_offset"],
            "reference_info": list(state["reference_info"]) if state["reference_info"] else None,
            "baseline_correction_points": [list(p) for p in state["baseline_correction_points"]],
            "integration_regions": state["integration_regions"],
            "impurity_tags": state["impurity_tags"],
        }

    @staticmethod
    def _state_from_page_payload(page_data):
        """The reverse of _page_payload_from_state - also handles a legacy
        v1 file, whose top-level fields are laid out identically to one
        (single-spectrum) page's worth of data here."""
        if page_data.get("type") == "overlay":
            series = []
            for s in page_data.get("series", []):
                x = np.frombuffer(base64.b64decode(s["x_b64"]), dtype=s["x_dtype"]).copy()
                y = np.frombuffer(base64.b64decode(s["y_b64"]), dtype=s["y_dtype"]).copy()
                series.append({
                    "name": s["name"], "x": x, "y": y,
                    "scale": s.get("scale", 1.0), "offset": s.get("offset", 0.0),
                })
            return {
                "type": "overlay",
                "series": series,
                "normalize": page_data.get("normalize", True),
                "reverse_axis": page_data.get("reverse_axis", True),
                "stacked": page_data.get("stacked", False),
                "ylim": tuple(page_data["ylim"]) if page_data.get("ylim") is not None else None,
                "original_xlim": tuple(page_data["original_xlim"]) if page_data.get("original_xlim") is not None else None,
                "original_ylim": tuple(page_data["original_ylim"]) if page_data.get("original_ylim") is not None else None,
            }
        raw_bytes = base64.b64decode(page_data["raw_fid_b64"])
        raw = np.frombuffer(raw_bytes, dtype=page_data["raw_fid_dtype"]).copy()
        ref_info = page_data.get("reference_info")
        return {
            "type": "single",
            "current_path": page_data.get("original_path"),
            "raw_fid": raw,
            "params": page_data.get("params", {}),
            "ppm_reference_offset": float(page_data.get("ppm_reference_offset", 0.0)),
            "reference_info": tuple(ref_info) if ref_info else None,
            "baseline_correction_points": [
                tuple(p) for p in page_data.get("baseline_correction_points", [])
            ],
            "integration_regions": page_data.get("integration_regions", []),
            "impurity_tags": page_data.get("impurity_tags", []),
        }

    # ------------------------------------------------------------ autosave --
    def _pick_autosave_path(self, folder):
        """Choose which numbered autosave slot to use in `folder`. If a
        slot is free, use it (this is what keeps a fresh session from
        clobbering an orphaned autosave left behind by an earlier crashed
        session - it gets its own slot instead). Once every slot is
        taken, reuse whichever is oldest, capping it at AUTOSAVE_MAX_FILES
        per folder."""
        candidates = [
            os.path.join(folder, f"sauceNMR_autosave_{n}.saucenmr")
            for n in range(1, AUTOSAVE_MAX_FILES + 1)
        ]
        existing = [p for p in candidates if os.path.exists(p)]
        for p in candidates:
            if p not in existing:
                return p
        existing.sort(key=lambda p: os.path.getmtime(p))
        return existing[0]

    def _autosave_current_page(self):
        """Silently save the currently active page next to its source FID,
        so unsaved work survives a crash or an accidental close. Runs on a
        timer - never interrupts the user, and any failure is swallowed."""
        try:
            if self.current_page_index is None or not (0 <= self.current_page_index < len(self.pages)):
                return
            page = self.pages[self.current_page_index]
            if page.get("type") != "single" or not self.current_path:
                return
            folder = os.path.dirname(self.current_path)
            if not folder or not os.path.isdir(folder):
                return

            state = self._capture_current_state()
            if state is None:
                return

            if not page.get("_autosave_path"):
                page["_autosave_path"] = self._pick_autosave_path(folder)

            payload = {
                "format": PROCESSED_FILE_MAGIC_V2,
                "app_version": APP_TITLE,
                "autosave": True,
                "pages": [self._page_payload_from_state(page["name"], state)],
            }
            with open(page["_autosave_path"], "w", encoding="utf-8") as f:
                json.dump(payload, f)
        except Exception:
            pass  # autosaving must never interrupt the user's work

    def _schedule_autosave(self):
        self._autosave_seconds_remaining -= 1
        if self._autosave_seconds_remaining <= 0:
            self._autosave_current_page()
            self._autosave_seconds_remaining = AUTOSAVE_INTERVAL_MS // 1000
        if hasattr(self, "autosave_countdown_label"):
            self.autosave_countdown_label.configure(
                text=f"Autosave in {self._autosave_seconds_remaining}s"
            )
        self.after(1000, self._schedule_autosave)

    def _clear_autosave_files(self):
        """Delete every autosave file created so far this session - called
        once the user does a real "Save processed NMR", since it now
        covers everything the autosaves were protecting."""
        for page in self.pages:
            path = page.get("_autosave_path")
            if path:
                try:
                    if os.path.exists(path):
                        os.remove(path)
                except Exception:
                    pass
                page["_autosave_path"] = None

    def save_processed_file(self):
        self._sync_current_page_state()  # make sure the active page's edits are captured too
        if not self.pages:
            messagebox.showinfo("Nothing to save", "Load and process a FID first.")
            return

        if self.current_page_index is not None and 0 <= self.current_page_index < len(self.pages):
            default_source_name = self.pages[self.current_page_index]["name"]
        else:
            default_source_name = self.pages[0]["name"]
        default_name = f"{default_source_name}_processed"

        path = filedialog.asksaveasfilename(
            title="Save processed NMR",
            defaultextension=PROCESSED_FILE_EXT,
            initialfile=default_name + PROCESSED_FILE_EXT,
            filetypes=[("SauceNMR processed file", "*" + PROCESSED_FILE_EXT), ("All files", "*.*")],
        )
        if not path:
            return

        pages_payload = []
        for page in self.pages:
            if page["state"] is None:
                continue  # shouldn't happen (every page gets synced above), but don't crash on it
            pages_payload.append(self._page_payload_from_state(page["name"], page["state"]))

        payload = {
            "format": PROCESSED_FILE_MAGIC_V2,
            "app_version": APP_TITLE,
            "pages": pages_payload,
        }

        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(payload, f)
        except Exception as exc:
            messagebox.showerror("Error saving file", str(exc))
            return

        n = len(pages_payload)
        self._clear_autosave_files()
        self.status.configure(
            text=f"Saved {n} page{'s' if n != 1 else ''} to " + os.path.basename(path)
        )

    def load_processed_file(self, path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f)
        except Exception as exc:
            messagebox.showerror("Error loading file", str(exc))
            return

        fmt = payload.get("format")
        # If we're opening one of our own autosave files, keep updating
        # that exact file going forward instead of picking a fresh slot -
        # a fresh slot (autosave_2) should only ever appear when the
        # ORIGINAL FID is reloaded while an unrecovered autosave_1 is
        # still sitting there, not when the autosave itself is the one
        # being worked on.
        reopened_autosave_path = path if AUTOSAVE_NAME_RE.match(os.path.basename(path)) else None

        if fmt == PROCESSED_FILE_MAGIC_V2:
            pages_payload = payload.get("pages", [])
            if not pages_payload:
                messagebox.showerror("Error loading file", "This file has no saved pages.")
                return
            loaded = 0
            for page_data in pages_payload:
                try:
                    state = self._state_from_page_payload(page_data)
                except Exception as exc:
                    messagebox.showerror(
                        "Error loading file",
                        f"Corrupt or unsupported data in page '{page_data.get('name', '?')}': {exc}",
                    )
                    continue
                page_type = state.get("type", "single")
                name = page_data.get("name") or self._page_name_for_path(state.get("current_path") or path)
                self._add_new_page(name, page_type=page_type)
                self.pages[self.current_page_index]["state"] = state
                if reopened_autosave_path is not None and loaded == 0:
                    self.pages[self.current_page_index]["_autosave_path"] = reopened_autosave_path
                self._show_page(self.pages[self.current_page_index])
                loaded += 1
            self._refresh_pages_list()
            self.status.configure(
                text=f"Reopened {loaded} page{'s' if loaded != 1 else ''} from {os.path.basename(path)}"
            )
            return

        if fmt == PROCESSED_FILE_MAGIC:
            # Legacy single-spectrum file - same per-page field layout, just
            # living at the top level instead of inside a "pages" list.
            try:
                state = self._state_from_page_payload(payload)
            except Exception as exc:
                messagebox.showerror("Error loading file", f"Corrupt or unsupported data: {exc}")
                return
            page_name = self._page_name_for_path(state["current_path"] or path)
            self._add_new_page(page_name)
            if reopened_autosave_path is not None:
                self.pages[self.current_page_index]["_autosave_path"] = reopened_autosave_path
            self._restore_state(state)
            shown_path = self.current_path or "(original file path unknown)"
            self.path_label.configure(text=f"{shown_path}\n[reopened from {os.path.basename(path)}]")
            n_regions = len(state["integration_regions"])
            n_tags = len(state["impurity_tags"])
            self.status.configure(
                text=f"Reopened processed NMR ({n_regions} integration(s), {n_tags} tag(s))"
            )
            return

        messagebox.showerror("Error loading file", "Not a recognized SauceNMR processed file.")

    # --------------------------------------------------------------- library --
    @staticmethod
    def _load_app_config():
        try:
            with open(APP_CONFIG_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    @staticmethod
    def _save_app_config(updates):
        config = SauceNMRApp._load_app_config()
        config.update(updates)
        try:
            os.makedirs(APP_CONFIG_DIR, exist_ok=True)
            with open(APP_CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(config, f)
        except Exception:
            pass  # a failed settings write shouldn't block anything else

    def _choose_library_folder(self):
        path = filedialog.askdirectory(title="Choose (or create) the shared library folder")
        if not path:
            return
        self.library_root.set(path)
        self._save_app_config({"library_root": path})
        self._refresh_library_list()

    def _library_compound_names(self):
        root = self.library_root.get()
        if not root or not os.path.isdir(root):
            return []
        names = []
        try:
            for entry in sorted(os.listdir(root), key=str.lower):
                if os.path.isdir(os.path.join(root, entry)) and not entry.startswith("."):
                    names.append(entry)
        except Exception:
            pass
        return names

    def _find_compound_folder(self, compound_name):
        """Case/whitespace-insensitive lookup so 'Dipp Thiourea' and 'dipp
        thiourea' land in the same folder instead of silently forking."""
        root = self.library_root.get()
        if not root or not os.path.isdir(root):
            return None
        target = compound_name.strip().lower()
        for entry in self._library_compound_names():
            if entry.strip().lower() == target:
                return os.path.join(root, entry)
        return None

    @staticmethod
    def _sanitize_filename(name):
        return re.sub(r'[\\/*?:"<>|]', "_", name).strip() or "untitled"

    def _validate_notebook_id(self, text):
        m = NOTEBOOK_ID_RE.match(text.strip())
        if not m:
            return None
        entry_num = int(m.group(3))
        if not (1 <= entry_num <= 155):
            return None
        return text.strip()

    def _find_compound_gold_star_path(self, compound_folder):
        """The one current gold-star file for a compound. Checks the flat
        layout first (a .saucenmr directly in the compound folder), then
        falls back to the old gold_star/ sub-folder so libraries created
        before this got simplified still show their existing gold stars."""
        try:
            direct = sorted(
                (f for f in os.listdir(compound_folder) if f.endswith(PROCESSED_FILE_EXT)),
                key=lambda f: os.path.getmtime(os.path.join(compound_folder, f)), reverse=True,
            )
        except Exception:
            direct = []
        if direct:
            return os.path.join(compound_folder, direct[0])
        legacy_dir = os.path.join(compound_folder, LIBRARY_GOLD_STAR_DIR)
        if os.path.isdir(legacy_dir):
            try:
                legacy_files = sorted(f for f in os.listdir(legacy_dir) if f.endswith(PROCESSED_FILE_EXT))
            except Exception:
                legacy_files = []
            if legacy_files:
                return os.path.join(legacy_dir, legacy_files[0])
        return None

    def _open_save_to_library_dialog(self):
        root = self.library_root.get()
        if not root or not os.path.isdir(root):
            messagebox.showinfo(
                "Choose a library folder first",
                "Pick a shared library folder in the Library tab before saving to it.",
            )
            return
        self._sync_current_page_state()
        if self.current_page_index is None or not self.pages:
            messagebox.showinfo("Nothing to save", "Load and process a spectrum first.")
            return

        win = ctk.CTkToplevel(self)
        win.title("Save to Library")
        win.configure(fg_color=PANEL_COLOR)
        win.geometry("420x320")
        # transient, not "-topmost": topmost pins the window above every
        # other application on the desktop even after you alt-tab away.
        win.transient(self)
        win.lift()

        ctk.CTkLabel(
            win, text="Lab notebook ID", font=ctk.CTkFont(size=12), text_color="#c7c9cf",
        ).pack(anchor="w", padx=18, pady=(18, 2))
        notebook_var = tk.StringVar(value="")
        ctk.CTkEntry(
            win, textvariable=notebook_var, height=32, corner_radius=8, placeholder_text="e.g. MS-1-33",
        ).pack(fill="x", padx=18)

        ctk.CTkLabel(
            win, text="Compound name", font=ctk.CTkFont(size=12), text_color="#c7c9cf",
        ).pack(anchor="w", padx=18, pady=(14, 2))
        compound_var = tk.StringVar(value="")
        compound_combo = ctk.CTkComboBox(
            win, values=self._library_compound_names(), variable=compound_var,
            height=32, corner_radius=8, button_color=ACCENT,
        )
        compound_combo.pack(fill="x", padx=18)

        ctk.CTkLabel(
            win, text="This becomes the gold star for this compound - replacing "
                       "whatever was there before, if anything.",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=380, justify="left",
        ).pack(anchor="w", padx=18, pady=(14, 0))

        error_label = ctk.CTkLabel(win, text="", font=ctk.CTkFont(size=11), text_color="#ff6b6b",
                                    wraplength=380, justify="left", anchor="w")
        error_label.pack(fill="x", padx=18, pady=(10, 0))

        def confirm():
            notebook_id = self._validate_notebook_id(notebook_var.get())
            if notebook_id is None:
                error_label.configure(
                    text="Notebook ID should look like MS-1-33 (2-3 letter initials, "
                         "notebook number, entry 1-155)."
                )
                return
            compound_name = compound_var.get().strip()
            if not compound_name:
                error_label.configure(text="Enter a compound name.")
                return
            win.destroy()
            self._save_current_page_to_library(notebook_id, compound_name)

        ctk.CTkButton(win, text="Save", command=confirm, height=34, corner_radius=8,
                      fg_color=ACCENT, hover_color="#2f8fe0").pack(fill="x", padx=18, pady=(16, 6))
        ctk.CTkButton(win, text="Cancel", command=win.destroy, height=32, corner_radius=8,
                      fg_color="transparent", hover_color="#22252b", text_color=TEXT_MUTED,
                      ).pack(fill="x", padx=18)

    def _save_current_page_to_library(self, notebook_id, compound_name):
        self._sync_current_page_state()
        root = self.library_root.get()
        compound_folder = self._find_compound_folder(compound_name) or os.path.join(
            root, self._sanitize_filename(compound_name)
        )
        try:
            os.makedirs(compound_folder, exist_ok=True)
        except Exception as exc:
            messagebox.showerror("Error", f"Couldn't create the compound folder:\n{exc}")
            return

        filename = f"{self._sanitize_filename(notebook_id)} {self._sanitize_filename(compound_name)}{PROCESSED_FILE_EXT}"
        target_path = os.path.join(compound_folder, filename)

        existing_path = self._find_compound_gold_star_path(compound_folder)
        if existing_path and os.path.abspath(existing_path) != os.path.abspath(target_path):
            proceed = messagebox.askyesno(
                "Replace the current gold star?",
                f"{compound_name} already has a gold star NMR ({os.path.basename(existing_path)}).\n\n"
                "Replace it with this one? The old file will be deleted.",
            )
            if not proceed:
                return
            try:
                os.remove(existing_path)
            except Exception as exc:
                messagebox.showerror("Error", f"Couldn't remove the old gold star:\n{exc}")
                return
        elif os.path.exists(target_path):
            if not messagebox.askyesno("File already exists", f"{filename} already exists here. Overwrite it?"):
                return

        state = self.pages[self.current_page_index]["state"]
        page_payload = self._page_payload_from_state(f"{notebook_id} {compound_name}", state)
        payload = {"format": PROCESSED_FILE_MAGIC_V2, "app_version": APP_TITLE, "pages": [page_payload]}
        try:
            with open(target_path, "w", encoding="utf-8") as f:
                json.dump(payload, f)
        except Exception as exc:
            messagebox.showerror("Error saving to library", str(exc))
            return

        self.status.configure(text=f"Saved to library: {compound_name} ({notebook_id})")
        self._refresh_library_list()

    def _build_library_tab(self, parent):
        frame = ctk.CTkFrame(parent, fg_color="transparent")

        self.library_root_label = ctk.CTkLabel(
            frame, text="", font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
            wraplength=260, justify="left", anchor="w",
        )
        self.library_root_label.pack(fill="x", pady=(0, 6))
        ctk.CTkButton(
            frame, text="Choose/change library folder...", command=self._choose_library_folder,
            height=32, corner_radius=8, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(fill="x", pady=(0, 6))
        ctk.CTkButton(
            frame, text="Save current page to Library...", command=self._open_save_to_library_dialog,
            height=34, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        ).pack(fill="x", pady=(0, 12))

        ctk.CTkLabel(frame, text="COMPARE TO CURRENT PAGE", font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=TEXT_MUTED).pack(anchor="w", pady=(0, 4))
        ctk.CTkLabel(
            frame, text="Check 1+ entries below - they'll be compared against whatever's currently open:",
            font=ctk.CTkFont(size=11), text_color=TEXT_MUTED, wraplength=250, justify="left",
        ).pack(anchor="w", pady=(0, 4))
        compare_row = ctk.CTkFrame(frame, fg_color="transparent")
        compare_row.pack(fill="x", pady=(0, 6))
        ctk.CTkButton(
            compare_row, text="Overlay vs. current", command=lambda: self._library_compare_checked(stacked=False),
            height=32, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        ).pack(side="left", fill="x", expand=True, padx=(0, 6))
        ctk.CTkButton(
            compare_row, text="Stack vs. current", command=lambda: self._library_compare_checked(stacked=True),
            height=32, corner_radius=8, fg_color=ACCENT, hover_color="#2f8fe0",
        ).pack(side="left", fill="x", expand=True)
        ctk.CTkButton(
            frame, text="Auto-integrate vs. checked gold star", command=self._library_auto_integrate_checked,
            height=32, corner_radius=8, fg_color=PANEL_COLOR, hover_color="#22252b",
            text_color="#d7d9de", border_width=1, border_color=PLOT_GRID_COLOR,
        ).pack(fill="x", pady=(0, 12))

        ctk.CTkLabel(frame, text="Search compounds", font=ctk.CTkFont(size=12),
                     text_color="#c7c9cf").pack(anchor="w", pady=(0, 2))
        ctk.CTkEntry(frame, textvariable=self.library_search_var, height=32, corner_radius=8).pack(
            fill="x", pady=(0, 10)
        )
        self.library_search_var.trace_add("write", lambda *a: self._filter_library_list())

        self.library_list_frame = ctk.CTkScrollableFrame(frame, fg_color=PANEL_COLOR, height=380)
        self.library_list_frame.pack(fill="both", expand=True)

        self._refresh_library_list()
        return frame

    def _library_compare_checked(self, stacked):
        """Compares the CURRENT page against whatever's checked below -
        that's the actual point (is my routine NMR a match for the gold
        star?), not comparing library entries to each other."""
        checked_paths = [p for p, var in self._library_check_vars.items() if var.get()]
        if not checked_paths:
            messagebox.showinfo(
                "Check an entry",
                "Check 1 or more library entries below - they'll be compared against the current page.",
            )
            return
        self._sync_current_page_state()
        if self.current_page_index is None or not self.pages:
            messagebox.showinfo("Nothing to compare", "Load and process a spectrum first.")
            return

        self.overlay_selected = {self.current_page_index}  # always compare against what's open now
        loaded_indices = []  # pages loaded just for this comparison - closed again once it's built
        for path in checked_paths:
            if not os.path.exists(path):
                continue
            before = len(self.pages)
            self.load_processed_file(path)
            for i in range(before, len(self.pages)):
                self.overlay_selected.add(i)
                loaded_indices.append(i)
                # Tag it so the overlay/stack legend shows which series is
                # the gold star at a glance - the page name flows straight
                # into the series name used for the legend label.
                name = self.pages[i]["name"]
                if not name.startswith("\u2605"):
                    self.pages[i]["name"] = "\u2605 " + name
        if len(self.overlay_selected) < 2:
            messagebox.showinfo("Nothing to compare", "Couldn't load enough of the checked entries.")
            return
        if stacked:
            self._show_stacked()
        else:
            self._show_overlay()
        for var in self._library_check_vars.values():
            var.set(False)

        # These pages only existed to build the comparison - keep the
        # Pages list to just the original current page and the new
        # overlay/stack page, not extra clutter. Close highest-index
        # first so earlier indices in the list stay valid as we go.
        overlay_msg = self.status.cget("text")
        for i in sorted(loaded_indices, reverse=True):
            if 0 <= i < len(self.pages):
                self._close_page(i)
        self.status.configure(text=overlay_msg)

    @staticmethod
    def _read_library_entry_integration_regions(path):
        """Reads a saved library entry's integration windows directly from
        its JSON - no need to actually load/plot it as a page just to see
        where its integrations were."""
        try:
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            pages = payload.get("pages", [])
            if not pages:
                return None
            return pages[0].get("integration_regions", [])
        except Exception:
            return None

    def _auto_add_integration_from_window(self, lo, hi):
        """Direct integration creation for auto-analysis. The gold star's
        ppm window is applied exactly as-is - no auto-adjustment/snapping,
        any fine-tuning for peak drift is on you, by design (drag the
        handles same as any other integration). The resulting H-count is
        freshly computed from THIS spectrum's own data, scaled against
        whatever reference you've already established on it - comparing
        that number against the gold star's is the actual point."""
        x = self.freq_axis
        mask = (x >= lo) & (x <= hi)
        if not np.any(mask):
            return None
        x_sub = x[mask]
        y_sub = self.spectrum_data.real[mask]
        raw_area = abs(float(_trapz(y_sub, x_sub)))
        if not self.integration_reference_area:
            return None
        display_value = raw_area / self.integration_reference_area
        self._add_integration_region(lo, hi, display_value, raw_area, is_reference=False)
        return self.integration_regions[-1]

    def _library_auto_integrate_checked(self):
        """Applies a gold star's integration windows to the current page -
        for checking whether a routine NMR actually matches the reference,
        window by window. Prerequisites: the current spectrum must already
        be ppm-referenced to the internal standard (L), and must already
        have its OWN 1H reference integration picked and assigned (I, then
        set the true H count) - that's what every other window's H-count
        gets scaled against, and it has to come from THIS spectrum, not be
        copied from the gold star's (different concentration, different
        receiver gain - the absolute numbers don't transfer, only the
        window positions and multiplicity assignments do)."""
        checked_paths = [p for p, var in self._library_check_vars.items() if var.get()]
        if len(checked_paths) != 1:
            messagebox.showinfo(
                "Check exactly one gold star",
                "Check exactly one gold-star entry below to auto-integrate against.",
            )
            return
        self._sync_current_page_state()
        if self.current_page_index is None or self.spectrum_data is None:
            messagebox.showinfo("Nothing to analyze", "Load and process a spectrum first.")
            return
        if self.reference_info is None:
            messagebox.showinfo(
                "Reference this spectrum first",
                "Auto-integrate needs this spectrum already referenced to the internal "
                "standard (press L), so its ppm axis lines up with the gold star's.",
            )
            return
        if not any(r.get("is_reference") for r in self.integration_regions):
            messagebox.showinfo(
                "Pick your reference integration first",
                "Integrate and assign this spectrum's own 1H reference peak first "
                "(I, then set its true H count in the edit table) - auto-integrate scales "
                "every other window against that, the same way any integration always does.",
            )
            return

        gold_regions = self._read_library_entry_integration_regions(checked_paths[0])
        if not gold_regions:
            messagebox.showerror("Error", "Couldn't read integration windows from that library entry.")
            return

        added = 0
        for snap in gold_regions:
            if snap.get("is_reference"):
                continue  # re-picked on this spectrum, never copied - see docstring
            region = self._auto_add_integration_from_window(snap["xmin"], snap["xmax"])
            if region is None:
                continue
            label = snap.get("multiplicity")
            if label:
                self._set_region_multiplicity(region, label, j_hz=snap.get("j_hz"), rep_ppm=snap.get("rep_ppm"))
            added += 1

        for var in self._library_check_vars.values():
            var.set(False)
        self.canvas.draw_idle()
        self.status.configure(
            text=f"Auto-integrated {added} window(s) from the gold star - fine-tune boundaries as needed"
        )

    def _refresh_library_list(self):
        """Full rescan: call this whenever the folder's contents may have
        changed (a new folder chosen, first opening this tab, after saving
        a compound to the library). The actual directory walk runs on a
        background thread (_scan_library_folder) since it can be slow - a
        shared library on a cloud-synced folder like Dropbox can turn every
        listdir/isdir/getmtime call into a network round-trip - so this
        returns immediately and the list fills in once the scan finishes,
        instead of the window sitting there waiting on it."""
        if not hasattr(self, "library_list_frame"):
            return
        root = self.library_root.get()
        self.library_root_label.configure(
            text=("Library: " + root) if root else "No library folder chosen yet."
        )
        for child in self.library_list_frame.winfo_children():
            child.destroy()

        if not root or not os.path.isdir(root):
            self._library_scan_cache = None
            ctk.CTkLabel(
                self.library_list_frame, text="Choose a library folder above to get started.",
                font=ctk.CTkFont(size=12), text_color=TEXT_MUTED, wraplength=250,
            ).pack(anchor="w", padx=8, pady=8)
            return

        ctk.CTkLabel(
            self.library_list_frame, text="Loading library\u2026",
            font=ctk.CTkFont(size=12), text_color=TEXT_MUTED,
        ).pack(anchor="w", padx=8, pady=8)

        self._library_scan_token += 1
        token = self._library_scan_token

        def worker(root_path=root, token=token):
            entries = self._scan_library_folder(root_path)
            # Hand the result back through a queue that the UI thread
            # polls (see _poll_library_scan). Calling into Tk - even
            # self.after - directly from a worker thread is not reliably
            # safe depending on how Tcl was built, so nothing here
            # touches the widget tree.
            self._library_scan_queue.put((token, root_path, entries))

        threading.Thread(target=worker, daemon=True).start()
        self.after(60, self._poll_library_scan)

    def _poll_library_scan(self):
        """Drain any finished background scans on the UI thread. Only runs
        while a scan is actually outstanding - it reschedules itself until
        a result arrives, rather than polling forever."""
        delivered = False
        try:
            while True:
                token, root_path, entries = self._library_scan_queue.get_nowait()
                delivered = True
                self._apply_library_scan_result(token, root_path, entries)
        except queue.Empty:
            pass
        if not delivered:
            self.after(60, self._poll_library_scan)

    def _scan_library_folder(self, root_path):
        """The actual directory walk: [(compound_name, gold_star_path_or_
        None), ...] for every compound folder under root_path. Pure os.*
        calls, no Tk access at all - safe to run off the main thread."""
        try:
            names = sorted(
                (e for e in os.listdir(root_path)
                 if os.path.isdir(os.path.join(root_path, e)) and not e.startswith(".")),
                key=str.lower,
            )
        except Exception:
            return []
        entries = []
        for name in names:
            gold_path = self._find_compound_gold_star_path(os.path.join(root_path, name))
            entries.append((name, gold_path))
        return entries

    def _apply_library_scan_result(self, token, scanned_root, entries):
        # Discard a stale scan - the folder may have been changed (or this
        # tab rebuilt) while it was still running in the background.
        if token != self._library_scan_token:
            return
        if not hasattr(self, "library_list_frame") or self.library_root.get() != scanned_root:
            return
        self._library_scan_cache = (scanned_root, entries)
        self._render_library_list(entries)

    def _render_library_list(self, entries):
        query = self.library_search_var.get().strip().lower()
        for child in self.library_list_frame.winfo_children():
            child.destroy()
        matches = [(name, gold) for name, gold in entries if query in name.lower()]
        if not matches:
            ctk.CTkLabel(
                self.library_list_frame,
                text="No compounds yet - save your first one above." if not query else "No matches.",
                font=ctk.CTkFont(size=12), text_color=TEXT_MUTED, wraplength=250,
            ).pack(anchor="w", padx=8, pady=8)
            return
        for name, gold_path in matches:
            self._build_library_compound_row(self.library_list_frame, name, gold_path)

    def _filter_library_list(self):
        """Bound to the search box - re-filters the list already fetched
        by _refresh_library_list without touching the filesystem again,
        so searching stays instant even on a slow/cloud-synced library."""
        if not hasattr(self, "library_list_frame"):
            return
        cache = self._library_scan_cache
        if cache is None or cache[0] != self.library_root.get():
            self._refresh_library_list()  # nothing scanned yet for this folder
            return
        self._render_library_list(cache[1])

    def _library_get_check_var(self, path):
        var = self._library_check_vars.get(path)
        if var is None:
            var = tk.BooleanVar(value=False)
            self._library_check_vars[path] = var
        return var

    def _build_library_compound_row(self, parent, compound_name, gold_path):
        card = ctk.CTkFrame(parent, fg_color=BG_COLOR, corner_radius=8)
        card.pack(fill="x", padx=6, pady=5)

        header = ctk.CTkFrame(card, fg_color="transparent")
        header.pack(fill="x", padx=10, pady=(8, 4))
        ctk.CTkLabel(
            header, text=compound_name, font=ctk.CTkFont(size=13, weight="bold"), anchor="w",
        ).pack(side="left")

        if gold_path:
            gold_row = ctk.CTkFrame(card, fg_color="transparent")
            gold_row.pack(fill="x", padx=10, pady=(0, 8))
            ctk.CTkCheckBox(
                gold_row, text="", variable=self._library_get_check_var(gold_path),
                width=16, checkbox_width=16, checkbox_height=16,
            ).pack(side="left", padx=(0, 6))
            ctk.CTkLabel(
                gold_row, text="\u2605 " + os.path.basename(gold_path), font=ctk.CTkFont(size=11),
                text_color="#ffd54a", anchor="w",
            ).pack(side="left", fill="x", expand=True)
            ctk.CTkButton(
                gold_row, text="Load", width=54, height=24, corner_radius=6, font=ctk.CTkFont(size=11),
                command=lambda p=gold_path: self.load_processed_file(p),
            ).pack(side="right")
        else:
            ctk.CTkLabel(
                card, text="No gold star yet", font=ctk.CTkFont(size=11), text_color=TEXT_MUTED,
            ).pack(anchor="w", padx=10, pady=(0, 8))

    def _refresh_corrected_fid(self):
        """Recompute self.complex_data from the raw FID, applying digital
        filter (group delay) removal if a delay value is set."""
        if self._raw_fid is None:
            self.complex_data = None
            return
        grpdly_val = self._parse_float(self.grpdly.get(), default=0.0) or 0.0
        if grpdly_val > 0:
            self.complex_data = self._remove_digital_filter(self._raw_fid, grpdly_val)
        else:
            self.complex_data = self._raw_fid.copy()

    @staticmethod
    def _remove_digital_filter(fid, grpdly):
        """Strip a Bruker digital-filter group delay from a raw FID using an
        FFT-based fractional circular shift (exact for a band-limited,
        periodic signal - the standard method also used by nmrglue etc.).
        `grpdly` is the delay in points, as stored in acqus (GRPDLY)."""
        n = len(fid)
        spectrum = np.fft.fft(fid)
        freqs = np.fft.fftfreq(n)
        shift = np.exp(2j * np.pi * freqs * grpdly)
        return np.fft.ifft(spectrum * shift)

    def _autodetect_acqus_params(self, fid_path):
        """Look for a Bruker acqus/acqu file next to the fid file and pull out
        SW_h (spectral width, Hz), O1 (transmitter offset, Hz), SFO1
        (spectrometer frequency, MHz), and GRPDLY (digital filter group
        delay, in points) so the spectrum can be shown in ppm and the
        digital-filter delay can be stripped from the FID automatically."""
        directory = os.path.dirname(fid_path)
        for name in ("acqus", "acqu", "ACQUS", "ACQU"):
            candidate = os.path.join(directory, name)
            if os.path.isfile(candidate):
                params = self._parse_acqus_file(candidate)
                if params:
                    return params
        return None

    def _parse_acqus_file(self, acqus_path):
        try:
            with open(acqus_path, "r", errors="ignore") as f:
                text = f.read()
        except Exception:
            return None

        def extract(pattern):
            m = re.search(pattern, text)
            if not m:
                return None
            try:
                return float(m.group(1))
            except ValueError:
                return None

        sw_hz = extract(r"##\$SW_h=\s*([\-0-9.eE]+)")
        o1_hz = extract(r"##\$O1=\s*([\-0-9.eE]+)")
        sfo1_mhz = extract(r"##\$SFO1=\s*([\-0-9.eE]+)")
        grpdly = extract(r"##\$GRPDLY=\s*([\-0-9.eE]+)")

        result = {}
        if sw_hz and sfo1_mhz:
            result.update({"sw_hz": sw_hz, "o1_hz": o1_hz or 0.0, "sfo1_mhz": sfo1_mhz})
        if grpdly and grpdly > 0:
            result["grpdly"] = grpdly

        return result if result else None

    def _read_fid(self, path):
        raw = open(path, "rb").read()

        endian = BYTE_ORDER_OPTIONS[self.byte_order_name.get()]
        base_dtype = DTYPE_OPTIONS[self.dtype_name.get()]
        dtype = np.dtype(endian + base_dtype)

        itemsize = dtype.itemsize
        n_values = len(raw) // itemsize
        remainder = len(raw) % itemsize
        if n_values == 0:
            raise ValueError("File is too small / empty for the selected data type.")
        if remainder != 0:
            raw = raw[: n_values * itemsize]

        values = np.frombuffer(raw, dtype=dtype)
        if len(values) % 2 != 0:
            values = values[:-1]

        values = values.astype(np.float64)
        real = values[0::2]
        imag = values[1::2]
        return real + 1j * imag

    def _plot_fid(self):
        data = self.complex_data
        x = np.arange(len(data))
        colors = self._theme_colors()

        self.ax.clear()
        self._style_axis(self.ax)
        self.ax.plot(x, data.real, color=colors["trace"], linewidth=0.8, label="Real")
        self.ax.plot(x, data.imag, color="#ff6b6b", linewidth=0.8, alpha=0.75, label="Imaginary")
        self.ax.set_xlabel("Point index")
        self._set_plot_title_and_ylabel("FID (time domain)", "Intensity")
        legend = self.ax.legend(facecolor=colors["bg"], edgecolor=colors["text"], labelcolor=colors["text"])

        self._apply_figure_layout()
        self.canvas.draw()
        self.full_xlim = self.ax.get_xlim()
        self.full_ylim = self.ax.get_ylim()
        self._init_selectors()

    def _parse_float(self, s, default=None):
        s = s.strip()
        if s == "":
            return default
        try:
            return float(s)
        except ValueError:
            return default

    def _build_unphased_spectrum(self):
        """Zero-fill + apodize + FFT the current FID, without applying any
        phase correction. Returns (spectrum, n_zf, zero_fill_factor, sw_hz,
        o1_hz, sf_mhz) or None if there's no data loaded."""
        if self.complex_data is None:
            return None

        try:
            zf_index = ZERO_FILL_OPTIONS.index(self.zero_fill_name.get())
        except ValueError:
            zf_index = 0
        zero_fill_factor = [1, 2, 4, 8][zf_index]

        lb_hz = self._parse_float(self.line_broadening.get(), default=0.0) or 0.0
        sw_hz = self._parse_float(self.spectral_width.get(), default=None)
        o1_hz = self._parse_float(self.transmitter_offset.get(), default=0.0) or 0.0
        sf_mhz = self._parse_float(self.spectrometer_freq.get(), default=None)

        fid = self.complex_data.copy()
        n = len(fid)

        if lb_hz and sw_hz:
            dwell = 1.0 / sw_hz
            t = np.arange(n) * dwell
            window = np.exp(-np.pi * lb_hz * t)
            fid = fid * window
        elif lb_hz and not sw_hz:
            self.status.configure(text="Line broadening ignored: enter Spectral Width (Hz) to use it.")

        n_zf = n * zero_fill_factor
        spectrum = np.fft.fftshift(np.fft.fft(fid, n=n_zf))
        return spectrum, n_zf, zero_fill_factor, sw_hz, o1_hz, sf_mhz

    def _refresh_unphased_cache(self):
        """Rebuild the unphased spectrum + frequency axis, caching the
        unphased spectrum so phase changes afterward are cheap (no need to
        redo zero-fill/apodization/FFT for every slider tick)."""
        built = self._build_unphased_spectrum()
        if built is None:
            return None
        spectrum, n_zf, zero_fill_factor, sw_hz, o1_hz, sf_mhz = built
        self._cached_spectrum_raw = spectrum

        if sw_hz:
            freq_hz = np.linspace(-sw_hz / 2, sw_hz / 2, n_zf, endpoint=False) + o1_hz
            if sf_mhz:
                self.freq_axis = freq_hz / sf_mhz + self.ppm_reference_offset
                self.freq_unit = "ppm"
            else:
                self.freq_axis = freq_hz
                self.freq_unit = "Hz"
        else:
            self.freq_axis = np.arange(n_zf) - n_zf // 2
            self.freq_unit = "index"

        return built

    def _live_reprocess(self):
        """Called from a trace on a processing field (zero-fill, line
        broadening, calibration numbers) - reprocesses immediately if a
        FID is already loaded, silently does nothing otherwise (e.g. while
        the field is still being populated during startup)."""
        if self._suspend_live_reprocess:
            return  # a bulk restore is repopulating the fields; it reprocesses once at the end
        if self._raw_fid is not None:
            self.run_fft()

    def run_fft(self):
        self._refresh_corrected_fid()
        built = self._refresh_unphased_cache()
        if built is None:
            return  # nothing loaded yet - live-triggered fields fire before that too, so stay quiet
        n_zf, zero_fill_factor = built[1], built[2]

        phase_deg = self._parse_float(self.phase_deg.get(), default=0.0) or 0.0
        self._set_view_switch("Spectrum")
        self.view_mode = "spectrum"
        self._plot_spectrum(phase_deg)
        if self.reference_info is not None:
            self._tag_solvent_peak(*self.reference_info)
        self.status.configure(
            text="FFT done - " + str(n_zf) + " points, zero-fill " + str(zero_fill_factor)
            + "x, axis in " + self.freq_unit
        )

    def auto_phase_correction(self):
        self._refresh_corrected_fid()
        built = self._refresh_unphased_cache()
        if built is None:
            messagebox.showinfo("No data", "Load a FID file first.")
            return

        best_phase = self._search_best_phase(self._cached_spectrum_raw)
        best_phase_wrapped = best_phase - 360.0 if best_phase > 180.0 else best_phase
        self._sync_phase_controls(best_phase_wrapped)
        self.status.configure(text=f"Auto-phase applied: {best_phase_wrapped:.2f} deg (fine-tune manually if needed)")

    @staticmethod
    def _phase_score(real_part):
        # Simplified entropy-based phasing objective (ACME-inspired):
        # a well-phased absorption spectrum has a smooth, mostly-positive
        # real part. We penalize negative excursions and reward a low-
        # entropy (peaky, not noisy) derivative.
        deriv = np.abs(np.diff(real_part))
        total = deriv.sum()
        if total <= 0:
            return 1e10
        p = deriv / total
        p = p[p > 1e-12]
        entropy = -np.sum(p * np.log(p))

        neg = real_part[real_part < 0]
        neg_penalty = float(np.sum(neg ** 2)) / (float(np.sum(real_part ** 2)) + 1e-12)

        return entropy + 1000.0 * neg_penalty

    def _search_best_phase(self, spectrum):
        # Re(z * e^-i*theta) == Re(z)*cos(theta) + Im(z)*sin(theta) - avoids
        # rebuilding a complex exponential and doing a full complex multiply
        # on every candidate angle, which is the hot loop for a big spectrum.
        spec_real = spectrum.real
        spec_imag = spectrum.imag

        def score_at(deg):
            theta = np.deg2rad(deg)
            rotated_real = spec_real * np.cos(theta) + spec_imag * np.sin(theta)
            return self._phase_score(rotated_real)

        best_phase = 0.0
        best_score = np.inf
        for deg in np.arange(0.0, 360.0, 2.0):
            score = score_at(deg)
            if score < best_score:
                best_score = score
                best_phase = deg

        # Refine around the coarse best angle
        for deg in np.arange(best_phase - 2.0, best_phase + 2.0, 0.05):
            score = score_at(deg)
            if score < best_score:
                best_score = score
                best_phase = deg

        return best_phase % 360.0

    # -------------------------------------------------------- live phase --
    def _on_phase_slider_drag(self, value):
        self._sync_phase_controls(float(value), update_text=True)

    def _on_phase_text_change(self, *args):
        if self._updating_phase:
            return
        if self._suspend_live_reprocess:
            return  # bulk restore: the phase is applied by the run_fft() at the end
        val = self._parse_float(self.phase_deg.get(), default=None)
        if val is None:
            return
        self._sync_phase_controls(val, update_text=False)

    def _sync_phase_controls(self, value, update_text=True):
        self._updating_phase = True
        if update_text:
            self.phase_deg.set(f"{value:.1f}")
        try:
            self.phase_slider.set(max(-180.0, min(180.0, value)))
        except Exception:
            pass
        self._updating_phase = False
        self._apply_phase_and_plot(value)

    def _apply_phase_and_plot(self, phase_deg_value):
        if self._cached_spectrum_raw is None:
            return
        rotated = self._cached_spectrum_raw * np.exp(-1j * np.deg2rad(phase_deg_value))
        baseline = self._baseline_curve(self.freq_axis)
        if baseline is not None:
            rotated = (rotated.real - baseline) + 1j * rotated.imag
        self.spectrum_data = rotated

        if self.spectrum_line is not None and self.view_mode == "spectrum":
            # Fast path: just update the line's y-data, keep current zoom/limits.
            # Use a forced synchronous draw (not draw_idle) - during a fast
            # slider drag, Tkinter can fire many <B1-Motion> events back to
            # back, and draw_idle()'s deferred redraw can get starved until
            # the drag stops, making updates look laggy/non-live.
            #
            # IMPORTANT: plot the REAL part (absorption mode), not the
            # magnitude. |z * e^(i*theta)| == |z| for any theta - magnitude
            # is mathematically phase-invariant, so a magnitude-mode plot
            # can never visibly respond to phase correction. The real part
            # is the only representation phase actually affects.
            self.spectrum_line.set_ydata(rotated.real)
            self.canvas.draw()
        # If the spectrum isn't currently on screen, spectrum_data is still
        # updated silently and will render fully next time _plot_spectrum runs.

    def _plot_spectrum(self, phase_deg_value=None):
        if phase_deg_value is None:
            phase_deg_value = self._parse_float(self.phase_deg.get(), default=0.0) or 0.0

        spectrum = self._cached_spectrum_raw * np.exp(-1j * np.deg2rad(phase_deg_value))
        x = self.freq_axis
        baseline = self._baseline_curve(x)
        if baseline is not None:
            spectrum = (spectrum.real - baseline) + 1j * spectrum.imag
        self.spectrum_data = spectrum

        # Snapshot annotations BEFORE clearing the axis - ax.clear() destroys
        # their underlying artists, but the data itself (region bounds,
        # integration values, multiplicity, impurity ppms/names) is still
        # valid and gets recreated on the fresh axis below. This is what
        # keeps integrations/tags from vanishing every time the spectrum is
        # reprocessed (new phase, zero-fill, or solvent reference).
        integration_snapshot = [self._region_snapshot(r) for r in self.integration_regions]
        impurity_snapshot = [(tag["ppm"], tag["name"], tag["origin_ppm"]) for tag in self.impurity_tags]

        self.ax.clear()
        self.pick_coord_text = None
        self.pick_hover_line = None
        self.detection_hover_artists = []
        self.impurity_tags = []
        self.solvent_tag = None
        self.integration_regions = []
        self.integration_drag = None
        self.active_drag_highlight = None
        # In-progress (not-yet-applied) baseline picks don't survive a fresh
        # replot - their markers belong to the axis we just cleared. Once a
        # correction is actually applied it lives in baseline_correction_points
        # instead, which does get reapplied above.
        self.baseline_points = []
        self.baseline_preview_line = None
        self.baseline_drag = None
        if hasattr(self, "baseline_count_label"):
            self.baseline_count_label.configure(text="0 point(s) picked")
        if hasattr(self, "apply_baseline_button"):
            self.apply_baseline_button.configure(state="disabled")
        self._style_axis(self.ax)
        self.spectrum_line, = self.ax.plot(x, spectrum.real, color=self._theme_colors()["trace"], linewidth=0.9)
        xlabel = {
            "ppm": "Chemical shift (ppm)",
            "Hz": "Frequency (Hz)",
            "index": "Frequency (relative index)",
        }[self.freq_unit]
        self.ax.set_xlabel(xlabel)
        self._set_plot_title_and_ylabel(self.plot_title_text.get() or "Spectrum", "Intensity")

        if self.reverse_axis.get():
            self.ax.set_xlim(x[-1], x[0])
        else:
            self.ax.set_xlim(x[0], x[-1])

        # Force the y-axis to auto-scale to the data without a full canvas
        # render (a full draw() is the expensive part of a replot - we only
        # need the resulting view limits here, not a rendered frame).
        self.ax.relim()
        self.ax.autoscale_view(scalex=False, scaley=True)
        self.full_xlim = self.ax.get_xlim()
        self.full_ylim = self.ax.get_ylim()

        # Immediately show the same "nice" baseline-margined view that
        # scrolling produces, instead of the raw full extent (which can be
        # dominated by a deep negative dispersion dip on some peak). This
        # avoids a jarring jump the first time the user scrolls.
        natural_top = float(spectrum.real.max())
        padded_top = natural_top * 1.05 if natural_top > 0 else natural_top + 1.0
        self.default_ylim = self._margined_ylim(padded_top)
        self.ax.set_ylim(*self.default_ylim)

        # Recreate whatever integrations/impurity tags existed before this
        # replot, now that the new axis has real xlim/ylim to draw against.
        for snap in integration_snapshot:
            self._restore_integration_region(snap, record_undo=False)
        for ppm, name, origin_ppm in impurity_snapshot:
            self._tag_impurity([ppm], name, origins=[origin_ppm])

        self._apply_figure_layout()
        self.canvas.draw()

        self._init_selectors()


def main():
    app = SauceNMRApp()
    app.mainloop()


if __name__ == "__main__":
    main()
