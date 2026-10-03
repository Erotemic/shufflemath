"""Semantic colors shared by every shufflemath Manim scene.

The point of the palette is not decoration: a color always means the same
mathematical role throughout the talk.

LOCAL     finite local riffle / mash randomization
EXCHANGE  cards crossing the working-set boundary
UNIFORM   the target uniform distribution / certified success
ERROR     residual nonuniformity / total variation
COST      physical time, effort, or optimization objective
ORACLE    perfect local randomization used by idealized prior work
EMPIRICAL measured or human-behavior parameters

Neutral grays are presentation-only and never carry a mathematical meaning.
Set ``SHUFFLEVIZ_THEME=light`` for the printable light variant.
"""
from __future__ import annotations

import os

DARK = {
    "BG": "#0E1319",
    "FG": "#ECEFF3",
    "MUTED": "#8B95A3",
    "FAINT": "#2A323D",
    "PANEL": "#161D26",
    "LOCAL": "#5AA9FF",
    "EXCHANGE": "#FFC24B",
    "UNIFORM": "#4ADE80",
    "ERROR": "#FF5CA8",
    "COST": "#B69CFF",
    "ORACLE": "#31C7D9",
    "EMPIRICAL": "#F26B3A",
    "REFUTED": "#E8484E",
}

LIGHT = {
    "BG": "#FBFBF8",
    "FG": "#1B1F24",
    "MUTED": "#6B7280",
    "FAINT": "#D5D9DE",
    "PANEL": "#EEF0F2",
    "LOCAL": "#1F6FD1",
    "EXCHANGE": "#C77C00",
    "UNIFORM": "#138A4B",
    "ERROR": "#D12A7B",
    "COST": "#6E4BD8",
    "ORACLE": "#007C91",
    "EMPIRICAL": "#D9541E",
    "REFUTED": "#C62828",
}

THEMES = {"dark": DARK, "light": LIGHT}
THEME = os.environ.get("SHUFFLEVIZ_THEME", "dark").lower()
if THEME not in THEMES:
    raise ValueError(f"SHUFFLEVIZ_THEME={THEME!r}: expected one of {', '.join(THEMES)}")
PALETTE = THEMES[THEME]
OUTPUT_SUFFIX = "" if THEME == "dark" else f"-{THEME}"


def rgb(hex_value: str) -> tuple[float, float, float]:
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))


def tint(hex_value: str, amount: float = 0.12) -> str:
    bg = rgb(PALETTE["BG"])
    mixed = [amount * c + (1 - amount) * b for c, b in zip(rgb(hex_value), bg)]
    return "#" + "".join(f"{round(255 * c):02X}" for c in mixed)
