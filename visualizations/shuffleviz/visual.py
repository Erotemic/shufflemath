"""Reusable card/deck/plot primitives for the shufflemath slides."""
from __future__ import annotations

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Arrow,
    Circle,
    Dot,
    Line,
    Rectangle,
    RoundedRectangle,
    VGroup,
)

from shuffleviz.style import FAINT, FG, MUTED, PANEL, tex


def card(width=0.34, height=0.48, color=FG, fill_opacity=0.08, stroke_width=1.4):
    return RoundedRectangle(
        width=width,
        height=height,
        corner_radius=0.04,
        stroke_color=color,
        stroke_width=stroke_width,
        fill_color=color,
        fill_opacity=fill_opacity,
    )


def deck_row(n: int, color: str, width: float = 7.0, height: float = 0.56, overlap: float = 0.72) -> VGroup:
    if n <= 0:
        return VGroup()
    step = width / max(n - 1 + 1 / overlap, 1)
    cwidth = step / overlap
    row = VGroup(*[card(cwidth, height, color=color) for _ in range(n)])
    row.arrange(RIGHT, buff=step - cwidth)
    return row


def packet(n: int, color: str, width=2.2, height=1.05, label: str | None = None) -> VGroup:
    box = RoundedRectangle(width=width, height=height, corner_radius=0.12, stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.08)
    count = tex(str(n), size=30, color=color).move_to(box)
    out = VGroup(box, count)
    if label:
        lab = tex(label, size=18, color=MUTED).next_to(box, DOWN, buff=0.1)
        out.add(lab)
    return out


def operation_box(label: str, color: str, width=1.6, height=0.8, subtitle: str | None = None) -> VGroup:
    box = RoundedRectangle(width=width, height=height, corner_radius=0.12, stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.1)
    main = tex(label, size=25, color=color).move_to(box)
    out = VGroup(box, main)
    if subtitle:
        sub = tex(subtitle, size=15, color=MUTED).next_to(box, DOWN, buff=0.08)
        out.add(sub)
    return out


def flow(items: list[VGroup], arrow_color=FAINT, buff=0.55) -> VGroup:
    group = VGroup()
    for i, item in enumerate(items):
        group.add(item)
        if i + 1 < len(items):
            arrow = Arrow(item.get_right(), items[i + 1].get_left(), buff=0.08, stroke_width=2, color=arrow_color, max_tip_length_to_length_ratio=0.16)
            group.add(arrow)
    group.arrange(RIGHT, buff=buff)
    return group


def urn(radius=1.0, color=FG, label: str | None = None) -> VGroup:
    body = RoundedRectangle(width=2 * radius, height=1.7 * radius, corner_radius=0.18, stroke_color=color, stroke_width=2, fill_color=PANEL, fill_opacity=0.7)
    rim = Line(body.get_corner(UP + LEFT) + RIGHT * 0.15, body.get_corner(UP + RIGHT) + LEFT * 0.15, color=color, stroke_width=3)
    out = VGroup(body, rim)
    if label:
        out.add(tex(label, size=20, color=MUTED).next_to(body, DOWN, buff=0.1))
    return out


def dots_in_box(box, count: int, color: str, cols: int = 5, radius: float = 0.055) -> VGroup:
    dots = VGroup()
    rows = (count + cols - 1) // cols
    left = box.get_left()[0] + 0.23
    top = box.get_top()[1] - 0.25
    dx = max(0.16, (box.width - 0.45) / max(cols - 1, 1))
    dy = max(0.16, (box.height - 0.45) / max(rows - 1, 1))
    for i in range(count):
        r, c = divmod(i, cols)
        dots.add(Dot([left + c * dx, top - r * dy, 0], radius=radius, color=color))
    return dots


def timeline(years_and_labels: list[tuple[int, str, str]], x0=-5.7, x1=5.7, y=0.0) -> VGroup:
    # Chronological but deliberately not time-proportional: recent shuffle
    # literature is dense, and proportional spacing makes 2023--2025 illegible.
    axis = Line([x0, y, 0], [x1, y, 0], color=FAINT, stroke_width=2)
    group = VGroup(axis)
    n = len(years_and_labels)
    for idx, (year, label, color) in enumerate(years_and_labels):
        t = idx / max(n - 1, 1)
        x = x0 + t * (x1 - x0)
        dot = Dot([x, y, 0], color=color, radius=0.07)
        yr = tex(str(year), size=17, color=MUTED).next_to(dot, DOWN, buff=0.12)
        lab = tex(label, size=15, color=color)
        lab.next_to(dot, UP, buff=0.16 if idx % 2 == 0 else 0.58)
        group.add(dot, yr, lab)
    return group
