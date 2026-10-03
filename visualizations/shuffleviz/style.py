"""Shared Manim layout and semantic styling for the shufflemath talk."""
from __future__ import annotations

import contextlib
import fcntl
import functools
import os
from pathlib import Path

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UL,
    UP,
    FadeOut,
    MathTex,
    Rectangle,
    Tex,
    TexTemplate,
    Text,
    VGroup,
    config,
)
from manim.mobject.svg.svg_mobject import SVGMobject
from manim.mobject.text import tex_mobject
from manim_slides import Slide

from shuffleviz.palette import OUTPUT_SUFFIX, PALETTE, tint


@contextlib.contextmanager
def _media_cache_lock():
    lock = Path(config.media_dir) / ".cache.lock"
    lock.parent.mkdir(parents=True, exist_ok=True)
    with open(lock, "w") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        yield


def _under_media_cache_lock(fill):
    @functools.wraps(fill)
    def locked(*args, **kwargs):
        with _media_cache_lock():
            return fill(*args, **kwargs)
    return locked


# Rendering several scenes in parallel otherwise races on Manim's LaTeX/SVG cache.
tex_mobject.tex_to_svg_file = _under_media_cache_lock(tex_mobject.tex_to_svg_file)
Text._text2svg = _under_media_cache_lock(Text._text2svg)
SVGMobject.generate_mobject = _under_media_cache_lock(SVGMobject.generate_mobject)

BG = PALETTE["BG"]
FG = PALETTE["FG"]
MUTED = PALETTE["MUTED"]
FAINT = PALETTE["FAINT"]
PANEL = PALETTE["PANEL"]
LOCAL = PALETTE["LOCAL"]
EXCHANGE = PALETTE["EXCHANGE"]
UNIFORM = PALETTE["UNIFORM"]
ERROR = PALETTE["ERROR"]
COST = PALETTE["COST"]
ORACLE = PALETTE["ORACLE"]
EMPIRICAL = PALETTE["EMPIRICAL"]
REFUTED = PALETTE["REFUTED"]

config.background_color = BG
FRAME_W = config.frame_width
FRAME_H = config.frame_height
LEFT_EDGE = -FRAME_W / 2 + 0.55
TOP_EDGE = FRAME_H / 2 - 0.45
MONO_FONT = "JetBrains Mono"

TEMPLATE = TexTemplate()
TEMPLATE.add_to_preamble(
    r"""
\usepackage{lmodern}
\renewcommand{\familydefault}{\sfdefault}
\usepackage{amsmath,amssymb}
\usepackage{xcolor}
\newcommand{\TV}{d_{\mathrm{TV}}}
\newcommand{\Unif}{\mathrm{Unif}}
\newcommand{\cost}{\mathrm{cost}}
"""
)
_UNITS_PER_CM_PER_FONT_SIZE = 14.173228 / 10 / 48


def tex(body: str, size: float = 30, color: str = FG, **kwargs) -> Tex:
    return Tex(body, font_size=size, color=color, tex_template=TEMPLATE, **kwargs)


def math(*parts: str, size: float = 36, color: str = FG, **kwargs) -> MathTex:
    return MathTex(*parts, font_size=size, color=color, tex_template=TEMPLATE, **kwargs)


def colored_math(*parts: tuple[str, str | None], size: float = 36) -> MathTex:
    mob = math(*[p for p, _ in parts], size=size)
    for sub, (_, color) in zip(mob, parts):
        if color is not None:
            sub.set_color(color)
    return mob


def para(body: str, width: float, size: float = 27, color: str = FG, align: str = "raggedright") -> Tex:
    cm = width / (_UNITS_PER_CM_PER_FONT_SIZE * size)
    return tex(
        rf"\begin{{minipage}}{{{cm:.3f}cm}}\{align} {body}\end{{minipage}}",
        size=size,
        color=color,
    )


def mono(body: str, size: float = 20, color: str = FG) -> Text:
    return Text(body, font=MONO_FONT, font_size=size, color=color)


def boxed(mob, color: str = FG, pad: float = 0.25) -> VGroup:
    rect = Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_color=color,
        stroke_width=2,
        fill_color=PANEL if color in (FG, MUTED) else tint(color),
        fill_opacity=1,
    ).move_to(mob)
    return VGroup(rect, mob)


def panel(mob, pad: float = 0.3, color: str | None = None) -> Rectangle:
    return Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_width=0,
        fill_color=PANEL if color is None else tint(color),
        fill_opacity=1,
    ).move_to(mob)


def role_legend() -> VGroup:
    rows = [
        (LOCAL, "local shuffle"),
        (EXCHANGE, "cross-pile exchange"),
        (UNIFORM, "uniform target"),
        (ERROR, "remaining error"),
        (COST, "physical cost"),
        (ORACLE, "perfect-local oracle"),
    ]
    out = VGroup()
    for color, label in rows:
        swatch = Rectangle(width=0.34, height=0.2, stroke_width=0, fill_color=color, fill_opacity=1)
        text = tex(label, size=20, color=MUTED).next_to(swatch, RIGHT, buff=0.12)
        out.add(VGroup(swatch, text))
    out.arrange(DOWN, aligned_edge=LEFT, buff=0.12)
    return out


class DeckSlide(Slide):
    """Shared chrome and speaker-note-aware build boundaries.

    ``handout = False`` marks an animation-first scene whose meaning depends on
    motion. Such scenes stay in the live/HTML deck but are omitted from the
    one-frame-per-scene static handout. A neighboring summary scene should carry
    the static mathematical conclusion.
    """

    title = ""
    kicker = ""
    section = "Shuffling under a working-set constraint"
    depth = ""
    handout = True
    skip_reversing = True
    wait_time_between_slides = 0.1

    def __init__(self, *args, **kwargs):
        deck = os.environ.get("SHUFFLEVIZ_DECK")
        if deck:
            kwargs.setdefault("output_folder", Path(f"slides-{deck}{OUTPUT_SUFFIX}"))
        super().__init__(*args, **kwargs)

    def slide_number(self):
        deck = os.environ.get("SHUFFLEVIZ_DECK")
        if not deck:
            return None
        from shuffleviz.build_slides import DECK_SCENES
        order = DECK_SCENES.get(deck, [])
        name = type(self).__name__
        return (order.index(name) + 1, len(order)) if name in order else None

    def footer_text(self):
        deck = os.environ.get("SHUFFLEVIZ_DECK")
        if deck:
            from shuffleviz.build_slides import PART_TITLES
            if deck in PART_TITLES:
                return PART_TITLES[deck]
        return self.section

    def construct(self):
        self.chrome = self.make_chrome()
        if self.chrome is not None:
            self.add(self.chrome)
        self._ended_on_src = False
        self.body()
        if not self._ended_on_src:
            self.wait(self.wait_time_between_slides)

    def make_chrome(self):
        items = VGroup()
        self._head = VGroup()
        if self.title:
            title = tex(self.title, size=44)
            max_w = FRAME_W - 1.1 - (1.8 if self.depth else 0)
            if title.width > max_w:
                title.scale_to_fit_width(max_w)
            title.move_to([LEFT_EDGE, TOP_EDGE, 0], aligned_edge=UL)
            items.add(title)
            self._head.add(title)
            if self.kicker:
                kick = tex(self.kicker, size=25, color=MUTED).next_to(title, DOWN, aligned_edge=LEFT, buff=0.16)
                items.add(kick)
                self._head.add(kick)
        if self.depth:
            badge = tex({"*": r"$\ast$ optional depth", "**": r"$\ast\ast$ backup"}[self.depth], size=19, color=MUTED)
            badge.move_to([FRAME_W / 2 - 0.45, TOP_EDGE - 0.05, 0], aligned_edge=UP + RIGHT)
            items.add(badge)
        footer = self.footer_text()
        if footer:
            f = tex(footer, size=17, color=MUTED).move_to([LEFT_EDGE, -FRAME_H / 2 + 0.3, 0], aligned_edge=LEFT)
            items.add(f)
        num = self.slide_number()
        if num:
            k, n = num
            lab = tex(rf"{k} / {n}", size=19, color=MUTED).move_to([FRAME_W / 2 - 0.45, -FRAME_H / 2 + 0.3, 0], aligned_edge=RIGHT)
            items.add(lab)
        return items

    @property
    def content_top(self):
        if self.chrome is None or not self.title:
            return TOP_EDGE
        return self._head.get_bottom()[1] - 0.24

    def say(self, notes: str, **kwargs):
        self.next_slide(notes=notes, **kwargs)
        self._ended_on_src = kwargs.get("src") is not None

    def fade_all_but_chrome(self, run_time=0.5):
        keep = {id(self.chrome)}
        mobs = [m for m in self.mobjects if id(m) not in keep]
        if mobs:
            self.play(*[FadeOut(m) for m in mobs], run_time=run_time)

    def body(self):  # pragma: no cover
        raise NotImplementedError
