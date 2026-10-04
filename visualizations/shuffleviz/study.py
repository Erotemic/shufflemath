"""Reusable pedagogy primitives for the long-form shufflemath study deck.

The study deck is intentionally redundant: definitions reappear when a concept
returns after a long gap. These helpers keep that repetition visually
consistent without turning the slides into dense walls of text.
"""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, Rectangle, VGroup

from shuffleviz.style import FG, MUTED, PANEL, UNIFORM, boxed, math, para, tex


def definition_box(term: str, definition: str, *, symbol: str | None = None, color: str = UNIFORM,
                   width: float = 10.6, body_size: float = 25) -> VGroup:
    """Definition card with a term, optional symbol, and a plain-language body."""
    head_parts = [tex(term, size=25, color=color)]
    if symbol:
        head_parts.append(math(symbol, size=27, color=color))
    head = VGroup(*head_parts).arrange(RIGHT, buff=0.28)
    body = para(definition, width - 0.65, body_size, color=FG)
    content = VGroup(head, body).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
    frame = Rectangle(
        width=width,
        height=content.height + 0.48,
        stroke_color=color,
        stroke_width=2,
        fill_color=PANEL,
        fill_opacity=1,
    ).move_to(content)
    return VGroup(frame, content)


def reminder_box(term: str, definition: str, *, symbol: str | None = None, color: str = MUTED,
                 width: float = 10.4, body_size: float = 23) -> VGroup:
    """A compact definition reminder used when a concept reappears later."""
    prefix = tex(r"Reminder:", size=20, color=color)
    name = tex(term, size=21, color=FG)
    head = VGroup(prefix, name).arrange(RIGHT, buff=0.16)
    if symbol:
        head.add(math(symbol, size=22, color=color).next_to(name, RIGHT, buff=0.18))
    body = para(definition, width - 0.55, body_size, color=FG)
    content = VGroup(head, body).arrange(DOWN, aligned_edge=LEFT, buff=0.10)
    return boxed(content, color, 0.18)


def glossary_grid(entries: list[tuple[str, str]], *, columns: int = 2, width: float = 11.4,
                  term_color: str = UNIFORM, body_size: float = 20) -> VGroup:
    """Two-column glossary suitable for checkpoint/reference slides."""
    if columns < 1:
        raise ValueError("columns must be positive")
    col_w = width / columns - 0.25
    cells = []
    for term, definition in entries:
        heading = tex(term, size=21, color=term_color)
        body = para(definition, col_w - 0.45, body_size, color=FG)
        content = VGroup(heading, body).arrange(DOWN, aligned_edge=LEFT, buff=0.07)
        frame = Rectangle(
            width=col_w,
            height=max(0.82, content.height + 0.26),
            stroke_color=MUTED,
            stroke_width=1.2,
            fill_color=PANEL,
            fill_opacity=0.78,
        ).move_to(content)
        cells.append(VGroup(frame, content))

    rows = []
    for start in range(0, len(cells), columns):
        row = VGroup(*cells[start:start + columns]).arrange(RIGHT, buff=0.25)
        rows.append(row)
    return VGroup(*rows).arrange(DOWN, buff=0.16)


def derivation_steps(steps: list[tuple[str, str]], *, width: float = 10.8,
                     body_size: float = 23) -> VGroup:
    """Numbered derivation rows: a short label plus a mathematical/text step."""
    rows = VGroup()
    for idx, (label, body) in enumerate(steps, 1):
        number = tex(str(idx), size=21, color=UNIFORM)
        label_mob = tex(label, size=21, color=MUTED)
        body_mob = para(body, width - 2.0, body_size, color=FG)
        content = VGroup(number, label_mob, body_mob).arrange(RIGHT, buff=0.22)
        frame = Rectangle(
            width=width,
            height=max(0.62, content.height + 0.20),
            stroke_color=MUTED,
            stroke_width=1.0,
            fill_color=PANEL,
            fill_opacity=0.7,
        ).move_to(content)
        rows.add(VGroup(frame, content))
    rows.arrange(DOWN, buff=0.12)
    return rows


def remember_box(text: str, *, color: str = UNIFORM, width: float = 10.5, size: float = 25) -> VGroup:
    """A single take-away statement for the end of a derivation."""
    return boxed(
        VGroup(
            tex(r"What to remember", size=21, color=color),
            para(text, width - 0.55, size, color=FG),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.11),
        color,
        0.20,
    )
