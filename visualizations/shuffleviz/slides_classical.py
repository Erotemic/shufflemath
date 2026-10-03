"""Part 1: classical riffle-shuffle foundations."""
from __future__ import annotations

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Axes,
    Create,
    Dot,
    FadeIn,
    FadeOut,
    Arrow,
    GrowArrow,
    LaggedStart,
    Line,
    Rectangle,
    Transform,
    VGroup,
)

from shuffleviz import model
from shuffleviz.style import (
    COST,
    ERROR,
    FG,
    LOCAL,
    MUTED,
    UNIFORM,
    DeckSlide,
    boxed,
    colored_math,
    math,
    para,
    role_legend,
    tex,
)
from shuffleviz.visual import card, deck_row, operation_box


class C00Title(DeckSlide):
    title = "How should you shuffle a deck that is too large to hold?"
    kicker = "From classical riffles to cost-optimal working-set protocols"
    section = "The shufflemath roadmap"

    def body(self):
        left = deck_row(24, LOCAL, width=5.2).shift(LEFT * 3.0 + DOWN * 0.6)
        right = role_legend().shift(RIGHT * 3.4 + DOWN * 0.35)
        q = para(
            r"A 99-card Commander deck is easy to \emph{split}, but the useful question is not simply ``how many shuffles?''  "
            r"It is which operations to perform, in what order, at what physical cost, until the remaining nonuniformity is certified small.",
            width=6.5,
            size=28,
        ).shift(LEFT * 2.6 + UP * 0.65)
        self.say("Motivation: the deck is larger than the comfortable working set. Color is semantic throughout the talk.")
        self.play(LaggedStart(*[FadeIn(c, shift=UP * 0.08) for c in left], lag_ratio=0.025), FadeIn(q))
        self.say("Introduce the semantic color legend. The visual vocabulary will persist across every literature and roadmap slide.")
        self.play(FadeIn(right))


class C01ThreeQuestions(DeckSlide):
    title = "Three different questions are often conflated"
    section = "Part 1 · classical riffles"

    def body(self):
        rows = VGroup(
            boxed(para(r"\textbf{Model:} what distribution does one physical shuffle induce?", 10.6, 27), LOCAL, 0.28),
            boxed(para(r"\textbf{Mixing:} after how many steps is the distribution close to uniform?", 10.6, 27), ERROR, 0.28),
            boxed(para(r"\textbf{Control:} which sequence of heterogeneous operations is cheapest?", 10.6, 27), COST, 0.28),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.35).shift(DOWN * 0.35)
        self.say("Classical shuffle theory mostly answers the first two questions. Our extension adds the third without discarding the first two.")
        self.play(LaggedStart(*[FadeIn(r, shift=RIGHT * 0.2) for r in rows], lag_ratio=0.22))


class C02InverseRiffle(DeckSlide):
    title = "GSR is easiest to see backwards: label, then stable-sort"
    kicker = "One inverse 2-shuffle gives every card an independent fair bit"
    section = "Part 1 · classical riffles"

    def body(self):
        labels = [0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0]
        cards = VGroup(*[card(0.52, 0.72, LOCAL, fill_opacity=0.09) for _ in labels])
        cards.arrange(RIGHT, buff=0.09).shift(UP * 0.7)
        bits = VGroup(*[tex(str(b), size=24, color=LOCAL).move_to(c) for b, c in zip(labels, cards)])
        before = VGroup(cards, bits)
        order = sorted(range(len(labels)), key=lambda i: labels[i])
        after_cards = VGroup(*[card(0.52, 0.72, LOCAL, fill_opacity=0.09) for _ in labels])
        after_cards.arrange(RIGHT, buff=0.09).shift(DOWN * 1.0)
        after_bits = VGroup(*[tex(str(labels[i]), size=24, color=LOCAL).move_to(after_cards[j]) for j, i in enumerate(order)])
        arrow = GrowArrow(Arrow([0, 0.25, 0], [0, -0.45, 0], color=LOCAL, stroke_width=4, buff=0.0))
        caption = tex(r"stable sort by the bit", size=24, color=MUTED).shift(DOWN * 0.1)
        self.say("The inverse description avoids reasoning about a random interleaving directly. Independent labels plus stable sort is the kernel we want to formalize first.")
        self.play(FadeIn(before))
        self.say("Stable sorting preserves the relative order within each label class, which is exactly the inverse-riffle structure.")
        self.play(arrow, FadeIn(caption), FadeIn(after_cards), FadeIn(after_bits))


class C03RepeatedLabels(DeckSlide):
    title = "Repeated riffles compose into one larger-label shuffle"
    kicker = r"$r$ inverse 2-shuffles $\Longleftrightarrow$ one $a$-shuffle with $a=2^r$"
    section = "Part 1 · classical riffles"

    def body(self):
        one = VGroup(*[tex(s, size=28, color=LOCAL) for s in ["0", "1"]]).arrange(RIGHT, buff=0.8)
        two = VGroup(*[tex(s, size=28, color=LOCAL) for s in ["00", "01", "10", "11"]]).arrange(RIGHT, buff=0.55)
        three = VGroup(*[tex(s, size=24, color=LOCAL) for s in ["000", "001", "010", "011", "100", "101", "110", "111"]]).arrange(RIGHT, buff=0.22)
        one.shift(UP * 1.2); two.shift(UP * 0.1); three.shift(DOWN * 1.1)
        formula = colored_math((r"2", LOCAL), (r"\to 4", LOCAL), (r"\to 8", LOCAL), (r"\to \cdots \to 2^r", LOCAL), size=34).shift(DOWN * 2.0)
        self.say("Composition is the key structural theorem: after r riffles, concatenate the r independent bits into one label.")
        self.play(FadeIn(one))
        self.say("Two rounds give four labels; three rounds give eight. This is the clean formal route to the a-shuffle law.")
        self.play(Transform(one.copy(), two), FadeIn(two))
        self.play(Transform(two.copy(), three), FadeIn(three), FadeIn(formula))


class C04ExactTV(DeckSlide):
    title = "Bayer--Diaconis gives exact finite total variation"
    kicker = "The famous seven-riffle story is about a whole 52-card deck under ideal GSR"
    section = "Part 1 · classical riffles"

    def body(self):
        ks = list(range(5, 13))
        vals52 = [float(model.gsr_tv(52, k)) for k in ks]
        vals99 = [float(model.gsr_tv(99, k)) for k in ks]
        axes = Axes(x_range=[5, 12, 1], y_range=[0, 1, 0.2], x_length=8.8, y_length=4.4, tips=False, axis_config={"color": MUTED}).shift(DOWN * 0.35)
        labx = tex("ideal riffles", size=20, color=MUTED).next_to(axes.x_axis, DOWN, buff=0.18)
        ylab = tex(r"$d_{TV}$", size=20, color=MUTED).next_to(axes.y_axis, LEFT, buff=0.12)
        p52 = [axes.c2p(k, v) for k, v in zip(ks, vals52)]
        p99 = [axes.c2p(k, v) for k, v in zip(ks, vals99)]
        l52 = VGroup(*[Line(a, b, color=UNIFORM, stroke_width=4) for a, b in zip(p52, p52[1:])], *[Dot(p, color=UNIFORM, radius=0.055) for p in p52])
        l99 = VGroup(*[Line(a, b, color=LOCAL, stroke_width=4) for a, b in zip(p99, p99[1:])], *[Dot(p, color=LOCAL, radius=0.055) for p in p99])
        legend = VGroup(tex("52 cards", size=22, color=UNIFORM), tex("99 cards", size=22, color=LOCAL)).arrange(DOWN, aligned_edge=LEFT, buff=0.12).move_to([4.8, 2.0, 0])
        self.say("This curve is exact, not a simulation. It is the classical baseline we want Lean to reproduce for local working piles.\n[Sources] Bayer & Diaconis (1992), Trailing the Dovetail Shuffle to its Lair.")
        self.play(Create(axes), FadeIn(labx), FadeIn(ylab))
        self.say("The 52-card curve motivates the cultural seven-riffle number. The 99-card whole-deck curve is slower, but whole-deck riffles are not our physical operation anyway.")
        self.play(Create(l52), Create(l99), FadeIn(legend))


class C05BayerDiaconis(DeckSlide):
    title = "1992 · Bayer--Diaconis is our local-shuffle foundation"
    section = "Part 1 · classical riffles"

    def body(self):
        known = boxed(para(r"\textbf{Known:} exact permutation probabilities after repeated GSR riffles, expressed through rising sequences / descents; cutoff near $(3/2)\log_2 n$.", 5.8, 25), UNIFORM)
        target = boxed(para(r"\textbf{Formalize:} inverse binary labels $\to$ $a$-shuffle composition $\to$ rising-sequence formula $\to$ exact TV for 49- and 50-card working piles.", 5.8, 25), LOCAL)
        known.shift(LEFT * 3.15 + DOWN * 0.35); target.shift(RIGHT * 3.15 + DOWN * 0.35)
        cite = tex(r"Bayer \\& Diaconis, \emph{Trailing the Dovetail Shuffle to its Lair}, 1992", size=20, color=MUTED).shift(DOWN * 2.45)
        self.say("This paper supplies our first exact local kernel. We are not trying to improve its classical mathematics; we need to transport it into the working-set protocol problem.\n[Sources] Bayer & Diaconis (1992).")
        self.play(FadeIn(known), FadeIn(target), FadeIn(cite))
