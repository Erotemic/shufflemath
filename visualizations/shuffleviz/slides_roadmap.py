"""Part 5: literature map and formalization roadmap."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, FadeIn, LaggedStart, Rectangle, VGroup

from shuffleviz.style import (
    COST,
    EMPIRICAL,
    ERROR,
    EXCHANGE,
    FG,
    LOCAL,
    MUTED,
    ORACLE,
    UNIFORM,
    DeckSlide,
    boxed,
    para,
    tex,
)
from shuffleviz.visual import timeline


class M01LiteratureMap(DeckSlide):
    title = "The literature is a set of model components, not a single linear ancestry"
    section = "Part 5 · formalization roadmap"

    def body(self):
        events = [
            (1992, "GSR exact mixing", LOCAL),
            (1998, "biased riffles", EMPIRICAL),
            (2012, "biased cuts", EMPIRICAL),
            (2015, "clumpy/dealer", EMPIRICAL),
            (2019, "large decks / BL", ORACLE),
            (2023, "unequal BL", EXCHANGE),
            (2024, "$S_k$ blocks", ORACLE),
            (2025, "general cut laws", LOCAL),
        ]
        tl = timeline(events, y=0.15)
        note = boxed(para(r"Our program formalizes the pieces needed to assemble a finite, costed working-set theorem. We do \emph{not} need to formalize every result from every paper before composing them.", 10.4, 25), UNIFORM).shift(DOWN * 2.05)
        self.say("The 1992 entry is the Gilbert--Shannon--Reeds (GSR) exact-mixing result. This sequence shows why the novelty claim must be narrow: nearly every individual ingredient already has a literature.\n[Sources] Bayer--Diaconis 1992; Fulman 1998; Assaf--Diaconis--Soundararajan 2012; Jonasson--Morris 2015; Nestoridi--White 2019; Diaconis--Fulman 2023; Griffin et al. 2023; Nestoridi--Priestley--Schmid 2024; Sellke--Shi--Wang 2025.")
        self.play(FadeIn(tl))
        self.say("The roadmap is therefore interface-driven: formalize the exact finite statements needed at each model boundary.")
        self.play(FadeIn(note))


class M02Status(DeckSlide):
    title = "Where the repository is now"
    section = "Part 5 · formalization roadmap"

    def body(self):
        done = VGroup(
            boxed(para(r"\textbf{L0 done:} exact finite distributions, kernels, stochastic matrices, TV, Dobrushin, costs.", 5.7, 25), UNIFORM),
            boxed(para(r"\textbf{L1 executable:} exact 50-state Commander Bernoulli--Laplace kernel and finite certificates.", 5.7, 25), UNIFORM),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.35).shift(LEFT * 3.15 + DOWN * 0.15)
        nexts = VGroup(
            boxed(para(r"\textbf{Next symbolic:} normalize / stationary / reversible / eigenmode / $(25,25)$ optimality.", 5.7, 25), EXCHANGE),
            boxed(para(r"\textbf{Next new kernel:} ideal GSR on 49--50 card working piles.", 5.7, 25), LOCAL),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.35).shift(RIGHT * 3.15 + DOWN * 0.15)
        self.say("The executable Commander chain is no longer the bottleneck. It gives us concrete regression targets while we replace finite certificates with symbolic theorems.")
        self.play(FadeIn(done), FadeIn(nexts))


class M03BLTheorems(DeckSlide):
    title = "Bernoulli--Laplace theorem ladder"
    kicker = "Turn one Commander instance into reusable mathematics"
    section = "Part 5 · formalization roadmap"

    def body(self):
        steps = [
            ("1", "Vandermonde row normalization", EXCHANGE),
            ("2", "hypergeometric stationary law", ORACLE),
            ("3", "detailed balance / reversibility", UNIFORM),
            ("4", "first eigenfunction and $\\lambda_1$", EXCHANGE),
            ("5", "finite schedule optimality certificates", COST),
        ]
        rows = VGroup()
        for num, label, color in steps:
            n = tex(num, size=24, color=color)
            box = Rectangle(width=8.7, height=0.62, stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.07)
            text = tex(label, size=24, color=FG).move_to(box)
            n.next_to(box, LEFT, buff=0.25)
            rows.add(VGroup(n, box, text))
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.23).shift(DOWN * 0.25)
        self.say("The current native-decide results are valuable executable certificates, but the reusable end state is a general symbolic Bernoulli--Laplace layer.")
        self.play(LaggedStart(*[FadeIn(r, shift=RIGHT * 0.15) for r in rows], lag_ratio=0.12))


class M04GSRTheorems(DeckSlide):
    title = "GSR theorem ladder"
    kicker = "This is the bridge from classical shuffle theory to our local working-set kernel"
    section = "Part 5 · formalization roadmap"

    def body(self):
        steps = VGroup(
            boxed(para(r"inverse binary labels define one 2-shuffle", 9.2, 24), LOCAL),
            boxed(para(r"$r$ repeated 2-shuffles $=$ one $2^r$-shuffle", 9.2, 24), LOCAL),
            boxed(para(r"permutation probability depends on rising sequences / descents", 9.2, 24), LOCAL),
            boxed(para(r"exact finite TV for $n=49,50$", 9.2, 24), ERROR),
            boxed(para(r"embed local kernels into the 99-card protocol state", 9.2, 24), EXCHANGE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22).shift(DOWN * 0.25)
        self.say("This layer should be formalized before any fitted human model. It is exact, compositional, and gives us trustworthy local error numbers.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.11))


class M05Composition(DeckSlide):
    title = "Composition theorem ladder"
    section = "Part 5 · formalization roadmap"

    def body(self):
        left = boxed(para(r"\textbf{Kernel facts:} TV contraction; Dobrushin coefficient; composition of finite kernels.", 5.7, 26), ERROR).shift(LEFT * 3.15 + UP * 0.55)
        right = boxed(para(r"\textbf{Protocol fact:} telescoping replacement bound for a heterogeneous sequence of kernels.", 5.7, 26), UNIFORM).shift(RIGHT * 3.15 + UP * 0.55)
        bottom = boxed(para(r"This is the architectural hinge: after it exists, every new local model only needs its own finite approximation-to-oracle bound to participate in the large-deck theorem.", 10.4, 25), LOCAL).shift(DOWN * 1.55)
        self.say("The composition theorem is where formalization pays compound interest. It isolates all later local-model work behind a single error interface.")
        self.play(FadeIn(left), FadeIn(right), FadeIn(bottom))


class M06ProtocolCertificates(DeckSlide):
    title = "Protocol search can stay outside Lean"
    kicker = "Search proposes; Lean checks"
    section = "Part 5 · formalization roadmap"

    def body(self):
        search = boxed(para(r"\textbf{Ordinary program:} enumerate or optimize a bounded action space; compute a Pareto frontier; emit a candidate plus compact evidence.", 5.7, 25), COST).shift(LEFT * 3.15 + DOWN * 0.15)
        verify = boxed(para(r"\textbf{Lean:} verify action semantics, total cost, terminal error bound, and bounded optimality claim when requested.", 5.7, 25), UNIFORM).shift(RIGHT * 3.15 + DOWN * 0.15)
        arrow = Arrow(search.get_right(), verify.get_left(), buff=0.18, color=MUTED, stroke_width=3)
        self.say("We should not formalize a large numerical optimizer prematurely. The proof object is the protocol certificate, not the search heuristic.")
        self.play(FadeIn(search), FadeIn(verify), FadeIn(arrow))


class M07RealismRoadmap(DeckSlide):
    title = "Only after the exact baseline is stable do we add human realism"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = VGroup(
            boxed(para(r"biased-cut inverse riffle", 8.6, 25), EMPIRICAL),
            boxed(para(r"Jonasson--Morris clumpy / dealer Markov labels", 8.6, 25), EMPIRICAL),
            boxed(para(r"untouched-tail / chunk participation models", 8.6, 25), ERROR),
            boxed(para(r"measured parameter intervals and robust optimization", 8.6, 25), COST),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.30).shift(DOWN * 0.2)
        self.say("This ordering protects us from fitting a complicated human model before we know the control architecture works on exact kernels.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.14))


class M08EndToEnd(DeckSlide):
    title = "The full research program is a chain of replaceable models"
    section = "Part 5 · formalization roadmap"

    def body(self):
        labels = [
            ("physical measurement", EMPIRICAL),
            ("local shuffle kernel", LOCAL),
            ("working-set exchange", EXCHANGE),
            ("compositional TV bound", ERROR),
            ("costed protocol search", COST),
            ("Lean certificate", UNIFORM),
            ("human instruction", FG),
        ]
        boxes = VGroup()
        for label, color in labels:
            box = Rectangle(width=1.6, height=1.0, stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.07)
            text = para(label, 1.35, 19, color=color, align="centering").move_to(box)
            boxes.add(VGroup(box, text))
        boxes.arrange(RIGHT, buff=0.25).shift(DOWN * 0.15)
        arrows = VGroup(*[
            Arrow(boxes[i].get_right(), boxes[i + 1].get_left(), buff=0.05, color=MUTED, stroke_width=2)
            for i in range(len(boxes) - 1)
        ])
        self.say("The important roadmap insight is modularity. The physical model can improve without changing the protocol semantics, and the search can improve without changing what Lean verifies.")
        self.play(LaggedStart(*[FadeIn(b) for b in boxes], lag_ratio=0.09), FadeIn(arrows))


class M09Closing(DeckSlide):
    title = "What we are trying to learn"
    section = "The shufflemath roadmap"

    def body(self):
        q = boxed(para(r"For a specific person's hands, sleeves, deck size, and shuffle behavior: \textbf{what is the cheapest finite physical protocol that we can certify reaches a chosen randomness target?}", 10.5, 31), UNIFORM).shift(UP * 0.45)
        line = para(r"Classical shuffle theory supplies the kernels.  Large-deck theory supplies the membership abstraction.  The new work is to connect them under a working-set constraint and optimize the connection without pretending the local shuffle is perfect.", 10.4, 25).shift(DOWN * 1.4)
        self.say("Close on the operational question. The presentation is intended to be a map of the mathematics, not merely a status report on Lean files.")
        self.play(FadeIn(q), FadeIn(line))
