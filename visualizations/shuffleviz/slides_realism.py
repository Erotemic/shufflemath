"""Part 3: biased cuts, clumpy shuffles, and human realism."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, FadeIn, LaggedStart, Rectangle, VGroup

from shuffleviz.style import (
    EMPIRICAL,
    ERROR,
    LOCAL,
    MUTED,
    UNIFORM,
    DeckSlide,
    boxed,
    para,
    tex,
)
from shuffleviz.visual import card


def _bit_cards(bits: list[int], y: float, color: str = LOCAL) -> VGroup:
    cards = VGroup(*[card(0.48, 0.68, color, fill_opacity=0.08) for _ in bits])
    cards.arrange(RIGHT, buff=0.07).move_to([0, y, 0])
    labels = VGroup(*[tex(str(b), size=22, color=color).move_to(c) for b, c in zip(bits, cards)])
    return VGroup(cards, labels)


class R01BiasedCuts(DeckSlide):
    title = "Biased cuts are already a developed riffle-shuffle model"
    kicker = "Change the label law; keep stable interleaving"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        fair = _bit_cards([0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0], 0.9)
        biased = _bit_cards([0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], -0.75, EMPIRICAL)
        fair_lab = tex(r"fair cut: $p=1/2$", size=24, color=LOCAL).next_to(fair, LEFT, buff=0.35)
        bias_lab = tex(r"biased cut: $p\neq1/2$", size=24, color=EMPIRICAL).next_to(biased, LEFT, buff=0.35)
        self.say("A persistent tendency to cut away from 50/50 is not itself a new model. It changes the label probabilities while retaining the inverse-riffle structure.")
        self.play(FadeIn(fair), FadeIn(fair_lab))
        self.say("This should be our first realism extension after ideal GSR because it changes one parameter without changing the whole architecture.")
        self.play(FadeIn(biased), FadeIn(bias_lab))


class R02BiasedLiterature(DeckSlide):
    title = "1998 / 2012 · Fulman and Assaf--Diaconis--Soundararajan"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        a = boxed(para(r"\textbf{Fulman (1998):} combinatorics of biased riffle shuffles.", 5.4, 27), LOCAL).shift(LEFT * 3.0 + UP * 0.55)
        b = boxed(para(r"\textbf{Assaf--Diaconis--Soundararajan (2012):} riffle shuffles with biased cuts and their mixing behavior.", 5.4, 27), EMPIRICAL).shift(RIGHT * 3.0 + UP * 0.55)
        t = boxed(para(r"\textbf{Our formal target:} parameterized inverse-label kernels and finite TV bounds that can be inserted into the same working-set protocol search as GSR.", 10.0, 25), UNIFORM).shift(DOWN * 1.35)
        self.say("These papers establish the biased-cut branch. We should formalize enough of the finite kernel to swap it into our protocol machinery, not reproduce every asymptotic theorem first.\n[Sources] Fulman (1998); Assaf, Diaconis & Soundararajan (2012).")
        self.play(FadeIn(a), FadeIn(b), FadeIn(t))


class R03ClumpyLabels(DeckSlide):
    title = "Cut bias and clumping are different phenomena"
    kicker = "Clumping means neighboring labels are correlated"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        independent = _bit_cards([0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1], 1.0)
        clumpy = _bit_cards([0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1], -0.55, EMPIRICAL)
        top = tex("independent labels", size=24, color=LOCAL).next_to(independent, LEFT, buff=0.35)
        bot = tex("correlated labels", size=24, color=EMPIRICAL).next_to(clumpy, LEFT, buff=0.35)
        note = boxed(para(r"Two shufflers can have the same cut-size distribution but very different local adjacency structure.", 8.2, 26), ERROR).shift(DOWN * 2.15)
        self.say("A biased cut changes how many cards go to each hand. Clumping changes correlations between neighboring assignments. They must be separate parameters.")
        self.play(FadeIn(independent), FadeIn(top), FadeIn(clumpy), FadeIn(bot))
        self.play(FadeIn(note))


class R04DealerVsClumpy(DeckSlide):
    title = "Jonasson--Morris: clumpy and dealer shuffles are Markov-label models"
    kicker = "Persistence favors runs; anti-persistence favors alternation"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        clumpy = _bit_cards([0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1], 0.95, EMPIRICAL)
        dealer = _bit_cards([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1], -0.65, UNIFORM)
        a = tex("clumpy: stay with the same hand", size=23, color=EMPIRICAL).next_to(clumpy, LEFT, buff=0.3)
        b = tex("dealer: alternate hands more strongly", size=23, color=UNIFORM).next_to(dealer, LEFT, buff=0.3)
        cite = tex(r"Jonasson \\& Morris, \emph{Rapid mixing of dealer shuffles and clumpy shuffles}, 2015", size=19, color=MUTED).shift(DOWN * 2.2)
        self.say("Their inverse model replaces independent binary labels with a two-state Markov source. That is almost exactly the kind of local imperfection we want to plug into our working-set layer.\n[Sources] Jonasson & Morris (2015), Rapid mixing of dealer shuffles and clumpy shuffles.")
        self.play(FadeIn(clumpy), FadeIn(a), FadeIn(dealer), FadeIn(b), FadeIn(cite))


class R05ClumpyTarget(DeckSlide):
    title = "2015 · the asymptotic theorem is not yet our operational theorem"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        known = boxed(para(r"\textbf{Known:} for fixed clumpy/dealer parameters, Jonasson--Morris prove an $O(\log^4 n)$ mixing upper bound.", 5.6, 26), UNIFORM).shift(LEFT * 3.1 + DOWN * 0.3)
        target = boxed(para(r"\textbf{We need:} exact or certified finite error for $n\approx 50$, then composition with exchanges and physical costs.", 5.6, 26), EMPIRICAL).shift(RIGHT * 3.1 + DOWN * 0.3)
        self.say("The prior theorem proves rapid mixing asymptotically. Our application needs a finite numerical certificate at working-pile size, because that value enters a protocol optimizer.\n[Sources] Jonasson & Morris (2015).")
        self.play(FadeIn(known), FadeIn(target))


class R06GeneralCuts(DeckSlide):
    title = "2025 · broad cut-size distributions still do not subsume clumping"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        left = boxed(para(r"\textbf{Sellke--Shi--Wang:} universality of cutoff for broad deterministic/random cut-size distributions under uniform interleaving.", 5.8, 25), LOCAL).shift(LEFT * 3.2 + DOWN * 0.2)
        right = boxed(para(r"\textbf{Keep separate:} cut imbalance is a marginal pile-size effect; clumps and untouched chunks are local dependence / support effects.", 5.8, 25), ERROR).shift(RIGHT * 3.2 + DOWN * 0.2)
        self.say("This recent result makes our modeling taxonomy sharper. A flexible cut-size law is not a catch-all model of human imperfection.\n[Sources] Sellke, Shi & Wang (2025), Universality of Cutoff for Riffle Shuffling.")
        self.play(FadeIn(left), FadeIn(right))


class R07ModelLadder(DeckSlide):
    title = "A realism ladder lets us add difficulty without losing the exact baseline"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        labels = [
            ("GSR", LOCAL, "independent fair bits"),
            ("biased cut", EMPIRICAL, "independent biased bits"),
            ("clumpy/dealer", EMPIRICAL, "Markov-correlated bits"),
            ("tail / chunk model", ERROR, "some cards scarcely participate"),
            ("measured human", UNIFORM, "robust parameter set"),
        ]
        rows = VGroup()
        for name, color, sub in labels:
            box = Rectangle(width=2.5, height=0.65, stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.08)
            main = tex(name, size=23, color=color).move_to(box)
            note = tex(sub, size=18, color=MUTED).next_to(box, RIGHT, buff=0.3)
            rows.add(VGroup(box, main, note))
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.28).shift(DOWN * 0.25)
        arrows = VGroup(*[
            Arrow(rows[i].get_bottom(), rows[i + 1].get_top(), buff=0.05, color=MUTED, stroke_width=2)
            for i in range(len(rows) - 1)
        ])
        self.say("The formalization should climb this ladder in order. Every richer model can be compared against the previous exact baseline and plugged into the same protocol layer.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.12), FadeIn(arrows))
