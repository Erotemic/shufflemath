"""Part 4: the combined costed working-set control problem."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Axes, Create, Dot, FadeIn, Line, VGroup

from shuffleviz.style import (
    COST,
    ERROR,
    EXCHANGE,
    LOCAL,
    MUTED,
    ORACLE,
    UNIFORM,
    DeckSlide,
    boxed,
    colored_math,
    math,
    para,
    tex,
)
from shuffleviz.visual import operation_box


class O01Protocol(DeckSlide):
    title = "Our object is a protocol, not a shuffle count"
    kicker = r"$\sigma=L^{r_0}X_{k_1}L^{r_1}X_{k_2}\cdots X_{k_q}L^{r_q}$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        ops = VGroup(
            operation_box(r"$L^{r_0}$", LOCAL, subtitle="local"),
            operation_box(r"$X_{k_1}$", EXCHANGE, subtitle="cross"),
            operation_box(r"$L^{r_1}$", LOCAL, subtitle="local"),
            operation_box(r"$X_{k_2}$", EXCHANGE, subtitle="cross"),
            operation_box(r"$L^{r_2}$", LOCAL, subtitle="local"),
        ).arrange(RIGHT, buff=0.55).shift(UP * 0.45)
        arrows = VGroup(*[
            Arrow(ops[i].get_right(), ops[i + 1].get_left(), buff=0.08, color=MUTED, stroke_width=2)
            for i in range(len(ops) - 1)
        ])
        objective = boxed(colored_math(
            (r"\min_{\sigma}\ ", COST),
            (r"\cost(\sigma)", COST),
            (r"\quad\text{s.t.}\quad", None),
            (r"\TV(\delta_{\rm start}K_\sigma,\Unif)\le\varepsilon", ERROR),
            size=34,
        ), COST).shift(DOWN * 1.45)
        self.say("Once local shuffling is finite rather than an oracle, repeated local steps matter. A schedule becomes a real control variable.")
        self.play(FadeIn(ops), FadeIn(arrows))
        self.say("The operational theorem we want is a constrained minimum-cost statement, not a folklore count of riffles.")
        self.play(FadeIn(objective))


class O02TwoErrors(DeckSlide):
    title = "Two memories have to die: internal order and pile membership"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        local = boxed(para(r"\textbf{Within-pile error:} cards that already share a working set have not yet been fully randomized by the finite local shuffle.", 5.7, 26), LOCAL).shift(LEFT * 3.15 + DOWN * 0.25)
        cross = boxed(para(r"\textbf{Membership error:} cards in different working sets have not interacted enough across the boundary.", 5.7, 26), EXCHANGE).shift(RIGHT * 3.15 + DOWN * 0.25)
        bottom = boxed(para(r"Nestoridi--White sets the first error to zero by assumption. Classical GSR ignores the second because every card participates in the same whole-deck shuffle.", 10.3, 24), ERROR).shift(DOWN * 2.15)
        self.say("Our problem is the product of two classical obstructions. The useful schedule balances them rather than solving either one in isolation.")
        self.play(FadeIn(local), FadeIn(cross), FadeIn(bottom))


class O03OracleComparison(DeckSlide):
    title = "Compare finite local shuffles with an oracle local randomizer"
    kicker = "This creates a compositional proof strategy"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        actual = VGroup(
            operation_box(r"$L_{r_0}$", LOCAL), operation_box(r"$X_{k_1}$", EXCHANGE), operation_box(r"$L_{r_1}$", LOCAL), operation_box(r"$X_{k_2}$", EXCHANGE), operation_box(r"$L_{r_2}$", LOCAL)
        ).arrange(RIGHT, buff=0.38).shift(UP * 0.85)
        oracle = VGroup(
            operation_box(r"$L_\infty$", ORACLE), operation_box(r"$X_{k_1}$", EXCHANGE), operation_box(r"$L_\infty$", ORACLE), operation_box(r"$X_{k_2}$", EXCHANGE), operation_box(r"$L_\infty$", ORACLE)
        ).arrange(RIGHT, buff=0.38).shift(DOWN * 0.55)
        bridges = VGroup(*[
            Arrow(actual[i].get_bottom(), oracle[i].get_top(), buff=0.07, color=ERROR, stroke_width=2)
            for i in (0, 2, 4)
        ])
        formula = math(r"\varepsilon_r=\sup_\mu\TV(\mu L_r,\mu L_\infty)", size=31, color=ERROR).shift(DOWN * 2.0)
        self.say("The ideal large-deck chain is analytically simple. We can treat finite local randomization as a perturbation of that oracle chain.")
        self.play(FadeIn(actual), FadeIn(oracle), FadeIn(bridges))
        self.say("Each local phase gets its own worst-case finite error epsilon_r.")
        self.play(FadeIn(formula))


class O04Telescope(DeckSlide):
    title = "The desired bridge theorem is a TV telescoping bound"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        theorem = boxed(math(
            r"\TV(K_0K_1\cdots K_n,\ L_0L_1\cdots L_n)"
            r"\le \sum_{i=0}^n \sup_x \TV(K_i(x,\cdot),L_i(x,\cdot))",
            size=32,
            color=ERROR,
        ), ERROR).shift(UP * 0.6)
        meaning = VGroup(
            boxed(para(r"Markov kernels contract total variation.", 4.8, 25), UNIFORM),
            boxed(para(r"Replace one imperfect phase at a time.", 4.8, 25), LOCAL),
            boxed(para(r"Add the local replacement errors.", 4.8, 25), ERROR),
        ).arrange(RIGHT, buff=0.3).shift(DOWN * 1.25)
        self.say("This theorem is the key interface between local shuffle theory and large-deck membership theory.")
        self.play(FadeIn(theorem))
        self.say("It is conservative but modular: every improved local bound immediately improves the whole protocol certificate.")
        self.play(FadeIn(meaning))


class O05Costs(DeckSlide):
    title = "Physical cost is heterogeneous"
    kicker = "A local mash and a full repartition need not cost the same time or effort"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        formula = boxed(colored_math(
            (r"\cost(\sigma)=", COST),
            (r"c_L\sum_i r_i", LOCAL),
            (r"+", None),
            (r"\sum_j c_X(k_j)", EXCHANGE),
            size=36,
        ), COST).shift(UP * 0.6)
        text = boxed(para(r"The interesting regime is not determined by mathematics alone. It depends on working-set size, seconds per local shuffle, seconds per cross-pile operation, and the local shuffle model.", 9.7, 26), COST).shift(DOWN * 1.25)
        self.say("Cost is part of the model rather than an afterthought. The same randomness target can prefer different protocols for different hands, sleeves, and deck thicknesses.")
        self.play(FadeIn(formula), FadeIn(text))


class O06Pareto(DeckSlide):
    title = "Search produces a Pareto frontier; Lean certifies selected frontier points"
    kicker = "Illustrative geometry of the optimization problem"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        axes = Axes(x_range=[0, 12, 2], y_range=[0, 1, 0.2], x_length=8.8, y_length=4.4, tips=False, axis_config={"color": MUTED}).shift(DOWN * 0.35)
        pts = [(1.2, .92), (2.2, .72), (2.8, .82), (3.4, .55), (4.6, .42), (5.0, .50), (6.2, .25), (7.4, .18), (8.6, .10), (10.2, .065)]
        dots = VGroup(*[Dot(axes.c2p(x, y), radius=0.07, color=ERROR) for x, y in pts])
        frontier = [(1.2, .92), (2.2, .72), (3.4, .55), (4.6, .42), (6.2, .25), (7.4, .18), (8.6, .10), (10.2, .065)]
        lines = VGroup(*[Line(axes.c2p(*a), axes.c2p(*b), color=UNIFORM, stroke_width=3.5) for a, b in zip(frontier, frontier[1:])])
        xl = tex("physical cost", size=20, color=COST).next_to(axes.x_axis, DOWN, buff=0.16)
        yl = tex("certified error", size=20, color=ERROR).next_to(axes.y_axis, LEFT, buff=0.10)
        caveat = tex("schematic — not measured protocol data", size=18, color=MUTED).shift(DOWN * 2.55)
        self.say("The optimizer may remain an ordinary program. Its job is to propose non-dominated schedules in a bounded action space.")
        self.play(Create(axes), FadeIn(xl), FadeIn(yl), FadeIn(dots), Create(lines), FadeIn(caveat))
        self.say("Lean only needs to verify the cost, terminal bound, and—where claimed—the bounded optimality certificate.")


class O07Robust(DeckSlide):
    title = "A human-facing recommendation should be robust, not overfitted"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        formula = boxed(math(r"\sup_{\theta\in\Theta}\TV(\delta_{\rm start}K_{\sigma,\theta},\Unif)\le\varepsilon", size=35, color=ERROR), ERROR).shift(UP * 0.8)
        rows = VGroup(
            boxed(para(r"cut bias interval", 3.4, 24), LOCAL),
            boxed(para(r"clumping / persistence interval", 3.4, 24), LOCAL),
            boxed(para(r"untouched-tail rate", 3.4, 24), LOCAL),
        ).arrange(RIGHT, buff=0.35).shift(DOWN * 0.65)
        bottom = para(r"Measure a person's operation times and plausible error parameters; optimize against the whole parameter set rather than declaring a single scalar ``shuffle efficiency.''", 10.7, 25).shift(DOWN * 1.95)
        self.say("The final recommendation system should tolerate uncertainty in the fitted human model. A parameter set is often more honest than a point estimate.")
        self.play(FadeIn(formula), FadeIn(rows), FadeIn(bottom))


class O08OperationalGoal(DeckSlide):
    title = "The end product is an operational theorem"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        statement = boxed(para(
            r"\textbf{Example target statement.} Under local model $M$, working-set bound $m$, cost ratio $\rho$ in interval $I$, and TV target $\varepsilon$, protocol $P$ has certified cost $C$; every protocol in bounded action class $\mathcal A$ with lower cost fails the target.",
            10.8,
            28,
        ), UNIFORM).shift(DOWN * 0.15)
        self.say("This is the bridge from shuffle mathematics to a recommendation someone can actually execute. It cleanly separates assumptions, cost, randomness target, and bounded optimality.")
        self.play(FadeIn(statement))
