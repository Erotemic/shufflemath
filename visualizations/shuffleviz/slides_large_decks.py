"""Part 2: large decks, Bernoulli--Laplace, and block dynamics."""
from __future__ import annotations

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Axes,
    Arrow,
    Create,
    Dot,
    FadeIn,
    FadeOut,
    LaggedStart,
    Line,
    Rectangle,
    ReplacementTransform,
    VGroup,
)

from shuffleviz import model
from shuffleviz.style import (
    ERROR,
    EXCHANGE,
    FG,
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
from shuffleviz.visual import dots_in_box, operation_box, packet, urn


class L01WorkingSet(DeckSlide):
    title = "The large-deck move: replace one impossible packet with two workable packets"
    kicker = "Commander reference problem: 99 cards split 50 / 49"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        whole = packet(99, FG, width=4.1, height=1.45, label="awkward whole deck").shift(UP * 0.65)
        left = packet(50, LOCAL, label="working pile A").shift(LEFT * 2.2 + DOWN * 1.1)
        right = packet(49, LOCAL, label="working pile B").shift(RIGHT * 2.2 + DOWN * 1.1)
        a1 = Arrow(whole.get_bottom() + LEFT * 0.45, left.get_top(), buff=0.12, color=LOCAL)
        a2 = Arrow(whole.get_bottom() + RIGHT * 0.45, right.get_top(), buff=0.12, color=LOCAL)
        self.say("The ergonomic constraint is the root of the problem. We can manipulate 49--50 cards comfortably even when 99 is awkward.")
        self.play(FadeIn(whole))
        self.say("The working-set split creates a new obstruction: cards in different packets cannot interact until we explicitly move them across the boundary.")
        self.play(FadeIn(left), FadeIn(right), Create(a1), Create(a2))


class L02NestoridiWhite(DeckSlide):
    title = "2019 · Nestoridi--White already studies shuffling large decks"
    kicker = "The nearest ancestor of our project"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        ops = VGroup(
            operation_box("split", EXCHANGE, width=1.35),
            operation_box("shuffle A", ORACLE, width=1.8, subtitle="perfect"),
            operation_box("shuffle B", ORACLE, width=1.8, subtitle="perfect"),
            operation_box("recombine", EXCHANGE, width=1.75),
            operation_box("cut / transfer", EXCHANGE, width=2.05),
        ).arrange(RIGHT, buff=0.35).shift(UP * 0.65)
        arrows = VGroup(*[
            Arrow(ops[i].get_right(), ops[i + 1].get_left(), buff=0.08, stroke_width=2, color=MUTED)
            for i in range(len(ops) - 1)
        ])
        point = boxed(para(r"Their local packets are \textbf{perfectly randomized}. Once a packet is uniform, another local shuffle has no effect, so local-shuffle count cannot be traded against repartition cost.", 10.5, 27), ORACLE).shift(DOWN * 1.2)
        cite = tex(r"Nestoridi \& White, \emph{Shuffling Large Decks of Cards and the Bernoulli--Laplace Urn Model}", size=18, color=MUTED).shift(DOWN * 2.45)
        self.say("This work establishes that the broad large-deck question is not novel. We inherit its membership-mixing viewpoint.\n[Sources] Nestoridi & White (2019), Shuffling Large Decks of Cards and the Bernoulli--Laplace Urn Model.")
        self.play(LaggedStart(*[FadeIn(o) for o in ops], lag_ratio=0.1), Create(arrows))
        self.say("The ideal local oracle is precisely the assumption we intend to remove.")
        self.play(FadeIn(point), FadeIn(cite))


class L03Macrostate(DeckSlide):
    title = "Perfect local randomization collapses 99! permutations to a 50-state statistic"
    kicker = r"$X =$ number of originally-left cards currently in the 50-card left pile"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        left = urn(1.35, ORACLE, "left pile: 50 cards").shift(LEFT * 2.35 + DOWN * 0.25)
        right = urn(1.35, ORACLE, "right pile: 49 cards").shift(RIGHT * 2.35 + DOWN * 0.25)
        ldots = dots_in_box(left[0], 15, EXCHANGE, cols=5, radius=0.07)
        rdots = dots_in_box(right[0], 10, LOCAL, cols=5, radius=0.07)
        formula = boxed(colored_math((r"X\in\{1,2,\ldots,50\}", ORACLE), size=36), ORACLE).shift(DOWN * 2.1)
        self.say("Conditional on which cards occupy each pile, perfect local randomization destroys all internal-order memory. The only remaining state is membership.")
        self.play(FadeIn(left), FadeIn(right), FadeIn(ldots), FadeIn(rdots))
        self.say("For the 50/49 split, X has only 50 feasible values. This is why exact Commander Bernoulli--Laplace calculations are tiny compared with 99!.")
        self.play(FadeIn(formula))


class L04Exchange(DeckSlide):
    title = "Bernoulli--Laplace: exchange $k$ uniformly sampled cards from each pile"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        left = urn(1.5, FG, "50").shift(LEFT * 2.5 + DOWN * 0.2)
        right = urn(1.5, FG, "49").shift(RIGHT * 2.5 + DOWN * 0.2)
        arrows = VGroup(
            Arrow(left.get_right() + UP * 0.35, right.get_left() + UP * 0.35, buff=0.08, color=EXCHANGE, stroke_width=5),
            Arrow(right.get_left() + DOWN * 0.35, left.get_right() + DOWN * 0.35, buff=0.08, color=EXCHANGE, stroke_width=5),
        )
        klabel = boxed(math(r"k", size=38, color=EXCHANGE), EXCHANGE).shift(UP * 0.95)
        formula = math(r"P_k(x,y)=\sum_a \Pr(a\ \text{left-origin cards leave})\Pr(y-x+a\ \text{return})", size=28).shift(DOWN * 2.0)
        self.say("The cross-working-set operation is itself a Markov kernel. Hypergeometric sampling gives an exact finite transition matrix.")
        self.play(FadeIn(left), FadeIn(right), FadeIn(klabel))
        self.say("The exchange size k is a control parameter, not a fixed law of nature.")
        self.play(Create(arrows), FadeIn(formula))


class L05K25(DeckSlide):
    title = "For 99 = 50 + 49, the first mode says: exchange about 25 cards"
    kicker = r"$\lambda_1(N,m,k)=1-\dfrac{Nk}{m(N-m)}$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        ks = list(range(15, 36))
        vals = [float(model.first_mode_factor(99, 50, k)) for k in ks]
        axes = Axes(x_range=[15, 35, 5], y_range=[-0.45, 0.45, 0.15], x_length=9.0, y_length=4.3, tips=False, axis_config={"color": MUTED}).shift(DOWN * 0.35)
        zero = Line(axes.c2p(15, 0), axes.c2p(35, 0), color=MUTED, stroke_width=1.5)
        pts = [axes.c2p(k, v) for k, v in zip(ks, vals)]
        curve = VGroup(*[Line(a, b, color=EXCHANGE, stroke_width=3.5) for a, b in zip(pts, pts[1:])])
        dots = VGroup(*[Dot(p, color=EXCHANGE if k != 25 else UNIFORM, radius=0.05 if k != 25 else 0.09) for k, p in zip(ks, pts)])
        callout = tex(r"nearest integer to $2450/99\approx24.747$", size=22, color=UNIFORM).next_to(axes.c2p(25, vals[10]), UP + RIGHT, buff=0.18)
        values = colored_math((r"\lambda_1(24)=37/1225", EXCHANGE), (r"\quad \lambda_1(25)=-1/98", UNIFORM), (r"\quad \lambda_1(26)=-62/1225", EXCHANGE), size=24).shift(DOWN * 2.55)
        self.say("The first nonconstant eigenmode crosses zero at a noninteger k. The nearest integer is 25.")
        self.play(Create(axes), Create(zero), Create(curve), FadeIn(dots))
        self.say("Lean currently certifies the finite arithmetic fact that k=25 minimizes the absolute value of this factor over 1 through 49; the symbolic eigenvalue theorem remains a target.")
        self.play(FadeIn(callout), FadeIn(values))


class L06CommanderTV(DeckSlide):
    title = "Membership memory collapses extremely fast under 25-card exchanges"
    kicker = "Exact 50-state computation from complete segregation"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        vals = model.commander_tv_series(25, 4)
        logs = [model.safe_log10(v, -7.0) for v in vals]
        axes = Axes(x_range=[0, 4, 1], y_range=[-7, 0, 1], x_length=8.8, y_length=4.5, tips=False, axis_config={"color": MUTED}).shift(DOWN * 0.35)
        points = [axes.c2p(k, v) for k, v in enumerate(logs)]
        lines = VGroup(*[Line(a, b, color=ERROR, stroke_width=4) for a, b in zip(points, points[1:])])
        dots = VGroup(*[Dot(p, color=ERROR if k < 2 else UNIFORM, radius=0.075) for k, p in enumerate(points)])
        labels = VGroup(*[tex(f"{v:.2g}", size=17, color=MUTED).next_to(p, UP, buff=0.08) for v, p in zip(vals, points)])
        ylab = tex(r"$\log_{10} d_{TV}$", size=20, color=MUTED).next_to(axes.y_axis, LEFT, buff=0.08)
        note = boxed(para(r"This is \textbf{only pile-membership mixing}. It is not yet a claim that two physical operations randomize the full deck.", 8.8, 23), ERROR).shift(DOWN * 2.55)
        self.say("The exact projected TV distance drops from about .84 after one exchange to .00248 after two and 2.58e-5 after three.")
        self.play(Create(axes), FadeIn(ylab), Create(lines), FadeIn(dots), FadeIn(labels))
        self.say("The warning is essential: this curve becomes a full-deck statement only under the perfect-local-randomization assumption.")
        self.play(FadeIn(note))


class L07UnequalUrns(DeckSlide):
    title = "2023 · unequal Bernoulli--Laplace theory matches the Commander asymmetry"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        left = boxed(para(r"\textbf{Known:} unequal urn sizes, unequal colors, exchange of $k$ objects, cutoff and spectral structure.", 5.7, 26), UNIFORM).shift(LEFT * 3.15 + DOWN * 0.25)
        right = boxed(para(r"\textbf{Formalize for us:} general admissible $N,m,k$ normalization, stationary law, reversibility, first eigenfunction and factor.", 5.7, 26), EXCHANGE).shift(RIGHT * 3.15 + DOWN * 0.25)
        cite = tex(r"Griffin--Hall--Hebner--Herzog--Selyuzhitsky--Wong--Wright, 2023", size=18, color=MUTED).shift(DOWN * 2.35)
        self.say("The 50/49 asymmetry is not an obstacle to theory. This paper is the natural spectral source for the general Bernoulli--Laplace formalization.\n[Sources] Griffin et al. (2023), Cutoff in the Bernoulli-Laplace Model With Unequal Colors and Urn Sizes.")
        self.play(FadeIn(left), FadeIn(right), FadeIn(cite))


class L08BlockDynamics(DeckSlide):
    title = "2024 · $S_k$ block dynamics is a neighboring working-set model"
    kicker = "Choose one contiguous block and perfectly shuffle it"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        cards = VGroup(*[Rectangle(width=0.42, height=0.68, stroke_color=FG, stroke_width=1.2, fill_opacity=0.02) for _ in range(24)])
        cards.arrange(RIGHT, buff=0.05).shift(DOWN * 0.15)
        block = Rectangle(width=4.6, height=0.94, stroke_color=ORACLE, stroke_width=3, fill_color=ORACLE, fill_opacity=0.08).move_to(cards[12])
        block.shift(LEFT * 0.15)
        label = tex(r"uniformly randomize this $k$-block", size=24, color=ORACLE).next_to(block, UP, buff=0.24)
        known = tex(r"Nestoridi--Priestley--Schmid, \emph{The $S_k$ Shuffle Block Dynamics}, 2024", size=19, color=MUTED).shift(DOWN * 1.7)
        difference = boxed(para(r"Close relative, different control surface: their local block update is an oracle; ours repeatedly applies an imperfect physical shuffle inside a bounded working set and separately pays to change membership.", 10.2, 24), EXCHANGE).shift(DOWN * 2.55)
        self.say("This is important prior art for partial-deck randomization. It prevents us from claiming novelty merely for updating a subdeck.\n[Sources] Nestoridi, Priestley & Schmid (2024), The S_k Shuffle Block Dynamics.")
        self.play(FadeIn(cards), FadeIn(block), FadeIn(label), FadeIn(known))
        self.say("Again the distinction is the oracle local shuffle versus finite-cost imperfect local steps.")
        self.play(FadeIn(difference))
