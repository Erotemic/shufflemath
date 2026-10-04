"""Deep-dive study scenes for Bernoulli--Laplace and large-deck shuffling."""
from __future__ import annotations

from fractions import Fraction

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Create, Dot, FadeIn, LaggedStart, Line, Rectangle, VGroup

from shuffleviz import model
from shuffleviz.style import ERROR, EXCHANGE, FG, LOCAL, MUTED, ORACLE, UNIFORM, DeckSlide, boxed, colored_math, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box, reminder_box
from shuffleviz.visual import dots_in_box, urn


SOURCE_NW = "Nestoridi and White (2019), Shuffling Large Decks of Cards and the Bernoulli--Laplace Urn Model."
SOURCE_UNEQUAL = "Griffin et al. (2023), Cutoff in the Bernoulli-Laplace Model With Unequal Colors and Urn Sizes."
SOURCE_SK = "Nestoridi, Priestley, and Schmid (2024), The S_k shuffle block dynamics."


class LD00PartPrimer(DeckSlide):
    title = "Part 2 notation: from cards to a two-urn membership chain"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        grid = glossary_grid([
            (r"$N$", r"total number of cards"),
            (r"$m$", r"size of the left working pile; right pile size is $N-m$"),
            (r"$r$", r"total number of marked/red cards; initially these may mean 'originally left'"),
            (r"$k$", r"number of cards sampled from each pile and swapped in one exchange"),
            (r"$X$", r"number of red cards currently in the left pile"),
            (r"$x,y$", r"particular old/new values of the random variable $X$"),
            (r"$P_k(x,y)$", r"probability one $k$-exchange moves count $x$ to count $y$"),
            (r"$\pi(x)$", r"stationary hypergeometric probability of count $x$"),
        ], body_size=18).shift(DOWN * 0.1)
        footer = tex(r"Commander specialization later: $N=99,\ m=50,\ r=50$.", size=22, color=UNIFORM).shift(DOWN * 2.65)
        self.say("This chapter uses r for the total number of red or originally-left cards, not for rising sequences. The notation is local to the chapter; this slide is the reset point.")
        self.play(FadeIn(grid), FadeIn(footer))


class LD01NestoridiWhiteProcedure(DeckSlide):
    title = "Nestoridi--White's two-pile $k$-cut shuffle, one operation at a time"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Split", r"Cut a $2n$-card deck into a top half and bottom half of $n$ cards each."),
            ("Perfect shuffle", r"Independently replace the order inside each half by a uniform random permutation."),
            ("Stack", r"Put the two shuffled halves back together in their original half order."),
            ("Deterministic cut", r"Move a fixed $k$ cards from the top of the deck to the bottom."),
            ("Repeat", r"On the next round, the two $n$-card halves are shuffled perfectly again."),
        ], body_size=21).shift(DOWN * 0.05)
        note = remember_box(r"Because the next round perfectly randomizes each half, the deterministic $k$-cut is equivalent at the membership level to swapping $k$ uniformly selected cards between the two halves.", width=10.8, size=22).shift(DOWN * 2.35)
        self.say(f"This exact procedure matters. Their local shuffle is an oracle: each half becomes perfectly uniform at every round. The following Bernoulli--Laplace reduction depends on that assumption.\n[Sources] {SOURCE_NW}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09), FadeIn(note))


class LD02PerfectLocalOracle(DeckSlide):
    title = "Definition: what does 'perfectly shuffle each pile' mean mathematically?"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        oracle = definition_box(
            "Perfect local randomization",
            r"Condition on exactly which labeled cards belong to a pile.  Replace their internal order by a uniform random permutation, independently of the other pile. All previous internal-order information is erased in one operation.",
            symbol=r"L_\infty",
            color=ORACLE,
        ).shift(UP * 0.62)
        implication = colored_math(
            (r"\text{membership fixed}", EXCHANGE),
            (r"\quad\Longrightarrow\quad", FG),
            (r"\text{internal order exactly uniform}", ORACLE),
            size=31,
        ).shift(DOWN * 0.75)
        warning = boxed(para(r"Our physical project cannot assume this for free.  A finite number of human riffles leaves residual local-order error, which later has to be propagated through the protocol.", 10.4, 24), ERROR).shift(DOWN * 1.65)
        self.say("This oracle is the conceptual seam between prior large-deck theory and our extension. Under the oracle, local mixing has zero residual error and zero need for repeated local shuffles.")
        self.play(FadeIn(oracle), FadeIn(implication), FadeIn(warning))


class LD03MembershipMicrostates(DeckSlide):
    title = "Why perfect local randomization lets us forget card order"
    kicker = "First forget positions within each pile; then exploit symmetry among card identities"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Label colors", r"Color the $r$ originally-left cards red and the remaining $N-r$ cards black."),
            ("Membership", r"After perfect local shuffles, the future membership dynamics do not depend on positions inside a pile."),
            ("Color symmetry", r"Cards with the same color enter the exchange rule symmetrically, so conditional on a count $X=x$, membership subsets of the same color composition have equal probability."),
            ("Macrostate", r"The likelihood of the color-membership process can therefore be represented by the single integer $X$: red cards in the left pile."),
        ], body_size=21).shift(DOWN * 0.15)
        self.say(f"Nestoridi and White explicitly use this color reduction after the perfect shuffle: it is why their symmetric-group walk can be analyzed as an urn chain.\n[Sources] {SOURCE_NW}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.10))


class LD04DefineStateX(DeckSlide):
    title = "The macrostate $X$ has a small, exactly known support"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        box = definition_box(
            "Membership count",
            r"$X$ is the number of the $r$ red cards that are currently in the left pile of size $m$.",
            symbol=r"X",
            color=EXCHANGE,
        ).shift(UP * 0.85)
        support = math(r"\max\{0,m-(N-r)\}\le X\le\min\{m,r\}", size=34, color=UNIFORM).shift(DOWN * 0.55)
        commander = math(r"N=99,m=50,r=50\quad\Longrightarrow\quad X\in\{1,\ldots,50\}", size=32).shift(DOWN * 1.45)
        self.say("The lower bound says the left pile cannot avoid holding some red cards if there are not enough black cards to fill it. For Commander there are only forty-nine black cards, so a fifty-card left pile must contain at least one red card.")
        self.play(FadeIn(box), FadeIn(support), FadeIn(commander))


class LD05HypergeometricPrimer(DeckSlide):
    title = "Mini-lesson: the hypergeometric law is sampling without replacement"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        definition = definition_box(
            "Hypergeometric probability",
            r"From a population with $g$ good and $b$ bad objects, draw $k$ objects uniformly without replacement. The probability of exactly $a$ good draws is the number of favorable $k$-subsets divided by all $k$-subsets.",
            symbol=r"\Pr(A=a)=\frac{\binom ga\binom b{k-a}}{\binom{g+b}k}",
            color=LOCAL,
        ).shift(UP * 0.62)
        example = derivation_steps([
            ("Population", r"3 red + 1 black card, draw one card."),
            ("Red draw", r"$\Pr(A=1)=\binom31\binom10/\binom41=3/4$."),
            ("Black draw", r"$\Pr(A=0)=\binom30\binom11/\binom41=1/4$."),
        ], width=9.7, body_size=22).shift(DOWN * 1.35)
        self.say("This is not a binomial draw: after one object is selected, the population changes. Hypergeometric coefficients will appear twice in every Bernoulli--Laplace transition, once for each urn.")
        self.play(FadeIn(definition), FadeIn(example))


class LD06StationaryCounting(DeckSlide):
    title = "Derive the stationary law by counting uniformly random left piles"
    kicker = r"$\pi(x)=\dfrac{\binom rx\binom{N-r}{m-x}}{\binom Nm}$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Uniform target", r"At full deck uniformity, every $m$-card subset is equally likely to occupy the left pile."),
            ("Denominator", r"There are $\binom Nm$ possible left-pile membership subsets."),
            ("Choose red", r"To have $X=x$, choose $x$ of the $r$ red cards: $\binom rx$ ways."),
            ("Choose black", r"Fill the other $m-x$ positions from the $N-r$ black cards: $\binom{N-r}{m-x}$ ways."),
            ("Divide", r"Favorable subsets / all subsets gives the hypergeometric stationary law."),
        ], body_size=20).shift(DOWN * 0.05)
        mean = math(r"\mathbb E_\pi[X]=\frac{mr}{N}", size=34, color=UNIFORM).shift(DOWN * 2.4)
        self.say("The stationary hypergeometric law is simply the distribution of red-card count in a uniformly random left subset. No spectral theory is needed to discover it.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.08), FadeIn(mean))


class LD07ExchangeVariables(DeckSlide):
    title = "One exchange is easiest to describe with two random counts"
    kicker = r"$X'=X-A+B$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        defs = VGroup(
            definition_box("$A$", r"number of red cards among the $k$ cards sampled from the left pile; these red cards leave the left pile", color=ERROR, width=5.35, body_size=20),
            definition_box("$B$", r"number of red cards among the $k$ cards sampled from the right pile; these red cards enter the left pile", color=UNIFORM, width=5.35, body_size=20),
        ).arrange(RIGHT, buff=0.4).shift(UP * 0.55)
        relation = colored_math((r"X'", FG), (r"=X", EXCHANGE), (r"-A", ERROR), (r"+B", UNIFORM), size=48).shift(DOWN * 0.85)
        independent = tex(r"Conditional on $X=x$, the two samples come from disjoint piles, so $A$ and $B$ are independent.", size=22, color=MUTED).shift(DOWN * 1.75)
        self.say("This identity is the entire transition mechanism. We start with x red cards in the left pile, subtract the red cards sent out, then add the red cards received from the right.")
        self.play(FadeIn(defs), FadeIn(relation), FadeIn(independent))


class LD08TransitionDerivation(DeckSlide):
    title = "Derive the exact transition probability $P_k(x,y)$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        left = math(r"\Pr(A=a\mid X=x)=\frac{\binom xa\binom{m-x}{k-a}}{\binom mk}", size=29, color=ERROR).shift(UP * 1.15)
        right = math(r"\Pr(B=b\mid X=x)=\frac{\binom{r-x}{b}\binom{(N-m)-(r-x)}{k-b}}{\binom{N-m}{k}}", size=27, color=UNIFORM).shift(UP * 0.35)
        constraint = math(r"y=x-a+b\quad\Longleftrightarrow\quad b=y-x+a", size=31, color=EXCHANGE).shift(DOWN * 0.55)
        result = math(
            r"P_k(x,y)=\sum_a \Pr(A=a\mid x)\Pr(B=y-x+a\mid x)",
            size=31,
        ).shift(DOWN * 1.45)
        note = tex("Terms with impossible draw counts are simply zero.", size=20, color=MUTED).shift(DOWN * 2.15)
        self.say("Once a is fixed, b is forced by the requested destination y. So the apparent two-dimensional count collapses to a single sum. This is the same simplification we used in the fast Lean executable certificate.")
        self.play(FadeIn(left), FadeIn(right), FadeIn(constraint), FadeIn(result), FadeIn(note))


class LD09ToyExample(DeckSlide):
    title = "Worked example: $N=8,m=4,r=4,k=1$ from state $X=3$"
    kicker = "Do the whole transition row by hand"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        setup = tex(r"left: 3 red + 1 black\qquad right: 1 red + 3 black", size=27, color=MUTED).shift(UP * 1.45)
        cases = derivation_steps([
            (r"$X'=2$", r"left sends red ($3/4$), right sends black ($3/4$): probability $9/16$."),
            (r"$X'=3$", r"both samples have the same color: $(3/4)(1/4)+(1/4)(3/4)=6/16$."),
            (r"$X'=4$", r"left sends black ($1/4$), right sends red ($1/4$): probability $1/16$."),
        ], width=10.4, body_size=21).shift(DOWN * 0.15)
        row = math(r"P(3,\cdot)=(0,0,9/16,6/16,1/16)\quad\text{for }y=0,1,2,3,4", size=29, color=UNIFORM).shift(DOWN * 2.05)
        check = math(r"9/16+6/16+1/16=1", size=26).shift(DOWN * 2.55)
        self.say("This small example is worth memorizing. Every large formula is just the same story with hypergeometric rather than one-card draws.")
        self.play(FadeIn(setup), LaggedStart(*[FadeIn(s) for s in cases], lag_ratio=0.12), FadeIn(row), FadeIn(check))


class LD10RowStochastic(DeckSlide):
    title = "Why every transition row sums to one"
    kicker = "A proof by probability, before a proof by binomial identities"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Sample", r"The pair $(A,B)$ has total probability one because each urn sample has a normalized hypergeometric law."),
            ("Map", r"Every realized pair $(A,B)$ determines exactly one destination $Y=x-A+B$."),
            ("Partition", r"The events $\{Y=y\}$ are disjoint and cover all outcomes."),
            ("Therefore", r"$\sum_yP_k(x,y)=1$ for every feasible state $x$."),
        ], body_size=22).shift(DOWN * 0.1)
        formal = remember_box(r"The symbolic Lean proof can realize this probabilistic partition directly, or reduce the sums to Vandermonde-type binomial identities. The theorem is structural, not Commander-specific.", width=10.6, size=22).shift(DOWN * 2.15)
        self.say("The native-decide row-stochastic certificate is useful, but this is the reusable proof idea we ultimately want formalized.")
        self.play(FadeIn(steps), FadeIn(formal))


class LD11DetailedBalanceDefinition(DeckSlide):
    title = "Reminder: detailed balance is a pairwise equilibrium identity"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        rem = reminder_box(
            "reversibility",
            r"A chain is reversible with stationary candidate $\pi$ when $\pi(x)P(x,y)=\pi(y)P(y,x)$ for every pair of states. It says stationary probability flow along each directed edge is exactly balanced by the reverse edge.",
            symbol=r"\pi(x)P(x,y)=\pi(y)P(y,x)",
            color=ORACLE,
        ).shift(UP * 0.5)
        implication = math(r"\text{detailed balance}\quad\Longrightarrow\quad\pi P=\pi", size=36, color=UNIFORM).shift(DOWN * 0.85)
        self.say("We repeat the definition because reversibility now does real work. It proves the hypergeometric law is stationary and later supports a self-adjoint spectral viewpoint.")
        self.play(FadeIn(rem), FadeIn(implication))


class LD12DetailedBalanceToy(DeckSlide):
    title = "Check detailed balance numerically in the 8-card toy chain"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        stationary = math(r"\pi(x)=\frac{\binom4x\binom4{4-x}}{\binom84}=\frac{1,16,36,16,1}{70}", size=31, color=ORACLE).shift(UP * 1.2)
        forward = math(r"\pi(3)P(3,4)=\frac{16}{70}\cdot\frac1{16}=\frac1{70}", size=32, color=EXCHANGE).shift(UP * 0.15)
        backward = math(r"\pi(4)P(4,3)=\frac1{70}\cdot1=\frac1{70}", size=32, color=UNIFORM).shift(DOWN * 0.75)
        why = para(r"From state 4 every left card is red and every right card is black, so a one-card swap must move to state 3. The unequal transition probabilities are exactly compensated by unequal stationary masses.", 10.5, 23).shift(DOWN * 1.75)
        self.say("Detailed balance does not mean P of x to y equals P of y to x. The stationary weights compensate. This tiny calculation is the pattern to recognize in the general identity.")
        self.play(FadeIn(stationary), FadeIn(forward), FadeIn(backward), FadeIn(why))


class LD13ReversibilityStationarity(DeckSlide):
    title = "Why Bernoulli--Laplace is reversible: reverse the same swap"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Microstate", r"Represent a state by the actual $m$-card membership subset in the left pile."),
            ("One move", r"Choose $k$ left cards and $k$ right cards uniformly and swap those two selected subsets."),
            ("Reverse", r"From the resulting membership subset, selecting those same two $k$-subsets reverses the move with the same sampling probability."),
            ("Uniform microstate law", r"Therefore the membership-subset chain is reversible under the uniform law on $m$-subsets."),
            ("Project", r"Lumping by red count $X$ gives the hypergeometric weights $\pi(x)$."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say(f"This microstate symmetry is the conceptual reversibility proof. The published two-pile model states the reversible transition matrix and hypergeometric stationary law explicitly.\n[Sources] {SOURCE_NW}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class LD14ConditionalExpectation(DeckSlide):
    title = "Derive the expected next membership count"
    kicker = r"$\mathbb E[X'\mid X=x]=x-\mathbb E[A\mid x]+\mathbb E[B\mid x]$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        means = VGroup(
            math(r"\mathbb E[A\mid x]=k\frac{x}{m}", size=31, color=ERROR),
            math(r"\mathbb E[B\mid x]=k\frac{r-x}{N-m}", size=31, color=UNIFORM),
        ).arrange(DOWN, buff=0.35).shift(UP * 0.7)
        expand = math(r"\mathbb E[X'\mid x]=x-k\frac{x}{m}+k\frac{r-x}{N-m}", size=35).shift(DOWN * 0.65)
        explanation = para(r"A simple sample mean gives each formula: a uniformly chosen card from the left is red with fraction $x/m$; a uniformly chosen card from the right is red with fraction $(r-x)/(N-m)$.", 10.4, 23).shift(DOWN * 1.6)
        self.say("We do not need the full transition matrix to discover the first eigenmode. First moments of the two hypergeometric samples are enough.")
        self.play(FadeIn(means), FadeIn(expand), FadeIn(explanation))


class LD15FirstEigenfunction(DeckSlide):
    title = "Center the count at equilibrium and an eigenfunction falls out"
    kicker = r"$\mu=mr/N$ and $f(x)=x-\mu$"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        steps = derivation_steps([
            ("Equilibrium mean", r"For the hypergeometric stationary law, $\mu=\mathbb E_\pi[X]=mr/N$."),
            (r"Subtract $\mu$", r"Take the conditional-mean formula and compute $\mathbb E[X'-\mu\mid X=x]$."),
            (r"Collect $x-\mu$", r"The constant terms cancel exactly, leaving a scalar multiple of the centered count."),
        ], body_size=21).shift(UP * 0.35)
        eig = math(r"\mathbb E[X'-\mu\mid X=x]=\left(1-\frac{Nk}{m(N-m)}\right)(x-\mu)", size=32, color=UNIFORM).shift(DOWN * 1.25)
        identify = colored_math((r"f(x)=x-\mu", LOCAL), (r"\qquad Pf=\lambda_1f", FG), (r"\qquad \lambda_1=1-\frac{Nk}{m(N-m)}", EXCHANGE), size=29).shift(DOWN * 2.05)
        self.say("This is the first nonconstant eigenfunction. It measures the simplest memory of the initial segregation: whether the left pile has too many or too few originally-left cards compared with equilibrium.")
        self.play(FadeIn(steps), FadeIn(eig), FadeIn(identify))


class LD16LambdaInterpretation(DeckSlide):
    title = r"Interpret $\lambda_1$: decay, cancellation, and overshoot"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        grid = glossary_grid([
            (r"$\lambda_1\approx1$", r"centered membership imbalance barely changes; this mode mixes slowly"),
            (r"$\lambda_1=0$", r"the expected centered imbalance is killed in one exchange"),
            (r"$0<\lambda_1<1$", r"imbalance keeps its sign but shrinks"),
            (r"$-1<\lambda_1<0$", r"imbalance overshoots the equilibrium mean and flips sign while shrinking"),
        ], body_size=20).shift(UP * 0.15)
        caution = remember_box(r"Making the first eigenvalue small does not prove the whole chain is mixed. Higher modes still matter. It is a principled explanation for why $k\approx m(N-m)/N$ is a promising exchange size, not a complete optimality theorem.", color=ERROR, width=10.8, size=22).shift(DOWN * 2.25)
        self.say("This distinction matters for k equals twenty-five. The first mode almost vanishes, which explains the dramatic improvement, but exact total variation still requires the full finite chain or stronger spectral control.")
        self.play(FadeIn(grid), FadeIn(caution))


class LD17CommanderParameters(DeckSlide):
    title = "Substitute the Commander numbers before looking at any plot"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        vals = derivation_steps([
            ("Deck", r"$N=99$: ninety-nine labeled cards total."),
            ("Working pile", r"$m=50$: left pile has fifty cards; right pile has forty-nine."),
            ("Color count", r"$r=50$: mark the cards originally in the left pile red."),
            ("Stationary mean", r"$\mu=mr/N=2500/99\approx25.253$."),
            ("Zero first mode", r"Solve $\lambda_1=0$: $k=m(N-m)/N=2450/99\approx24.747$."),
            ("Integer action", r"The nearest legal integer exchange size is $k=25$, giving $\lambda_1=-1/98$."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say("We can now predict k equals twenty-five without brute-force ranking. The exact ranking then checks whether higher modes change that local intuition.")
        self.play(LaggedStart(*[FadeIn(v) for v in vals], lag_ratio=0.08))


class LD18ProjectionFullDeckCaveat(DeckSlide):
    title = "When does membership TV equal full-deck TV?"
    kicker = "Only when the conditional microstate law is already the correct one"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        ideal = boxed(para(r"\textbf{Perfect-local oracle:} conditional on the current membership pattern, both pile orders are exactly uniform. Symmetry also makes microstates within a macro-count class equiprobable. Then the full likelihood ratio is constant on each class, so TV can collapse exactly to the count chain.", 5.45, 21), ORACLE).shift(LEFT * 3.1 + DOWN * 0.15)
        physical = boxed(para(r"\textbf{Finite physical riffles:} internal pile order can still remember the past. Two full-deck states with the same membership count need not have the same likelihood. The 50-state TV is then only a membership diagnostic, not the whole answer.", 5.45, 21), ERROR).shift(RIGHT * 3.1 + DOWN * 0.15)
        self.say("This is perhaps the most important caveat in part two. The state compression is exact under the oracle assumptions. Our new research problem begins precisely when local randomization is finite and imperfect.")
        self.play(FadeIn(ideal), FadeIn(physical))


class LD19MixingTheorems(DeckSlide):
    title = "What Nestoridi--White proves beyond the finite transition matrix"
    kicker = "Different regimes need different proof tools"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        grid = glossary_grid([
            ("small $k/n$", r"coupling gives an upper bound on the order of $(n/k)\log(n/\varepsilon)$ for the equal two-pile model"),
            ("$k/n\to b$", r"coupling gives logarithmic-in-$n$ upper bounds with constants depending on $b$"),
            (r"$k\approx n/2$", r"explicit spectral analysis with dual Hahn polynomials handles the near-half-exchange regime"),
            ("lower bounds", r"second-moment arguments show the chain cannot mix substantially earlier in appropriate regimes"),
        ], body_size=18).shift(UP * 0.15)
        target = remember_box(r"For our first formalization pass we do not need the entire asymptotic theory. We need the finite kernel, stationary law, reversibility, the first eigenfunction, and exact/certified protocol bounds. The deeper spectral results tell us what reusable structure exists if finite search stops scaling.", width=10.8, size=21).shift(DOWN * 2.25)
        self.say(f"The paper uses coupling, spherical-function or dual-Hahn spectral methods, and second-moment methods in different parameter regimes. We should understand those tools, but formalize only the interfaces our finite protocol theorem actually needs.\n[Sources] {SOURCE_NW}")
        self.play(FadeIn(grid), FadeIn(target))


class LD20LargeDeckGlossary(DeckSlide):
    title = "Large-deck / Bernoulli--Laplace glossary and checkpoint"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        grid = glossary_grid([
            ("perfect-local oracle", r"exact uniform randomization of each pile conditional on membership"),
            (r"$X$", r"red/original-left cards in the left pile"),
            ("hypergeometric", r"sampling without replacement; controls both exchange draws and the stationary count law"),
            (r"$A,B$", r"red cards leaving / entering the left pile in one exchange"),
            (r"$X'=X-A+B$", r"membership-count update equation"),
            (r"$P_k(x,y)$", r"one-step Bernoulli--Laplace transition probability"),
            (r"$\pi(x)$", r"hypergeometric stationary probability $\binom rx\binom{N-r}{m-x}/\binom Nm$"),
            ("reversible", r"stationary flow balances pairwise in both directions"),
            (r"$f(x)=x-mr/N$", r"first centered membership eigenfunction"),
            (r"$\lambda_1$", r"$1-Nk/[m(N-m)]$, its one-step decay/flip factor"),
            ("projection caveat", r"count-chain TV equals full-deck TV only when the conditional microstate distribution has the required symmetry/oracle form"),
            ("Commander", r"$N=99,m=50,r=50$; first mode nearly canceled by $k=25$"),
        ], body_size=16).scale(0.95).shift(DOWN * 0.1)
        self.say("Checkpoint: you should be able to derive the hypergeometric stationary law, the transition sum, and lambda one from the random experiment rather than memorizing the formulas.")
        self.play(FadeIn(grid))


class LD19ACoupling(DeckSlide):
    title = "Advanced tool: coupling turns convergence into a meeting-time problem"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "*"

    def body(self):
        box = definition_box(
            "Coupling",
            r"A joint random pair $(X,Y)$ whose marginals have the two distributions we want to compare.  We are free to correlate the pair strategically as long as each marginal law stays correct.",
            symbol=r"(X,Y)",
            color=LOCAL,
        ).shift(UP * 0.7)
        inequality = math(r"d_{TV}(\mathcal L(X),\mathcal L(Y))\le\Pr[X\ne Y]", size=38, color=UNIFORM).shift(DOWN * 0.55)
        chain = para(r"For Markov chains, run one copy from the difficult starting state and another copy from stationarity. Couple their random updates so that once they meet they move together forever. If $T$ is the meeting time, then $d_{TV}(P^t(x,\cdot),\pi)\le\Pr(T>t)$.", 10.5, 23).shift(DOWN * 1.55)
        self.say(f"Coupling is one of Nestoridi--White's upper-bound tools. The coupling inequality says we can upper-bound TV by constructing any convenient joint process that makes the two copies meet quickly.\n[Sources] {SOURCE_NW}")
        self.play(FadeIn(box), FadeIn(inequality), FadeIn(chain))


class LD19BPathCoupling(DeckSlide):
    title = "Advanced tool: path coupling proves global contraction from neighboring states"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Metric graph", r"Choose a distance $d(x,y)$ on states and identify elementary neighboring pairs, often those with $d=1$."),
            ("Local coupling", r"For each neighboring pair, couple one transition from $x$ and $y$ so that $\mathbb E[d(X',Y')]\le\beta d(x,y)$ with $\beta<1$."),
            ("Paths", r"Connect arbitrary $x$ and $y$ by a shortest path of neighboring states."),
            ("Glue", r"The local contraction extends along the path, giving exponential decay of expected distance for arbitrary starting pairs."),
            ("Mixing", r"Convert small expected distance / meeting probability into a TV upper bound."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say(f"Path coupling is valuable because a huge state space can have a simple local geometry. Nestoridi--White use coupling and path-coupling ideas for upper bounds in large-deck/urn models.\n[Sources] {SOURCE_NW}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class LD19CSpectralDecomposition(DeckSlide):
    title = "Advanced tool: spectral decomposition expands memory into eigenmodes"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "*"

    def body(self):
        rem = reminder_box(
            "eigenfunction",
            r"An observable $f$ satisfying $Pf=\lambda f$. Its expected value decays as $\lambda^t$ after $t$ steps.",
            symbol=r"Pf=\lambda f",
            color=LOCAL,
        ).shift(UP * 1.0)
        steps = derivation_steps([
            ("Reversible chain", r"Detailed balance makes the Markov operator self-adjoint in the weighted inner product $\langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)$."),
            ("Orthogonal modes", r"Self-adjoint finite operators admit an orthogonal eigenbasis. A general density/error can be decomposed into those modes."),
            ("Time evolution", r"After $t$ steps, a mode with eigenvalue $\lambda_j$ is multiplied by $\lambda_j^t$."),
            ("Slowest modes", r"Eigenvalues closest to $\pm1$ control long-lived memory; modes near zero disappear rapidly."),
        ], width=10.6, body_size=19).shift(DOWN * 0.85)
        self.say("This is the mathematical reason the first-mode calculation is informative. Full spectral analysis generalizes that idea from one centered-count statistic to a whole orthogonal basis of memory modes.")
        self.play(FadeIn(rem), FadeIn(steps))


class LD19DDualHahn(DeckSlide):
    title = "Why dual Hahn polynomials appear in Bernoulli--Laplace spectral theory"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "**"

    def body(self):
        definition = definition_box(
            "Orthogonal polynomial family",
            r"A sequence $p_0(x),p_1(x),\ldots$ such that $\sum_x\pi(x)p_i(x)p_j(x)=0$ for $i\ne j$.  For a reversible chain whose transition rule has the right algebraic structure, these polynomials can be eigenfunctions of the Markov operator.",
            color=LOCAL,
        ).shift(UP * 0.7)
        bl = boxed(para(r"For Bernoulli--Laplace, the stationary weight is hypergeometric and the relevant finite orthogonal-polynomial system is the dual Hahn family.  The degree-one member is the centered count $x-mr/N$ that we already derived directly; higher degrees encode higher-order membership fluctuations.", 10.4, 23), UNIFORM).shift(DOWN * 0.9)
        target = tex("Formalization strategy: derive low modes directly first; import the full polynomial machinery only if later bounds require it.", size=20, color=MUTED).shift(DOWN * 2.15)
        self.say(f"Nestoridi--White explicitly diagonalize the near-half-exchange two-pile chain using dual Hahn polynomials. The name is less important than the structure: hypergeometric stationary weights come with a natural orthogonal polynomial basis.\n[Sources] {SOURCE_NW}")
        self.play(FadeIn(definition), FadeIn(bl), FadeIn(target))


class LD19ESecondMomentLowerBound(DeckSlide):
    title = "Advanced tool: second moments prove a chain is still far from stationarity"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Choose a witness", r"Find a statistic $f$ whose expectation is very different under the time-$t$ law and stationary law."),
            ("Control variance", r"Bound $\mathrm{Var}(f)$ under both laws so the statistic is concentrated near its respective mean."),
            ("Separate events", r"Choose a threshold between the two means. Chebyshev or a sharper concentration inequality makes the two laws assign very different probabilities to the threshold event."),
            ("Convert to TV", r"The event characterization of total variation turns that probability gap into a lower bound on $d_{TV}$."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say(f"Nestoridi--White use second-moment methods for lower bounds. This is the same TV witness philosophy as the rising-sequence event in Bayer--Diaconis, but the witness statistic and concentration analysis are different.\n[Sources] {SOURCE_NW}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.10))


class LD21SKBlockDynamicsDeep(DeckSlide):
    title = "$S_k$ block dynamics: a different oracle-locality model"
    kicker = "Choose a contiguous block and replace its internal order by a uniform permutation"
    section = "Part 2 · large decks and Bernoulli--Laplace"

    def body(self):
        definition = definition_box(
            r"$S_k$ shuffle",
            r"On a deck of $N$ cards, each length-$k$ consecutive block has a rate-1 Poisson clock in the continuous-time formulation. When a block's clock rings, its $k$ cards are uniformly permuted while all cards outside the block stay fixed.",
            symbol=r"S_k",
            color=ORACLE,
        ).shift(UP * 0.55)
        compare = glossary_grid([
            (r"$k=2$", r"uniformly permuting two adjacent cards gives the adjacent-transposition dynamics"),
            (r"$k=N$", r"the whole deck is replaced by a uniform permutation in one block update"),
            ("their locality", r"spatial: a contiguous interval of positions is updated"),
            ("our locality", r"ergonomic: a bounded working set is physically shuffled, while membership changes require separate operations"),
        ], body_size=17).shift(DOWN * 1.25)
        self.say(f"The S-k paper studies TV mixing and cutoff for a block-dynamics model that interpolates between adjacent local moves and global uniform shuffling. It is important neighboring prior art, but its local update is again a perfect uniform oracle.\n[Sources] {SOURCE_SK}")
        self.play(FadeIn(definition), FadeIn(compare))

class LD19D2SymmetryReduction(DeckSlide):
    title = "Where the orthogonal polynomials come from: symmetry of the subset walk"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "**"

    def body(self):
        steps = derivation_steps([
            ("Microstates", r"A left-pile membership state is an $m$-subset $S\subset\{1,\ldots,N\}$.  There are $\binom Nm$ such microstates."),
            ("Group action", r"Relabeling the $N$ cards by any permutation in $S_N$ sends $m$-subsets to $m$-subsets and preserves the exchange rule."),
            ("Fix a reference", r"Relative to one reference subset $S_0$, two states are equivalent under the stabilizer of $S_0$ exactly when they have the same intersection size $|S\cap S_0|$."),
            ("Radial coordinate", r"That intersection size is the Bernoulli--Laplace count coordinate.  Functions depending only on it are the radial / orbit-invariant observables."),
        ], body_size=19).shift(DOWN * 0.05)
        self.say("The one-dimensional count chain is not an arbitrary trick. It is the radial part of a highly symmetric random walk on m-subsets. This symmetry is what makes an orthogonal-polynomial diagonalization possible.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class LD19D3GelfandPairPrimer(DeckSlide):
    title = "Advanced symmetry language: a Gelfand pair makes the radial algebra commutative"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "**"

    def body(self):
        box = definition_box(
            "Gelfand pair (working definition)",
            r"For a finite group $G$ and subgroup $H$, the pair $(G,H)$ is a Gelfand pair when the convolution algebra of functions constant on $H$-double-cosets is commutative.  Commutativity means the associated radial averaging operators can be simultaneously diagonalized.",
            symbol=r"(S_N,\ S_m\times S_{N-m})",
            color=LOCAL,
        ).shift(UP * 0.65)
        chain = derivation_steps([
            ("Double cosets", r"For the subset action, $H=S_m\times S_{N-m}$ preserves the reference left pile.  An $H$-double-coset is indexed by how many elements move across the boundary."),
            ("Commuting operators", r"Exchange kernels of different sizes live in the same commutative radial algebra, so they share a common eigenbasis."),
            ("Spherical functions", r"The common radial eigenfunctions are the zonal spherical functions of the pair; in this finite subset problem they are expressed by Hahn/dual-Hahn-type orthogonal polynomials."),
        ], width=10.5, body_size=18).shift(DOWN * 1.3)
        self.say(f"Nestoridi--White describe their near-half-exchange diagonalization using spherical-function theory and dual Hahn polynomials. This slide gives the structural reason those objects appear rather than treating the polynomial name as magic.\n[Sources] {SOURCE_NW}")
        self.play(FadeIn(box), FadeIn(chain))


class LD19D4SelfAdjointProof(DeckSlide):
    title = "Derive self-adjointness from detailed balance"
    kicker = r"\langle f,Pg\rangle_\pi=\langle Pf,g\rangle_\pi"
    section = "Part 2 · large decks and Bernoulli--Laplace"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Weighted inner product", r"Define $\langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)$."),
            ("Expand", r"$\langle f,Pg\rangle_\pi=\sum_{x,y}\pi(x)f(x)P(x,y)g(y)$."),
            ("Balance", r"Use $\pi(x)P(x,y)=\pi(y)P(y,x)$ to replace the stationary flow."),
            ("Swap dummy names", r"The sum becomes $\sum_{x,y}\pi(y)P(y,x)f(x)g(y)=\langle Pf,g\rangle_\pi$."),
            ("Consequence", r"Finite-dimensional self-adjoint operators have real eigenvalues and an orthogonal eigenbasis, giving a clean modal decomposition of mixing."),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("This proof is short enough that the deck should actually show it. It is the bridge from a combinatorial detailed-balance identity to the spectral theorem used in the deeper Bernoulli--Laplace analysis.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))
