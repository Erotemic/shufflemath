"""Part 0: mathematical language used throughout the shufflemath study course.

These scenes intentionally repeat definitions that an expert might normally
skip. The goal is that later literature slides never require the learner to
reverse-engineer notation from context.
"""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Create, Dot, FadeIn, LaggedStart, Line, Rectangle, VGroup

from shuffleviz.style import ERROR, FG, LOCAL, MUTED, PANEL, UNIFORM, DeckSlide, boxed, colored_math, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box


class F00StudyCourse(DeckSlide):
    title = "How to use this deck"
    kicker = "This is a study course, not a conference talk"
    section = "Part 0 · mathematical foundations"

    def body(self):
        rows = derivation_steps([
            ("Concrete first", r"Every new model starts with a small deck or urn example that can be followed by hand."),
            ("Define symbols", r"A symbol appears only after its state space, meaning, and units have been stated."),
            ("Derive", r"Important formulas are built from the random experiment rather than quoted as magic identities."),
            ("Generalize", r"Only after the finite example works do we state the literature theorem or asymptotic result."),
            ("Formalize", r"Each chapter ends by identifying the exact finite theorem interface we eventually want in Lean."),
        ], body_size=22).shift(DOWN * 0.2)
        self.say("Treat this as a course you can pause and revisit. The deliberate redundancy is a feature: later parts repeat definitions rather than assuming you remember a symbol from forty scenes ago.")
        self.play(LaggedStart(*[FadeIn(r, shift=RIGHT * 0.12) for r in rows], lag_ratio=0.08))


class F01StateSpace(DeckSlide):
    title = "Definition: a state space lists every configuration the model distinguishes"
    kicker = r"We write the finite state space as $\Omega$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        definition = definition_box(
            "State space",
            r"A finite set $\Omega$ whose elements are the configurations we choose to track.  A model may deliberately forget information: the full deck uses permutations; the Bernoulli--Laplace projection later remembers only a membership count.",
            symbol=r"\Omega",
        ).shift(UP * 0.55)
        examples = VGroup(
            boxed(math(r"\Omega=S_{52}", size=31, color=LOCAL), LOCAL, 0.22),
            boxed(math(r"\Omega=\{0,1,2,3,4\}", size=31, color=UNIFORM), UNIFORM, 0.22),
        ).arrange(RIGHT, buff=0.65).shift(DOWN * 1.45)
        labels = VGroup(
            tex("all 52-card permutations", size=20, color=MUTED).next_to(examples[0], DOWN, buff=0.13),
            tex("a five-state membership count", size=20, color=MUTED).next_to(examples[1], DOWN, buff=0.13),
        )
        self.say("A state is not necessarily the whole physical world. It is exactly the information the mathematical model retains. Losing information can be a theorem-backed symmetry reduction, or it can be an invalid approximation; we must distinguish those cases.")
        self.play(FadeIn(definition), FadeIn(examples), FadeIn(labels))


class F02Distribution(DeckSlide):
    title = "Definition: a probability distribution assigns mass to states"
    kicker = r"$\mu(x)\ge0$ and $\sum_{x\in\Omega}\mu(x)=1$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        box = definition_box(
            "Distribution / law",
            r"A function $\mu:\Omega\to[0,1]$ with total mass one.  It describes uncertainty about the current state, not one particular sampled state.",
            symbol=r"\mu",
        ).shift(UP * 0.78)
        point = colored_math((r"\delta_x(y)=", FG), (r"\mathbf 1\{y=x\}", LOCAL), size=34).shift(DOWN * 0.55 + LEFT * 2.7)
        uniform = colored_math((r"U(y)=", FG), (r"1/|\Omega|", UNIFORM), size=34).shift(DOWN * 0.55 + RIGHT * 2.7)
        captions = VGroup(
            tex("point mass: state known exactly", size=20, color=MUTED).next_to(point, DOWN, buff=0.15),
            tex("uniform law: every state equally likely", size=20, color=MUTED).next_to(uniform, DOWN, buff=0.15),
        )
        self.say("Two distributions recur constantly. Delta sub x means all mass sits at one starting configuration. U is the uniform target. A shuffle acts on distributions, taking the initial law toward U.")
        self.play(FadeIn(box), FadeIn(point), FadeIn(uniform), FadeIn(captions))


class F03PermutationConvention(DeckSlide):
    title = "Permutation convention: order and inverse answer different questions"
    section = "Part 0 · mathematical foundations"

    def body(self):
        order = boxed(math(r"\pi=[1,4,2,5,6,3,7,8]", size=33, color=LOCAL), LOCAL).shift(UP * 0.95)
        meaning1 = para(r"One-line order: position 1 contains card 1, position 2 contains card 4, and so on.", 9.6, 24).next_to(order, DOWN, buff=0.2)
        inv = boxed(math(r"\pi^{-1}=[1,3,6,2,4,5,7,8]", size=33, color=UNIFORM), UNIFORM).shift(DOWN * 0.9)
        meaning2 = para(r"Inverse order: original card 1 is at position 1, original card 2 is at position 3, original card 3 is at position 6, and so on.", 9.6, 24).next_to(inv, DOWN, buff=0.18)
        self.say("We will be explicit about permutation orientation because the inverse-riffle description is much simpler than the forward physical permutation. The two contain the same information, but different statistics are visually natural on them.")
        self.play(FadeIn(order), FadeIn(meaning1), FadeIn(inv), FadeIn(meaning2))


class F04RandomVariableAndLaw(DeckSlide):
    title = "Definition: a random variable extracts a statistic from a random state"
    kicker = r"$X:\Omega\to\mathcal X$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        definition = definition_box(
            "Random variable",
            r"A deterministic function of the random state.  The randomness is in the sampled state $\omega\sim\mu$; the map $X(\omega)$ merely records a feature we care about.",
            symbol=r"X",
        ).shift(UP * 0.65)
        example = colored_math(
            (r"X(\pi)=", FG),
            (r"\#\{\text{original-left cards now in the left pile}\}", UNIFORM),
            size=29,
        ).shift(DOWN * 0.75)
        law = math(r"\Pr_\mu[X=x]=\sum_{\omega:X(\omega)=x}\mu(\omega)", size=31).shift(DOWN * 1.65)
        self.say("A key strategy in this project is to find a random variable whose law is much smaller than the original state space, but still controls the likelihood ratio we care about. Rising-sequence count does this for ideal riffles; membership count does it under a perfect local-shuffle oracle.")
        self.play(FadeIn(definition), FadeIn(example), FadeIn(law))


class F05MarkovKernel(DeckSlide):
    title = "Definition: a Markov kernel is one randomized operation"
    kicker = r"$K(x,y)=\Pr[X_{t+1}=y\mid X_t=x]$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        box = definition_box(
            "Markov kernel",
            r"For each current state $x$, $K(x,\cdot)$ is a probability distribution over next states. Thus $K(x,y)\ge0$ and every row sums to one.",
            symbol=r"K:\Omega\times\Omega\to[0,1]",
        ).shift(UP * 0.65)
        rows = math(r"\forall x:\qquad \sum_{y\in\Omega}K(x,y)=1", size=36, color=UNIFORM).shift(DOWN * 0.7)
        examples = tex(r"Examples later: one riffle $R$, one $k$-card exchange $X_k$, one perfect-local oracle $L_\infty$.", size=23, color=MUTED).shift(DOWN * 1.65)
        self.say("A kernel is the common language that lets us compose physically different operations. Riffles, transfers, perfect local randomization, and fitted human models can all expose the same interface.")
        self.play(FadeIn(box), FadeIn(rows), FadeIn(examples))


class F06MatrixUpdate(DeckSlide):
    title = "A distribution moves through a kernel by averaging its rows"
    kicker = r"$(\mu K)(y)=\sum_x\mu(x)K(x,y)$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        steps = derivation_steps([
            ("Start", r"The current state equals $x$ with probability $\mu(x)$."),
            ("Conditional move", r"Given $x$, the operation reaches $y$ with probability $K(x,y)$."),
            ("Multiply", r"The joint contribution through $x$ is $\mu(x)K(x,y)$."),
            ("Sum paths", r"Sum over every possible old state: $(\mu K)(y)=\sum_x\mu(x)K(x,y)$."),
        ], body_size=23).shift(DOWN * 0.1)
        self.say("This is just the law of total probability. Matrix notation is useful because a row probability vector multiplied by a row-stochastic matrix performs exactly this update.")
        self.play(LaggedStart(*[FadeIn(s, shift=RIGHT * 0.1) for s in steps], lag_ratio=0.12))


class F07KernelComposition(DeckSlide):
    title = "Composition remembers execution order"
    kicker = r"$(KL)(x,z)=\sum_yK(x,y)L(y,z)$ means: first $K$, then $L$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        x = boxed(tex("state $x$", size=26), LOCAL).shift(LEFT * 4.2)
        y = boxed(tex("intermediate $y$", size=26), MUTED).shift(LEFT * 0.2)
        z = boxed(tex("state $z$", size=26), UNIFORM).shift(RIGHT * 4.2)
        a1 = Arrow(x.get_right(), y.get_left(), color=LOCAL, buff=0.15)
        a2 = Arrow(y.get_right(), z.get_left(), color=UNIFORM, buff=0.15)
        k = math(r"K(x,y)", size=25, color=LOCAL).next_to(a1, UP, buff=0.1)
        l = math(r"L(y,z)", size=25, color=UNIFORM).next_to(a2, UP, buff=0.1)
        formula = math(r"(KL)(x,z)=\sum_yK(x,y)L(y,z)", size=36).shift(DOWN * 1.6)
        self.say("We use row-vector convention. The product KL means execute K first and L second. We will repeat this reminder when protocols become long, because reversing this convention silently changes the physical algorithm.")
        self.play(FadeIn(x), FadeIn(y), FadeIn(z), Create(a1), Create(a2), FadeIn(k), FadeIn(l), FadeIn(formula))


class F08Stationary(DeckSlide):
    title = "Definition: a stationary distribution is unchanged by one step"
    kicker = r"$\pi K=\pi$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        box = definition_box(
            "Stationary distribution",
            r"A distribution $\pi$ satisfying $\pi K=\pi$. If the chain starts from $\pi$, applying one more transition does not change its law.",
            symbol=r"\pi",
        ).shift(UP * 0.65)
        warning = boxed(para(r"Stationary does \emph{not} by itself mean the chain converges to $\pi$.  Irreducibility, periodicity, or other structure controls convergence.", 10.0, 24), ERROR).shift(DOWN * 1.25)
        self.say("Uniform is stationary for many card shuffles because shuffling a uniformly random deck leaves it uniform. Bernoulli--Laplace has a hypergeometric stationary law after we project to a count statistic.")
        self.play(FadeIn(box), FadeIn(warning))


class F09Reversible(DeckSlide):
    title = "Definition: reversibility balances probability flow pairwise"
    kicker = r"$\pi(x)K(x,y)=\pi(y)K(y,x)$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        box = definition_box(
            "Detailed balance / reversibility",
            r"Under stationary weights $\pi$, the probability current from $x$ to $y$ exactly matches the current from $y$ to $x$. A kernel with this property is reversible with respect to $\pi$.",
            symbol=r"\pi(x)K(x,y)=\pi(y)K(y,x)",
        ).shift(UP * 0.58)
        deriv = math(r"\sum_x\pi(x)K(x,y)=\sum_x\pi(y)K(y,x)=\pi(y)\sum_xK(y,x)=\pi(y)", size=30).shift(DOWN * 1.15)
        note = tex("Detailed balance is stronger than stationarity, but often much easier to verify combinatorially.", size=21, color=MUTED).shift(DOWN * 2.0)
        self.say("Pairwise balance immediately implies stationarity: sum the detailed-balance identity over x. This trick will reappear in the Bernoulli--Laplace chapter.")
        self.play(FadeIn(box), FadeIn(deriv), FadeIn(note))


class F10TVDefinition(DeckSlide):
    title = "Definition: total variation is the mass that must be rearranged"
    kicker = r"$d_{TV}(\mu,\nu)=\tfrac12\sum_x|\mu(x)-\nu(x)|$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        box = definition_box(
            "Total variation distance",
            r"For two distributions on the same finite state space, add the absolute probability discrepancies and divide by two. The factor $1/2$ avoids counting mass removed from one state and added to another twice.",
            symbol=r"d_{TV}(\mu,\nu)",
        ).shift(UP * 0.75)
        toy = derivation_steps([
            ("Example", r"$\mu=(1/2,1/2,0)$ and $\nu=(1/3,1/3,1/3)$."),
            ("Differences", r"Absolute differences are $1/6,1/6,1/3$."),
            ("Distance", r"Half their sum is $\tfrac12(2/3)=1/3$."),
        ], width=9.4, body_size=22).shift(DOWN * 1.25)
        self.say("TV ranges from zero to one. Zero means identical distributions. One means disjoint supports: observing the state tells you perfectly which distribution generated it.")
        self.play(FadeIn(box), FadeIn(toy))


class F11TVEventForm(DeckSlide):
    title = "Equivalent view: TV is the best distinguishing event"
    kicker = r"$d_{TV}(\mu,\nu)=\max_{A\subseteq\Omega}|\mu(A)-\nu(A)|$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        event = definition_box(
            "Event",
            r"Any subset $A\subseteq\Omega$. Saying '$A$ occurred' means the sampled state landed in that subset. We write $\mu(A)=\sum_{x\in A}\mu(x)$.",
            symbol=r"A\subseteq\Omega",
            color=LOCAL,
        ).shift(UP * 0.8)
        formula = math(r"d_{TV}(\mu,\nu)=\max_A|\mu(A)-\nu(A)|", size=40, color=UNIFORM).shift(DOWN * 0.65)
        intuition = remember_box(r"To prove a lower bound on TV, invent an event that one law makes substantially more likely than the other.  Bayer--Diaconis does exactly this with a low-rising-sequence event.", width=10.7, size=23).shift(DOWN * 1.7)
        self.say("This characterization turns a norm into a guessing game. If an event has probability .65 under the shuffled law and .316 under uniform, that single event already witnesses TV at least .334.")
        self.play(FadeIn(event), FadeIn(formula), FadeIn(intuition))


class F12TVContraction(DeckSlide):
    title = "A common randomized post-processing step cannot increase TV"
    kicker = r"$d_{TV}(\mu K,\nu K)\le d_{TV}(\mu,\nu)$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        steps = derivation_steps([
            ("Expand", r"$(\mu K)(y)-(\nu K)(y)=\sum_x(\mu(x)-\nu(x))K(x,y)$."),
            ("Triangle", r"$|\sum_x a_xK(x,y)|\le\sum_x|a_x|K(x,y)$ because $K(x,y)\ge0$."),
            ("Sum over $y$", r"Swap the finite sums and use $\sum_yK(x,y)=1$."),
            ("Conclude", r"The $\ell_1$ difference can only shrink; dividing by two gives the TV inequality."),
        ], body_size=21).shift(DOWN * 0.1)
        self.say("This is the data-processing principle we will use in the perturbation theorem. Once two laws have become close, applying the same future randomized operations cannot make them farther apart in TV.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.11))


class F13MarkovEigenfunction(DeckSlide):
    title = "Eigenfunctions track modes of memory"
    kicker = r"$(Kf)(x)=\mathbb E[f(X_{t+1})\mid X_t=x]$"
    section = "Part 0 · mathematical foundations"

    def body(self):
        operator = definition_box(
            "Markov operator on observables",
            r"Instead of pushing distributions forward, a kernel can act backward on a statistic $f$: $(Kf)(x)=\sum_yK(x,y)f(y)$, the conditional expectation of the next statistic given the current state.",
            symbol=r"Kf",
            color=LOCAL,
        ).shift(UP * 0.75)
        eig = math(r"Kf=\lambda f\qquad\Longrightarrow\qquad \mathbb E[f(X_t)\mid X_0=x]=\lambda^t f(x)", size=33, color=UNIFORM).shift(DOWN * 0.7)
        meaning = para(r"$|\lambda|$ near 1 means this mode decays slowly.  $\lambda=0$ kills the mode in one step.  A negative eigenvalue flips its sign while shrinking by $|\lambda|$.", 10.4, 24).shift(DOWN * 1.65)
        self.say("This language explains why exchange size twenty-five is special for Commander. The centered membership count is an eigenfunction, and its eigenvalue is almost zero at k equals twenty-five.")
        self.play(FadeIn(operator), FadeIn(eig), FadeIn(meaning))


class F14MixingTime(DeckSlide):
    title = "Definition: mixing time asks when every starting state is close to stationarity"
    section = "Part 0 · mathematical foundations"

    def body(self):
        formula = math(r"t_{\mathrm{mix}}(\varepsilon)=\min\Big\{t:\max_x d_{TV}(K^t(x,\cdot),\pi)\le\varepsilon\Big\}", size=35, color=UNIFORM).shift(UP * 0.4)
        glossary = glossary_grid([
            (r"$K^t(x,\cdot)$", r"law after $t$ steps when the chain started exactly at state $x$"),
            (r"$\pi$", r"the stationary target law"),
            (r"$\max_x$", r"worst-case starting state; no favorable initialization is assumed"),
            (r"$\varepsilon$", r"the tolerance chosen for 'close enough'"),
        ], body_size=19).shift(DOWN * 1.15)
        self.say("Mixing time belongs to a family of chains or to a specific finite chain with a chosen tolerance. Always ask: which metric, which starting states, which epsilon, and which kernel?")
        self.play(FadeIn(formula), FadeIn(glossary))


class F15Cutoff(DeckSlide):
    title = "Definition: cutoff is an abrupt asymptotic mixing transition"
    kicker = "It is stronger than merely having a mixing time"
    section = "Part 0 · mathematical foundations"

    def body(self):
        axes = VGroup(
            Line(LEFT * 4.3 + DOWN * 1.2, RIGHT * 4.3 + DOWN * 1.2, color=MUTED),
            Line(LEFT * 4.3 + DOWN * 1.2, LEFT * 4.3 + UP * 1.6, color=MUTED),
        )
        curve = VGroup(
            Line(LEFT * 4.0 + UP * 1.35, LEFT * 0.55 + UP * 1.25, color=ERROR, stroke_width=4),
            Line(LEFT * 0.55 + UP * 1.25, RIGHT * 0.45 + DOWN * 0.85, color=ERROR, stroke_width=4),
            Line(RIGHT * 0.45 + DOWN * 0.85, RIGHT * 4.0 + DOWN * 1.05, color=ERROR, stroke_width=4),
        )
        labels = VGroup(
            tex("distance near 1", size=20, color=MUTED).shift(LEFT * 3.0 + UP * 1.7),
            tex("narrow transition window", size=20, color=UNIFORM).shift(RIGHT * 0.35 + UP * 0.35),
            tex("distance near 0", size=20, color=MUTED).shift(RIGHT * 3.0 + DOWN * 1.5),
        )
        note = remember_box(r"For a sequence of growing chains, cutoff means the drop from unmixed to mixed happens in a window whose width is negligible compared with the mixing-time scale.", width=10.6, size=23).shift(DOWN * 2.35)
        self.say("The seven-riffle phenomenon is a finite manifestation of a cutoff-scale result. Do not interpret cutoff as a literal discontinuity or as a claim that a single integer suddenly makes the distribution uniform.")
        self.play(Create(axes), Create(curve), FadeIn(labels), FadeIn(note))


class F16FoundationsGlossary(DeckSlide):
    title = "Foundations glossary"
    kicker = "Reference slide — return here whenever later notation feels slippery"
    section = "Part 0 · mathematical foundations"

    def body(self):
        grid = glossary_grid([
            (r"$\Omega$", r"finite state space: configurations retained by the model"),
            (r"$\mu,\nu,\pi$", r"probability distributions; $\pi$ usually denotes a stationary law"),
            (r"$\delta_x$", r"point mass concentrated at state $x$"),
            (r"$U$", r"uniform distribution on the current finite state space"),
            (r"$K(x,y)$", r"Markov kernel: probability of next state $y$ given current state $x$"),
            (r"$\mu K$", r"distribution after applying kernel $K$ once"),
            (r"$KL$", r"composition: first $K$, then $L$ under our row-vector convention"),
            (r"$d_{TV}$", r"total variation distance; also the largest event-probability gap"),
            (r"$Kf$", r"conditional expectation of observable $f$ after one step"),
            (r"$\lambda$", r"eigenvalue: multiplicative decay/flip factor of an eigenmode"),
            (r"$t_{mix}(\varepsilon)$", r"first time every initial state is within TV tolerance $\varepsilon$ of stationarity"),
            ("cutoff", r"asymptotically sharp drop from far to close in a relatively narrow time window"),
        ], body_size=16).scale(0.94).shift(DOWN * 0.15)
        self.say("This glossary is intentionally part of the live deck. The point is not to memorize everything now; it is to have a stable vocabulary to return to as the models become more specialized.")
        self.play(FadeIn(grid))

class F04BProjectionAndLumping(DeckSlide):
    title = "Projection versus lumping: when is a smaller state space exact?"
    kicker = r"A statistic $\phi:\Omega\to\mathcal X$ always defines a projection; only some projections define a closed Markov chain"
    section = "Part 0 · mathematical foundations"

    def body(self):
        defs = VGroup(
            definition_box(
                "Projection / statistic",
                r"A deterministic map $\phi$ that forgets part of the state.  The projected random variable is $X=\phi(\omega)$.  This is always legitimate as a way to record less information.",
                symbol=r"\phi:\Omega\to\mathcal X",
                color=LOCAL,
                width=5.35,
                body_size=20,
            ),
            definition_box(
                "Strong lumping",
                r"The projection is Markov on its own when every two microstates $\omega,\omega'$ with the same macrostate have identical total transition probability into every macrostate class.",
                symbol=r"\sum_{\phi(\eta)=y}K(\omega,\eta)=\sum_{\phi(\eta)=y}K(\omega',\eta)",
                color=UNIFORM,
                width=5.35,
                body_size=18,
            ),
        ).arrange(RIGHT, buff=0.35).shift(UP * 0.4)
        warning = remember_box(
            r"A small projected chain can be useful even without exact lumping, but then its TV distance is only a diagnostic.  To replace the full chain exactly, prove the symmetry/lumping statement or prove that conditional microstates have the required law.",
            color=ERROR,
            width=10.8,
            size=21,
        ).shift(DOWN * 1.65)
        self.say("This distinction prevents a recurring mistake. Counting red cards in an urn is always a valid statistic. Treating that count as the whole Markov state requires additional symmetry. Under the perfect-local oracle that symmetry is exact; under finite riffles it need not be.")
        self.play(FadeIn(defs), FadeIn(warning))
