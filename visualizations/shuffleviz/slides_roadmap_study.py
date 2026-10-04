"""Study-course roadmap scenes: turn literature understanding into theorem interfaces."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Create, FadeIn, LaggedStart, Rectangle, VGroup

from shuffleviz.style import COST, EMPIRICAL, ERROR, EXCHANGE, FG, LOCAL, MUTED, ORACLE, UNIFORM, DeckSlide, boxed, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box


class MD00RoadmapPrimer(DeckSlide):
    title = "Part 5 goal: convert understanding into a theorem dependency graph"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("Model", r"What is the finite state space and the exact random operation?"),
            ("Invariant", r"What stationary law, symmetry, or sufficient statistic makes the model tractable?"),
            ("Quantify", r"What finite distance-to-target theorem do we need at the parameter sizes we actually use?"),
            ("Compose", r"What interface lets this component plug into the larger working-set protocol?"),
            ("Certify", r"Which claims belong in Lean, and which numerical search steps may remain ordinary untrusted computation?"),
        ], body_size=21).shift(DOWN * 0.05)
        self.say("The roadmap is not a chronological to-do list. It is a dependency graph from mathematical definitions to the operational theorem. Literature results matter insofar as they supply or motivate one of these interfaces.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.09))


class MD01DependencyDAG(DeckSlide):
    title = "The theorem dependency DAG"
    section = "Part 5 · formalization roadmap"

    def body(self):
        top = VGroup(
            boxed(tex("finite probability / kernels", size=20, color=FG), FG),
            boxed(tex("exact TV / Dobrushin", size=20, color=ERROR), ERROR),
        ).arrange(RIGHT, buff=0.7).shift(UP * 1.75)
        mid = VGroup(
            boxed(tex("GSR local kernel", size=20, color=LOCAL), LOCAL),
            boxed(tex("Bernoulli--Laplace exchange", size=20, color=EXCHANGE), EXCHANGE),
            boxed(tex("realistic local kernel", size=20, color=EMPIRICAL), EMPIRICAL),
        ).arrange(RIGHT, buff=0.55).shift(UP * 0.25)
        comp = boxed(tex("composition / perturbation theorem", size=22, color=UNIFORM), UNIFORM).shift(DOWN * 1.15)
        goal = boxed(tex("cost-optimal certified protocol", size=24, color=COST), COST).shift(DOWN * 2.35)
        arrows = VGroup()
        for a in top:
            for b in mid:
                arrows.add(Arrow(a.get_bottom(), b.get_top(), buff=0.08, color=MUTED, stroke_width=1.5, max_tip_length_to_length_ratio=0.08))
        for b in mid:
            arrows.add(Arrow(b.get_bottom(), comp.get_top(), buff=0.08, color=MUTED, stroke_width=1.7))
        arrows.add(Arrow(comp.get_bottom(), goal.get_top(), buff=0.08, color=MUTED, stroke_width=2.2))
        self.say("The important architecture is that GSR and a future measured human model are siblings behind the same local-kernel interface. Neither should be baked into the protocol semantics.")
        self.play(FadeIn(top), FadeIn(mid), FadeIn(comp), FadeIn(goal), Create(arrows))


class MD02MathLeanDictionary(DeckSlide):
    title = "Mathematics-to-Lean dictionary"
    section = "Part 5 · formalization roadmap"

    def body(self):
        grid = glossary_grid([
            ("finite distribution", r"`Convexity.StdSimplex Rat α` in the current exact finite layer"),
            ("Markov kernel", r"`α → Dist β`; composition is the finite bind / mixture operation"),
            ("stochastic matrix", r"derived computational/spectral view; rows lie in `Matrix.rowStochastic`"),
            ("TV distance", r"exact rational finite sum; theorem-facing metric for finite certificates"),
            ("Dobrushin coefficient", r"finite supremum/max of row-to-row TV distances"),
            ("stationary law", r"distribution equality `π K = π` or the matrix equivalent"),
            ("reversibility", r"pointwise detailed-balance equality under a candidate stationary law"),
            ("eigenfunction", r"finite function satisfying the Markov-operator equation `K f = λ • f`"),
            ("protocol", r"finite list/typed sequence of kernels plus a cost interpretation"),
            ("certificate", r"exact statement that a concrete protocol satisfies cost/error and optional bounded-optimality claims"),
        ], body_size=16).shift(DOWN * 0.05)
        self.say("This dictionary protects the formalization from becoming an unrelated parallel vocabulary. Each mathematical object introduced in the study deck should have one obvious formal representation.")
        self.play(FadeIn(grid))


class MD03BLFormalTargets(DeckSlide):
    title = "Bernoulli--Laplace: theorem-by-theorem formal target"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("BL-1 support", r"Characterize feasible count states $\max(0,m-(N-r))\le x\le\min(m,r)$."),
            ("BL-2 transition", r"Define the two hypergeometric samples $A,B$ and prove the single-sum formula for $P_k(x,y)$."),
            ("BL-3 stochastic", r"Prove nonnegativity and row normalization symbolically for general admissible $N,m,r,k$."),
            ("BL-4 stationary", r"Define $\pi(x)=\binom rx\binom{N-r}{m-x}/\binom Nm$ and prove normalization."),
            ("BL-5 reversible", r"Prove detailed balance $\pi(x)P(x,y)=\pi(y)P(y,x)$."),
            ("BL-6 first mode", r"Prove $f(x)=x-mr/N$ is an eigenfunction with $\lambda_1=1-Nk/[m(N-m)]$."),
            ("BL-7 projection", r"State precisely when the macro-count law gives the full-deck likelihood ratio/TV under perfect local randomization."),
            ("BL-8 finite cert", r"Retain executable exact Commander checks as regression/certificate theorems."),
        ], width=10.8, body_size=17).shift(DOWN * 0.05)
        self.say("This is the order I would formalize. It starts from the random experiment and builds structural theorems before reusing the existing Commander constants.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.06))


class MD04GSRFormalTargets(DeckSlide):
    title = "GSR: theorem-by-theorem formal target"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("GSR-1 inverse model", r"Define independent binary labels and stable sorting on labeled finite decks."),
            ("GSR-2 equivalence", r"Prove inverse labels induce the inverse of the forward binomial-cut/proportional-drop riffle law."),
            ("GSR-3 composition", r"Prove $k$ binary inverse riffles equal one uniform $2^k$-label stable sort."),
            ("GSR-4 descents", r"Characterize compatible label sequences for a fixed target permutation via weak inequalities and strict steps at descents."),
            ("GSR-5 count", r"Formalize the stars-and-bars count $\binom{a+n-r(\pi)}n$."),
            ("GSR-6 Eulerian", r"Count permutations by descents and collapse exact TV to the Eulerian sum."),
            ("GSR-7 local constants", r"Certify exact/rational or proved interval bounds for working-pile sizes 49 and 50 at the riffle counts used by protocols."),
        ], width=10.8, body_size=18).shift(DOWN * 0.05)
        self.say("The classical chapter was intentionally derived in the same order as this formal theorem ladder. The presentation should therefore become a direct proof-design reference rather than merely motivational material.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.07))


class MD05CompositionFormalTargets(DeckSlide):
    title = "Composition: theorem-by-theorem formal target"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("COMP-1 TV basics", r"Triangle inequality, convexity under common weights, and ordinary Markov-kernel contraction."),
            ("COMP-2 kernel error", r"Define $\Delta(K,L)=\max_x d_{TV}(K_x,L_x)$ and prove $d_{TV}(\mu K,\mu L)\le\Delta(K,L)$."),
            ("COMP-3 telescope", r"Prove the heterogeneous replacement bound for a finite list of actual/ideal kernels."),
            ("COMP-4 Dobrushin", r"Define $\delta(K)$ and prove quantitative contraction $d_{TV}(\mu K,\nu K)\le\delta(K)d_{TV}(\mu,\nu)$."),
            ("COMP-5 weighted telescope", r"For hybrids $H_i=L_1\cdots L_iK_{i+1}\cdots K_T$, prove the exact bound $\sum_i\Delta(K_i,L_i)\prod_{j>i}\delta(K_j)$."),
            ("COMP-6 protocol theorem", r"Combine actual-vs-ideal error with ideal-vs-uniform membership error."),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("This layer has the highest reuse value. Once complete, adding a new local model should not require reproving the large-deck theorem; the new model supplies a kernel approximation certificate and plugs in.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.08))


class MD06RealismFormalTargets(DeckSlide):
    title = "Realistic local models: formalize in increasing order of dependence"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("R-1 biased independent labels", r"General $\mathbf p$-shuffle kernel and product-label composition $\mathbf p\otimes\mathbf q$."),
            ("R-2 finite bounds", r"Strong-stationary/collision upper bound $\binom n2(\sum p_i^2)^k$ and sharper finite computations where needed."),
            ("R-3 correlated source", r"Finite-state source process for left/right labels, with a precise mapping from source words to stable-sort deck permutations."),
            ("R-4 repeated correlated shuffles", r"Define kernel powers/composition without assuming independent address coordinates."),
            ("R-5 measurement", r"Map observed human shuffles to a certified parameter uncertainty set $\Theta$."),
            ("R-6 robust bound", r"Prove/compute a uniform local approximation error over $\theta\in\Theta$."),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("Do not begin with the richest human model. The biased independent-label layer exercises the general local-kernel interface while retaining exact composition, then correlated models deliberately break that convenience.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.08))


class MD07WhatNotToFormalizeFirst(DeckSlide):
    title = "Deep literature to understand now, but not necessarily formalize first"
    section = "Part 5 · formalization roadmap"

    def body(self):
        grid = glossary_grid([
            ("full dual-Hahn theory", r"understand why it diagonalizes Bernoulli--Laplace; low eigenmodes may be enough for our first finite theorem"),
            ("asymptotic cutoff profiles", r"important conceptual validation; our first operational theorem needs finite $N=99$ bounds"),
            ("all quasisymmetric identities", r"understand the descent-set probability bridge; formalize only the identities used for our biased local kernel"),
            ("full $S_k$ cutoff proof", r"important neighboring block-dynamics theory, but not the kernel our physical protocol currently executes"),
            ("numerical optimizer internals", r"search can remain ordinary code; formalize the candidate certificate and bounded-optimality claim"),
            ("one fixed human fit", r"formalize a parameterized model and uncertainty set rather than baking in today's measurements"),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("A deep dive is not the same as a demand to formalize every theorem we study. Understanding the neighboring mathematics helps us choose elegant interfaces and recognize when a future obstacle already has a known tool.")
        self.play(FadeIn(grid))


class MD08ProofVsComputation(DeckSlide):
    title = "Where exact computation belongs versus symbolic proof"
    section = "Part 5 · formalization roadmap"

    def body(self):
        symbolic = boxed(para(r"\textbf{Symbolic theorem}\nNormalization, stationary law, reversibility, eigenfunction identity, GSR counting formula, TV contraction/telescope, and semantics of protocol composition. These should hold for general finite parameters.", 5.25, 21), UNIFORM).shift(LEFT * 3.0 + DOWN * 0.05)
        compute = boxed(para(r"\textbf{Executable certificate}\nExact 99-card TV constants, ranking bounded schedules, checking a concrete Pareto frontier, and evaluating rational bounds for a chosen measured parameter set. These may legitimately remain computations whose results are certified.", 5.25, 21), COST).shift(RIGHT * 3.0 + DOWN * 0.05)
        self.say("The elegance criterion is not 'replace all computation by proof.' It is 'prove the reusable structure once, compute the instance-specific facts exactly, and make the trusted boundary explicit.'")
        self.play(FadeIn(symbolic), FadeIn(compute))


class MD09StudyChecklist(DeckSlide):
    title = "Pre-formalization study checklist"
    kicker = "Do not start proving a chapter until these questions feel routine"
    section = "Part 5 · formalization roadmap"

    def body(self):
        rows = derivation_steps([
            ("Can I simulate it by hand?", r"For a tiny example, can I enumerate one transition and explain every probability?"),
            ("Can I derive the invariant?", r"Can I explain why the proposed stationary law is natural before manipulating formulas?"),
            ("Can I name the sufficient statistic?", r"What information is being forgotten, and what theorem makes that forgetting exact?"),
            ("Can I state the metric?", r"TV, separation, relative $L^\infty$, or something else -- and why is that metric relevant?"),
            ("Can I explain the proof tool?", r"Counting, coupling, spectral decomposition, second moment, strong stationary time, or perturbation -- what does it buy?"),
            ("Can I state our interface?", r"Which exact finite theorem from this chapter is consumed by the next chapter?"),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("This is the real purpose of the Manim deck. It is a gate for mathematical understanding before we encode proof details in Lean.")
        self.play(LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.08))


class MD10MasterGlossary(DeckSlide):
    title = "Master glossary: model boundaries at a glance"
    section = "Part 5 · formalization roadmap"

    def body(self):
        grid = glossary_grid([
            ("GSR", r"ideal riffle: binomial cut + order-preserving proportional interleave; inverse = fair independent labels + stable sort"),
            (r"$a$-shuffle", r"uniform independent $a$-valued inverse labels + stable sort"),
            (r"$\mathbf p$-shuffle", r"biased independent categorical inverse labels + stable sort"),
            ("clumpy/dealer", r"correlated left/right source labels favoring repeats / alternation"),
            ("Bernoulli--Laplace", r"membership chain induced by swapping uniformly sampled subsets between piles"),
            ("perfect-local oracle", r"exact uniform randomization inside each working pile"),
            (r"$S_k$ block dynamics", r"uniformly randomize a contiguous length-$k$ block when its clock rings"),
            (r"$d_{TV}$", r"finite probability distance and maximum event gap"),
            (r"$\Delta(K,L)$", r"worst-row approximation error between two kernels"),
            (r"$\delta(K)$", r"Dobrushin contraction coefficient of one kernel"),
            ("cutoff", r"asymptotically abrupt transition from unmixed to mixed"),
            ("strong stationary time", r"stopping time at which the chain's state is exactly stationary"),
            ("coupling", r"joint construction of two laws/chains used to bound their distance"),
            ("eigenmode", r"observable whose conditional expectation is scaled by one eigenvalue each step"),
            ("Pareto frontier", r"protocols not dominated simultaneously in cost and certified error"),
            ("robust protocol", r"one certified uniformly over a declared model-parameter uncertainty set"),
        ], body_size=14).scale(0.90).shift(DOWN * 0.05)
        self.say("This is the glossary to print beside the formalization work. Every loaded term in the project should reduce to one of these definitions rather than becoming local jargon.")
        self.play(FadeIn(grid))
