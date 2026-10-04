"""Deep-dive study scenes for biased and correlated riffle models."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Create, FadeIn, LaggedStart, Line, Rectangle, VGroup

from shuffleviz.style import EMPIRICAL, ERROR, FG, LOCAL, MUTED, UNIFORM, DeckSlide, boxed, colored_math, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box, reminder_box


SOURCE_FULMAN = "Fulman (1998), The combinatorics of biased riffle shuffles."
SOURCE_ADS = "Assaf, Diaconis, and Soundararajan (2012), Riffle shuffles with biased cuts."
SOURCE_JM = "Jonasson and Morris (2015), Rapid mixing of dealer shuffles and clumpy shuffles."
SOURCE_SSW = "Sellke, Shi, and Wang (2025), Universality of Cutoff for Riffle Shuffling."


class RD00PartPrimer(DeckSlide):
    title = "Part 3 vocabulary: three different ways a human riffle can deviate from Gilbert--Shannon--Reeds (GSR)"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        grid = glossary_grid([
            ("cut bias", r"the two packet sizes are not distributed like a fair binomial split"),
            ("interleave bias", r"given the packet sizes, the next card may not be chosen in the ideal proportional-to-remaining way"),
            ("clumping", r"successive source labels are positively correlated, producing longer same-hand runs"),
            ("dealer behavior", r"successive source labels are negatively correlated, favoring alternation"),
            (r"$\mathbf p$", r"probability vector for inverse labels in a general biased $a$-shuffle"),
            ("measured model", r"a kernel family whose parameters are estimated from a person's actual shuffles"),
        ], body_size=18).shift(DOWN * 0.05)
        warning = remember_box(r"Do not use 'imperfect riffle' as one scalar defect. Different physical failures change different parts of the probability law and therefore require different mathematics.", color=ERROR, width=10.8, size=22).shift(DOWN * 2.35)
        self.say("This chapter separates mechanisms that are often conflated. A biased cut with ideal interleaving is mathematically different from a fair cut followed by clumpy release behavior.")
        self.play(FadeIn(grid), FadeIn(warning))


class RD01BiasedTwoShuffle(DeckSlide):
    title = "Biased two-shuffle: change the cut probability, keep the riffle structure"
    kicker = r"$C\sim\mathrm{Binomial}(n,p)$ instead of $\mathrm{Binomial}(n,1/2)$"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        p = definition_box(
            "Bias parameter",
            r"Let $p\in[0,1]$.  In the inverse description, each card independently receives label 0 with probability $p$ and label 1 with probability $1-p$.",
            symbol=r"p",
            color=EMPIRICAL,
        ).shift(UP * 0.8)
        cut = math(r"\Pr(C=c)=\binom nc p^c(1-p)^{n-c}", size=35, color=LOCAL).shift(DOWN * 0.55)
        fair = math(r"p=1/2\quad\Longrightarrow\quad\text{ordinary GSR 2-shuffle}", size=29, color=UNIFORM).shift(DOWN * 1.4)
        self.say(f"Fulman's biased riffle framework retains the same order-preserving interleaving structure while allowing an arbitrary label probability vector. The two-label case is the cleanest entry point.\n[Sources] {SOURCE_FULMAN}")
        self.play(FadeIn(p), FadeIn(cut), FadeIn(fair))


class RD02InverseBiasedLabels(DeckSlide):
    title = "The inverse description is still independent labels — just not equally likely"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        steps = derivation_steps([
            ("Label", r"For each original card $i$, draw $B_i\in\{0,1\}$ independently with $\Pr(B_i=0)=p$."),
            ("Stable-sort", r"Move all 0-labeled cards first and all 1-labeled cards second, preserving original order within each label."),
            ("Packet size", r"The number of 0 labels is exactly the first packet size $C$, hence $C\sim\mathrm{Binomial}(n,p)$."),
            ("Conditional interleave", r"Given $C=c$, all label strings with $c$ zeros have the same probability, so all compatible order-preserving interleavings are uniform."),
        ], body_size=21).shift(DOWN * 0.05)
        self.say("This equivalence is powerful because cut bias remains an independent-label model. Most of the stable-sort and descent machinery survives; only the label weights change.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.10))


class RD03GeneralPShuffle(DeckSlide):
    title = "Fulman's general biased $a$-shuffle uses a probability vector"
    kicker = r"$\mathbf p=(p_1,\ldots,p_a),\qquad p_i\ge0,\ \sum_i p_i=1$"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        box = definition_box(
            "Biased $a$-shuffle",
            r"Independently label every card by $i\in\{1,\ldots,a\}$ with probability $p_i$, then stable-sort by the labels.  Equivalently, cut into $a$ piles with multinomial pile sizes and uniformly interleave the piles while preserving order within each pile.",
            symbol=r"\mathbf p",
            color=EMPIRICAL,
        ).shift(UP * 0.45)
        special = VGroup(
            math(r"\mathbf p=(1/2,1/2)\quad\text{GSR}", size=29, color=UNIFORM),
            math(r"\mathbf p=(p,1-p)\quad\text{biased two-shuffle}", size=29, color=LOCAL),
        ).arrange(DOWN, buff=0.25).shift(DOWN * 1.35)
        self.say(f"This is one of Fulman's equivalent definitions. It generalizes the inverse-label picture without introducing dependence between cards.\n[Sources] {SOURCE_FULMAN}")
        self.play(FadeIn(box), FadeIn(special))


class RD04CompositionTensor(DeckSlide):
    title = "Repeated biased shuffles compose by concatenating independent labels"
    kicker = r"\mathbf p\otimes\mathbf q=(p_iq_j)_{(i,j)}"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        steps = derivation_steps([
            ("First shuffle", r"Card receives label $I$ with distribution $\mathbf p$ and the deck stable-sorts by $I$."),
            ("Second shuffle", r"Independently, the same card receives label $J$ with distribution $\mathbf q$ and the current deck stable-sorts by $J$."),
            ("Stable-sort composition", r"Exactly as in the fair case, the result equals one stable sort by the lexicographic pair $(J,I)$."),
            ("Pair probability", r"Independence gives $\Pr(J=j,I=i)=q_jp_i$, so the combined label distribution is the product vector."),
        ], body_size=21).shift(DOWN * 0.1)
        example = math(r"(p,1-p)\otimes(q,1-q)=(pq,\,(1-p)q,\,p(1-q),\,(1-p)(1-q))", size=27, color=EMPIRICAL).shift(DOWN * 2.2)
        self.say(f"Fulman's convolution law is the biased analogue of two fair bits becoming one two-bit address. It gives a semigroup structure on label distributions.\n[Sources] {SOURCE_FULMAN}")
        self.play(FadeIn(steps), FadeIn(example))


class RD05CollisionProbability(DeckSlide):
    title = "A useful scalar appears: probability that two independent labels collide"
    kicker = r"c(\mathbf p)=\sum_i p_i^2"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        deriv = derivation_steps([
            ("Two cards", r"Give two different cards independent labels $I,J\sim\mathbf p$."),
            ("Same label", r"$\Pr(I=J)=\sum_i\Pr(I=i,J=i)=\sum_ip_i^2$."),
            ("Why it matters", r"Equal labels preserve the old relative order of those two cards; collisions are a direct source of surviving order memory."),
            ("Repeated shuffles", r"Under product-label composition, the collision probability multiplies across rounds."),
        ], body_size=21).shift(DOWN * 0.05)
        fair = math(r"(1/2,1/2):\quad c=1/2", size=31, color=UNIFORM).shift(DOWN * 2.1)
        self.say(f"Fulman's analysis repeatedly exposes sum p-squared as a natural measure of label concentration. It is not a complete mixing metric, but it quantifies how often two cards fail to receive a distinguishing label.\n[Sources] {SOURCE_FULMAN}")
        self.play(FadeIn(deriv), FadeIn(fair))


class RD06StrongUniformTime(DeckSlide):
    title = "Why 'all card labels are distinct' is such a powerful stopping event"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        steps = derivation_steps([
            ("Combined address", r"After several inverse shuffles, each card carries a longer random address."),
            ("No collision", r"Suppose all $n$ card addresses are distinct."),
            ("Sort", r"Stable sorting by distinct addresses is just ordinary sorting by i.i.d. random keys."),
            ("Symmetry", r"Conditional on distinct i.i.d. keys, every relative ordering of the card identities is equally likely."),
            ("Consequence", r"The first round at which all addresses are distinct can be used as a strong stationary time: at that stopping time the deck order is exactly uniform."),
        ], body_size=20).shift(DOWN * 0.1)
        note = remember_box(r"This gives upper bounds through collision probabilities. It does not say the deck cannot be close to uniform before the last collision disappears; strong stationary times are sufficient certificates, not generally exact TV formulas.", color=ERROR, width=10.7, size=21).shift(DOWN * 2.3)
        self.say(f"This distinct-address idea is a conceptual bridge between inverse-label combinatorics and mixing-time bounds in biased riffle work.\n[Sources] {SOURCE_FULMAN}")
        self.play(FadeIn(steps), FadeIn(note))


class RD07DistanceMetrics(DeckSlide):
    title = r"Literature warning: TV, separation, and relative $L^\infty$ are different metrics"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        grid = glossary_grid([
            (r"$d_{TV}(\mu,\pi)$", r"$\tfrac12\sum_x|\mu(x)-\pi(x)|$; maximum event-probability discrepancy"),
            (r"$\mathrm{sep}(\mu,\pi)$", r"$\max_x\left(1-\mu(x)/\pi(x)\right)$ when $\pi(x)>0$; detects states that are underrepresented"),
            (r"$d_\infty(\mu,\pi)$", r"$\max_x|\mu(x)/\pi(x)-1|$; worst relative pointwise error"),
            ("cutoff statement", r"must always name the metric: a chain can have related but nonidentical cutoff locations or profiles in different metrics"),
        ], body_size=18).shift(UP * 0.05)
        self.say("Assaf, Diaconis, and Soundararajan prove sharp results for separation and relative L-infinity in biased-cut riffles. Those are important, but we must not silently quote them as total-variation theorems.\n[Sources] " + SOURCE_ADS)
        self.play(FadeIn(grid))


class RD08BiasedCutLiterature(DeckSlide):
    title = "Biased-cut theory: what is actually being generalized?"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        lineage = derivation_steps([
            ("GSR", r"fair binary labels / symmetric binomial cut; exact finite formulas and cutoff behavior."),
            ("Fulman", r"arbitrary independent label probabilities $\mathbf p$; combinatorial identities, composition, strong-stationary-time bounds."),
            ("Assaf--Diaconis--Soundararajan", r"biased initial cuts with sharp asymptotic cutoff analysis in separation and relative $L^\infty$, using quasisymmetric-function and generating-function methods."),
            ("Our use", r"extract finite kernel definitions and error bounds that can be composed with working-set exchanges; do not formalize the entire asymptotic apparatus unless needed."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say(f"This is why 'biased cuts' is not our novelty. It already has a deep theory. The open synthesis for us is finite-cost local error plus large-deck exchange plus heterogeneous physical cost.\n[Sources] {SOURCE_FULMAN}; {SOURCE_ADS}")
        self.play(LaggedStart(*[FadeIn(s) for s in lineage], lag_ratio=0.10))


class RD09CutBiasVsClumping(DeckSlide):
    title = "Cut bias and clumping are not the same defect"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        cut = boxed(para(r"\textbf{Biased cut:} the total number of cards assigned to each hand is skewed. Conditional on that total, source labels may still be exchangeable and the interleaving may still be ideal.", 5.35, 22), LOCAL).shift(LEFT * 3.05 + UP * 0.3)
        clump = boxed(para(r"\textbf{Clumping:} neighboring source labels prefer to repeat. Two source words with the same total left/right counts can have different probabilities because their run structures differ.", 5.35, 22), EMPIRICAL).shift(RIGHT * 3.05 + UP * 0.3)
        example = colored_math((r"0011", EMPIRICAL), (r"\quad\text{vs}\quad", FG), (r"0101", EMPIRICAL), size=42).shift(DOWN * 1.4)
        caption = tex("same cut size, different run pattern", size=22, color=MUTED).next_to(example, DOWN, buff=0.18)
        self.say("A model that records only cut size cannot represent clumping. Correlation lives in the order of the source labels, not merely their total number.")
        self.play(FadeIn(cut), FadeIn(clump), FadeIn(example), FadeIn(caption))


class RD10CorrelatedSource(DeckSlide):
    title = "A pedagogical clumpy/dealer source: a two-state Markov chain"
    kicker = "This symmetric parameterization is for intuition; papers may use different notation"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        matrix = math(r"T_s=\begin{pmatrix}s&1-s\\1-s&s\end{pmatrix}", size=43, color=EMPIRICAL).shift(UP * 0.8)
        defs = glossary_grid([
            (r"$s=1/2$", r"independent fair labels: the GSR source-word law"),
            (r"$s>1/2$", r"same hand tends to repeat: clumpy runs"),
            (r"$s<1/2$", r"hand tends to switch: dealer-like alternation"),
            ("stationary labels", r"the symmetric chain has marginal probability $1/2$ for each hand even though adjacent labels are correlated"),
        ], body_size=18).shift(DOWN * 1.0)
        self.say(f"Jonasson and Morris define clumpy and dealer shuffles through enhanced or suppressed probability of drawing the next card from the same hand compared with GSR. This symmetric two-state chain is a compact teaching model of that dependence, not a claim about their exact parameter notation.\n[Sources] {SOURCE_JM}")
        self.play(FadeIn(matrix), FadeIn(defs))


class RD11RunLength(DeckSlide):
    title = "Correlation becomes visible as a run-length distribution"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        steps = derivation_steps([
            ("Start a run", r"Condition on the current hand label."),
            ("Continue", r"With probability $s$, the next source label is the same, so the run continues."),
            ("Stop", r"With probability $1-s$, the next label switches hands."),
            ("Therefore", r"$\Pr(L=\ell)=s^{\ell-1}(1-s)$ for $\ell\ge1$: a geometric run length."),
            ("Mean", r"$\mathbb E[L]=1/(1-s)$. At $s=1/2$ the mean run is 2; larger $s$ creates longer clumps."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say("This gives a physically interpretable parameter. Instead of asking a person whether their shuffle is clumpy, we can estimate the empirical distribution of same-hand run lengths and infer a dependence model.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class RD12Nonexchangeability(DeckSlide):
    title = "Correlation breaks exchangeability: source words with the same cut size differ"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        word1 = math(r"\Pr(0011)=\frac12\,s(1-s)s=\frac12s^2(1-s)", size=32, color=EMPIRICAL).shift(UP * 0.85)
        word2 = math(r"\Pr(0101)=\frac12\,(1-s)^3", size=32, color=LOCAL).shift(DOWN * 0.1)
        equal = math(r"s=1/2\quad\Longrightarrow\quad\Pr(0011)=\Pr(0101)=1/16", size=28, color=UNIFORM).shift(DOWN * 1.0)
        consequence = remember_box(r"For $s\ne1/2$, knowing only 'two left and two right cards' no longer determines the source-word probability.  Run structure is now part of the sufficient state for the local shuffle model.", color=ERROR, width=10.6, size=22).shift(DOWN * 1.95)
        self.say("This four-symbol calculation is the simplest concrete reason the elegant independent-label composition law no longer applies unchanged. Dependence changes which words are likely even at fixed pile size.")
        self.play(FadeIn(word1), FadeIn(word2), FadeIn(equal), FadeIn(consequence))


class RD13JonassonMorrisTheorem(DeckSlide):
    title = "Jonasson--Morris: correlated dealer/clumpy shuffles can still mix rapidly"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        known = boxed(para(r"\textbf{Published qualitative result:} dealer and clumpy shuffle families with non-GSR same-hand dependence are shown to mix in $O(\log^4 n)$ shuffles under their model assumptions.", 10.3, 26), UNIFORM).shift(UP * 0.65)
        implications = glossary_grid([
            ("Good news", r"short-range correlation does not automatically destroy polylogarithmic mixing"),
            ("Not enough for us", r"an asymptotic big-O theorem does not directly give a certified finite error after, say, 7 shuffles of 49 cards"),
            ("Formalization target", r"define a finite correlated-label kernel and prove computable/rigorous finite bounds for our parameter range"),
            ("Measurement target", r"estimate whether real human source-label sequences look clumpy, dealer-like, or need a richer dependence model"),
        ], body_size=18).shift(DOWN * 1.2)
        self.say(f"The literature tells us correlated hand behavior is mathematically tractable and can still mix rapidly. But our application needs finite, parameter-specific error certificates, not only an asymptotic order bound.\n[Sources] {SOURCE_JM}")
        self.play(FadeIn(known), FadeIn(implications))


class RD14GeneralCutLaw(DeckSlide):
    title = "Recent theory allows much more general cut-size laws"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        setup = definition_box(
            "General cut-fraction law",
            r"For an $N$-card riffle, the first packet size $C_N$ need not be binomial.  Study the normalized fraction $C_N/N$ and its limiting distribution, while retaining order-preserving interleaving mechanics.",
            symbol=r"C_N/N\Rightarrow\mu",
            color=EMPIRICAL,
        ).shift(UP * 0.6)
        result = boxed(para(r"Sellke--Shi--Wang prove a universality result: under broad cut distributions, the mixing-time constant on the $\log N$ scale is determined explicitly by the limiting cut law; they also treat deterministic/random sequences of cut rules and multipartite variants.", 10.4, 23), UNIFORM).shift(DOWN * 1.05)
        relevance = tex("This expands the cut model; it does not by itself model adjacent-card clumping.", size=21, color=ERROR).shift(DOWN * 2.15)
        self.say(f"This 2025 result reinforces the separation of concerns: very general marginal cut-size behavior is already studied. Correlated card-release mechanics remain a different axis.\n[Sources] {SOURCE_SSW}")
        self.play(FadeIn(setup), FadeIn(result), FadeIn(relevance))


class RD15ModelInterfaces(DeckSlide):
    title = "What must a realistic local-shuffle model expose to the protocol layer?"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        grid = glossary_grid([
            ("kernel", r"a finite transition law on labeled local deck orders, or a certified abstraction of it"),
            ("parameters", r"cut bias, same-hand persistence, untouched-tail probability, sleeve/friction covariates, etc."),
            ("error certificate", r"a rigorous bound on distance from the chosen local oracle after a specified number of physical shuffles"),
            ("composition law", r"how repeated local shuffles combine; exact semigroup if available, otherwise a computable repeated kernel"),
            ("measurement map", r"how observed physical shuffles estimate or bound the model parameters"),
            ("uncertainty set", r"parameter interval/set over which the final protocol should remain certified"),
        ], body_size=18).shift(DOWN * 0.05)
        self.say("The protocol optimizer should not care whether the local kernel came from fair GSR, biased independent labels, a correlated Markov source, or an empirical table. It should depend on a small verified interface.")
        self.play(FadeIn(grid))


class RD16RealismGlossary(DeckSlide):
    title = "Realistic-riffle glossary and checkpoint"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        grid = glossary_grid([
            ("biased cut", r"non-fair distribution of packet sizes; can still use independent labels"),
            (r"$\mathbf p$-shuffle", r"independent categorical labels with probabilities $p_i$, followed by stable sort"),
            (r"$\mathbf p\otimes\mathbf q$", r"product label distribution describing composition of independent biased shuffles"),
            (r"$\sum p_i^2$", r"probability two independent labels collide"),
            ("separation", r"worst relative underrepresentation $\max_x(1-\mu(x)/\pi(x))$"),
            (r"relative $L^\infty$", r"worst pointwise relative error $\max_x|\mu(x)/\pi(x)-1|$"),
            ("clumpy", r"same-hand source labels positively correlated; longer runs"),
            ("dealer", r"source labels favor switching hands; shorter/more alternating runs"),
            ("correlated labels", r"word probability depends on run pattern, not merely total label counts"),
            ("finite target", r"for our use, derive explicit local-kernel error bounds at pile sizes near 49--50, not only asymptotic big-O mixing"),
        ], body_size=16).shift(DOWN * 0.1)
        self.say("Checkpoint: you should be able to explain why cut bias preserves independent-label machinery while clumping does not, and why asymptotic rapid mixing is not yet the finite certificate our protocol needs.")
        self.play(FadeIn(grid))


class RD06AExactFulmanBound(DeckSlide):
    title = "Fulman's collision bound: derive the finite TV upper bound"
    kicker = r"$\|P_{n,a;\mathbf p}^{*k}-U\|_{TV}\le\binom n2\left(\sum_i p_i^2\right)^k$"
    section = "Part 3 · more realistic local shuffles"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Address matrix", r"After $k$ biased inverse shuffles, give each card its length-$k$ address. Each coordinate is an independent draw from $\mathbf p$."),
            ("Bad event", r"The strong-uniform-time certificate has not fired if at least two cards still have identical addresses."),
            ("One pair", r"For a fixed pair of cards, one coordinate matches with probability $\sum_i p_i^2$, so all $k$ coordinates match with probability $(\sum_i p_i^2)^k$."),
            ("Union bound", r"There are $\binom n2$ card pairs, so the probability of any address collision is at most $\binom n2(\sum_i p_i^2)^k$."),
            ("TV bound", r"A strong stationary time bounds distance to uniform by the probability the stopping event has not occurred."),
        ], body_size=19).shift(DOWN * 0.05)
        self.say(f"This is a beautiful finite bound because every term has a direct probabilistic meaning. Fulman proves exactly this total-variation upper bound. It is conservative but explicit and compositional.\n[Sources] {SOURCE_FULMAN}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class RD08AQuasisymmetricBridge(DeckSlide):
    title = "Advanced bridge: biased shuffle probabilities are quasisymmetric functions"
    kicker = "The descent constraints from the fair derivation survive; unequal label weights change the sum"
    section = "Part 3 · more realistic local shuffles"
    depth = "*"

    def body(self):
        dset = definition_box(
            "Inverse descent set",
            r"For a forward permutation $w$, define $\mathrm{iDes}(w)=\mathrm{Des}(w^{-1})\subseteq\{1,\ldots,n-1\}$. These are exactly the positions where the inverse stable-sort label sequence is forced to increase strictly.",
            symbol=r"\mathrm{iDes}(w)",
            color=LOCAL,
        ).shift(UP * 0.85)
        qfun = math(
            r"Q_D(\mathbf p)=\sum_{\substack{i_1\le\cdots\le i_n\\ j\in D\Rightarrow i_j<i_{j+1}}}p_{i_1}\cdots p_{i_n}",
            size=29,
            color=EMPIRICAL,
        ).shift(DOWN * 0.55)
        theorem = math(r"P_{\mathbf p}(w)=Q_{\mathrm{iDes}(w)}(\mathbf p)", size=36, color=UNIFORM).shift(DOWN * 1.4)
        intuition = para(r"Compare this with the fair $a$-shuffle count.  When every $p_i=1/a$, every compatible label sequence has the same weight $a^{-n}$, so the weighted sum collapses to 'number of compatible labels divided by $a^n$'.", 10.5, 21).shift(DOWN * 2.15)
        self.say(f"Assaf--Diaconis--Soundararajan make the quasisymmetric-function connection explicit: the fundamental quasisymmetric function is exactly the weighted sum over weak label sequences with strict steps at inverse descents. This is the biased analogue of our stars-and-bars derivation.\n[Sources] {SOURCE_ADS}")
        self.play(FadeIn(dset), FadeIn(qfun), FadeIn(theorem), FadeIn(intuition))


class RD08BExtremalPermutations(DeckSlide):
    title = r"Why identity and reversal control separation and relative $L^\infty$"
    section = "Part 3 · more realistic local shuffles"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Monotonicity", r"If one inverse descent set contains another, its fundamental quasisymmetric sum has more forced strict inequalities and therefore no larger probability for nonnegative label weights."),
            ("Most constrained", r"The reversal has every possible inverse descent, so it is the least likely permutation."),
            ("Least constrained", r"The identity has no inverse descents, so it is the most likely permutation."),
            ("Separation", r"Worst underrepresentation is therefore achieved at reversal: $\mathrm{SEP}=1-n!P(\mathrm{rev})$."),
            (r"relative $L^\infty$", r"For convolution powers in the biased two-shuffle setting, the worst relative overrepresentation is at identity: $n!P(\mathrm{id})-1$."),
        ], body_size=19).shift(DOWN * 0.05)
        self.say(f"The quasisymmetric partial order turns an optimization over n-factorial permutations into two extremal permutations. This is the structural reason the biased-cut paper can write closed expressions for separation and relative L-infinity.\n[Sources] {SOURCE_ADS}")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))

class RD06SSTDefinition(DeckSlide):
    title = "Definition: a strong stationary time is an exact-randomness stopping certificate"
    section = "Part 3 · more realistic local shuffles"

    def body(self):
        box = definition_box(
            "Strong stationary time",
            r"A randomized stopping time $T$ for a Markov chain with stationary law $\pi$ such that, for every time $t$, the state $X_T$ conditioned on $T=t$ has law $\pi$.  Equivalently, $X_T\sim\pi$ and $X_T$ is independent of $T$.",
            symbol=r"\Pr(X_T=x,T=t)=\pi(x)\Pr(T=t)",
            color=UNIFORM,
        ).shift(UP * 0.55)
        consequences = derivation_steps([
            ("At the stop", r"When the certificate fires, the chain is not merely close to stationary: the stopped state is exactly stationary."),
            ("Before the stop", r"If we inspect at deterministic time $t$, failure to have stopped is the only obstruction supplied by this certificate."),
            ("Tail bound", r"A strong stationary time gives $\mathrm{sep}(\mathcal L(X_t),\pi)\le\Pr(T>t)$, hence also $d_{TV}\le\Pr(T>t)$."),
        ], width=10.5, body_size=20).shift(DOWN * 1.35)
        self.say("Strong stationary time is stronger language than ordinary coupling. It gives an event whose occurrence certifies exact stationarity. That is why address collisions lead to clean biased-riffle upper bounds.")
        self.play(FadeIn(box), FadeIn(consequences))


class RD08A0QuasisymmetricPrimer(DeckSlide):
    title = "What does 'quasisymmetric' mean here?"
    kicker = "The coefficient depends on relative index order, but not on the particular increasing indices chosen"
    section = "Part 3 · more realistic local shuffles"
    depth = "*"

    def body(self):
        symmetric = boxed(para(r"\textbf{Symmetric polynomial:} swapping variable names $p_1,p_2,\ldots$ leaves the polynomial unchanged.  Only the multiset of exponents matters.", 5.1, 20), UNIFORM).shift(LEFT * 3.0 + UP * 0.45)
        quasi = boxed(para(r"\textbf{Quasisymmetric:} coefficients are invariant under replacing an increasing index pattern $i_1<\cdots<i_k$ by another increasing pattern $j_1<\cdots<j_k$, but arbitrary permutations of the variable order need not preserve the value.", 5.1, 20), LOCAL).shift(RIGHT * 3.0 + UP * 0.45)
        example = derivation_steps([
            ("Order matters", r"$p_1^2p_2+p_2^2p_3+\cdots$ can be quasisymmetric even though exchanging $p_1$ and $p_3$ changes it."),
            ("Why shuffles care", r"Stable sorting uses an ordered alphabet of labels.  A forced strict increase says label $i_j$ must come before a larger label $i_{j+1}$, so index order is part of the combinatorics."),
        ], width=10.5, body_size=19).shift(DOWN * 1.45)
        self.say(f"The biased-shuffle probability is naturally quasisymmetric because label values have an order used by the stable sort, but their actual numerical names are irrelevant. Assaf--Diaconis--Soundararajan exploit exactly this structure.\n[Sources] {SOURCE_ADS}")
        self.play(FadeIn(symmetric), FadeIn(quasi), FadeIn(example))


class RD08CDescentPositionMatters(DeckSlide):
    title = "Worked quasisymmetric example: bias makes descent position matter"
    kicker = r"With two labels, the same number of descents can have different probabilities"
    section = "Part 3 · more realistic local shuffles"
    depth = "*"

    def body(self):
        setup = reminder_box(
            r"biased two-label shuffle",
            r"Use labels $0,1$ independently with probabilities $p$ and $1-p$, then stable-sort.  For a target permutation, inverse descents force strict increases in the compatible label sequence.",
            color=EMPIRICAL,
        ).shift(UP * 1.05)
        left = boxed(math(r"D=\{1\}:\ i_1<i_2\le i_3\Rightarrow(0,1,1)\Rightarrow p(1-p)^2", size=24, color=LOCAL), LOCAL, 0.20).shift(LEFT * 2.9 + DOWN * 0.35)
        right = boxed(math(r"D=\{2\}:\ i_1\le i_2<i_3\Rightarrow(0,0,1)\Rightarrow p^2(1-p)", size=24, color=UNIFORM), UNIFORM, 0.20).shift(RIGHT * 2.9 + DOWN * 0.35)
        conclusion = remember_box(r"For $p=1/2$ both weights are $1/8$, so only the number of descents matters.  For $p\ne1/2$, their locations matter: the sufficient statistic refines from descent count to inverse descent set.", width=10.7, size=21).shift(DOWN * 1.75)
        self.say("This is the crucial conceptual upgrade from fair to biased labels. Fair Gilbert--Shannon--Reeds (GSR) collapses permutations by how many rising sequences they have. Bias breaks that collapse: where the strict steps occur affects the product of label probabilities.")
        self.play(FadeIn(setup), FadeIn(left), FadeIn(right), FadeIn(conclusion))
