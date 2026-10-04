"""Deep-dive study scenes for compositional error bounds and protocol optimization."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, Arrow, Create, FadeIn, LaggedStart, Line, Rectangle, VGroup

from shuffleviz.style import COST, ERROR, EXCHANGE, FG, LOCAL, MUTED, ORACLE, UNIFORM, DeckSlide, boxed, colored_math, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box, reminder_box
from shuffleviz.visual import operation_box


class OD00PartPrimer(DeckSlide):
    title = "Part 4 notation: actual kernels, ideal kernels, errors, and costs"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        grid = glossary_grid([
            (r"$R_\theta$", r"one actual local shuffle under physical/model parameter $\theta$"),
            (r"$L_\infty$", r"ideal perfect-local oracle used as a comparison kernel"),
            (r"$X_k$", r"cross-working-set operation exchanging or transferring $k$ cards"),
            (r"$\sigma$", r"a finite protocol: an ordered sequence of local and cross-pile operations"),
            (r"$\Delta(K,L)$", r"worst-state TV distance between two kernels"),
            (r"$\delta(K)$", r"Dobrushin coefficient: worst TV distance between two rows of one kernel"),
            (r"$\varepsilon$", r"chosen terminal error tolerance"),
            (r"$C(\sigma)$", r"physical cost assigned to a protocol"),
        ], body_size=17).shift(DOWN * 0.05)
        self.say("The control chapter is where the literature components become one theorem. Keep two different deltas separate: capital Delta compares two kernels; lowercase delta measures how strongly one kernel contracts differences between inputs.")
        self.play(FadeIn(grid))


class OD01ProtocolComposition(DeckSlide):
    title = "A physical protocol is an ordered product of Markov kernels"
    kicker = r"$\sigma=R^{r_0}X_{k_1}R^{r_1}\cdots X_{k_q}R^{r_q}$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        ops = VGroup(
            operation_box(r"$R^{r_0}$", LOCAL, width=1.55, subtitle="local riffles"),
            operation_box(r"$X_{k_1}$", EXCHANGE, width=1.55, subtitle="exchange"),
            operation_box(r"$R^{r_1}$", LOCAL, width=1.55, subtitle="local riffles"),
            operation_box(r"$\cdots$", MUTED, width=1.35),
            operation_box(r"$X_{k_q}$", EXCHANGE, width=1.55, subtitle="exchange"),
            operation_box(r"$R^{r_q}$", LOCAL, width=1.55, subtitle="local riffles"),
        ).arrange(RIGHT, buff=0.34).shift(UP * 0.45)
        arrows = VGroup(*[
            Arrow(ops[i].get_right(), ops[i + 1].get_left(), buff=0.05, color=MUTED, stroke_width=2)
            for i in range(len(ops) - 1)
        ])
        law = math(r"\mu_{\mathrm{final}}=\mu_0K_\sigma", size=38, color=UNIFORM).shift(DOWN * 1.2)
        convention = tex("row-vector convention: read the product from left to right in execution order", size=21, color=MUTED).shift(DOWN * 2.0)
        self.say("Every candidate human instruction becomes a finite kernel composition. This gives us one semantic object to evaluate for error and one finite action sequence to evaluate for physical cost.")
        self.play(LaggedStart(*[FadeIn(o) for o in ops], lag_ratio=0.08), Create(arrows), FadeIn(law), FadeIn(convention))


class OD02OracleProtocol(DeckSlide):
    title = "Define an ideal comparison protocol before bounding the physical one"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        actual = math(r"K_\sigma=R_\theta^{r_0}X_{k_1}R_\theta^{r_1}\cdots X_{k_q}R_\theta^{r_q}", size=28, color=LOCAL).shift(UP * 0.8)
        ideal = math(r"K_\sigma^{\star}=L_\infty X_{k_1}L_\infty\cdots X_{k_q}L_\infty", size=30, color=ORACLE).shift(DOWN * 0.15)
        why = remember_box(r"The ideal protocol isolates the membership-mixing problem already understood by Bernoulli--Laplace theory.  The actual-vs-ideal comparison isolates finite local-shuffle error.  Triangle inequality then combines them.", width=10.6, size=22).shift(DOWN * 1.55)
        self.say("This comparison is an analysis device, not a physical recommendation. We never pretend the oracle is available; we use it as an intermediate law whose behavior is easier to certify.")
        self.play(FadeIn(actual), FadeIn(ideal), FadeIn(why))


class OD03KernelDistance(DeckSlide):
    title = "Definition: compare two operations by their worst input-state TV error"
    kicker = r"$\Delta(K,L)=\max_{x\in\Omega}d_{TV}(K(x,\cdot),L(x,\cdot))$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        box = definition_box(
            "Uniform kernel error",
            r"For each possible input state $x$, compare the next-state distributions produced by $K$ and $L$.  Then take the worst case.  This makes the bound safe no matter what distribution reaches this protocol step.",
            symbol=r"\Delta(K,L)",
            color=ERROR,
        ).shift(UP * 0.55)
        consequence = math(r"d_{TV}(\mu K,\mu L)\le\Delta(K,L)\qquad\text{for every input law }\mu", size=33, color=UNIFORM).shift(DOWN * 1.0)
        self.say("The supremum over x is what makes errors compositional. We do not need to know the exact random input distribution at a later local-shuffle step in order to bound the damage of replacing its oracle by a finite physical kernel.")
        self.play(FadeIn(box), FadeIn(consequence))


class OD04KernelDistanceProof(DeckSlide):
    title = "Derive the one-step kernel comparison bound"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        steps = derivation_steps([
            ("Mixtures", r"$\mu K=\sum_x\mu(x)K(x,\cdot)$ and $\mu L=\sum_x\mu(x)L(x,\cdot)$."),
            ("Convexity of TV", r"Distance between two mixtures with the same weights is at most the weighted average of component distances."),
            ("Average row error", r"$d_{TV}(\mu K,\mu L)\le\sum_x\mu(x)d_{TV}(K_x,L_x)$."),
            ("Worst row", r"Every term is at most $\Delta(K,L)$ and the $\mu(x)$ weights sum to one."),
            ("Conclusion", r"$d_{TV}(\mu K,\mu L)\le\Delta(K,L)$."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say("Nothing asymptotic is hiding here. This is a finite convexity argument and is an excellent early Lean target because it becomes the reusable interface for every later local model.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.09))


class OD05CommonSuffixContraction(DeckSlide):
    title = "After one approximation error occurs, a common future cannot amplify it"
    kicker = r"$d_{TV}(\mu KA,\mu LA)\le d_{TV}(\mu K,\mu L)$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        rem = reminder_box(
            "TV contraction",
            r"Applying the same Markov kernel to two distributions cannot increase their total variation distance.",
            symbol=r"d_{TV}(\alpha A,\beta A)\le d_{TV}(\alpha,\beta)",
            color=UNIFORM,
        ).shift(UP * 0.7)
        combined = math(r"d_{TV}(\mu KA,\mu LA)\le d_{TV}(\mu K,\mu L)\le\Delta(K,L)", size=35, color=ERROR).shift(DOWN * 0.75)
        self.say("This is why we can charge an approximation error at the moment it occurs and then forget the exact suffix. Future common operations can only preserve or reduce that discrepancy.")
        self.play(FadeIn(rem), FadeIn(combined))


class OD06ThreeStepTelescope(DeckSlide):
    title = "Telescope three replacements before writing the general theorem"
    kicker = r"$K_1K_2K_3$ versus $L_1L_2L_3$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        chain = VGroup(
            math(r"\mu K_1K_2K_3", size=28, color=LOCAL),
            math(r"\mu L_1K_2K_3", size=28),
            math(r"\mu L_1L_2K_3", size=28),
            math(r"\mu L_1L_2L_3", size=28, color=ORACLE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.42).shift(LEFT * 2.8 + DOWN * 0.05)
        labels = VGroup(
            tex(r"replace $K_1$", size=21, color=ERROR),
            tex(r"replace $K_2$", size=21, color=ERROR),
            tex(r"replace $K_3$", size=21, color=ERROR),
        )
        for j, lab in enumerate(labels):
            lab.next_to(chain[j], RIGHT, buff=1.0)
        bounds = VGroup(
            math(r"\le\Delta(K_1,L_1)", size=25, color=ERROR),
            math(r"\le\Delta(K_2,L_2)", size=25, color=ERROR),
            math(r"\le\Delta(K_3,L_3)", size=25, color=ERROR),
        )
        for j, b in enumerate(bounds):
            b.next_to(labels[j], RIGHT, buff=0.45)
        total = math(r"d_{TV}(\mu K_1K_2K_3,\mu L_1L_2L_3)\le\Delta_1+\Delta_2+\Delta_3", size=30, color=UNIFORM).shift(DOWN * 2.45)
        self.say("The telescope is just triangle inequality along a path of hybrid protocols. Consecutive hybrids differ in one kernel only; the common suffix contracts that local difference.")
        self.play(LaggedStart(*[FadeIn(x) for x in chain], lag_ratio=0.15), FadeIn(labels), FadeIn(bounds), FadeIn(total))


class OD07GeneralTelescope(DeckSlide):
    title = "General perturbation theorem: local kernel errors add"
    kicker = r"$d_{TV}(\mu K_1\cdots K_T,\mu L_1\cdots L_T)\le\sum_{t=1}^T\Delta(K_t,L_t)$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        box = definition_box(
            "Telescoping replacement bound",
            r"Build $T+1$ hybrid protocols. Hybrid $j$ uses ideal kernels for the first $j$ positions and actual kernels afterward. Triangle inequality sums adjacent hybrid distances; each adjacent pair differs at one position and is bounded by that kernel's worst-row TV error.",
            symbol=r"\sum_t\Delta_t",
            color=UNIFORM,
        ).shift(UP * 0.45)
        significance = remember_box(r"This theorem is the architectural hinge.  Once it exists, every new local-shuffle model can participate by supplying a finite bound $\Delta(R_\theta^r,L_\infty)$; the large-deck composition proof does not need to know how that bound was obtained.", width=10.7, size=21).shift(DOWN * 1.55)
        self.say("The simple sum can be conservative because it assumes no later mixing washes out earlier error. Dobrushin coefficients give a principled refinement next.")
        self.play(FadeIn(box), FadeIn(significance))


class OD08DobrushinDefinition(DeckSlide):
    title = "Definition: the Dobrushin coefficient measures how much a kernel forgets its input"
    kicker = r"$\delta(K)=\max_{x,x'}d_{TV}(K(x,\cdot),K(x',\cdot))$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        box = definition_box(
            "Dobrushin coefficient",
            r"Compare every pair of rows of the same kernel. If all input states produce nearly the same next-state law, $\delta(K)$ is small and the kernel strongly forgets its input. Always $0\le\delta(K)\le1$.",
            symbol=r"\delta(K)",
            color=LOCAL,
        ).shift(UP * 0.55)
        cases = glossary_grid([
            (r"$\delta(K)=0$", r"every row is identical; one step completely erases the old state"),
            (r"$\delta(K)=1$", r"some pair of inputs remain perfectly distinguishable after one step; the generic TV contraction may be no better than nonexpansion"),
        ], body_size=19).shift(DOWN * 1.25)
        self.say("Do not confuse lowercase delta of one kernel with capital Delta between two different kernels. Dobrushin is a contraction property; capital Delta is an approximation error.")
        self.play(FadeIn(box), FadeIn(cases))


class OD09DobrushinContraction(DeckSlide):
    title = "Dobrushin refines TV contraction by a quantitative factor"
    kicker = r"$d_{TV}(\mu K,\nu K)\le\delta(K)d_{TV}(\mu,\nu)$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        steps = derivation_steps([
            ("Baseline", r"Ordinary data processing only gives a factor of 1."),
            ("Row diameter", r"$\delta(K)$ bounds how far apart any two possible next-state laws can be."),
            ("Mixture coupling", r"Decompose the signed difference between $\mu$ and $\nu$ into matched and unmatched mass; only the unmatched mass needs to be transported between rows."),
            ("Result", r"The surviving discrepancy is at most the unmatched mass $d_{TV}(\mu,\nu)$ times the worst row diameter $\delta(K)$."),
        ], body_size=20).shift(DOWN * 0.05)
        self.say("This theorem lets later strongly mixing operations discount earlier approximation error. It is mathematically more informative than blindly adding every epsilon at full weight.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.10))


class OD10WeightedTelescope(DeckSlide):
    title = "Exact weighted telescope: future actual kernels discount earlier errors"
    kicker = r"d_{TV}(\mu K_1\cdots K_T,\mu L_1\cdots L_T)\le\sum_{i=1}^T\Delta_i\prod_{j=i+1}^T\delta(K_j)"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        definitions = reminder_box(
            "symbols",
            r"Let $\Delta_i=\Delta(K_i,L_i)$ compare actual kernel $K_i$ with ideal kernel $L_i$.  Let $\delta(K_j)$ be the Dobrushin contraction coefficient of the actual suffix kernel $K_j$.  An empty product equals 1.",
            color=LOCAL,
        ).shift(UP * 0.95)
        formula = math(
            r"d_{TV}(\mu K_1\cdots K_T,\mu L_1\cdots L_T)"
            r"\le\sum_{i=1}^T\Delta(K_i,L_i)\prod_{j=i+1}^T\delta(K_j)",
            size=29,
            color=UNIFORM,
        ).shift(DOWN * 0.45)
        plain = remember_box(
            r"This is not merely a heuristic.  Choose hybrids that idealize the prefix and keep the actual suffix.  The error introduced at position $i$ is at most $\Delta_i$ immediately, then contracts through the common actual suffix by at most $\prod_{j>i}\delta(K_j)$.",
            width=10.7,
            size=21,
        ).shift(DOWN * 1.65)
        self.say("We can make the product-of-contractions statement exact by fixing the hybrid convention. Here the suffix after the replaced position is always the actual suffix, so the contraction factors are the Dobrushin coefficients of the actual K kernels.")
        self.play(FadeIn(definitions), FadeIn(formula), FadeIn(plain))


class OD10AWeightedTelescopeProof(DeckSlide):
    title = "Proof of the weighted telescope, one hybrid at a time"
    section = "Part 4 · the costed working-set control problem"
    depth = "*"

    def body(self):
        steps = derivation_steps([
            ("Hybrids", r"Define $H_i=L_1\cdots L_iK_{i+1}\cdots K_T$ for $i=0,\ldots,T$.  Thus $H_0=K_1\cdots K_T$ and $H_T=L_1\cdots L_T$."),
            ("Triangle", r"$d_{TV}(\mu H_0,\mu H_T)\le\sum_i d_{TV}(\mu H_{i-1},\mu H_i)$."),
            ("Common prefix", r"Before position $i$, both adjacent hybrids have the same input law $\alpha_i=\mu L_1\cdots L_{i-1}$."),
            ("Local replacement", r"Immediately after position $i$, $d_{TV}(\alpha_iK_i,\alpha_iL_i)\le\Delta(K_i,L_i)$."),
            ("Common suffix", r"Both laws then pass through $K_{i+1}\cdots K_T$. Repeated Dobrushin contraction multiplies the discrepancy by at most $\prod_{j=i+1}^T\delta(K_j)$."),
            ("Sum", r"Add the adjacent-hybrid bounds to obtain the weighted telescope exactly."),
        ], body_size=17).shift(DOWN * 0.02)
        self.say("This is the proof we eventually want Lean to know. Every step is finite: triangle inequality, the worst-row kernel bound, and repeated Dobrushin contraction. No asymptotics or spectral theory are required.")
        self.play(LaggedStart(*[FadeIn(s) for s in steps], lag_ratio=0.08))


class OD11TotalErrorBudget(DeckSlide):
    title = "Split terminal error into ideal membership error plus local-approximation error"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        triangle = math(
            r"d_{TV}(\mu_0K_\sigma,U)\le d_{TV}(\mu_0K_\sigma,\mu_0K_\sigma^\star)+d_{TV}(\mu_0K_\sigma^\star,U)",
            size=27,
        ).shift(UP * 0.85)
        left = boxed(para(r"\textbf{Actual vs ideal:} bounded compositionally by local-kernel approximation errors, possibly discounted by later contraction.", 5.2, 22), ERROR).shift(LEFT * 3.0 + DOWN * 0.65)
        right = boxed(para(r"\textbf{Ideal vs uniform:} Bernoulli--Laplace membership mixing under perfect local randomization; exact finite computation or symbolic bounds.", 5.2, 22), ORACLE).shift(RIGHT * 3.0 + DOWN * 0.65)
        self.say("This triangle inequality is the conceptual decomposition of the whole project. Prior large-deck theory controls the right term; finite realistic local-shuffle analysis controls the left term.")
        self.play(FadeIn(triangle), FadeIn(left), FadeIn(right))


class OD12CostModel(DeckSlide):
    title = "Definition: optimization needs an explicit physical cost model"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        simple = math(r"C(\sigma)=c_R\sum_{i=0}^q r_i+\sum_{i=1}^q c_X(k_i)", size=36, color=COST).shift(UP * 0.9)
        grid = glossary_grid([
            (r"$r_i$", r"number of local shuffles in phase $i$"),
            (r"$c_R$", r"cost of one local shuffle: time, effort, wear, or a normalized unit"),
            (r"$c_X(k)$", r"cost of the cross-pile operation at exchange size $k$; may be constant or size-dependent"),
            (r"$\rho=c_X/c_R$", r"useful dimensionless ratio when exchange cost is approximately constant"),
        ], body_size=18).shift(DOWN * 0.75)
        self.say("Cost is part of the theorem statement, not an afterthought. Different hands or table layouts can make cross-pile manipulation far more expensive than another local riffle, changing the optimal protocol even when the probability kernels stay the same.")
        self.play(FadeIn(simple), FadeIn(grid))


class OD13OptimizationProblem(DeckSlide):
    title = "The finite control problem"
    kicker = r"$\min_\sigma C(\sigma)$ subject to $d_{TV}(\mu_0K_\sigma,U)\le\varepsilon$"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        box = definition_box(
            "Feasible protocol",
            r"A protocol $\sigma$ is feasible for tolerance $\varepsilon$ when its certified terminal error bound is at most $\varepsilon$. Among feasible protocols we seek one with minimum physical cost inside a declared search/action space.",
            symbol=r"\sigma",
            color=COST,
        ).shift(UP * 0.5)
        reminder = remember_box(r"'Optimal' is meaningless without three declarations: the allowed operations, the cost function, and the randomness/error target.  A bounded-search optimality theorem should state all three explicitly.", color=ERROR, width=10.5, size=22).shift(DOWN * 1.5)
        self.say("The aim is not to prove one universal shuffle recipe. It is to solve a parameterized finite control problem whose answer changes with the user, deck, physical model, and desired tolerance.")
        self.play(FadeIn(box), FadeIn(reminder))


class OD14ParetoDominance(DeckSlide):
    title = "Before choosing $\varepsilon$, compute the cost/error Pareto frontier"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        definition = definition_box(
            "Dominance",
            r"Protocol $A$ dominates protocol $B$ when $A$ has no greater cost and no greater certified error, with at least one strict improvement. A Pareto-optimal protocol is not dominated by another candidate.",
            symbol=r"(C_A,E_A)\preceq(C_B,E_B)",
            color=COST,
        ).shift(UP * 0.6)
        example = math(r"A:(8,0.02)\quad B:(10,0.03)\quad\Longrightarrow\quad A\text{ dominates }B", size=31, color=UNIFORM).shift(DOWN * 0.85)
        note = tex("Units here are schematic: cost 8 vs 10, error 0.02 vs 0.03.", size=20, color=MUTED).shift(DOWN * 1.65)
        self.say("The frontier is often more useful than a single optimum. It shows how much extra physical effort buys each decrease in certified error, and lets the user choose a tolerance after seeing the tradeoff.")
        self.play(FadeIn(definition), FadeIn(example), FadeIn(note))


class OD15SearchVsCertificate(DeckSlide):
    title = "Search proposes a protocol; Lean certifies the claim"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        search = boxed(para(r"\textbf{Search layer}\nEnumerate bounded schedules, dynamic-program, use branch-and-bound, or maintain a Pareto frontier.  Floating-point heuristics may prioritize candidates as long as exact evidence is produced for finalists.", 5.25, 22), COST).shift(LEFT * 3.0 + DOWN * 0.1)
        proof = boxed(para(r"\textbf{Certificate layer}\nVerify operation semantics, exact cost, exact/rational error bounds, and -- when claimed -- optimality within the declared finite action space.", 5.25, 22), UNIFORM).shift(RIGHT * 3.0 + DOWN * 0.1)
        arrow = Arrow(search.get_right(), proof.get_left(), buff=0.15, color=MUTED, stroke_width=3)
        self.say("We do not need to formalize a sophisticated optimizer in Lean. The trusted boundary is the compact certificate. Search can evolve independently as long as Lean checks the mathematical claim it emits.")
        self.play(FadeIn(search), FadeIn(proof), Create(arrow))


class OD16RobustOptimization(DeckSlide):
    title = "Measured human parameters are uncertain, so optimize robustly"
    kicker = r"E_{\mathrm{robust}}(\sigma)=\sup_{\theta\in\Theta}d_{TV}(\mu_0K_\sigma(\theta),U)"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        defs = VGroup(
            definition_box(r"$\theta$", r"parameters of the local physical-shuffle model: cut bias, same-hand persistence, untouched-tail rate, and so on", color=LOCAL, width=5.25, body_size=20),
            definition_box(r"$\Theta$", r"a confidence/uncertainty set containing plausible parameter values rather than one fitted point estimate", color=ERROR, width=5.25, body_size=20),
        ).arrange(RIGHT, buff=0.45).shift(UP * 0.55)
        robust = math(r"\min_\sigma C(\sigma)\quad\text{s.t.}\quad\sup_{\theta\in\Theta}E(\sigma,\theta)\le\varepsilon", size=34, color=UNIFORM).shift(DOWN * 1.0)
        self.say("A recipe should not lose its guarantee because our estimate of one human parameter moved slightly after collecting ten more shuffles. Robust optimization converts measurement uncertainty into an explicit worst-case requirement.")
        self.play(FadeIn(defs), FadeIn(robust))


class OD17OperationalTheorem(DeckSlide):
    title = "What the final operational theorem should say"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        theorem = boxed(para(r"Given a deck size, working-set sizes, a certified family of local-shuffle kernels over parameter set $\Theta$, allowed cross-pile operations, physical costs, and tolerance $\varepsilon$: this concrete protocol has cost $C$, its terminal distribution is within $\varepsilon$ of uniform for every $\theta\in\Theta$, and no cheaper protocol in the declared finite search space satisfies the same guarantee.", 10.6, 27), UNIFORM).shift(UP * 0.25)
        line = tex("That is the theorem a human can actually use.", size=27, color=COST).shift(DOWN * 1.95)
        self.say("All of the literature deep dive is in service of this end-to-end statement. Each chapter supplies one theorem interface needed to make this operational certificate honest.")
        self.play(FadeIn(theorem), FadeIn(line))


class OD18ControlGlossary(DeckSlide):
    title = "Composition / optimization glossary and checkpoint"
    section = "Part 4 · the costed working-set control problem"

    def body(self):
        grid = glossary_grid([
            (r"$K_\sigma$", r"actual kernel obtained by composing the physical operations in protocol $\sigma$"),
            (r"$K_\sigma^\star$", r"ideal comparison protocol, usually replacing finite local shuffles by perfect-local oracles"),
            (r"$\Delta(K,L)$", r"worst-state TV difference between two kernels"),
            ("TV contraction", r"common post-processing cannot increase TV"),
            ("telescope", r"replace one kernel at a time and sum the resulting local approximation errors"),
            (r"$\delta(K)$", r"Dobrushin row-diameter coefficient controlling quantitative contraction"),
            ("error budget", r"ideal membership-mixing error + actual-vs-ideal local approximation error"),
            (r"$C(\sigma)$", r"declared physical cost of a protocol"),
            ("Pareto frontier", r"nondominated cost/error tradeoffs"),
            ("robust error", r"worst certified error across an uncertainty set of human/model parameters"),
            ("search", r"untrusted proposal mechanism that may use ordinary numerical code"),
            ("certificate", r"compact exact claim checked by Lean"),
        ], body_size=16).scale(0.95).shift(DOWN * 0.1)
        self.say("Checkpoint: derive the telescope from triangle inequality plus contraction, explain capital Delta versus Dobrushin delta, and state exactly what is meant by an optimal protocol.")
        self.play(FadeIn(grid))
