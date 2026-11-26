# Shufflemath: an arbitrary-finite-deck formalization campaign

**Roadmap date:** 2026-11-15 (America/New_York)  
**Basis:** `shufflemath-source-2026-11-15T200601-5-6ec82508fa1b.tar.gz`, Git revision `6ec82508fa1bce8b15e2c37dd1a73bdcb22d38f8`  
**Status:** New **strategic roadmap**, not a historical rewrite of `docs/lean_plan.md`, `docs/agent_handoff.md`, or either previous dated review.  
**Audience:** Qwen and subsequent formalization contributors.  
**Objective:** Prove theorems about **every finite collection of distinct cards**, their allocations to working piles, exchanges, local shuffles, and protocol convergence. Commander (`N=99`) is a **specialization and regression benchmark**, not the foundational definition.

> **Fundamental change of focus.** The mathematical object is a finite, labeled card universe and a partition of its positions into piles, not a 99-card Commander deck. First make the existing *two-pile* theory fully parametric, then build *multi-pile, multi-category* mathematics, and only then extend to drawing, dealing, discarding, and changing pile sizes. No generic theorem should import a `Commander*` module. Preserve the already proved 99-card declarations as applications; do not delete their concrete numeric certificates or change the source semantics silently.

## 1. Method, limits, and status honesty

This roadmap is grounded in source-level inspection of 33 `Shufflemath/*.lean` modules, `docs/lean_plan.md`, `docs/agent_handoff.md`, `docs/problem.md`, and the prior November 15 reviews. It distinguishes **source-present** from **still to prove**. A source declaration does not imply that its proposed generalization compiles. The reviewer did not compile Lean (the pinned `lake`/`lean` executables were unavailable). The source snapshot contains no `docs/planning/` tree; this document creates a new directory without claiming that older active plans have migrated.

**Do not confuse four notions of correctness:** (i) the count chain, (ii) the allocation/membership chain, (iii) literal swaps of ordered cards, and (iv) perfect-local or finite-GSR resampling. A theorem about (i) is not automatically about (iii); an allocation update followed by a uniform ordering is not a literal position swap. State the input distribution and any reset hypotheses in every exported mixing theorem.

**Definition of campaign completion.** A substantial library of parameterized, compiled theorems (not simply polymorphic definitions) must imply the old 99-card results and produce nontrivial theorems for at least two *different* small deck configurations and for a multi-pile card-allocation system. Quantitative mixing and cost certificates should be stated for an arbitrary admissible finite configuration, with numerical Commander results as examples.

## 2. Existing inventory: what is general, partially general, or overly specialized

| Existing module(s) | Present state | Recommended reusable destination / action |
| --- | --- | --- |
| `Finite`, `Markov`, `Matrix`, `TotalVariation`, `Dobrushin`, `Perturbation` | Generic finite exact probabilities, kernels, TV/contraction | **Retain.** Reuse these, and perform the separate build-cost cleanup from the dated quality review; do not reimplement probability theory |
| `FiberDisintegration`, `FiberLifting`, `OracleRefinement`, `PhysicalExchangeReduction`, `PhysicalRefinement` | Generic observation/lift/intertwining and conditional physical-refinement theorems | **Retain as organizing theorems.** Instantiate on new finite-deck and pile-configuration spaces; share the two schedule inductions after measuring |
| `GSR` | Generic inverse-label shuffle of `List (Fin n)`, label-product composition law | Keep generic proof; add a **permutation-of-any-finite-pile** interpretation and uniform finite-GSR TV estimate; do not implement GSR separately for each pile size |
| `Cost`, `ProtocolCertificate` | Generic costed kernels/certificates | Retain; instantiate on generic pile systems and eventually changing-size actions |
| `FinsetFiberCount`, `FinsetCombinatorics` | Generic finite-set counting ingredients | Reuse in fiber counting; migrate redundant specialized `ExchangeOverlap` constructions via compatibility lemmas |
| `BernoulliLaplaceGeneral`, `BernoulliLaplaceFiber` | **Already parameterized** by `N,m,r,k`: admissible count states, exact exchange probabilities, stationary distribution, detailed balance, first centered mode | Preserve as the two-pile/two-color theorem, but express it as a **corollary of generic pile membership and symmetric exchanges**. Leave expensive first-mode proof in a companion module if measured builds improve |
| `ExchangeOverlap` | Most symbolic counting is generic; `generalCL_ns` covers the Commander non-saturating regime; a Commander specialization appears at the end | Consolidate `generalCL` under `generalCL_ns`, generalize its interpretation through a count-projection proof, keep Commander only as a corollary |
| `CommanderPermutation`, `CommanderFiberWitness`, `CommanderFiberCount`, `CommanderFiberMembership` | `Equiv.Perm (Fin 99)`, hard-coded left 50/right 49, fiber counts | Replace mathematical work with `FiniteDeck.TwoPile`, `FiniteDeck.Fibers`, `FiniteDeck.Histogram`; **preserve old names as thin specialization wrappers** |
| `CommanderMembershipKernels`, `CommanderMembershipOrbits` | `Membership := {S : Finset (Fin 99) // S.card=50}` and extensive four-part orbit proof | Extract general `m`-subset membership, uniform fiber lift, and **partition-equivariance/orbit** theorem. Avoid rewriting a 903-line four-case permutation for each application |
| `CommanderPhysicalExchange`, `CommanderMembershipExchange` | Chosen 25+25 position subsets, membership update, `rawExchange := rawExchangeMembership` followed by `localLift`; concrete final A3 equality is **open** | Factor through generic **subset exchange law**, independently define **literal paired-position swap**, and prove membership pushforward. Derive the 99-card A3 as an instance, rather than finishing another Commander-only counting proof |
| `CommanderLocalGSR`, `CommanderDeckGSR` | `Fin 50 × Fin 49` local permutation structure; product-law/TV work on pile lists; full deck GSR still open | Move to product of **any finite pile permutations** and transport generic GSR; prove membership preservation and row-TV in abstract first |
| `CommanderFullDeckDisintegration` | Conditional and unconditional Commander full-deck fiber/oracle theorems; physical theorem conditional on A3 | Specialize general finite-deck disintegration and physical intertwining; retain exact rational 99-card TV results as regression |
| `BernoulliLaplace`, `BernoulliLaplaceCommanderBridge`, `BernoulliLaplaceSemantic` | Concrete 50-state/99-card exact matrix and array certificates | **Retain in `Examples/Commander` eventually.** Do not prematurely turn enormous concrete rational certificates into symbolic `N`-computations |

**Important limitation of `ExchangeAdmissible`:** it requires `0 < m < N`, `0 < k` and `k ≤ min(m,N-m)`. That is sensible for a nontrivial exchange but not the desired universal *definition* of a finite deck or its local identity operation. Keep separate (a) weak structural assumptions `m ≤ N`, (b) legal exchanges allowing `k=0` where helpful, (c) strict positivity assumptions for nontrivial mixing. In particular, zero-card piles and `N=0` are valid for basic partition/fiber theorems, even though they have trivial or no exchanges.

## 3. Canonical mathematical model: finite positions and finite identities

### 3.1 One deck, two working piles

Begin with **`N : Nat`** and cards `Fin N`. Give the deck a canonical representation `Equiv.Perm (Fin N)`, interpreted as *position → card identity*. The left positions are the first `m` positions (`m ≤ N`), and the right positions are the rest. For proof engineering, use the explicit two-part position equivalence

\[
\mathrm{Fin}(N)\;\simeq\;\mathrm{Fin}(m)\;\oplus\;\mathrm{Fin}(N-m),\qquad m\le N.
\]

Define `TwoPileMembership N m := {S : Finset (Fin N) // S.card = m}`. From a deck `d`, project the image of the first `m` positions to `membership d`. A marked subset `M : Finset (Fin N)` with `M.card=r` then defines `count_M(S)=|S∩M|`, whose valid values are the existing `BLState N m r`.

**Boundary contract:** the *deck and membership* APIs should admit `N=0`, `m=0`, `m=N`, and an empty marked set. Exchange-specific lemmas may require both piles nonempty and `k≥1`. Do not use Commander’s `Fin 50` encoding of counts `1..50` in a general statement: admissible counts include zero in general.

For arbitrary named cards `Card` with `[Fintype Card]` and `[DecidableEq Card]`, use `N = Fintype.card Card` and an explicit equivalence `Fin N ≃ Card`, or work directly with a deck `Fin N ≃ Card`. **Do not** choose a numerical enumeration and bake that choice into the mathematics. All theorems should transport along finite equivalences; a card's printed text is an attribute, not necessarily its unique identity.

### 3.2 Arbitrarily many fixed-size piles

Let `Pile` be any finite type and `capacity : Pile → Nat`, with `∑ p, capacity p = N`. Use the position type

\[
\mathrm{Position}(P,\mathbf n) := \sum_{p:P}\mathrm{Fin}(n_p).
\]

A completely ordered global state is an equivalence `Position P capacity ≃ Card` with `Fintype.card Card = ∑ p, capacity p`. A pile allocation is the induced function `Card → Pile` satisfying the exact capacities; equivalently it is a partition of `Card` into indexed sets. Prefer **position `Sigma` and card-allocation primitives** over a pile-count-dependent maze of `Fin` coercions. `Finpartition` is a possible Mathlib bridge, not a prerequisite: a function with cardinality constraints may elaborate more easily.

This model handles any number of players and working sets while preserving card identity and within-pile ordering. The two-pile `Fin N` model must be proved equivalent to the `Pile := Fin 2` instance, once, rather than maintained as two incomparable mathematical universes.

### 3.3 Distinct identities versus observed categories

A **category function** `color : Card → Color` (finite `Color`) describes visible types, original stacks, editions, or other properties. It is *not* a quotient of the true physical card universe. Two cards with identical text can still be distinct pieces of cardboard. Define the histogram

\[
X_{p,c} := |\{a : Card : allocation(a)=p\land color(a)=c\}|.
\]

The histogram has row sums `n_p` and column sums `r_c = |color^{-1}(c)|`. It is a coarser observation of an ordered deck, not the deck itself. Its dimension depends on `Pile` and `Color`, not on a Commander-specific 50-state indexing trick.

### 3.4 Changing pile sizes: a separate layer

To describe dealing, drawing, discarding, and returning cards, introduce an *extended* state `Σ (capacity : Pile → Nat), (∑ capacity = N) × OrderedDeck capacity` (schematic). An action then maps between fibers of different capacities. All cards still exist: a discard pile is a pile, not deletion from the universe. For variable player counts or new cards, use a later, explicit state/type transition; do not mix it into the first fixed-card theory.

Uniform on ordered decks **conditional on a given capacity vector** is a sensible target. There need not be a single stationary uniform law on the union of variable-capacity states for one-way draw/discard actions. Do not apply fixed-capacity reversibility or Bernoulli–Laplace stationarity without establishing the right invariant law.

## 4. Canonical theorem ladder (mathematical statements before Lean tactics)

**Progress update (Nov 15-16, 2026):** G1 (2 lemmas), G2 (Fintype-free fiber: `fiberSet_card`, `fibTransitive`, `fibersPartition`, `fibersEqual`, `fiberCount`), G3 (`subsetExchangeCount`, `ReachSetConcrete`+`_card`+`_image`, `leftPosition`/`rightPosition`, `PhysicalSwap` swap + `_parts_disjoint`/`_card`/`literalSwapMembership`/`_conjugate`, `subsetExchangeKernel` + `symmetric`/`rowOne`/`colOne`/`stationary`/`equivariant`), and **G4 T4 counting core** (`countFiber_card`, `countFiber_blStationary`, `subsetExchangeKernel_equivariant`, `powersetCard_markedSplit`+`pmcDecomp`/`pmcInvFirst`/`pmcInvSecond`) are now **proven and in the library** (full build green, gate 37/37). **Remaining:** T2 transitivity on the marked-count fibers (generalize `membershipFiber_transitive` to the (m-pile, x-marked) level); T4 `count : Membership → BLState` projection + the count-level hypergeometric transition formula + the uniform-fiber intertwining (the big theorem that discharges Commander A3 by instantiation); T3 physical↔membership projection + T2/T3 synthesis + the generic full-deck theorem; T5 (multivariate hypergeometric stationarity).

Below, each formula is a **target mathematical theorem**, not a claim that a Lean declaration already exists. Choose names/contracts close to these, compile small modules, and record exact resulting Lean names.

### T1 — uniform fiber counting, any finite piles

For any fixed allocation `A : Card → Pile` with pile sizes `n_p`, the ordered decks inducing `A` satisfy

\[
|\{d : \operatorname{allocation}(d)=A\}|=\prod_{p:P} n_p!.
\]

In the two-pile case this is `m! (N-m)!`. Then

\[
|\{A : \forall p,\;|A^{-1}(p)|=n_p\}| = \frac{N!}{\prod_p n_p!},
\]

so an unordered allocation under uniform `Deck` is **uniform among legal allocations**. Prove by equivalence between the fiber and the product of ordering equivalences of each pile; do **not** enumerate `N!` permutations or rely on numerical `native_decide`. In Lean prefer `Fintype.card_congr`/`Fintype.card_equiv`/finite `Sigma` or `Pi` structure, with factorial identities as separate corollaries. `Nat.multinomial` already provides a relevant Mathlib factorial identity.

### T2 — histogram fiber counts and multivariate hypergeometric stationarity

For valid `X = (x_{p,c})`, where the categories have counts `r_c`, the number of card allocations realizing `X` is

\[
\prod_{c:\mathrm{Color}}\binom{r_c}{(x_{p,c})_{p:\mathrm{Pile}}}.
\]

The number of **ordered decks** realizing `X` is this quantity times `∏_p n_p!`. Under global uniform deck order, the histogram has probability

\[
\pi(X) =
\frac{\prod_c\binom{r_c}{(x_{p,c})_p}}
     {\binom{N}{(n_p)_p}}.
\]

This is a **multivariate hypergeometric** law. Its two-pile/two-color specialization is exactly `blStationary N m r` and the associated fiber count. Prove `marginalLaw` and `fiberLaw` identities by disintegration: a uniform deck is uniform over allocation fibers conditional on allocation, and likewise uniform over each histogram fiber conditional on `X`.

**Edge cases:** zero-size piles/categories contribute `0! = 1` and must not create illegal divisions; use cardinality multiplication identities before converting to `Rat` so positivity/cancellation is localized.

### T3 — the universal two-pile subset-exchange law

For legal `0 ≤ k ≤ min(m,N-m)`, let `S,T` be two `m`-subsets of `Card`. Sample independently and uniformly a `k`-subset `A ⊆ S` and a `k`-subset `B ⊆ Card\S`, and set `T=(S\A)∪B`. Then

\[
K_{N,m,k}(S,T) =
\begin{cases}
\bigl[\binom{m}{k}\binom{N-m}{k}\bigr]^{-1},
 & |S\setminus T|=|T\setminus S|=k,\\
0, &\text{otherwise}.
\end{cases}
\]

The witness pair is **uniquely** `A=S\T`, `B=T\S`. This provides the simplest fundamental theorem for arbitrary `N`: no 25/25-specific case analysis, no Markov-state indexing, no 99-card orbit required to define the kernel. Derive **symmetry** `K(S,T)=K(T,S)` and stationarity of the uniform distribution on `m`-subsets. Obtain the `k=0` identity case for free. A uniform ordered-deck law is stationary under any *literal, bijective position permutation* applied according to source-independent sampling; do not silently use this claim for membership-resampling models with different semantics.

**Literal physical semantics:** separately define a deterministic swap of selected **positions**, with a stated bijection pairing the selected left and right positions. Prove that its membership projection has the preceding law, *independent of the pairing*. A further perfect local reset turns the post-swap membership into a uniform ordering within each pile. This establishes a faithful physical model and the exact abstraction boundary missing from `CommanderPhysicalExchange.rawExchange`.

### T4 — generic count projection, equivariance, and BL law

Given `M` of size `r`, `count(S)=|S∩M|`. Prove `count : Membership N m → BLState N m r`. The subset-exchange kernel is invariant under permutations of `Card` preserving `M`. This group acts transitively on each fixed-count membership fiber. Therefore, starting from uniform membership conditional on count `x`, the result is uniform membership conditional on its new count `y`.

At the count level prove

\[
\Pr(Y=y\mid X=x) =
\frac{\displaystyle\sum_{a=0}^{k}
 \binom{x}{a}\binom{m-x}{k-a}
 \binom{r-x}{\,y-x+a\,}
 \binom{N-m-r+x}{\,k-y+x-a\,}}
 {\binom{m}{k}\binom{N-m}{k}},
\]

where binomial coefficients outside their natural range contribute zero and every parameter is admissible. **Care:** the source's current guarded `Nat` definition handles negative would-be indices explicitly; do not directly replace it by a saturating-`Nat` version of this displayed formula. Reuse `BernoulliLaplaceGeneral.transitionNumerator` and the proved `BernoulliLaplaceFiber.detailedBalance`/`ExchangeOverlap.generalCL_ns` as algebraic bridges **where their exact hypotheses apply**. In particular, `generalCL_ns` assumes `k ≤ y`, so it is **not** by itself an all-state (`x,y`) kernel identity; prove the missing low-target cases or use the direct subset-kernel argument. Preserve the distinction between symbolic partial-range identities and unconditional transition theorems.

This yields the uniform-fiber intertwining

`(uniform count-fiber membership) >> (subsetExchange) = (BL exchange) >> (uniform count-fiber membership)`

in **generic** `N,m,r,k`. Combining with T1 and the literal swap/local-reset semantics yields a generic full-deck physical-perfect theorem. **The Commander F3 A3 premise should be discharged by instantiating this theorem at `(99,50,50,25)`**, not by another 99-only proof. Do not claim that the *physical kernel on arbitrary individual deck inputs* equals the oracle count-reset kernel: the equation concerns fiber-uniform inputs and appropriate lifts.

### T5 — multiple piles and categories

For a fixed capacity vector and pair of piles `i≠j`, exchange `k ≤ min(n_i,n_j)` uniformly selected cards from each. At the allocation level, the same unique `(out_i,out_j)` argument gives a reversible symmetric kernel. At the histogram level, sample category counts `a_c` and `b_c` with

\[
\Pr(a,b\mid X) =
\frac{\prod_c\binom{X_{i,c}}{a_c}\binom{X_{j,c}}{b_c}}
 {\binom{n_i}{k}\binom{n_j}{k}},\qquad
\sum_c a_c=\sum_c b_c=k,
\]

and update rows `i,j` by `X'_{i,c}=X_{i,c}-a_c+b_c`, `X'_{j,c}=X_{j,c}+a_c-b_c` (all components must remain nonnegative). Derive this kernel by **lumping the allocation chain**, not by duplicating the BL combinatorics for each category/pile. Prove that the multivariate hypergeometric `π` from T2 is stationary, and show that every individual pairwise exchange is reversible. Arbitrary fixed products of such kernels preserve `π` but are **not generally reversible as a product**.

The central symmetry theorem should quantify over the category-preserving permutation group `∏_c Sym(color^{-1}(c))`; orbit classes are exactly the valid histogram fibers. This is the many-pile generalization of the large `CommanderMembershipOrbits` proof. Prefer a **generic partition/bijection lemma**, not four explicit cases per action.

**Mixing caveat:** symmetry and stationarity do not establish convergence. A schedule that never connects some piles cannot mix globally. An eventual finite-time TV theorem must state connectivity/irreducibility or give a concrete supported schedule and quantitative contraction/spectral/coupling bound.

**G5 progress (2026-11-25, commit `67a36c5`):** the foundational two-pile/two-color reduction is **proven** in `Shufflemath/FiniteDeck/Piles.lean` (new leaf module, builds clean): the `k`-pile type machinery (`realizesAllocation`/`MultiFiber`) plus the 2-pile specialization, and the headline **`twoPile_equivFiber`** — the two-pile `MultiFiber` over the allocation `(A, univ\A)` is **in bijection** with the G2 `FibType` over `A` (`Equiv.ofBijective`, no `N!` enumeration). This is the "two-pile/two-color reduction matches G2-G4" half of the G5 gate: it makes every G2-G4 counting/disintegration/TV result transfer to the 2-pile setting. The `Finset.image_sdiff` + `univImage_eq_univ` reduction (`twoPile_pred_iff`) is the key lemma (it sidesteps the `Finset.mem_image` wall). **G5 status (2026-12-31 update):** the general-`k` product-factorial fiber count is **LANDED and green** — the bijection `multiPile_equivFiber` and the count formula `multiPile_card : Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!` are proved in `Shufflemath/FiniteDeck/MultiPileFiber.lean` via `Equiv.ofBijective` on the two round-trips + `Fintype.card_congr` + `Fintype.card_pi` + `Fintype.card_perm`, exactly the route the `g5-multipile-twoPile-reduction.md` strategy doc recommended (sidestepping the `letI`-on-`∀`-subtype `Fintype` wall). The 2-pile numeric corollary `twoPile_card` is in `Piles.lean`; the 3-pile/2-category example (`ThreePileTwoColor.lean`) and the B3 histogram core (`Histograms.lean`) are landed. **G5 status (2026-11-26, commit `8749def`):** the histogram-level `πK = π` stationary-law identity is **LANDED and green** — `validHistSet`/`validHistPi` (+ `validHistPi_mass`), `histogramTransition` (the honest two-pile histogram-level exchange kernel), `stationary_inner`, `histogramTransition_rowSum`, and `histogramTransition_stationary` (the πK = π identity `∑ X ∈ validHistSet, validHistPi X * histogramTransition … X Y = validHistPi Y`) in `Shufflemath/FiniteDeck/HistogramFiber.lean`. Remaining G5: the `G5capstone` multi-pile exchange kernel-equality (the B4 kernel lumping on top of this + the final headline).

**A1 complete (2027-01-05, commit `ef4a3a6`):** the allocation-carrier program G5 depends on
(`Shufflemath/FiniteDeck/MultiExchange.lean` + `UniformExchange.lean`) is now fully done, including
the last open item — the **A1.5 concrete `N=2` sanity witness** in a new module
`Shufflemath/FiniteDeck/A1Witness.lean`: `A0`/`A1` (the two one-card-per-pile owners of a two-card,
two-pile deck, `A1 := swapPiles A0 0 1`), `A0_ne_A1`, `swapPiles_A0_eq_A1`/`swapPiles_A1_eq_A0`
(the exchange and its involution), and `swapKernel_equivariant_at2` (the A1.4 relabel-invariance
headline at `N=2`). **So the next G5 item is:** the `G5capstone` multi-pile exchange kernel-equality
(the B4 kernel lumping + stationary law), which builds on the now-landed general-`k`
fiber bijection (`multiPile_equivFiber`), the general-`k` product-factorial fiber count
(`multiPile_card : Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!` in
`MultiPileFiber.lean`), the 2-pile numeric corollary `twoPile_card` (`Piles.lean`), and the
3-pile, 2-category example (`ThreePileTwoColor.lean`). The on-mission `TV < 1/1000` headline is already met independently by
`DobrushinDecay99` (41 perfect exchanges), so the G5/G6 work is toward the general multi-pile
campaign, not the already-met TV target.

### T6 — generic local permutations and finite inverse-GSR

For fixed pile capacities, within-pile reordering forms `∏_p Equiv.Perm (Fin (n_p))`. Prove the induced action on the ordered deck is a bijection, preserves allocation, and that any ordered deck within a given allocation fiber can be obtained by such reordering. The two-pile `pileRelabelEquiv` construction becomes a specialization.

Transport the existing `GSR.idealShuffle`, `GSR.idealShuffle_comp`, and `GSR.productLabelShuffle_uniform_eq_ideal` through a **single** list/permutation bridge per pile. For an inverse `a`-shuffle of `n` distinct cards, the distinct-label event implies an exactly uniform relative order. This yields the proposed uniform row-TV bound

\[
\sup_d \operatorname{TV}(K_{n,a}(d,\cdot), U_n)
\le \Pr(\text{label collision})
\le \min\left(1,\frac{\binom{n}{2}}{a}\right), \quad a\ge1.
\]

(The sharper exact collision probability is `1 - a(a-1)…(a-n+1)/a^n` for `a≥n`; if `a<n`, the probability is 1.) Prove the conditioning/distribution statement, not just the union bound. For independent per-pile shuffles, add row-TV errors, capped at 1. By composition and `PhysicalRefinement`, derive for any fixed-size finite protocol

\[
\operatorname{TV}(\mu K_{\mathrm{finite}},U)
\le \operatorname{TV}(\mu K_{\mathrm{perfect}},U)
   +\sum_{\text{local actions }t}\epsilon_t.
\]

A physical-action cost for an `a=2^q` inverse shuffle must count **`q` binary riffles**, not one arbitrary `a`-way operation. This is a first quantitative guarantee, possibly loose; sharper GSR theory is an enhancement, not a prerequisite for an end-to-end result.

### T7 — changing capacities, dealing, and discard/recycle

After T5 and T6, add typed actions between valid capacity states: `draw`, `deal`, `discard`, `recycle`, `cut`, `move block`, and `shuffle pile`. Prove three distinct facts for each: conservation of named cards, exact mapping of capacities, and the intended stochastic law on ordering/allocation. Model black-card and white-card stacks as distinct card universes or a tagged universe with **type-respecting** actions; never allow a mathematically convenient but physically forbidden cross-type exchange.

Start with **one** operation: sample the top card from a uniformly shuffled draw pile and move it to a player's hand or discard. Demonstrate a sound conditional-uniform result. Only then generalize to variable counts, hand secrecy, game-specific dealing rules, and known vs unknown card identities. A draw from a *nonuniformly ordered* deck is not a uniform sample: preserve the hypothesis that makes this inference valid.

### T8 — general quantitative mixing, lower bounds, and cost optimization

The exact finite kernel gives a formal, if potentially expensive, TV certificate for any specified `N` and schedule. But a useful arbitrary-`N` mathematics library should also prove **symbolic** results:

1. **Structural:** uniform stationary distributions, equivariance, exact lumping and conditional-TV isometries for every finite configuration.
2. **Upper bounds:** local-GSR collision bounds, telescoping across schedules, and a valid global bound for actual mixing of memberships/histograms. Consider coupling or reversible-operator estimates; do not assume that a one-step Dobrushin coefficient is nontrivial.
3. **Lower bounds:** exploit the already proved first BL mode (`blFirstModeFunc`) and bounded test functions. The mode factor in the two-pile model is `1 - N*k/(m*(N-m))`; it can yield a nontrivial TV lower bound when the initial state has nonzero first-mode component. Near its zero, higher modes are needed.
4. **Sharp theory (separate research track):** the remaining BL eigenmodes/Johnson-scheme geometry, higher-dimensional multi-urn spectra, asymptotic mixing and cutoff under stated scaling assumptions. Do not make this a blocker for the finite constructive theorems.
5. **Optimization:** implement generic finite action schedules and certified *feasibility* first. Minimize costs only relative to an explicitly finite admissible class and an explicit target (actual TV or certified upper bound). Claiming optimality of a conservative sufficient bound is **not** physical-optimality.

**Different initial laws are different theorems:** fixed ordered deck, uniform conditional on histogram, uniform conditional on allocation, and worst-case deck. The first two can have very different TV after the same schedule. Explicitly name which law is assumed.

## 5. Ordered Lean implementation plan with concrete acceptance gates

**Development constraint:** Qwen should implement *one small compiling generic theorem at a time*, rather than starting a giant `FiniteDeck.lean` file. The suggested module names are tentative; preserve the existing `module`, `public import`, `@[expose] public section` conventions and avoid cycles. Do not create or switch Git worktrees. Preserve old theorem APIs as specialized wrappers until callers have migrated.

| Gate | New/affected module | Exact deliverable | Acceptance (no credit for only a sketch) |
| --- | --- | --- | --- |
| **G0: baseline** | Documentation and verification harness only | Inventory public declarations, Commander specializations and import dependencies; baseline targeted build times and failing/missing theorem obligations | Explicit target builds cover `CommanderMembershipExchange`, `CommanderDeckGSR`, `ExchangeOverlap`, `FinsetFiberCount`; current test suite runs; no unverified 'F3 complete' claim |
| **G1: minimal finite deck** | `FiniteDeck/TwoPile.lean` | `Deck N`, `Membership N m`, projection, nonempty/surjective, position split/merge equivalence | Small `N,m` instances (including `N=0`, `m=0`, `m=N`) compile; no imports from `Commander*` |
| **G2: counting & disintegration** | `FiniteDeck/TwoPileFiber.lean`, `FiniteDeck/TwoColor.lean` | `m!(N-m)!` per allocation; `choose N m`; BL histogram fibers; uniform-deck disintegration | Derive the existing Commander F1/F2 count and lift facts for `(99,50,50)` by specialization; cross-check small exact examples |
| **G3: universal exchange** | `FiniteDeck/SubsetExchange.lean`, `FiniteDeck/PhysicalSwap.lean` | Exact membership mass formula; symmetry and stationary law; fixed-pair physical swap and membership pushforward | Compile for arbitrary `N,m,k`; `k=0` identity; explicit 99-card membership kernel is an instance |
| **G4: macro intertwining** | `FiniteDeck/BLRefinement.lean` | Marked-set-equivariance/transitivity, projection to the generic BL kernel and two-layer intertwining; physical perfect-local theorem | **Discharge Commander A3** and its conditional full-deck physical theorem by specialization; NO abstract `hMembershipExchange` left in the exported concrete theorem |
| **G5: multi-pile algebra** | `FiniteDeck/Piles.lean`, `FiniteDeck/Histograms.lean`, `FiniteDeck/MultiExchange.lean` | Product-factorial fiber count, multinomial stationary law, pairwise exchange and lumping | Two-pile/two-color reduction matches G2-G4; at least one 3-pile, 2-category example compiles |
| **G6: local-GSR lift** | `FiniteDeck/LocalPermutations.lean`, `FiniteDeck/LocalGSR.lean` | Product-of-pile-permutation action; finite-GSR deck kernel; TV collision bound and schedule telescope | A parameterized, unconditional **comparison inequality** for any legal fixed-size schedule, plus one explicit schedule with a nontrivial terminal TV bound and its 99-card specialization |
| **G7: moving capacity** | `FiniteDeck/ChangingPiles.lean`, `FiniteDeck/DealDraw.lean` | Transfer-one-card action and conditional-uniform law; conservation and update of capacity | A toy draw/deal/discard configuration with 3+ piles typechecks and states precisely which uniformity assumption is needed |
| **G8: certificates** | Generic protocol/cost wrappers and `Examples/Commander` | One complete symbolic finite-`N` bound, concrete parameter certificates, and a bounded cost frontier | Theorem statements explicitly quantify over legal configurations and mention epsilon/cost units/initial law; Commander is only an example |
| **G9: optional deep math** | `FiniteDeck/Spectral*.lean` | Higher modes, mixing windows, coupling/spectral bounds | Independent theorems with cited conditions and tested specializations; **not** a dependency of G0-G8 |

**Practical priority:** G1–G4 are the immediate campaign pivot; they both generalize the project and provide a route to the outstanding Commander F3 theorem. G5 is the first significant new mathematics for Cards Against Humanity-style multi-pile systems. G6 gets a quantitative finite protocol. G7 is needed for gameplay operations, but should not complicate G1–G6. The prior proof-quality review's deduplication work should be performed when the corresponding generalized theorem replaces the specialized proof—not as a separate large refactor that delays the generic mathematics.

### Stable Lean API targets (schematic; names/types must be checked while compiling)

```lean
-- Type sketches, NOT copy/paste-ready Lean code.
abbrev Deck (N : Nat) := Equiv.Perm (Fin N)
abbrev Membership (N m : Nat) := { S : Finset (Fin N) // S.card = m }

-- Generic two-pile theorem contracts:
--   fixedMembership_fiber_card : cardinality = m! * (N-m)!
--   membership_uniform_marginal : uniform deck -> uniform membership
--   subsetExchange_mass : exact S -> T probability as in T3
--   subsetExchange_symmetric : K S T = K T S
--   subsetExchange_to_BL : count projection equals blExchangeKernel p
--   uniformCount_intertwines_subsetExchange : the G4 kernel equality
--   literalSwap_membership_law : physical position-swap pushforward = subsetExchange
--   perfectLocal_physical_refinement : full deck TV = macro TV under stated input lift
```

**Type-checking note:** the `Membership` subtype is populated only when `m≤N`. Do not introduce an unguarded `Nonempty (Membership N m)` instance or a division by `choose N m` for `m>N`. Hide structural assumptions in a `TwoPileSpec` if that reduces repeated obligations. With a general `Pile` type, demand `∑ capacity = card Card` before constructing ordered decks.

## 6. Concrete proof strategies for Qwen (avoid another multi-session elaboration wall)

1. **Build equivalences, not giant case splits.** Fiber cardinality is a bijection between orderings and product of per-pile orderings. Symmetry/invariance follows from transported equivalences. Use `Equiv` and `Fintype.card_congr`; reduce factorial arithmetic only after combinatorial equivalence is established.
2. **Make the membership kernel primary.** T3 has a one-line mathematical characterization by symmetric difference and a unique witness. The count chain is a projection of this kernel; the deck kernel is a lift with explicitly proved semantics. This reverses the current tendency to start at a Commander count matrix and construct elaborate bridges backward.
3. **Prove the weakest useful general lemma once.** Extract `finsetType_perm` and `distUniform_ofInvariantTransitive` to generic finite-equivariance modules; prove histogram orbits under partition-preserving card permutations. Keep Commander thin wrappers. Do not paste the old four-part `orbitMap` into every new module.
4. **Avoid saturating-subtraction bugs.** The existing `generalCL_ns` history documents why pointwise reindexing through `Nat` subtraction can be false outside the actual support. Isolate support, reindex with bijections on legal intervals, use signed indices or guarded binomials when appropriate, and have the compiler check every boundary case.
5. **`simp only` for delicate finite probabilities.** Avoid unrestricted `simp`/`field_simp` unfolding permutations, `Finsupp` weights, and `Finset` membership. State a local point-mass lemma; use `StdSimplex.weights_inj` and `Finsupp.ext` only at the final kernel-level step. Prior F2 elaboration failures came from expansion, not necessarily from the mathematics.
6. **Separate laws from executable certificates.** Symbolic proofs should not reduce `N!` or materialize a `Fintype (Equiv.Perm (Fin N))`. Preserve array-matrix certificates and `native_decide` only for small finite states, preferably in `Examples/` or `Certificates/` modules. For arbitrary `N`, present exact symbolic formulas plus optional evaluation at concrete parameters.
7. **Preserve statement compatibility during migration.** First add a general theorem; then make the old named theorem an application; then remove duplicated proof bodies if callers compile. Verify that the new version has no stronger hidden hypotheses, particularly nonempty-pile, `k>0`, special-card and `m+r≤N` boundaries. Preserve dated prior reviews.
8. **Keep compile times visible.** Record cold and warm `lake build` of changed targets and reverse importers. Split heavy combinatorics/first-mode proofs from the small definition/API modules. A shorter proof is not automatically cheaper to elaborate. Do not increase module/import sprawl when one canonical primitive suffices.
9. **Check semantic equivalence before optimizing.** `rawExchange` in the current code is membership sampling plus `localLift`; it is not a literal paired-position swap. Prove their relationship *after* local reset and do not silently rename one as the other.
10. **Use examples and counterexamples strategically.** Small exhaustive enumerations validate formulas and catch incorrect boundary conditions but are not Lean proofs. Test at least `(N,m,r,k)=(6,3,2,1)`, `(7,2,3,1)`, `(8,4,0,2)`, `(8,4,8,2)`, `(8,4,4,0)` and the original `(99,50,50,25)`. Test 3 unequal piles with repeated categories and a draw into a hand. A theorem that assumes `m+r≤N` is not sufficient for the Commander specialization.
11. **No new overlarge umbrella module.** Commit in small increments; record theorem name, input assumptions, concrete build command, evidence of the build, and one missing dependency edge. Build directly affected optional modules because the `Shufflemath.lean` aggregator does not import them all. Preserve the no-worktrees policy.

## 7. Cards Against Humanity: what this would and would not establish

Consider distinct white cards currently distributed among a draw stack, several player hands, and a discard stack; and a separate universe of black cards with its own draw/discard stacks. Under the proposed architecture, **all of these are instances of finite labeled cards, piles, categories, and capacity-changing transfers**. Game rules determine which operations are allowed. Text duplicates remain distinct physical cards.

**Immediately useful generic theorems** are per-pile fiber counts, exchange probabilities for fixed-size allocations, stationarity/reversibility where valid, quantitative local-shuffle approximation, and compositional bounds on a specified shuffle/recycle protocol. For drawing cards, a more appropriate statement is that drawing from a uniform conditional ordering yields uniform card selection from the current draw pile, plus a corresponding update of the conditional law of remaining cards.

**Not automatically proved** are fairness under strategic player selection, adversarial knowledge, selection bias of discarded cards, hidden information, or stationarity when the draw/discard flow is one-way. Once card choices depend on text or player preferences, a category/behavior-conditioned policy may break symmetry. That dependence must appear explicitly in the kernel and in any fairness theorem. “All cards eventually become uniform” is neither a consequence of card conservation nor a sensible theorem for every permitted game action.

**Concrete multi-pile demonstration to demand:** 12 distinctly identified white cards, distributed among a 6-card draw pile, two 2-card hands, and a 2-card discard. Prove the ordered-deck/allocation fiber law, a uniform local riffle on the draw pile preserves membership of each other zone, and one specified deal/return action has the claimed conditional distribution. This is a **toy mathematical instance**, not a statement about actual game deck counts or rules.

## 8. Verification, comparative measurements, and the definition of done

For every gate:

- **Theorem inventory:** exact fully qualified theorem name; what is quantified (`N`, `Pile`, `Color`, capacities, exchange size, starting law), and which premises are discharged vs still conditional.
- **Small examples:** one boundary case, one non-Commander example, and the Commander specialization when applicable; Python or finite enumeration as regressions, never substitutes for Lean.
- **Build evidence:** relevant direct `lake build Shufflemath.<Module>` target(s), plus reverse importers and `./dev/verify_next_phase.sh` where appropriate. Do not claim Lean verification in the absence of a build.
- **Refactoring evidence:** old theorem name preserved as a wrapper; duplicate proof removed only after clients compile; module import dependencies do not become cyclic.
- **Physical-model evidence:** deterministic positional semantics, membership pushforward, local-reset behavior, finite-GSR approximation clearly distinguished.
- **Historical record:** add dated reviews/decisions, do not edit the November 15 reviews. Once the first generic gate compiles, propose a **separate explicit change** to `docs/lean_plan.md`/`AGENTS.md` to make this roadmap operational. Do not quietly replace the agent's active task queue in the same patch as this roadmap.

**Milestone proof of success:** the most informative single end-to-end theorem is a generic physical-perfect two-pile mixing identity, applied to arbitrary admissible `(N,m,r,k)` from a *fiber-uniform* input, followed by a generic finite-GSR TV budget. The most informative extension is the multi-pile/multi-color hypergeometric stationary law with exact fiber cardinalities. Everything Commander-specific should then be selectable by parameters rather than re-proved from scratch.

## 9. External mathematics and library API worth studying

These are related work and implementation leads, **not** evidence that the proposed Lean theorems already exist in this repository:

- P. Diaconis and M. Shahshahani, “Time to Reach Stationarity in the Bernoulli–Laplace Diffusion Model,” *SIAM Journal on Mathematical Analysis* 18(1), 1987, 208–218, DOI: https://doi.org/10.1137/0518016 . Relevant to the spectral/group-action research track (classic balanced one-ball regime).
- T. Griffin, B. Hall, J. Hebner, D. Herzog, D. Selyuzhitsky, K. Wong, and J. Wright, “Cutoff in the Bernoulli-Laplace Model With Unequal Colors and Urn Sizes,” https://arxiv.org/abs/2308.08676 . Relevant to the general two-pile parameter range; asymptotic results require their stated scaling assumptions.
- R. Goenka, J. Hermon, and D. Schmid, “Cutoff for generalised Bernoulli-Laplace urn models,” https://arxiv.org/abs/2511.10630 . Directly relevant to multi-color/multi-urn and labeled-stack mixing, but uses a particular family of parameters and redistribution mechanisms; do not claim its cutoff results apply to every arbitrary pile system.
- Mathlib 4 [`Nat.multinomial` documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Multinomial.html) and [`Finpartition` documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Partition/Finpartition.html). Check the pinned Mathlib snapshot before selecting theorem names; the online documentation may describe a later version.

## 10. First three instructions to Qwen

1. **Read this roadmap and the two dated November 15 proof reviews.** Create a concise *source-to-target theorem manifest* for G1–G4 in a new planning status document: each current Commander declaration, generalized target, and open/compiled state. Do not modify historical reviews or claim G1–G4 are built because their equations appear here.
2. **Implement only G1 and the first T1 counting lemma.** Keep it independent of Commander. Prove `m!(N-m)!` for arbitrary `N,m` by an explicit finite equivalence; compile it and show one small numerical specialization. This establishes whether the proposed representation leads to clean Lean proofs before adding multi-pile structure.
3. **Build the generic subset-exchange membership kernel (T3), and make G4 the immediate scientific target.** Prefer deriving Commander A3 as an instance of the general intertwining theorem rather than assembling a second specialized proof. Report actual theorem names/build results and the next missing lemma, not a new speculation-heavy planning loop.

**Strategic rule:** the point is to extract and prove the *general mathematics*, not to expand an existing Commander proof into a bigger file with `N` written everywhere. The proof campaign should become smaller in repeated combinatorial reasoning as it becomes larger in mathematical scope.
