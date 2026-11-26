# Histogram-observation specialization of the disintegration machinery (T2)

**Status:** strategy document (2026-12-31) — the next honestly-scoped G5 landing.
Not a theorem; nothing in this document is claimed as proved until it compiles.

## What is landed (verified green on `main`)

- Fiber counts at the allocation level: `twoPile_equivFiber` / `multiPile_equivFiber`,
  `multiPile_card : Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!` (`MultiPileFiber.lean`),
  `twoPile_card` (`Piles.lean`), and the 3-pile, 2-category example (`ThreePileTwoColor.lean`).
- The allocation-level counting identity at the kernel level: `lumpedNum c X a`
  (`Histograms.lean`) = `∏_j choose (X j) (a j)`, factored two-pile
  (`twoPile_lumpedNum_factor`), normalized (`lumpedConditionalMass`, `lumpedTransition`),
  with `lumpedTransition_factors` (kernel = product of per-pile conditional masses).
- The kernel machinery: bounds (`lumpedNum_le_choose`, `lumpedConditionalMass_le_one`,
  `lumpedTransition_le_one`), stochasticity (`lumpedConditionalMass_rowSum`,
  `lumpedTransition_rowSum`, `fin_lumped_rowSum` bridge), exact support (zero/positive
  per-pile and two-pile, `lumpedTransition_eq_zero_iff`), well-definedness ((0,1] on the
  valid interior, `lumpedTransition_kernel_well_defined`), reversibility
  (`exchangeTargets_symmetric` + `lumpedTransition_swap`).
- The type-generic disintegration toolbox (`FiberDisintegration.lean`): `fiberSet`,
  `fiberLaw`, `marginalLaw`, `marginalLaw_mass`, `fiberLaw_mass`, `fiberLaw_recovers`,
  `marginal_comp_fiber_eq_uniform`, `stationary_disintegrates_of_mass`.
- Bernoulli-Laplace specialization (two-pile/two-color): `blStationary`,
  `blStationaryDist`, `blRowStochastic` — the T2 π for the two-pile/two-color case.

## The precise gap

The T2 histogram identity is about the **histogram observation**, not the membership
observation: `observe : β → α` where `β` is the space of microscopic states (ordered
decks, or `k`-subsets with a per-pile category breakdown) and `α` is the space of
histograms `X = (x_{p,c})_{p:Pile,c:Category}`. The generic machinery is landed, but it
has only been specialized to `membership` (via A3KernelLaw) and `blStationary` (the
Bernoulli-Laplace two-pile/two-color case). The remaining obligation for the T2
specialization:

1. Define the histogram observation `β → Hist` over the relevant state space.
2. Prove the histogram-fiber count: the number of microscopic states realizing `X`
   equals `∏_c choose (r_c, x_p) · ∏_p n_p!` (the T2 fiber count, with the factorial
   product for the within-pile ordering).
3. Specialize `marginalLaw`/`fiberLaw` (or `stationary_disintegrates_of_mass`) to the
   histogram observation, i.e. prove `uniform deck = uniform over histogram fiber
   conditional on X`, and that `marginalLaw` equals the T2 multivariate-hypergeometric
   law `π(X) = ∏_c binom(r_c, x_p) / multinomial(N; n_p)`.
4. From there, the `πK = π` stationary law and the `G5capstone` headline assemble.

## The two routes to step 2/3, and their status

**Route A — Sigma-lumping (Fintype-walled).** Define the histogram fiber as a `Sigma`
type over the per-category breakdown and rewrite with `Fintype.card_congr`. The
documented failure mode: `rw`/`simp`/`conv` cannot rewrite the
pile-index-dependent `⟨q, ⋯⟩` subtype-proof term (see `g5-multipile-twoPile-reduction.md`).
Do not re-litigate this route; it was already tried and hit the wall.

**Route B — list-based Vandermonde (clean, incomplete).** The per-pile list-form total
`histAllocSum (List.ofFn X) k = choose (ΣX) k` (`fin_lumped_rowSum`) is landed. What is
missing: the **allocation-chain extraction** — proving that the conditional probability
of the per-(a,b) lumped kernel arises as the fiber-uniform law over the allocation
fiber, i.e. the identity relating the landed `lumpedConditionalMass`/`lumpedTransition`
(the explicit product form) to the generic `fiberLaw`/`marginalLaw` at the
histogram-over-allocation observation. The cardinality identity is the honest
intermediate step; it is the missing "derive Pr(a,b|X) from the allocation chain" item.

## Scoped next theorems

1. **Histogram-fiber count (Route B).** For a two-pile/two-color allocation, prove
   `#decks realizing X = ∏_c choose (r_c, x_p) · ∏_p n_p!`. This is the B3 histogram
   core refined from `histAllocSum` to a fiber-count statement.
2. **Marginal law (T2).** `marginalLaw histogramObs = π` (the multivariate-hypergeometric
   law), via `stationary_disintegrates_of_mass` applied to the T2-weighted stationary law.
3. **Stationary law (T2/G5capstone).** `π K = π` — the two-pile `blStationary` identity
   generalized to the histogram state space.

## Honest scope of this document

This document scopes the work. It claims no theorems. The Sigma-lumping route stays
walled; Route B (list-based) is the candidate, and step 1 is the honest first landing.
