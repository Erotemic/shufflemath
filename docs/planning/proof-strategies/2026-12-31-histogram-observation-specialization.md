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

## Landed (2026-12-31, this session) — the allocation-level fiber count

**`Shufflemath/FiniteDeck/HistogramFiber.lean`** (new module, wired into the
aggregator + verify gate; gate green, 37 tests):

- `histFiber N color X` — the pile-0 sets consistent with per-category pile-0
  counts `X` (a filtered-powerset fiber, mirroring `powersetCard_markedSplit`).
- **`twoHist_fiber_card`** — the T2 allocation-level fiber count for the
  two-pile/two-color case, via the `Finset.card_bij'` product bijection
  (per-category powersetCards) mirroring the landed `powersetCard_markedSplit`
  idiom:

  `(histFiber N color X).card = choose r_0 (X 0) * choose r_1 (X 1)`

  where `r_c = #category-c cards`.  The product `∏_c choose (r_c, x_{0,c})` is
  the numerator of the two-pile T2 histogram law at the allocation level; the
  deck-level identity (`× ∏_p n_p!`) is genuinely the Sigma-lumping wall
  (documented above) — the fiber-over-`X` type needs the pile-index-dependent
  dependent-subtype rewrite, which is blocked, and the doc's "Scoped next
  theorems" step 1 names exactly this composition.
- **`allocFiberCount`** — the total two-pile allocation count: the number of
  pile-0 sets of size `n_0` is `choose N n_0` (landed `Finset.card_powersetCard`).

**Honest remaining gap (unchanged):** the ordered-deck fiber count
`#decks realizing X = [∏_c binom(r_c, x_{0,c})] · ∏_p n_p!` — the deck-level
composition — and the `πK = π` stationary law.  Both are the documented
Sigma-lumping/stationary-law work, not tactics.

## Landed (2026-12-31, this session) — marginal-law specialization

`Shufflemath/FiniteDeck/HistogramFiber.lean` now also carries the **histogram
specialization of the landed `FiberDisintegration` machinery** (the T2 marginal
law at the allocation level, over the full allocation space):

- `Hist2 N` — bounded two-pile histogram values `Fin 2 → Fin (N+1)` (finite
  codomain; per-category pile-0 counts, each ≤ N).
- `histObs` — the histogram observation over the full allocation space
  `Finset (Fin N)` (the pile-0 sets, all sizes): per-category pile-0 counts.
- `fiberSet_histObs` — the fiber of the observation is exactly the landed
  `histFiber` (equality of `Finset`s; `Finset.card_bij'`-independent identity).
- **`histMarginalLaw_mass`** — the T2 marginal-mass identity over the full
  allocation space:

  `Dist.mass (marginalLaw histObs) X = (choose r_0 (X 0).val * choose r_1 (X 1).val : Rat) / (2 ^ N)`

  — the per-category binomial product divided by the total-allocation count
  (`2 ^ N`, via landed `Fintype.card_finset`).  Composition of three landed
  pieces: `marginalLaw_mass` + `fiberSet_histObs` + `twoHist_fiber_card`.

This lands the T2 marginal-law piece at the **allocation level over the full
space**.  The size-constrained variant (the T2 **size-`n`** law, denominator
`choose N n`) and the deck-level identity (`× ∏_p n_p!`) remain the Sigma-lumping
wall documented above — the size-`n` fiber is an indexed dependent subtype whose
card computation is the blocked pile-index-dependent rewrite.  The `πK = π`
stationary law (T2/G5capstone) remains unlanded, as before.

## Landed (2026-12-31, this session) — the T2 size-`n` marginal law

`Shufflemath/FiniteDeck/HistogramFiber.lean` now also carries the **size-`n`**
marginal law — the T2-true law — as a **plain Finset-card / Rat identity**,
with no dependent subtypes (the documented Sigma-lumping wall stays untouched):

- `sizeNHistFiber N color n X` — pile-0 sets of size `n` consistent with per-category
  counts `X` (a size-filtered histFiber).
- **`card_split`** — the size of a pile-0 set is the sum of its per-category
  filtered card counts (two color classes; `Disjoint` split via
  `card_union_eq_card_add_card.mpr`).
- **`sizeN_histFiber_card`** — the T2 size-`n` fiber count:

  `#size-n fiber = if X 0 + X 1 = n then choose r_0 (X 0) * choose r_1 (X 1) else 0`

  (when `X 0 + X 1 = n` the fiber is exactly the landed `histFiber`, so the
  landed `twoHist_fiber_card` applies; otherwise the size constraint forces
  every per-category-consistent set to have size `X 0 + X 1 ≠ n`, so the fiber
  is empty).
- **`sizeN_marginal_law_mass`** — the honestly-scoped T2 marginal law at the
  allocation level:

  `#fiber(X) / #allocations(n) = [choose r_0 (X 0) * choose r_1 (X 1)] / (choose N n)`

  when `X 0 + X 1 = n`, else `0`.  This is the actual T2 shape: per-category
  binomial product over `choose N n` (the size-`n` allocation count, landed as
  `allocFiberCount`) — the multivariate-hypergeometric law **numerator** over
  the size-`n` allocation space, as a `Rat` identity.  No
  `marginalLaw`-over-subtype construction needed.

**Honest remaining gap (unchanged):** the deck-level identity (`× ∏_p n_p!`) is
still the documented Sigma-lumping wall.

## Landed (2026-11-26, this session) — the T2 histogram-level `πK = π` stationary law

`Shufflemath/FiniteDeck/HistogramFiber.lean` now also carries the honest
two-pile/two-color stationary-law identity (roadmap T5 line 176):

- `validHistSet N m r0 r1` — the valid two-pile histogram state space as a
  `Finset (Hist2 N)` carrier (total size `m`, per-category bounds `r0`, `r1`):
  `(Finset.univ : Finset (Hist2 N)).filter (fun X => (X 0).val + (X 1).val = m ∧ (X 0).val ≤ r0 ∧ (X 1).val ≤ r1)`.
- `validHistPi N m r0 r1 X` — the honest T2 π law over that space:
  `(choose r_0 (X 0) * choose r_1 (X 1) : Rat) / choose N m`.
- `validHistPi_mass` — `∑ X ∈ validHistSet, validHistPi X = 1`: strict 1-mass
  over the valid-histogram carrier (Vandermonde + filter-sum identity).
- `histogramTransition N m r0 r1 k X X'` — the honest two-pile histogram-level
  exchange kernel (`noncomputable def`): the number of `(a, b)` sub-allocations
  consistent with `X` and producing `X'`, normalized by `choose m k * choose (N - m) k`.
- **`stationary_inner`** — the per-`(a, b)` inner-sum collapse: for every valid
  `Y`, if `X ∈ validHistSet` then
  `∑ X ∈ validHistSet, validHistPi X * (if Y = X - a + b then sw(X, a, b) else 0) = validHistPi Y * sw(Y)`,
  with `sw(Y) = choose (Y 0) b.1 * choose (Y 1) b.2 * choose (r0 - Y 0) a.1 * choose (r1 - Y 1) a.2` —
  proved for both the `Y`-matches-`(X - a + b)` case and the zero case (the zero
  case needs the double Vandermonde `∑ b sw(Y) = choose(m, k) * choose (N - m) k`).
- **`histogramTransition_rowSum`** — the honest kernel row-sum identity:
  `∑ X', histogramTransition N m r0 r1 k X X' = 1` over the valid-histogram carrier
  (Fubini over `(X, a, b)`, the `zero`-row case collapses by exhaustion, the
  support case by the two Vandermondes).
- **`histogramTransition_stationary`** — the πK = π stationary-law identity:
  `∑ X ∈ validHistSet, validHistPi X * histogramTransition N m r0 r1 k X Y = validHistPi Y`
  for every valid `Y`. Proof: Fubini over `(X, a, b)`; collapse the per-`(a, b)`
  inner sum via `stationary_inner` (one-term collapse to `π(Y) · sw(Y) / D`);
  the two Vandermonde splits of `∑_{a,b} sw(Y) = choose (m, k) * choose (N - m, k)`;
  universal normalisation `D = choose m k * choose (N - m) k`.

`histogramTransition` unifies the two-pile/two-color exchange (T4) at the
histogram-observation level and is stationary under `validHistPi` — together
with `validHistPi_mass`, the honest T2 marginal law and its stationary law are
now fully landed at the allocation level.

**Honest remaining gap (unchanged):** the ordered-deck fiber count
`#decks realizing X = [∏_c binom(r_c, x_{0,c})] · ∏_p n_p!` — the deck-level
composition — is still the documented Sigma-lumping wall. Also still open: the
G5 multi-pile capstone headline (B4 kernel lumping + the final assembly). The
size-`n` marginal law lands the *numerator/denominator shape* of the T2 law,
not a `marginalLaw`/`fiberLaw` object (that needs the size-`n` allocation space
as a dependent subtype — the blocked route).
