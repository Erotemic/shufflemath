# Structural proof strategies for Qwen — revised against the 19:12 snapshot

**Date:** 2026-11-18 (evening revision)
**Source snapshot:** `shufflemath-source-2026-11-18T191243-5-0a9355945c13.tar.gz`, Git HEAD `0a93559` (last substantive Lean commit `ad60b54`).
**Replaces:** the **undelivered** earlier `2026-11-18-structural-shortcuts-for-qwen.md` overlay based on morning commit `d31e99d`. This is a working strategy, **not** a historical review and **not** a replacement for existing roadmap/review files.
**Status:** inspection of current Lean source and Git history; 37 Python tests passed. The pinned Lean/Lake toolchain is unavailable to the reviewer, so **suggested Lean statements have not been compiled**. Names cited as already proved are in the uploaded source; pseudocode signatures below are targets to check against the local elaborator.

## 0. The key change: finish A3 with what is already proved

The mathematical suggestions in the earlier overlay remain broadly useful, but its **execution order is outdated**. Do **not** suspend A3 to construct `SymmetricQuotient` now. Qwen has spent the intervening sessions assembling almost everything needed for the concrete Commander law. Finish that small remaining integration first; then extract the generic theory for arbitrary finite decks.

### Newly proved since the earlier snapshot

| Actual declaration | Current location | Why it changes the advice |
| --- | --- | --- |
| `mu_x_constant_on_countFiber` | `CommanderMembershipExchange.lean` | Within-count output mass is **already constant** by the equivariance/orbit argument. Do not redo transitivity or switch to a new orbit proof to finish A3. |
| `rawExchangeMembership_pointMass` | `CommanderA3ExchangePushforward.lean` | The membership mass of one outcome is already `1/#exchangeChoice` times its preimage count. Do not reopen `Finsupp.mapDomain`. |
| `uniformPushforward_pointMass` | `CommanderA3UniformPushforward.lean` | Generic normalization under a uniform finite pushforward is already proved. |
| `newLeftCount_eq_transitionNumerator` | `CommanderA3Kernel.lean` | The concrete selected-position pair count is already the exact BL numerator. Import and apply it; don't expand its large proof. |
| `exchangeChoice_card_eq_transitionDenominator` and `membershipCount_newMembership` | `CommanderMembershipExchange.lean` | Numerator normalization and count predicate alignment are already available. |
| `fiberSum_eq_preimageCard` | `FinsetCombinatorics.lean` (`ad60b54`) | The 54th-session disjoint-fiber double-count is **resolved**. Do not return to the failed `Sigma`/`HEq` equivalence. |

**Still not a theorem:** the full concrete `hMembershipExchange` equality, the unconditional physical-perfect corollary, the **pointwise** arbitrary-`N` membership-kernel intertwining, a full-deck literal paired-position swap, generic multi-pile theory, and explicit finite-GSR TV certificates. `FiniteDeck.BLRefinement.uniformFiber_intertwines` is a **count-aggregate equality**, not the missing pointwise membership-valued kernel equality.

The first instruction for Qwen is: **use these six committed ingredients, not fresh combinatorial scaffolding**. Defer nonessential refactors until A3 compiles.

## 1. An even smaller A3 path: package the event-mass double-count

The immediate obstacle is the total mass that the *raw exchange* assigns to all memberships with marked count `c`. Do not try to derive this by unfolding the distributions at every step. Package it once as a **generic finite-event pushforward** theorem. It is a two-lemma corollary of code that now exists.

### 1A. Generic event mass of a uniform pushforward (first small commit)

Suggested *statement shape* (adjust namespace/typeclass syntax in the local Lean):

```lean
-- Suggested in a small generic module or beside uniformPushforward_pointMass.
-- The output Y MUST be finite for these existing lemmas.
theorem uniformPushforward_eventMass
    {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (S : Finset Y) :
    (∑ y ∈ S, Dist.mass ((GSR.uniformDist X).map f) y) =
      (Fintype.card X : Rat)⁻¹ *
        (Fintype.card {x : X // f x ∈ S} : Rat) := by
  -- 1. Rewrite each summand by uniformPushforward_pointMass f y.
  -- 2. Factor out (Fintype.card X : Rat)⁻¹ with Finset.mul_sum.
  -- 3. Move Nat casts across Finset.sum (norm_cast / Nat.cast_sum).
  -- 4. Apply FinsetCombinatorics.fiberSum_eq_preimageCard Y f S.
  -- Do not unfold StdSimplex, mapDomain, or Equiv.Perm.
  ...
```

Be disciplined about the orientation of `Finset.mul_sum`, coercions from `Nat` to `Rat`, and `Fintype.card` versus the cardinality of `Finset.univ.filter`. Keep **one** proof of this finite-event formula. It also generalizes directly to multi-pile transitions later.

**Important type trap:** `membershipCount : Membership → Nat`, and `Nat` is **not** a `Fintype`. In the current source, both `uniformPushforward_pointMass` and `apply_deterministic_eq_map` require a *finite codomain*. Therefore a tempting `uniformPushforward_pointMass (membershipCount ∘ newMembership)` does **not** apply without first generalizing those lemmas. The safe route is to keep the codomain `Membership` (which is finite) and use the event

```lean
let countFiber (c : Nat) : Finset Membership :=
  (Finset.univ : Finset Membership).filter
    (fun m => membershipCount m = c)
```

This avoids rebuilding `StdSimplex.map` support lemmas solely to use an infinite codomain. If a direct `map_map` lemma later proves more convenient, ensure the codomain-side mass formula works for arbitrary `Y` (for instance via the finite-support API); do **not** assume the present statement does.

### 1B. Bridge the exchange-choice subtype to the filtered product (second small commit)

Write the single count bridge, for each deck `d` and `c : Nat`:

```
Fintype.card {j : exchangeChoice //
  membershipCount (newMembership d j.1.1 (leftCard25 j.1.2)
                                    j.2.1 (rightCard25 j.2.2)) = c}
  = ((leftChoices ×ˢ rightChoices).filter
      (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = c)).card
  = transitionNumerator 99 50 25 (leftOriginalCount d) c
```

The **first equality is a finite-type/finset representation bridge**, not a probability theorem. Use a bijection between the product of two selected-subset subtype types (`exchangeChoice`) and the subtype of the `leftChoices ×ˢ rightChoices` product. Each direction is just adding/removing membership witnesses. Preserve the count predicate via `membershipCount_newMembership`. Prefer `Fintype.card_congr` + `Fintype.card_of_subtype` or `Finset.card_bij'`; with fixed product components, the inverse laws should reduce by `Subtype.ext`/`Prod.ext`, not dependent `Sigma` equality. Prove it **as a separate lemma** so Lean does not re-elaborate this bridge in the large A3 proof.

The **second equality is already `CommanderA3Kernel.newLeftCount_eq_transitionNumerator`**. The current theorem internally imports `_Probe47v`; use its compiled declaration, not a new summation argument. Once A3 is green, move the production-relevant probe lemmas into named stable modules and eliminate production imports of `_Probe*` in a separate cleanup.

### 1C. Count-fiber mass for one source deck (third small commit)

Instantiate `uniformPushforward_eventMass` with:

- `X := exchangeChoice`, `Y := Membership`;
- `f j := newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)`;
- `S := countFiber c` (the finite `Membership` event, not a `Nat` codomain).

Use `rawExchangeMembership`'s existing `.map` definition, the choice-count bridge, and `exchangeChoice_card_eq_transitionDenominator`. Obtain the **event-mass law**

```
∑ m ∈ countFiber c, Dist.mass (rawExchangeMembership d) m
  = (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat)
      / (transitionDenominator 99 50 25 : Rat).
```

Or use the already-proved point-mass lemma, followed by `fiberSum_eq_preimageCard`, to reach exactly the same equation. **Choose one** implementation. The event-mass wrapper is preferable for reuse; if it creates an unexpected instance problem, finish by the direct point-mass + disjoint-fiber calculation. Both lead to the same short last step.

Do not claim that the `uniformPushforward_pointMass` theorem alone proves this: it handles **one membership**, not the total mass of a count-fiber. The new `fiberSum_eq_preimageCard` is what closes that gap.

### 1D. Average over the macro-source fiber without enumerating decks

The preceding mass depends on `d` **only** through `leftOriginalCount d`. For `project d = x`, use `project_count` / `membershipCount_of_project` to identify this count with `commanderLeftCount x`. Then the macro fiber law averages **a constant**, so its total is the same constant. Avoid materializing or normalizing `99!` permutations.

If the algebra becomes cluttered, first prove a *generic finite-event kernel application* lemma (finite codomain):

```
eventMass (FiniteKernel.apply μ K) S
  = ∑ d, Dist.mass μ d * eventMass (K d) S
```

by `FiniteKernel.apply_mass`/`apply_mass_dom` and `Finset.sum_comm`. Its role is only to interchange a finite event sum and a finite mixture. Then use `fiberLaw_mass` to kill rows outside `project d = x` and `Dist.sum_mass` to collapse the constant. In the final Commander theorem, reference the event-mass lemma by name; do not unfold its implementation.

**A separate issue:** `commanderExchange25_countMass` is already the RHS count law and handles infeasible `c` with an `if`. Check that the LHS numerator formula agrees in all `c`, not only those in `Fin 50`; the event is empty outside the feasible range. Either prove the target identity for all `Nat` with those zero cases, or compare at the typed `CommanderState` level and use an explicit count-encoding bridge.

### 1E. Recover the entire pointwise A3 kernel using the *existing* constancy lemma

Let `μx := (comp (fiberLaw project project_surjective) rawExchangeMembership) x`.
For target `m`, put `c := membershipCount m`, `F_c := countFiber c`. Then:

```
∀ m' ∈ F_c, Dist.mass μx m' = Dist.mass μx m
```

is exactly what `mu_x_constant_on_countFiber` supplies. Thus

```
∑ m' ∈ F_c, Dist.mass μx m' = (F_c.card : Rat) * Dist.mass μx m.
```

Combine with the count law and `membershipFiber_card` to get the RHS of `hMembershipExchange_rhs_mass`. **No new transitivity or invariance proof is needed.**

For `F_c.card > 0`, do **not** prove positivity by expanding binomial coefficients: `m ∈ F_c`, so `Finset.card_pos` has the witness `m`. For the RHS feasibility test (`1 ≤ c ∧ c ≤ 50`), obtain some `d` with `membership d = m` from `membership_surjective`; `membershipCount_of_deck` and `commanderLeftCount (project d) = (project d).val + 1` give the bounds without inclusion-exclusion arithmetic.

Now use `FiniteKernel.ext` or `funext` + distribution extensionality, apply `hMembershipExchange_lhs_reduces` to put the LHS in `μx` form, and rewrite the RHS by `hMembershipExchange_rhs_mass`. Instantiate the previously *conditional* `two_physical_perfect_exchanges_uniform_of_counts`. This is the A3 acceptance gate; no `sorry` or extra hypothesis named `hMembershipExchange` may remain in the **unconditional corollary**.

**Please do not start another 900-line Commander orbit, another `Fintype.card_sigma` proof, or a second generic hypergeometric count proof.** They are already unnecessary for this gate.

## 2. After A3: the beautiful reusable result is symmetric lumping

This **still makes sense** and becomes the organizing theorem for arbitrary two-pile and multi-pile models. But it is now **the next reusable abstraction**, not the blocker to completing the already-advanced A3.

Let `X` be a finite microstate type, `obs : X → Y` a surjective observation, `K : FiniteKernel X X` symmetric, and `P : FiniteKernel Y Y` a *strong lumping*: for every `s : X`, the mass of `K s` on `obs⁻¹(y)` is `P (obs s) y`.

Then there is a short, source-independent proof:

```
|F_x| P(x,y)
  = Σ_{s∈F_x} Σ_{t∈F_y} K(s,t)
  = Σ_{t∈F_y} Σ_{s∈F_x} K(t,s)
  = |F_y| P(y,x).
```

This gives detailed balance under fiber-size weights. For any `t ∈ F_y`, the *output from a uniformly chosen source fiber* has mass

```
(1/|F_x|) Σ_{s∈F_x} K(s,t)
    = P(y,x)/|F_x|                (symmetry + reverse row lumping)
    = P(x,y)/|F_y|                (double-count balance).
```

That is the **pointwise uniform-fiber intertwining**, not merely the aggregate count identity. With normalization it also proves `π(x)=|F_x|/|X|` is stationary for `P`.

**Lean order:** (1) `edgeSum_balance` using `Finset.sum_comm`, (2) `fiberCard_detailedBalance` using strong lumpability, (3) `fiberLaw_intertwines` by extensionality and `fiberLaw_mass`, (4) stationary quotient law. Keep this in a standalone `Shufflemath/SymmetricQuotient.lean` importing generic finite probability modules only; **no Commander/FiniteDeck imports**. You may take the two equalities at the sum level as hypotheses before constructing typed `FiniteKernel`s, which reduces elaboration cost.

**Two vital hypotheses:** `K` must be symmetric, and the quotient must be **strongly lumpable**. Being reversible alone under a nonuniform measure is not this theorem. The product of two symmetric kernels is not generally symmetric, although products of kernels sharing the same stationary law preserve that law. A state-independent mixture of symmetric kernels *is* symmetric.

### Apply it to G4 with a genuine generic micro-kernel

`FiniteDeck.SubsetExchange.subsetExchangeKernel_symm`, `_rowOne`, `_colOne`, and `_stationary` prove the matrix-level facts. `FiniteDeck.BLRefinement.yMoves_card_eq_transitionNumerator`, `countFiberMemb_card`, and `uniformFiber_intertwines` supply the count analysis. What is still missing is a **typed** kernel and the row-to-fiber mass statement connecting these layers.

Proof architecture:

1. Put the existing rational matrix `subsetExchangeKernel` on a finite type of legal `m`-subsets (`Membership N m` or the subtype of `pileSet N m`). Use `_rowOne` for stochasticity. Preserve the matrix definition as the canonical calculation; do not prove row sums again.
2. Prove `rowFiberMass`: for any source membership `S` with marked count `x`, summing the kernel over destinations with marked count `y` equals `BernoulliLaplaceGeneral.transitionWeight N m r k x y`. The unique leave/enter pair `(S\T, T\S)` is the key bijection. Use `yMoves_card_eq_transitionNumerator`; treat all boundary counts, not only those covered by `generalCL_ns`'s `k ≤ y` hypothesis.
3. Apply `SymmetricQuotient` to get a **full membership-valued** kernel equation. Keep `BLRefinement.uniformFiber_intertwines` as a derived aggregate lemma or compatibility wrapper, not the claimed full theorem.
4. Specialize this general theorem to Commander as an independent **regression corollary**, not a duplicate proof. Compare to the already-closed Commander A3; investigate if the two encodings agree without rewriting the compiled proof.

The subtle bridge is **literal physical selected positions → uniformly selected card subsets**. Because a deck is a bijection, the two selected-position spaces map bijectively to the subsets of card identities in their respective piles. Prove this pushforward equivalence once; do not make every generic transition theorem reopen finite permutations.

## 3. Faithful physical semantics: separate position swaps from local randomization

`CommanderPhysicalExchange.rawExchange` currently composes the **membership-level** exchange `rawExchangeMembership` with a uniform membership-fiber resample `localLift`. It is not itself the deck-valued operation of swapping `25` selected position pairs under a fixed matching. Likewise `FiniteDeck.PhysicalSwap` currently defines `newLeftCards` and `literalSwapMembership` (membership, not full-deck permutation).

To justify a theorem about **the literal physical action**, construct a permutation of positions for each selected pair of `k`-sets with an explicit pairing `e : selectedLeft ≃ selectedRight`. Swap each pair; fix every other position. Prove the permutation is an involution (or directly bijective). Acting on an input deck by that position permutation gives a genuine deck-valued swap, and its membership is exactly the existing `newLeftCards`/`literalSwapMembership` outcome, independent of the pairing.

Two separate statements then become easy to distinguish:

- **Physical membership pushforward:** any fixed bijective pairing yields the same membership transition law after uniformly selecting the two sets.
- **Physical swap followed by independent perfect local shuffling:** its resulting deck law equals the current `rawExchange` membership-and-`localLift` construction (once the choice-pushforward bridge is proved).

Avoid claiming the second distribution is identical to the *bare* physical swap. The latter retains ordering information; the local resample intentionally discards it. Start this after A3; it is crucial for the protocol's semantics, not for the missing scalar-count algebra.

## 4. Multi-pile/category mathematics: pushforward first, count later

For arbitrary finite piles (capacities `n_i` with sum `N`), represent an allocation as a map from **distinct cards** to pile IDs with prescribed fiber sizes. A histogram records each pile's counts in each category; it does not identify cards of the same category.

Useful general identities, proven without enumerating permutations:

- For a fixed allocation of labeled cards to ordered piles, its ordered-deck fiber contains `∏_i n_i!` arrangements.
- For fixed category totals `r_j` and histogram entries `x_ij`, the number of distinct-card allocations with that histogram is `∏_j r_j! / ∏_{i,j} x_ij!`. For Lean `Nat` counting, prefer the multiplicative identity `fiberCard * ∏ x_ij! = ∏ r_j!` over premature division.
- Uniform allocations induce the multivariate hypergeometric histogram law. Two piles/two categories recover the BL law.

For a pair of piles `i,j`, *define* exchange as the pushforward of uniform choices of a `k`-subset from each pile. The kernel is then normalized by construction; don't prove a multivariate Vandermonde identity as a precondition for defining it. The inverse move from target back to source swaps the *same* changed-card sets, so the allocation-level kernel is symmetric. The category-profile transition law is then obtained by counting independent choices across categories:

```
∏_category choose(x_i, a) * choose(x_j, b),
```

summed over selection profiles `a,b` with totals `k` and the required target counts.

Strong lumpability follows because these counts depend only on the histogram, or from transitive category-preserving relabelings. **Choose the shorter proof**, then apply `SymmetricQuotient`. A state-independent mixture of symmetric pair-exchange kernels also works. A state-dependent choice of which piles to exchange needs a separate invariance argument.

Keep a single finite allocation type with explicit capacity constraints; do not burden the first proofs with variable-capacity draws/discards. Those need a time-dependent or sigma-indexed state type and different transition semantics.

## 5. Finite GSR: prove rank uniformity on the collision-free event

For an `n`-card pile with independent uniform labels in `Fin a`, stably sort by labels. Conditional on labels being pairwise distinct, all `n!` rank orderings are equally likely. Hence the shuffle law is a mixture of the uniform permutation law (on the no-collision event) and some other law (on the collision event):

```
TV(GSR(n,a), Uniform(n))
  ≤ Pr(any labels collide)
  ≤ min(1, Nat.choose n 2 / a).
```

For `t` binary riffles, existing `GSR.idealShuffle_comp` gives effective alphabet `a=2^t`; the bound becomes `min(1,n(n-1)/2^(t+1))`. For independent piles, add the pilewise bounds and cap at 1.

The difficult Lean insight is to represent stable sorting as a **permutation of `Fin n`**, not as a uniform distribution on unrestricted lists. To prove collision-free rank uniformity either:

- use equivariance under relabeling of the `n` card positions, or
- count exactly `choose(a,n)` injective label assignments per relative ordering.

Do not calculate all `n!` shuffle probabilities. Do not confuse the GSR label law with uniformity **unconditionally**; ties introduce the approximation error. Treat `n ≤ 1` and `a < n` explicitly; the trivial TV bound 1 handles zero probability of all distinct labels. The remaining engineering is a stable-sort-to-permutation bridge and a finite-event TV coupling bound. The current Commander local GSR and generic product-TV results can then supply protocol composition.

## 6. General finite mixing: connectivity before spectrum

Uniform stationarity by itself does **not** establish convergence. E.g. at `N=4,m=2,k=2`, full exchange maps every left subset to its complement and leaves three disconnected pairs. Lazifying that `k=2` kernel does not connect them.

For `0<m<N`, use **lazy one-card exchange** `L=(I+K_1)/2`. From membership `S` to `T`, repeatedly swap a card in `S\T` with one in `T\S`; this decreases `d=|S\T|` by 1. Let `ell=min(m,N-m)` and `q=1/(2*m*(N-m))`. Pad the path to `ell` steps with self-loops. Every target then receives at least `q^ell` probability after `ell` steps. With `C=choose(N,m)`, this is a uniform minorization with `epsilon=C*q^ell > 0`, yielding

```
TV(μ L^(t*ell), UniformMembership) ≤ (1-epsilon)^t.
```

This bound is very loose but fully symbolic and valid for *every* starting membership distribution. In Lean, first prove the distance-reducing path and its positive probability; then a generic minorization-to-TV contraction lemma. **Do not require one-step Dobrushin contraction** or the entire spectrum to certify finite mixing. For full ordered decks, additionally include within-pile permutation generators; membership mixing does not imply deck-order mixing.

For multiple piles, connectivity of the **legal transposition graph** (plus self-loops) is the relevant hypothesis. Be explicit about empty piles, whether fixed capacities are positive, and whether the allowed swaps actually generate the full arrangement state space.

## 7. What mixing bounds do and do not prove for games

Strong lumpability means the observed histogram is Markov, even from a point-mass microstate. It does **not** mean that a histogram near equilibrium implies a full deck near uniform. A deck of only one card category has a trivial histogram yet can remain completely ordered.

A perfect local shuffle uniformizes *order given membership*, not membership given category counts. For arbitrary starting decks, bound nonuniformity within the observed fiber separately, or prove full-deck mixing directly, or add a true full-fiber randomization step.

For Cards Against Humanity-style **one-shot** dealt hands, if the whole shuffled deck is within `ε` TV of uniform, any deterministic deal/readout — and any randomized, state-independent dealing kernel — produces an observation law within `ε` TV of the corresponding uniform-deck observation (TV data processing). This avoids prematurely formalizing the entire game. Dynamic draws, recycling, discard rules, two card universes, and variable capacities do require their own type-safe evolving-state model.

## 8. Cost certificates: three different targets

1. **Feasibility:** a concrete protocol and a proved terminal TV upper bound `≤ ε`.
2. **Bounded optimization:** a provably cost-minimal schedule in an explicitly **finite** candidate class (action alphabet, maximum length, and an exact cost convention). Optimizing a sufficient TV certificate need not optimize actual TV.
3. **Global optimality:** a lower bound for all protocols in a well-specified, potentially larger class. Do not claim it from (2).

The existing generic first-eigenfunction machinery may provide lower bounds for some regimes, but a vanishing first mode can require another witness. Do not make sharp spectra or global optimality block a useful general finite-deck theorem or one explicit protocol certificate.

## 9. Lean proof-engineering rules tailored to the current failure modes

- **Compiled lemmas are opaque building blocks.** Use `exact named_theorem` or `rw [named_theorem]` rather than unfolding `Equiv.Perm (Fin 99)`, `leftOrigSet` filters, `StdSimplex`, or large `Fintype` instances in a deep proof. The previous `leftOrigSet` reduction wall was solved by an intermediate *named*, separately compiled theorem, not by larger heartbeat limits.
- **Do not redo solved work.** In particular, `fiberSum_eq_preimageCard` is now compiled; stop the 54th-session `Sigma`/`HEq` exploration. `mu_x_constant_on_countFiber` and the 47v choice count are also done.
- **Put generic algebra before specialization.** A 10-line event-mass theorem is worth more than another hundred lines of 99-specific `Finsupp` normalization. Conversely, do **not** build `SymmetricQuotient` until A3 is closed: that would be generalized detour, not immediate leverage.
- **Avoid codomain assumptions by reading signatures.** `apply_mass_dom` avoids `[Fintype beta]`, but `apply_deterministic_eq_map` and `uniformPushforward_pointMass` still require it. For an event in `Nat`, keep a finite `Membership` event or deliberately generalize the generic lemma in isolation.
- **Use canonical types and stable imports.** Prove generic `Membership N m` results independent of Commander; retain existing Commander theorem names as wrappers when generalization is compiled. The production `CommanderA3Kernel` currently imports `_Probe47v`; after closure move that proof into a stable named module and retire probe dependencies in a separate, measured change.
- **Proof-complexity hygiene.** Inspect imported theorem signatures and Mathlib API before writing dependent equivalences. Prefer `Finset.card_biUnion` and finite fibers over a custom `Sigma` bijection with heterogeneous proof-equalities. Do not add a new `Fintype` instance when a canonical one exists.
- **Verification is an actual build, not a status label.** The checked-in `dev/verify_next_phase.sh` covers Commander A3 helpers but not the six new `FiniteDeck` modules; targeted `lake build Shufflemath.FiniteDeck.BLRefinement` (and related modules) is therefore a separate required gate. The reviewer could not run Lean; Qwen must record its own build results.
- **Small coherent commits:** one generic helper; one subtype/choice bridge; one count law; one macro average; one kernel equality. If a lemma gets stuck, leave the *smallest* failing statement and actual Lean error, not another large documentation trail.

## 10. Explicit execution order and stopping criteria

**Immediate A3 closure (do now):**

1. Confirm that `ad60b54`'s `FinsetCombinatorics.fiberSum_eq_preimageCard` builds, together with `CommanderA3ExchangePushforward` and `CommanderA3Kernel`.
2. Prove `uniformPushforward_eventMass` **or** use `rawExchangeMembership_pointMass` + the committed `fiberSum_eq_preimageCard` directly. Do not implement both derivations.
3. Prove exchange-choice preimage count = product-filter count = `newLeftCount_eq_transitionNumerator`; apply the already-proved denominator theorem.
4. Prove `rawExchange_membershipCount_mass` for one deck, then collapse the macro-source uniform fiber using `project_count` and normalized mass.
5. Combine the count-fiber total with `mu_x_constant_on_countFiber`, `membershipFiber_card`, and `hMembershipExchange_rhs_mass` to establish **the full `hMembershipExchange`**. Obtain the unconditional physical-perfect corollary. Build the complete affected Commander modules.

**Next general finite-deck foundation:**

6. Prove the generic symmetric finite-kernel quotient theorem, then the **full pointwise** `FiniteDeck` subset-exchange/BL intertwining, with the choice-to-reachable-target row bridge explicit.
7. Prove the genuine arbitrary-`N` paired-position swap, then the local-shuffle composition semantics. Use Commander as a regression specialization, not a foundational type.
8. Build multi-pile allocations and category histograms, exchange kernels defined by finite uniform-choice pushforward, and the multivariate hypergeometric quotient law.

**Quantitative/deck-facing results:**

9. Establish the finite-GSR collision TV bound and transfer it through independent piles and protocol schedules; develop the constructive lazy-one-swap mixing bound separately.
10. Produce one explicit finite-`N` (and one Commander) sufficient protocol certificate, then bounded cost optimization and only later global lower bounds.

**Acceptance for every theorem:** no admitted holes in its proof graph; targeted `lake build` succeeds with the repository's pinned toolchain; its public statement says exactly whether the law is a *count* law, *membership* law, or *full-deck* law; no hidden hypothesis is dropped; any test-specific numeric result is a specialization of the general theorem where possible. Preserve historical reviews unchanged.

