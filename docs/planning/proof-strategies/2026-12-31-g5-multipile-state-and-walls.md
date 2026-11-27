# G5 multi-pile — state, walls, and next increments

**Session:** 2026-12-31 (resumed after compaction; then resumed again post-compaction)
**Status:** G5's headline `G5capstone` (the k×c multi-pile exchange kernel-equality)
was blocked by two structural walls. **Wall 1 (Histograms import-exposure) is now
CRACKED and landed** — the root cause was not a missing import but the
classic-`Finset`-API refactor (details below); the module is rewritten against this
Mathlib's API, builds green, and is integrated into the aggregator + verify script.
**Wall 2 (general-k product-fiber Fintype) remains** — it needs the product-fiber
`Fintype` instance, the real capstone blocker. The build is green (37 tests OK,
EXIT 0); everything committed. **Both B3 histogram lemmas are now proven**:
`lump_pileTotal` (row-total = pile size) and `lump_categoryTotal` (column-total =
category-`j` count of the piles' union, from a disjoint-piles hypothesis).  **And
the B4 kernel symmetry is now proven** (follow-up 7): the allocation-level exchange
is a **reversible symmetric kernel** — `exchangeTargets_symmetric` shows the swap of
the two leaving sets is a bijection between the forward and backward exchange
target-sets, so their counts are equal.

**2026-12-31 follow-up (2-category example):** the reusable G5 machinery now
compiles for `k >= 3` and `c >= 2` in a worked concrete instance —
`Shufflemath/FiniteDeck/ThreePileTwoColor.lean` (six named cards, two categories,
three piles of two) proves its fiber count (`Fintype.card (MultiFiber 6 3 pile3
pile3) = 8`, via the reusable `multiPile_card`) and its lumped-histogram row/column
totals (via the reusable `lump_pileTotal` / `lump_categoryTotal`). The concrete
combinatorial premises (partition, disjointness) are proved constructively; the
pure `Nat`/`Finset` computation facts use `native_decide`, legitimate here because
the card space is the six-element `Fin 6`, not a `99!` universe.

**2026-12-31 follow-up 2 (T5 within-pile orbit, general `k`):** the 2-pile
`WithinPileOrbit.embed_m_imageLeft` result is generalized to arbitrary `k` in a
new module `Shufflemath/FiniteDeck/MultiPileOrbit.lean`.  `glueBlocks_imagePile`
proves that a global deck glued from a *family of per-pile equivalences*
`e i : {x // x ∈ P i} ≃ {x // x ∈ P i}` maps each pile `P i` onto itself
(structurally, via `glueBlocks_apply_member` — no `native_decide`, no `99!`
enumeration), and `glueBlocks_preservesEveryPile` lifts it to
`∀ j, (P j).image (glueBlocks … e) = P j`: the within-pile action group preserves
the whole allocation/fiber.  `example3_withinPile` (in `ThreePileTwoColor.lean`)
instantiates it for the 3-pile allocation.  This is the membership-preservation
half of the G5 3-pile gate; the distribution-level within-pile kernel and B4 /
`G5capstone` remain.

## What is in the repo right now (ground truth)

- `Shufflemath/FiniteDeck/Piles.lean` — **committed, builds clean.** The 2-pile
  *fiber* bijection is already here and proven:
  - `MultiPile`, `PileCard`, `MultiFiber` (type defs)
  - `twoPile_toMembershipFiber` (bijection) + `twoPile_toMembershipFiber_injective`
  - `swapFiber_card` (fiber size = `m! (N-m)!`)
  - `multiFiber_card_eq_fiberCount`
  It is **leaner than the handoff describes** — the fiber-count capstone for
  `k = 2` is already proven, not just sketched.
- `Shufflemath/FiniteDeck/Histograms.lean` — **now committed, builds green**
  (previously untracked WIP that failed to build — see Wall 1, resolved).  Defines
  the `lump` histogram (category counts inside a pile) + the row-total theorem
  `lump_pileTotal`.  This is the reusable arbitrary-finite-deck core that B4
  (multi-pile exchange) and T5 (within-pile orbit) build on; it generalizes
  `Fiber.lean`'s `swapFiber` (k = 2).

## Wall 1 — `Histograms.lean` import-exposure — **RESOLVED**

**File:** `Shufflemath/FiniteDeck/Histograms.lean`.

**Root cause (the actual diagnosis — it was NOT a missing import).**  The classic
`Finset` spellings the WIP file used no longer exist as `Finset`-namespace names in
this Mathlib version:
- `Finset.count` — **refactored away** (no `def count` in `Finset/Card|Basic|Fold`);
  use `s.filter p |>.card`.
- `Finset.PairwiseDisjoint` — **not a `Finset` method**; it lives at the `Set`
  level.  Coerce a `Finset` with `(s : Set ι)` and write `(s : Set ι).PairwiseDisjoint f`;
  `Finset.card_biUnion` accepts that hypothesis (the exact idiom is already in
  `FiniteDeck/Fiber.lean`: `fiberDisjoint` proves the `Set`-coerced
  `PairwiseDisjoint`, then `Finset.card_biUnion hDisj` inside a `calc`).
- `Finset.insert` — use the `{a, b}` Finset literal notation instead.

Everything else (`Finset.card`, `Finset.filter`, `Finset.biUnion`,
`Finset.mem_biUnion`, `Finset.disjoint_iff_ne`, `Finset.univ`, `Finset.image`,
`Finset.sdiff`) resolves fine from `Finset.Basic` + `Finset.Powerset` — the same
imports the green `Piles.lean`/`Fiber.lean` use.

**Fix applied:** rewrote `lump` as `(cardPile i).filter (fun x => color x = j) |>.card`
and proved `lump_pileTotal` with the `Set`-coerced `PairwiseDisjoint` +
`Finset.card_biUnion` + a `Finset.mem_biUnion`/`Finset.mem_filter` cover lemma —
mirroring `Fiber.lean`'s proven pattern.  Added the module to the `Shufflemath.lean`
aggregator and `dev/verify_next_phase.sh`.  **Builds green; 37-test gate passes.**

**Column-total `lump_categoryTotal` — now proven (2026-12-31):** summing `lump`
over all piles equals the category-`j` count of the piles' union, from a
`hPiles : ∀ i j, i ≠ j → Disjoint (cardPile i) (cardPile j)` hypothesis, by
`Finset.card_biUnion` on the filtered sub-piles plus `Finset.filter_biUnion`
(the actual lemma name — `Finset.biUnion_filter` does not exist in this Mathlib).
`Disjoint` is the bare (Set-coerced) one; this Mathlib has **no `Finset.Disjoint`**
(the same classic-`Finset`-API refactor that removed `Finset.count`).

## Wall 2 — general-k product-fiber `Fintype` (Fintype sub-wall CRACKED under `Classical`)

`Piles.lean` stops at the 2-pile fiber.  G5's headline needs a `MultiFiber`-like
Fintype **for arbitrary `k` and `c`** (the product fiber over a pile *partition*),
and `G5capstone` (the multi-pile exchange kernel-equality) needs that type with a
working `Fintype` instance so `Fintype.card` / `card_bij` / the kernel sum are
well-typed.

**Fintype sub-wall CRACKED (2026-12-31).** The reason the `{e // ∀ p : Fin k, …}`
subtype did not synthesize a `Fintype` constructively is that the per-pile
image-membership predicate is not constructively decidable.  Under `open Classical`
it is: `Fintype (MultiFiber N k posPile cardPile)` **synthesizes for arbitrary
`k`** (probed `#check Fintype.card (MultiFiber N k …) : ℕ`, no error).  The 2-pile
numeric corollary `twoPile_card : Fintype.card (MultiFiber N 2 (twoPilePos) (twoPileCard))
= m!·(N-m)!` is now **proved** in `Piles.lean` via `Classical.choice (twoPile_equivFiber …)`
+ `Fintype.card_congr` + `fiberCount` — the standard classical escape, not the
`letI`-on-`∀`-subtype chase (see `docs/planning/2026-11-25-batch5b-headline-handoff.md`
for the original `Fintype`-instance wall on the batch-5b headline).

**Remaining for `G5capstone`** (now bounded): the explicit bijection
`MultiFiber N k P C ≃ Π i, Equiv (↥(P i)) (↥(C i))` is **LANDED**
(`Shufflemath/FiniteDeck/MultiPileFiber.lean`, `multiPile_equivFiber`, via
`Equiv.ofBijective` on the two round-trips).  The count formula
`Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!` (a `Fin k → …` product
`Fintype` via `Fintype.Pi` + `Fintype.card_perm`) is the **remaining next
step**, then the multi-pile exchange kernel-equality on top (`G5capstone`).

## Next steps (in order)

1. ~~Fix `Histograms.lean` imports~~ — **DONE.**  `Histograms.lean` builds and is
   integrated; B3's lumping core is green.
2. ~~`lump_categoryTotal` (column-total)~~ — **DONE.**  Proved from a
   pairwise-disjoint-piles hypothesis by `Finset.card_biUnion` +
   `Finset.filter_biUnion`.
3. ~~Wall 2 Fintype sub-wall + `pileEquiv` + `PileFiber` + `MultiPileFiber`~~
   — **DONE.**  `twoPile_card`, the per-pile restriction equiv `pileEquiv`, the
   fiber bijection (forward/inverse/crux/deck + equiv round-trips),
   `multiPile_equivFiber`, and the count formula **`multiPile_card`
   (`Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!`)** are all landed in
   `MultiPileFiber.lean`.
4. ~~3-pile, 2-category example (static)~~ — **DONE (2026-12-31, commit `f3446cd`).**
   `Shufflemath/FiniteDeck/ThreePileTwoColor.lean` compiles the reusable
   machinery for `k = 3`, `c = 2`: fiber count = `8` (via `multiPile_card`) and
   the row/column histogram totals (via `lump_pileTotal` / `lump_categoryTotal`).
   This satisfies the G5 gate's **"at least one 3-pile, 2-category example
   compiles"** acceptance (roadmap line 235).
5. ~~T5 / multi-pile within-pile orbit (the example's *dynamics* half)~~ —
   **DONE (this session).**  New module
   `Shufflemath/FiniteDeck/MultiPileOrbit.lean` generalizes the 2-pile
   `WithinPileOrbit.embed_m_imageLeft` route to arbitrary `k`:
   `glueBlocks_imagePile` proves a global deck glued from a *family of per-pile
   equivalences* `e i : {x // x ∈ P i} ≃ {x // x ∈ P i}` maps each pile `P i`
   onto itself, and `glueBlocks_preservesEveryPile` lifts that to
   `∀ j, (P j).image (glueBlocks … e) = P j` — i.e. the within-pile action group
   (riffle on one pile, identity elsewhere) preserves the whole allocation /
   fiber.  Proved **structurally** via `glueBlocks_apply_member` (no
   `native_decide`, no `99!` enumeration).  `example3_withinPile` in
   `ThreePileTwoColor.lean` instantiates it for the `pile3` allocation (k=3).
   This lands the **membership-preservation** half of the G5 3-pile, 2-category
   gate (roadmap line 285) and the multi-pile T5 orbit core (roadmap line 182).
   The *distribution-level* within-pile kernel (uniform measure over the orbit +
   the histogram row-invariance) is the remaining T5 refinement.

**2026-12-31 follow-up 3 (B4 allocation-level exchange count):** the pairwise
multi-pile exchange **count** is now proven in a new module
`Shufflemath/FiniteDeck/MultiPileExchange.lean`.  For two **disjoint** piles
`A` (size `m`) and `B` (size `n`), a `k`-exchange (swap `k` cards each way, the
map `exchangePair A B oi oj = ((A\oi)∪oj, (B\oj)∪oi)`) reaches exactly
`choose m k * choose n k` pairs — `pairwiseExchangeCount`, the allocation-level
denominator of the T5 histogram kernel and the multi-pile generalization of the
2-pile `SubsetExchange.subsetExchangeCount` (which is the special case
`B = univ \ A`).  The proof is the reconstruction identity
`A \ ((A\oi)∪oj) = oi` (disjointness kills the cross-terms), which makes the
exchange map injective on `(k-subsets of A) × (k-subsets of B)`
(`exchangePair_injOn`), so the reachable count is the domain count
(`Finset.card_image_of_injOn` + `Finset.card_powersetCard`).  Integrated into the
aggregator + verify gate (green, 37 tests).  The **involutivity/reversibility**
(`exchangePair_involution`: `exchangePair ((A\oi)∪oj) ((B\oj)∪oi) oj oi = (A,B)`
— the T5 "unique (out_i,out_j) argument" / reversible symmetric kernel) is now
**also proven** in the same module.  Remaining B4: the **histogram lumping**
(multivariate-hypergeometric T5 transition + stationary law) and the
`G5capstone` kernel-equality.
6. **B4 allocation-level count + involutivity** — **DONE (this session).**  New
   module `Shufflemath/FiniteDeck/MultiPileExchange.lean` proves
   `pairwiseExchangeCount` (the T5 denominator `choose m k * choose n k`, the
   disjoint-pile generalization of the 2-pile `subsetExchangeCount`) and
   `exchangePair_involution` (the exchange is an involution up to the swap of
   the leaving sets — the T5 "reversible symmetric kernel" at the allocation
   level, roadmap T5 line 167).  **Remaining B4 sub-steps, in order**:
   (a) **histogram lumping** — the transition *denominator* (the multivariate
   Vandermonde, follow-up 4 below) is now **landed**; what remains is the
   transition *numerator* (per-allocation multivariate-hypergeometric mass) and
   the stationary law; then (b) the `G5capstone` multi-pile exchange
   kernel-equality (the full headline).

**2026-12-31 follow-up 4 (B4 histogram denominator — multivariate Vandermonde):**
the *denominator* of the T5 histogram-level transition is now proven in
`MultiPileExchange.lean`.  `histAllocSum xs k` sums, over every allocation of
`k` cards across the category counts `xs = [X_0, …, X_{c-1}]`, the product of
per-category binomials `∏_i C(X_i, a_i)`; `histAllocSum_choose` proves
`histAllocSum xs k = C(∑ xs, k)` — the **multivariate Vandermonde** (the
c-category generalization of Mathlib's 2-way `Nat.add_choose_eq`), proved by
induction on `xs` reusing `Nat.add_choose_eq` at each cons-step, entirely in the
antidiagonal form so no range↔antidiagonal transport is needed.  This lumps the
allocation-level exchange count into the histogram level: summing the
per-category numerator over all `k`-allocations of a pile recovers `choose m k`
for that pile.  **Next B4:** the per-allocation *numerator* (multivariate
hypergeometric mass for a fixed `(a,b)`) and the stationary law.

**2026-12-31 follow-up 5 (B4 histogram numerator — per-category binomial atom):**
the per-category building block of the T5 numerator is now proven in
`Histograms.lean`.  `allocCard c X a i` counts the ways to choose exactly `a i`
cards from the `X i` cards of category `i` (the `a_i`-subsets of the `X_i`-card
category, as a `Finset.powersetCard`); `allocCard_choose` proves
`allocCard c X a i = choose (X i) (a i)`, the single-factor binomial.  This is the
atom whose **product over categories** (and the two-pile product) gives the full
T5 numerator `∏_c C(X_{i,c}, a_c)·C(X_{j,c}, b_c)`; it composes with follow-up 4's
`histAllocSum_choose` (the denominator) to build the full histogram transition
`Pr(a,b|X) = [∏_c C(X_{i,c},a_c)·C(X_{j,c},b_c)] / [C(n_i,k)·C(n_j,k)]`.  It is
self-sufficient (`Finset.card_powersetCard` + `Finset.card_univ` +
`Fintype.card_fin`; the only new import is `Mathlib.Data.Nat.Choose.Basic`).
**Next B4:** the *stationary law* (the multivariate-hypergeometric `π` is the
invariant measure of the exchange kernel) — the product-over-categories numerator
itself is now landed in follow-up 6.

**2026-12-31 follow-up 6 (B4 histogram numerator — product over categories;
Fintype-of-`Π` sub-wall bypassed):** the **product-over-categories numerator** is
now proven in `Histograms.lean`.  `catAlloc c X a j : Finset (Finset (Fin (X j)))`
is the per-category fiber (the `a_j`-subsets of the `X_j`-card category), and
`allocPi_card` proves
`((Finset.univ : Finset (Fin c)).pi (fun j => catAlloc c X a j)).card =
 (Finset.univ : Finset (Fin c)).prod (fun j => choose (X j) (a j))` — the number of
full category-allocations of one pile is the product of the per-category
binomials, i.e. the per-pile factor `∏_c C(X_{i,c}, a_c)` of the T5 numerator.
**Key route (bypasses the Fintype-of-`Π` sub-wall):** the theorem is stated with
`Finset.pi` + `Finset.card_pi` (a pure `Finset.card` computation), **not** with a
`Fintype (Π j, catAlloc … j)` instance — the latter does not synthesize at
statement level.  The root cause (isolated this session): the premise
`∀ j, Fintype (catAlloc … j)` itself fails for a *generic* `j` (the per-category
`Fintype (Finset.powersetCard …)` has no auto instance once the index is a free
variable, so `Pi.instFintype`'s `[∀ a, Fintype (β a)]` premise is unprovable at
statement level).  `Finset.card_pi` (`#(s.pi t) = ∏_{i ∈ s} #(t i)`) reduces the
product count to the per-category `#(t i) = choose (X i) (a i)` (the same
`Finset.card_powersetCard` + `card_univ` + `card_fin` as `allocCard_choose`).
New imports: `Mathlib.Data.Finset.Prod` (for `Finset.pi`) and
`Mathlib.Data.Fintype.BigOperators` (for `Finset.card_pi`).
**Next B4:** the stationary law (multivariate-hypergeometric `π` invariant under
the exchange kernel) and the `G5capstone` multi-pile kernel-equality headline.

**2026-12-31 follow-up 7 (B4 kernel symmetry — the reversible symmetric kernel,
allocation level):** the exchange kernel's **symmetry** is now proven in
`MultiPileExchange.lean`.  `exchangeTargets N A B A' B' k` is the set of
`(oi, oj)` `k`-exchanges (`oi ⊆ A`, `oj ⊆ B`, each of size `k`) that land exactly
on the target `(A', B')`.  `exchangeTargets_symmetric` proves
`#(exchanges (A,B) → (A',B')) = #(exchanges (A',B') → (A,B))`: the swap
`(oi, oj) ↦ (oj, oi)` is a **bijection** between the two target-sets — the forward
image lands by the involutivity `exchangePair_involution` (each pile's borrowed
set sits inside the exchanged pile, so the swap is back in the domain), and the
backward image by the same with the piles swapped; injectivity is immediate (a pair
determines its swap).  The count-equality follows by `Finset.card_image_of_injOn`
+ the image-set equality.  This is the precise allocation-level statement of the T5
"reversible symmetric kernel" (roadmap T5 line 167): the kernel is symmetric, so on
a finite allocation space the uniform distribution is stationary under a single
exchange move.  The proof is purely combinatorial (reuses
`exchangePair_involution` + the disjoint-pile membership bookkeeping); no
`native_decide`, no deck enumeration.  **Caveat recorded:** the *lumped*
(color-level) kernel's reversibility is **not** a formal consequence of this —
lumping a reversible full-allocation chain can break reversibility — so the
stationary law at the color level remains a separate, subtler target, as does the
`G5capstone` kernel-equality.

The build gate stays green (37 tests) through all of it.

## Build / commit conventions (unchanged)

- `./dev/verify_next_phase.sh` = the build gate (37 tests, exit 0).
- `Histograms.lean` is now tracked; keep any further WIP that does not build
  **untracked** so it never blocks the gate.
- Stage only changed files; keep `.pi-glla/*` tooling files out of commits;
  publish the tally with the model trailer per the standing rules.

## `pileEquiv` (per-pile restriction equiv) — **LANDED** (`Shufflemath/FiniteDeck/PileEquiv.lean`)

**Mathematical status: PROVEN and now in the library.** `pileEquiv (N k) (P C)
(i) (e) (hi) : Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i}` is a bijection:
injective via `Subtype.ext` + `Equiv.symm_apply_apply` + `e` injective; surjective
via `Finset.mem_image.mp` (a preimage `w ∈ P i` with `e w = z.1`) + `Equiv.apply_eq`.
It is a `noncomputable def` (uses `Equiv.ofBijective`) in its own module
`Shufflemath/FiniteDeck/PileEquiv.lean` (added to the aggregator + verify script;
gate green, 37 tests). It is the building block of the general-`k` product-fiber
equivariance (Wall 2): the full `MultiFiber` fiber is a product of these per-pile
equivs, `Fintype.card = ∏_i (|P i|)! = ∏_i (|C i|)!`.

**Elaboration root cause (precise, for the next product-equiv attempt):** the
surjectivity step rewrites the membership `z.1 ∈ C i` into `z.1 ∈ (P i).image
(fun q => e q)` using `hi : (P i).image (fun q => e q) = C i`.  This works in a
*plain* file (the `_ProbeG5pile.lean` probe) but **fails in any `module` file**
(Piles.lean, or a standalone module) with *“tactic execution is stuck, goal
contains metavariables: `?m.108 ∈ Finset.image ?m.106 ?m.107`.”*  The module system's
**deferred** elaboration runs the anonymous `by` inside `Finset.mem_image.mp (by
rw [hi]; …)` *before* the expected-type metavariables (`z.1`, `P i`, `e`) are
unified, so `rw` sees an all-metavariable goal.  The fix (applied): pull the
proof into a **named `have hmem : z.1 ∈ (P i).image (fun q => e q) := by rw [hi];
exact z.2`** with a *concrete* type — the `have`'s goal is fully resolved, so `rw`
sees concrete terms.  (`open Classical`, `Eq.mp/mpr`, and eta-reducing the image
do NOT fix it; only giving the `by` a concrete `have` goal does.) **Rule of thumb
for the next product-equiv / G5capstone:** any `by` that rewrites a subtype
membership from a pile-equality hypothesis must be wrapped in a named `have` with
an explicit concrete type, not inlined as an anonymous `by` argument.

## `PileFiber.lean` (deck ↔ per-pile equivs) — **LANDED**

The general-`k` fiber bijection's forward map, inverse, and crux realization, in
a new module `Shufflemath/FiniteDeck/PileFiber.lean` (integrated into the
aggregator + verify script; gate green, 37 tests).  Built on `pileEquiv`
(per-pile restriction equiv) and `glueBlocks` (generic partition/Sigma gluing
from `Partition.lean`):

- `multiPileToEquivs (d : MultiFiber N k P C) : (i : Fin k) → Equiv (↥(P i)) (↥(C i))`
  — a realizing deck gives, per pile, the restriction equiv (just `pileEquiv`).
- `gluedRealizes` — **the crux**: the deck `glueBlocks P C hP hC e` obtained by
  gluing a family of per-pile equivs *realizes the allocation*: each
  `(P i).image (glueBlocks …) = C i`.  Proved by `Finset.ext` + `Finset.mem_image`:
  ⊆ via `glueBlocks_apply_member` (the glued deck on `x ∈ P i` equals the local
  equiv at `x`, which lands in `C i`) and ⊇ via the local equiv's surjectivity
  (`(e i).surjective`).
- `equivsToMultiPile` — packages `⟨glueBlocks P C hP hC e, gluedRealizes⟩`, the
  inverse direction (per-pile equivs → a realizing deck).
- `roundTripDecks` — **LANDED**: `equivsToMultiPile (multiPileToEquivs d) .1 = d.1`
  — gluing a deck's own per-pile equivs recovers the deck.  Proof: `Equiv.ext` →
  unique-ownership `hP.1 x` gives the pile `j` owning `x` → `glueBlocks_apply_member`
  (the glued deck on `x ∈ P j` = the local equiv at `x`) → `simp [pileF, pileEquiv,
  Equiv.ofBijective]` (the local equiv is `pileEquiv … j d.1 (d.2 j)`, whose
  forward map `pileF` sends `⟨x, hxj⟩` to `⟨d.1 x, _⟩`).

**Round-trip status — BOTH LANDED.**  `roundTripDecks` (gluing a deck's own
per-pile equivs recovers the deck) is in `PileFiber.lean`; `roundTripEquivs`
(taking the per-pile equivs of a glued deck recovers the family) is in
`MultiPileFiber.lean`.  With both, `Equiv.ofBijective (multiPileToEquivs N k P C)`
packages the headline fiber bijection **`multiPile_equivFiber : MultiFiber N k P C
≃ (i : Fin k) → Equiv (↥(P i)) (↥(C i))`** (`MultiPileFiber.lean`): injective via
`roundTripDecks` (`a.1 = (g (f a)).1`, then `f a = f b` collapses the two glued
decks, then `(g (f b)).1 = b.1`), surjective via `roundTripEquivs` (`f (g f') = f'`).
**Count formula — LANDED.**  `multiPile_card : Fintype.card (MultiFiber N k P C)
= ∏ i, (|C i|)!` (with per-pile `equivFiberCard`) is in `MultiPileFiber.lean`.
**Remaining next step:** `G5capstone` — the multi-pile exchange kernel-equality
(the headline theorem tying the fiber structure to the exchange dynamics).

**Elaboration notes for the round-trips:** keep the gluing family / deck *inlined*
(bare `glueBlocks …`, not a named def) so `glueBlocks_apply_member` applies without
def-unfolding; `change` eta-reduces `(fun q => d q)` to `d` inside the image; and a
section-bound `variable e` must be *applied explicitly* (`gluedRealizes N k P C hP
hC e`) when a sibling def references it — a bare reference is treated as an
unapplied function (the same `@`-apply pattern as `pileF` inside `pileEquiv`).

**The count formula — LANDED (2026-12-31 session).**  Two lemmas in
`MultiPileFiber.lean`:
* `equivFiberCard (i : Fin k) (hCard : (P i).card = (C i).card) :
   Fintype.card (Equiv {x // x ∈ P i} {x // x ∈ C i}) = Nat.factorial ((C i).card)`
   — build `he : ↥(P i) ≃ ↥(C i)` via `Fintype.equivOfCardEq (by simp [Fintype.card_coe,
   hCard])`, then `rw [Fintype.card_equiv he]` and `simp [Fintype.card_coe, hCard]`.
   The key lemma is `Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
   Fintype.card (α ≃ β) = (Fintype.card α)!` (`Mathlib.Data.Fintype.Perm`).
* `multiPile_card (hP) (hC) (hCardEq : ∀ i, (P i).card = (C i).card) :
   Fintype.card (MultiFiber N k P C) = (Finset.univ : Finset (Fin k)).prod
   (fun i => Nat.factorial ((C i).card))` — `rw [Fintype.card_congr (multiPile_equivFiber
   N k P C hP hC)]` then `rw [Fintype.card_pi]` (*separate* `rw`s), then
   `apply Finset.prod_congr rfl`, then `intro i _` and
   `exact equivFiberCard N k P C i (hCardEq i)`.
**Gotchas that cost the session:** (a) a section-bound `variable (hP)`/`(hC)` is
picked up as an implicit parameter of a later **`def`** but NOT of a later
**`theorem`** when it is not named in the statement — so `multiPile_card` takes
`hP`/`hC` as *explicit* parameters (the body then reads them fine); (b) the
factorial postfix `!` mis-parses before `)` — write `Nat.factorial ((C i).card)`;
(c) `Fintype.card_pi` reduces the bare `∏ i, …` form, so apply `Fintype.card_congr`
and `Fintype.card_pi` as *separate* `rw`s and close with `Finset.prod_congr rfl`
(same finset on both sides); (d) when calling a same-section theorem you must pass
the section variables explicitly (`equivFiberCard N k P C i …`).  **Then `G5capstone`.**

## `ThreePileTwoColor.lean` — the 3-pile, 2-category example — **LANDED**

A worked concrete instance proving the G5 machinery compiles for `k >= 3` and
`c >= 2`.  Six named cards (`Fin 6`), two categories, three piles of two:

- `color6 : Fin 6 → Fin 2` — cards `0,1,2` are category `0`, cards `3,4,5` are
  category `1` (three of each).
- `pile3 : Fin 3 → Finset (Fin 6)` — pile `i` is `{x // x.val / 2 = i.val}`,
  i.e. `0 = {0,1}`, `1 = {2,3}`, `2 = {4,5}` (consecutive pairs).
- `pile3_mem (x) (i) : x ∈ pile3 i ↔ x.val / 2 = i.val` — the membership
  characterization (via `Finset.mem_filter` + `Finset.mem_univ`, built as a
  manual `And` since `Finset.mem_univ` is a proof, not an `iff`, and cannot sit
  in a `rw` list).
- `pile3_partition : IsPartition pile3` — **constructive** (coverage via
  `Nat.div_lt_iff_lt_mul` + `Fin.isLt`; unique ownership via `Fin.eq_of_val_eq`).
- `pile3_disjoint : ∀ i j, i ≠ j → Disjoint (pile3 i) (pile3 j)` — proven by
  `rw [Finset.disjoint_iff_inter_eq_empty]` then `refine Finset.ext fun x => ?_`
  (NOT `rw [Finset.ext]` — `Finset.ext` is a *function* `(∀ x, x ∈ s ↔ x ∈ t) →
  s = t`, and rw-ing it leaves a metavariable pattern) and `simp [Finset.mem_inter,
  pile3_mem]` (the full `simp` set reduces `x ∈ ∅` to `False`; `Finset.mem_empty`
  does not exist).  The reduced goal `x.val/2 = i.val → ¬(x.val/2 = j.val)` is a
  single implication, not a conjunction.
- **`example3_fiberCard : Fintype.card (MultiFiber 6 3 pile3 pile3) = 8`** — via
  `rw [multiPile_card 6 3 pile3 pile3 … (fun i => rfl)]` then the pure-Nat
  `prod3 : (∏ i : Fin 3, (|pile3 i|)!) = 8` by `native_decide`.
- **`example3_rowTotal0`** (row-total = `2`) and **`example3_colTotal0` /
  `example3_colTotal1`** (each column-total = `3`, the two-category
  demonstration) — via `lump_pileTotal` / `lump_categoryTotal` (called with all
  implicit args `(k := 3) (N := 6) (c := 2)` made explicit) then `native_decide`
  on the resulting pure `Finset` computation.

**Why `native_decide` is fine here (and where it is not):** the reusable
`multiPile_card` / `lump_*` theorems do the structural work; `native_decide` is
only ever asked to compute a **concrete, closed** `Nat`/`Finset` value (`prod3`,
the row/col totals) over the six-element `Fin 6` — never a `99!` universe and
never a goal with a free `Fin` index (a free variable makes `native_decide`
report *“Expected type must not contain free variables”*).  That is why the
partition/disjoint premises are proved **constructively** and the row total is
stated for a *concrete* pile (`pile 0`), not a general `i`.  `IsPartition` and
`Finset.Disjoint` (Set-coerced) are not `native_decide`-able (their `Decidable`
instances fall back to classical `propDecidable`, and `Disjoint`'s `intro`-ed
hypotheses are Set-memberships, not Finset-memberships) — hence the constructive
`IsPartition` proof and the `disjoint_iff_inter_eq_empty` route.


---

## Follow-up 8 (post-compaction resync): the T5 two-pile transition is stochastic

**Landed:** `MultiPileExchange.twoPileExchangeTotal` and
`twoPileTransitionStochastic` (module now imports `Histograms` +
`Mathlib.Data.Rat.Defs`; gate green, 37 tests).

* `twoPileExchangeTotal (X Y : List Nat) (k) :
    histAllocSum X k * histAllocSum Y k = choose (∑ X) k * choose (∑ Y) k` —
  the two-pile multi-category T5 transition's *total* (sum of the
  multivariate-hypergeometric numerator over every valid pair of category
  selections) is the **universal** denominator, independent of the category
  counts.  It is the two landed per-pile Vandermondes
  (`Histograms.histAllocSum_choose`) composed: one `rw`.
* `twoPileTransitionStochastic (X Y) (k) (hX : k ≤ ∑ X) (hY : k ≤ ∑ Y) :
    ((histAllocSum X k * histAllocSum Y k) : Rat) /
      ((choose (∑ X) k * choose (∑ Y) k) : Rat) = 1` — the normalized two-pile
  T5 transition kernel has **row-sum 1** (a valid Markov transition; the
  nonzeriness is `Nat.choose_pos` + `Nat.ne_of_gt` + `Nat.mul_ne_zero`, closed
  by `field_simp`).

**Why this is the right next step (T2/T5, roadmap lines 105, 176, 235):** the
multivariate-hypergeometric stationary law is the headline T5 result; its
*prerequisite* is that the two-pile transition is a well-defined stochastic
kernel — the row-sum is universal (Vandermonde: it depends only on the pile
sizes `∑ X`, `∑ Y`, not the category counts), so the normalized row-sum is
`1` for every histogram `X`.  That is exactly what these two state.  The
2-pile/2-*color* special case is the already-proven `blStationary` (G4); this
is the multi-*category* generalization at the transition level.

**The sigma-type lumping route is the known Fintype wall (documented, not
re-tried).** Probing "derive the kernel by lumping the allocation chain" via the
disjoint-union-of-categories type `Σ (j : Fin c), Fin (X j)` hits:
`Fintype (Σ j, Fin (X j))` does not synthesize (`Sigma.instFintype` needs
`∀ j, Fintype (Fin (X j))`, a Pi-instance that does not resolve for the
free-`Nat`-family), and `Finset.sigma` / `Finset.card_sigma` are not in the
imported modules.  This is the same `letI`-on-`∀`-subtype Fintype wall recorded
in `g5-multipile-twoPile-reduction.md`.  The clean route is the `List`-based
`histAllocSum_choose` Vandermonde (already landed), which this increment uses
directly — same identity, no Fintype friction.

**Remaining T5 (the genuine, non-Fintype wall):** the *column-sum / symmetry*
(`#exchanges(X→X') = #exchanges(X'→X)` via the allocation-level swap involution
→ the kernel is symmetric/doubly-stochastic) and the *multivariate-hypergeometric
stationary law* (`π K = π`).  The column-sum needs the allocation-level fiber
sets (`Fib(X)`, the exchange map), which are the `∀`-subtype Fintype wall; the
stationary law then needs the lumped detailed balance, which does **not** reduce
to the trivial swap (the lumped measure `π` is not uniform, and `#e(X→X') =
#e(X'→X)` alone gives symmetry of `K`, not `π`-stationarity — the latter is a
genuine combinatorial identity, see roadmap line 176 caveat).  Next increment:
either crack the allocation-level symmetry (transport the Fintype through the
explicit `Equiv`, per `g5-multipile-twoPile-reduction.md` option 1) or state and
probe the detailed balance directly.

---

## 2026-11-25 session follow-up (post-F3/G5 resync): capstone state

**Repo state at resync:** `lake build` + `dev/verify_next_phase.sh` green (37 tests, exit 0).
The G5 fiber structure is fully landed (`PileFiber.lean`, `MultiPileFiber.lean`):
`multiPile_equivFiber` (fiber ≃ per-pile equiv family) and the count
`multiPile_card : Fintype.card (MultiFiber N k P C) = ∏_i (|C i|)!`
(`∏ i, Nat.factorial ((C i).card)` form via `Fintype.card_congr` + `Fintype.card_pi` +
`equivFiberCard`).  The 2-pile numeric corollary `twoPile_card` (`Piles.lean`), the
3-pile/2-category example (`ThreePileTwoColor.lean`, fiber count 8 + row/col totals),
the T5 within-pile orbit core (`MultiPileOrbit.lean`), the B3 histogram core
(`Histograms.lean`, `lump_pileTotal`/`lump_categoryTotal`), and the B4 allocation-level
kernel are all landed and green.

**B4 kernel-side (landed in `MultiPileExchange.lean`):** allocation-level count
(`pairwiseExchangeCount` = `choose m k * choose n k`), involutivity
(`exchangePair_involution`), the allocation-level kernel symmetry
(`exchangeTargets_symmetric`: `#(exchangeTargets A B A' B' k) = #(exchangeTargets A' B' A B k)`),
the multivariate-hypergeometric numerator identity (`histAllocSum_choose`), the
two-pile stochasticity (`twoPileExchangeTotal` + `twoPileTransitionStochastic` — the
normalized two-pile T5 transition kernel has row-sum 1), and the `FiberMP`
well-definedness (`exchangePairFiberMP`, the exchange kernel lands in the allocation
state space).

**Landed (this session, commit `ec03a3c`):** the per-(a,b) lumped numerator is now a
standalone named `def` in `Histograms.lean` (`lumpedNum`), and the **two-pile joint
numerator factors as the product of the per-pile weights** (`twoPile_lumpedNum_factor`:
`∏_c C(X_c,a_c) · ∏_c C(Y_c,b_c) = ∏_c [C(X_c,a_c)·C(Y_c,b_c)]`) — the Fubini-style
factorization that is the explicit per-(a,b) target of the G5capstone. Both theorems
verified (`lake build Shufflemath.FiniteDeck.Histograms` + full 37-test gate green).

**Landed (this session, commit `b9e732a`):** the **normalized** two-pile lumped transition is
now a named `Rat`-valued object in `Histograms.lean`: `lumpedConditionalMass` (per-pile conditional
mass = numerator / choose(ΣX, k) — the multivariate-hypergeometric conditional factor) and
`lumpedTransition` (the joint numerator / universal denominator), with
`lumpedTransition_factors` proving the two-pile kernel is the product of the two per-pile conditional
masses. All verified (lake build + full 37-test gate green).

**Landed (this session, commit `3bd7409`):** the **two-pile kernel swap symmetry** —
`lumpedTransition_swap`: swapping the two piles (with their allocations) leaves the kernel invariant —
both the numerator and the denominator are products symmetric in the two piles.  This is the kernel-side
mirror of `exchangeTargets_symmetric` (the fiber-count symmetry) — the exchange is reversible at both
levels.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `2c4d61a`):** the **two-pile kernel well-definedness** —
`lumpedTransition_kernel_well_defined`: on the valid interior (fully valid allocations, `Σa = Σb = k`,
`k ≤ ΣX`, `k ≤ ΣY`) the joint kernel is strictly positive (the per-pile numerators and the joint
denominator are positive) and bounded by `1` (each per-pile conditional mass is in `[0, 1]`).  This is
the probability-like-object statement for the T5 kernel at the allocation-level — the composition of
the exact support, the positivity and the bound.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `3709b4d`):** the exact-support **iff** for the two-pile kernel —
`prod_choose_eq_zero_iff` (a lumped numerator is zero exactly when some per-category allocation exceeds the
category bound) and `lumpedTransition_eq_zero_iff` (the joint kernel is zero exactly on the invalid
allocations — a per-category violation in either pile, or `k` beyond a pile's total).  Together with the
positivity pair, the two-pile kernel is zero exactly outside the valid rectangle with a legal `k` and is in
`(0, 1]` on the valid interior.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `ac6347b`):** the **two-pile exact support** —
`lumpedTransition_eq_zero_of_exceed_left`/`_right` (any per-category violation in either pile forces the
joint numerator to vanish, hence the ratio is zero) and `lumpedTransition_pos_of_valid` (any pair of fully
valid allocations gives a positive numerator product — `Nat.choose_pos` on each factor — and a positive
denominator, hence a positive transition mass).  The two-pile kernel is zero exactly outside the valid
allocation rectangle and positive inside it.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `ffad091`):** the **exact support** of the lumped conditional mass —
`lumpedConditionalMass_eq_zero_of_exceed` (any per-category violation `a j > X j` forces a zero factor in
the product, hence a zero numerator and a zero mass) and `lumpedConditionalMass_pos_of_valid` (a fully valid
allocation `a j ≤ X j` for all `j`, summed to `k`, gives a positive product (`Nat.choose_pos`), a positive
denominator (`k ≤ ΣX`), and hence a positive mass).  The kernel is zero exactly on the allocations that do
not fit the pile.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `6af4fbb`):** the **two-pile normalized row-sum** (Fin-c form) —
`lumpedTransition_rowSum`: the joint numerator `histAllocSum (ofFn X) k * histAllocSum (ofFn Y) k` row-sums to
the joint universal denominator `choose (ΣX) k · choose (ΣY) k` in the `Fin c → ℕ`-indexed spelling — the
joint normalized total is `1` for any legal `k` in both piles (`k ≤ ΣX`, `k ≤ ΣY`).  This is the
Fin-`c`-indexed form of the joint stochasticity in `twoPileTransitionStochastic`.  Verified (lake build +
full 37-test gate green).

**Landed (this session, commit `899bb0c`):** the **two-pile conditional-mass bound** —
`lumpedTransition_le_one`: the two-pile T5 transition kernel (product of the two per-pile conditional masses)
is at most `1` for any valid pair of allocations `(a, b)` (`Σa = Σb = k`), requiring both piles to have a
nonempty number of `k`-subsets (`choose (ΣX) k ≠ 0`, `choose (ΣY) k ≠ 0`).  Each factor is in `[0, 1]` (the
per-pile bound just landed), so the product is too.  Verified (lake build + full 37-test gate green).

**Landed (this session, commit `7c13ef4`):** the **per-pile normalized row-sum** —
`lumpedConditionalMass_rowSum`: `numerator / choose (ΣX) k = 1` for any legal `k` (`k ≤ ΣX`), via
`fin_lumped_rowSum` (the Fin c ↔ List bridge) and `field_simp` — the per-pile half of the T5 stochasticity
headline (the two-pile version `twoPileTransitionStochastic` composes the same numerator structure at the
joint level). Verified (lake build + full 37-test gate green).

**Landed (this session, commit `db28f32`):** the single-term **Vandermonde bound** on the lumped numerator —
`lumpedNumList_le_choose` (the List-form bound: each per-pile numerator term `∏ C(X_c,a_c)` is at most the universal
denominator `choose (ΣX) k`, by induction on the category list, each cons-step a
`Nat.add_choose_eq` + `Finset.single_le_sum` application against the antidiagonal total); `list_zip_ofFn_map_choose`
(the `List.ofFn` bridge, by induction on `c`); `lumpedNum_le_choose` (the `Fin c → ℕ`-indexed form, bridging via
`List.prod_ofFn` / `List.sum_ofFn`); and the **conditional-mass bound** `lumpedConditionalMass_le_one`
(`lumpedConditionalMass c X a k ≤ 1` — the normalized per-pile conditional mass of any valid allocation is at most
one, with a zero-denominator case). Verified (lake build + full 37-test gate green). These bound the T5 kernel's
per-(a) numerator against its universal denominator — the per-(a) half of the kernel's well-definedness.

**Landed (this session, commit `cbbe214`):** the Fin`c` ↔ List bridge — `fin_lumped_rowSum`
states `histAllocSum (List.ofFn X) k = choose (Finset.univ.sum X) k`, so the `Fin c → ℕ` kernels in
`Histograms.lean` (`lumpedConditionalMass` / `lumpedTransition`, normalized by `choose (univ.sum X) k`) inherit
the antidiagonal-route total with no new machinery. Verified (lake build + full 37-test gate green).

**What remains (the G5capstone), honestly:**
1. The *histogram-level* lumped kernel — derive `Pr(a,b|X) = [∏_c C(X_{i,c},a_c)·C(X_{j,c},b_c)] / [C(n_i,k)·C(n_j,k)]` from the allocation chain (the list-based `histAllocSum` Vandermonde is the clean route; the `Sigma`-lumping route is Fintype-walled) and prove its row-sum/stochastic + column-sum/symmetry.
2. The *multivariate-hypergeometric stationary law* `π K = π` (the T2 `π` from `docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md` line ~107, not landed anywhere in the repo).
3. The full `G5capstone` kernel-equality headline tying the fiber structure to the exchange dynamics.

The numeric machinery is fully proven; the remaining items are genuinely-open
combinatorial identities (the lumped detailed balance), not improvable tactics or
new walls.  A redundant reinvention of the general-`k` fiber bijection (a fresh
`_ProbeG5prodCard.lean` using `pileOf`) was tried this session and hit the same
dependent-subtype-rewrite wall documented in `g5-multipile-twoPile-reduction.md`
(`rw`/`simp`/`conv` fail on the pile-index-dependent `⟨q, ⋯⟩` subtype-proof term);
it was deleted rather than committed — the landed `multiPile_equivFiber` route
(`glueBlocks`) is the correct one and needs no new work.

**2026-11-27 session 112 continuation (range count):**
`fixedPairAlloc_range_card` — the distinct exchanged allocations are exactly the image of the injective
fixed-pair exchange map, so the range has exactly `choose (n i) k * choose (n j) k` points — the same
denominator as the kernel mass (`fixedPairKernel_mass_choose`). The kernel is uniform over the range,
and the row-sum over the range is exactly `1`.

**2026-11-27 session 112 continuation (binomial mass form):**
`fixedPairKernel_mass_choose` — the kernel's mass is the reciprocal of the product of the two per-pile
binomials, the two-pile analog of the T5 denominator (`choose m k * choose n k`).

**2026-11-27 session 112 continuation (the two-sided transport consumed in-situ, deeper):**
`fixedPairAlloc_injective` now consumes the two-sided transport directly — the last step uses
`mapPick_injective` (a corollary of `mapPick_eq_of_card_eq`) for both piles, eliminating the
duplicated finset-level `Finset.image_inj` route.

**2026-11-27 session 112 continuation (the two-sided transport consumed in-situ):**
`mapPick_injective` is now a first-class corollary of `mapPick_eq_of_card_eq` — the card set
determines the pick. The two-sided transport is consumed by the allocation machinery, not just
parallel to it.

**2026-11-27 session 112 continuation (the two-sided transport consumed):**
`mapPickEquiv_injective` (`Function.Injective (mapPickEquiv A i k)` — one line via `Equiv.injective`)
and `mapPick_eq_of_card_eq` (two picks whose card sets are equal are equal — via `Subtype.ext` on the
card-set equality + the equiv's injectivity). The two-sided transport is now consumed as a first-class
object, not just a packaged bijection.

**2026-11-27 session 112 continuation (the two-sided transport landed, first-class):**
`mapPickEquiv` — the two-sided `Equiv (Pick (n i) k) (pileCardSet A i k)`, the G5capstone two-sided
transport envelope. The forward map is `mapPick` (pick → card set); the inverse is `pickOfCardSet'`
(card set → pick). Both round trips are the landed identities: left_inv is `pickOfCardSet'_mapPick`
(the full reverse identity, picks-of-the-same-type) and right_inv is the card-hypothesis round trip
`mapPick_pickOfCardSet'` (the card set of the built pick is `W` — `ext` + image-image chain).
`pileCardSet` is the `k`-subsets of pile `i`'s cards. This makes the two-sided mapPick bijection a
first-class object the two-pile fixed-pair transport can consume.

**2026-11-27 session 112 continuation (the FULL reverse identity landed):**
`pickOfCardSet'_mapPick` — `pickOfCardSet' A i (mapPick A i u) hsub (mapPick_card A i u) = u`. The
card-hypothesis restatement (`pickOfCardSet'`) avoids the dependent-subtype cast wall entirely: the
constructed pick's card annotation comes from the hypothesis `hcard : W.card = k`, so both sides of the
identity are picks of the same type `Pick (n i) k` — no `Equiv.cast`, no projection reduction, no
dependent-subtype friction. Proved via `ext` + the same image-image membership chain as the
finset-level identity (the landed `pickOfCardSet_mapPick_underlying` is strictly subsumed). This closes
the two-sided mapPick bijection at the full Pick level.

**2026-11-27 session 112 continuation v2 (the finset-level reverse identity landed):**
`pickOfCardSet_mapPick_underlying` proves the underlying index finset of the pick built from
`mapPick A i u` is the original index finset `u.1` — the load-bearing content of the reverse identity,
proved via ext + image membership (forward: recover `x` from the image-source `y` via the equiv
injectivity after `apply_symm_apply` + congrArg-on-`val`; reverse: exhibit the image witness as
`⟨(pileEquivOf A i x).val, _⟩` and close via `symm_apply_apply`). The full subtype identity stays parked —
the `Equiv.cast` projection does not reduce definitionally (the cast is Eq.mpr on a subtype with no
clean subtype-cast simp lemma in this Mathlib), the same dependent-subtype wall class as the G5capstone.

**2026-11-27 session 112 continuation (two-sided mapPick bijection, landed):** the
card-set direction of the two-pile fixed-pair transport is now two-sided at the
card-set level: `pickOfCardSet` (the reverse of `mapPick` — the pick whose card set is
exactly `W`, via the size-bijection applied backwards through `pileEquivOf`, card count
via `card_image_of_injOn` + `Fintype.card_coe`), `mapPick_pickOfCardSet` (the round trip —
the card set of the built pick is exactly `W`, via `Finset.image_image` + `Finset.image_congr`
+ image-image membership), and `mapPick_injective` (two picks with the same card set are
equal — via `Finset.image_inj` on `pileEquivOf.val`). The remaining reverse identity
`pickOfCardSet A i (mapPick A i u) hsub = u` is recorded as an honestly-parked item —
the card annotation `(mapPick A i u).card` of the constructed pick is not rewritable into
the target `Pick (n i) k` type (the dependent-subtype friction documented above; the
`Eq.mpr`/cast route is the recorded durable fix, mirroring the scoped-block route of the
`tupleExtensionEquiv` two-sided bijection). No statement weakened. Verified: full build
green, 37/37 tests, 0 sorries.

**Landed (this session, T2 deck-level identity — `Shufflemath/FiniteDeck/HistogramFiber.lean`):**
`deckFiber` (the finset of decks whose induced left-pile allocation has per-category
counts `X`), `deckFiber_eq_biUnion` (the fiber equals the disjoint biUnion of the
per-`C` fibers `fiberSetPile` over the histogram fiber `histFiber`), `fiberSetPile_card`
(a fixed-`C` per-allocation fiber has `m!·(N-m)!` decks — the landed `fiberCount`
through `fiberSet`/`fiberSet_eq_pile`), and **`deckFiber_card`**, the T2 deck-level
identity:

```
#deckFiber(X) = if X 0 + X 1 = m
    then (histFiber N color X).card * m! * (N - m)!
    else 0
```

— i.e. the number of ordered decks realizing histogram `X` is the allocation-fiber
count `∏_c choose (r_c, X c)` (the landed `twoHist_fiber_card`) times `∏_p n_p!`
(two-pile: `m!·(N-m)!`), composed with disjointness of the per-`C` fibers
(`Finset.card_biUnion` + `fiberSetPile_card`).  The `if` guard is honest: a deck's
left pile has exactly `m` cards, so any histogram consistent with a left-pile
allocation must sum to `m`.  Verified (lake build green; full 37-test gate OK;
independent numeric check N=4,m=2,color 2+2: all nine `(x_0,x_1)` counts match).
The remaining T2 items are unchanged and remain genuinely blocked (see above): the
`marginalLaw`/`fiberLaw` objects over the size-`n` allocation space (dependent
`⟨q, ⋯⟩` subtype-proof rewrite wall), and the `πK = π` multivariate-hypergeometric
stationary law.

**Landed (this session, deck-level π law):** `deckFiber_prob` — the roadmap T2
π(X) in the two-pile/two-color specialization: `#deckFiber(X) / N! = [∏_c choose
(r_c, X c)] / choose N m` when `X 0 + X 1 = m`, else 0.  Composed from the landed
`deckFiber_card` via the Nat-level identity `#deckFiber(X) · choose N m =
∏_c choose (r_c, X c) · N!` (`Nat.choose_mul_factorial_mul_factorial hm`), then
`div_eq_div_iff`.  Verified (lake build green, full 37-test gate OK, 0 sorries,
numeric sanity check N=4/m=2 matches brute force).  The `πK = π` stationary law and
the marginalLaw/fiberLaw subtype-space objects remain blocked (see above).

**Update (this session, deck-level π ↔ BL law):** the deck-level π law is
now bridged to the BL stationary law — `deckFiber_prob_eq_blStationary` in
`HistogramFiber.lean`: for a two-color deck with category-0 card count `r`, the
deck-level π law (`deckFiber_prob`) at the admissible special-count macrostate
`⟨X 0, …⟩` is **exactly** `BernoulliLaplaceGeneral.blStationary N m r` — the
roadmap T2 exit criterion ("Its two-pile/two-color specialization is exactly
`blStationary N m r`").  Composed from the landed `deckFiber_prob` +
`blStationary`, with the two-color bookkeeping discharged inline
(`filter_card_twoColor`).  The size-`n` marginal/fiber law `Dist`-objects have
since landed too (`sizeNMarginalLaw` / `sizeNFiberLaw` + mass identities), so the
remaining T2-line item is the πK = π stationary law only.

**Numeric verification of πK = π (this session, post-landing):** an independent
brute-force walk over the histogram-state space (the lumped-kernel semantics of
`lumpedTransition`: numerator = `∏_c choose(X_c, a_c)·choose(Y_c, b_c)`,
denominator = universal `choose(m,k)·choose(N-m,k)`) confirms, across 9 cases —
N=4/m=2 (r=2+2, k=1,2), N=5/m=3 (r=3+2, k=1,2), N=6/m=3 (r=2+4, k=1,2,3),
N=5/m=2 (r=5+0, k=1), N=6/m=4 (r=3+3, k=2) — that (i) the lumped kernel row-sums
to 1 and (ii) the multivariate-hypergeometric π (the landed deck-level π law,
`∏_c choose(r_c, X_c)/choose(N, m)`) is invariant under the two-pile histogram
exchange kernel: `∑_X π(X)·K(X→X') = π(X')`.  This is honest evidence that the
πK = π stationary-law claim (roadmap T5 line 176) is **true** at the
histogram level; the formal Lean proof remains the documented next step
(state-space formalization + the lumped detailed balance), not a tactic wall.

**Landed (this session, πK = π state space + π law + mass):** the πK = π
formalization has landed through step (b) — `validHistSet` (the valid
two-pile/two-color histogram state space as a `Finset` carrier, `2a5e4a4`),
`validHistSet_nonempty`, the `validHistPi` kernel-π law (`choose(r_0, X 0)·
choose(r_1, X 1)/choose(N, m)`, the landed `deckFiber_prob` formula) and
`validHistPi_mass` (`∑ π(X) = 1` over `validHistSet`, proved via the honest
valid-`i` bijection + Vandermonde).  Landed `54632a7`.

**Landed (this session, kernel definition):** `histogramTransition` — the
`∑_{a,b}`-over-preimages reduction of the landed `lumpedTransition` to the
valid histogram state space (`Finset.antidiagonal k` carrier, values as
Nat): K(X → X') sums, over every per-category removed/added pair `(a, b)`
with total `k`, the two-pile-exchange numerator
`choose(X_0, a_0)·choose(X_1, a_1)·choose(r_0 − X_0, b_0)·choose(r_1 − X_1, b_1)`
normalized by `choose(m, k)·choose(N − m, k)`, weighted by the shift
constraint `X'_0 = X_0 − a_0 + b_0`, `X'_1 = X_1 − a_1 + b_1`.  Landed `6e0934b`.

**Landed (this session, row-sum):** `histogramTransition_rowSum` — the row-sum
half of the T5/T2 kernel landing: `∑_{X' ∈ validHistSet} histogramTransition N m r0 r1 k X X' = 1`.
Route: (i) Fubini over `(X', a, b)` (the preimage re-indexing — `X' = X - a + b` is a
bijection in `X'` for fixed `(a, b)`); (ii) the per-`(a, b)` inner sum collapses to a
single-term value (the unique valid histogram `H` determined by `X, a, b` — the
`by_cases hw` split discharges the `choose`-zero degenerate case); (iii) the
outer `(a, b)`-sum factors as `∑_a choose(X_0, a_0)·choose(X_1, a_1) = choose(m, k)`
(the landed Vandermonde `Nat.add_choose_eq`) times `∑_b choose(r_0 − X_0, b_0)·choose(r_1 − X_1, b_1) = choose(N − m, k)`
(same shape with `r - X`), normalized by `choose(m, k)·choose(N − m, k) = 1`.
Build green (3200 jobs), 0 sorries.  Not a tactic wall.

**Landed (this session, commit `8749def`):** step (d) the detailed-balance identity
`∑_{X valid} validHistPi N m r0 r1 X · histogramTransition N m r0 r1 k X X' = validHistPi N m r0 r1 X'`
— the genuine combinatorial `∑_{a,b}`-preimage re-indexing with a non-uniform π weight
(the πK = π tail).  Proved as `histogramTransition_stationary` in
`Shufflemath/FiniteDeck/HistogramFiber.lean`: Fubini over `(X, a, b)`; the per-`(a, b)`
inner sum collapses via `stationary_inner` (one-term collapse to `π(X') · sw(X') / D`);
the two Vandermonde splits of `∑_{a,b} sw(X') = choose (m, k) * choose (N - m) k`;
universal normalisation `D = choose m k * choose (N - m) k`.  Build green, 0 sorries.
The πK = π stationary-law tail of the T2 histogram-level kernel is now **proved**.

**Landed (this session, commit after `8749def`):** the honest bridge —
`histogramTransition_eq_sum_lumpedTransition` in `HistogramFiber.lean`: the finite
`Finset`-carrier kernel `histogramTransition` is exactly the per-(a, b) sum of the
explicit two-pile product kernel `lumpedTransition` (the T5 kernel shape) over the
shift-consistent preimages, with the denominator collapse discharged by the per-category
bounds.  The honest kernel and the explicit lumped kernel are now literally equal as
Rat-valued functions on the valid interior — the "derive the kernel by lumping the
allocation chain" claim, as a Lean identity.

**Remaining, honestly scoped:** the deck-level fiber count (`× ∏_p n_p!`, Sigma-lumping
wall — do not re-litigate) and the G5 capstone headline (B4 kernel lumping + the final
assembly) remain open; both are genuinely-open combinatorial identities, not gaps in
the histogram-level T2 landing.
