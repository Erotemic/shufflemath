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
category-`j` count of the piles' union, from a disjoint-piles hypothesis).

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
2. ~~`lump_categoryTotal` (column-total)~~ — **DONE** (this session): proved from a
   pairwise-disjoint-piles hypothesis by `Finset.card_biUnion` + `Finset.filter_biUnion`.
3. **Wall 2 — Fintype sub-wall CRACKED + `pileEquiv` + `PileFiber` +
   `MultiPileFiber` LANDED.**  `twoPile_card` and the per-pile restriction equiv
   **`pileEquiv`** (`Shufflemath/FiniteDeck/PileEquiv.lean`) are in, and the fiber
   bijection's forward map + inverse + crux + deck round-trip
   (`Shufflemath/FiniteDeck/PileFiber.lean`), the equiv round-trip + the headline
   fiber `Equiv` **`multiPile_equivFiber : MultiFiber N k P C ≃ Π i, Equiv
   (↥(P i)) (↥(C i))`** (`Shufflemath/FiniteDeck/MultiPileFiber.lean`) are in too.
   Remaining: the count formula `Fintype.card (MultiFiber N k P C) = ∏_i
   (|C i|)!` → `G5capstone` (the multi-pile exchange kernel-equality).
4. **B4** `MultiExchange` + **T5** within-pile orbit, on top of the above.

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

