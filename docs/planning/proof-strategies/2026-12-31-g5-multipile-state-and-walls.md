# G5 multi-pile — state, walls, and next increments

**Session:** 2026-12-31 (resumed after compaction; then resumed again post-compaction)
**Status:** G5's headline `G5capstone` (the k×c multi-pile exchange kernel-equality)
was blocked by two structural walls. **Wall 1 (Histograms import-exposure) is now
CRACKED and landed** — the root cause was not a missing import but the
classic-`Finset`-API refactor (details below); the module is rewritten against this
Mathlib's API, builds green, and is integrated into the aggregator + verify script.
**Wall 2 (general-k product-fiber Fintype) remains** — it needs the product-fiber
`Fintype` instance, the real capstone blocker. The build is green (37 tests OK,
EXIT 0); everything committed.

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

**Remaining on this thread (bounded):** the column-total `lump_categoryTotal`
(summing `lump` over piles = the deck's category-`j` count) additionally needs the
piles to be **pairwise disjoint** (a valid allocation): with a
`hPiles : ∀ i j, i ≠ j → Disjoint (cardPile i) (cardPile j)` hypothesis it goes
through by `Finset.card_biUnion` on the filtered piles plus `Finset.biUnion_filter`.
A natural next micro-increment.

## Wall 2 — general-k product-fiber `Fintype` instance (the real capstone)

`Piles.lean` stops at the 2-pile fiber.  G5's headline needs a `MultiFiber`-like
Fintype **for arbitrary `k` and `c`** (the product fiber over a pile *partition*),
and `G5capstone` (the multi-pile exchange kernel-equality) needs that type with a
working `Fintype` instance so `Fintype.card` / `card_bij` / the kernel sum are
well-typed.  This is the genuine remaining blocker (see
`docs/planning/2026-11-25-batch5b-headline-handoff.md` for the `Fintype`-instance
wall on the batch-5b headline).

## Next steps (in order)

1. ~~Fix `Histograms.lean` imports~~ — **DONE.**  `Histograms.lean` builds and is
   integrated; B3's lumping core is green.
2. **`lump_categoryTotal`** — add the column-total with a disjoint-piles hypothesis
   (bounded; `Finset.card_biUnion` + `Finset.biUnion_filter`).
3. **Wall 2** — the general-k product fiber + `Fintype` instance + `G5capstone`
   (the capstone).
4. **B4** `MultiExchange` + **T5** within-pile orbit, on top of the above.

The build gate stays green (37 tests) through all of it.

## Build / commit conventions (unchanged)

- `./dev/verify_next_phase.sh` = the build gate (37 tests, exit 0).
- `Histograms.lean` is now tracked; keep any further WIP that does not build
  **untracked** so it never blocks the gate.
- Stage only changed files; keep `.pi-glla/*` tooling files out of commits;
  publish the tally with the model trailer per the standing rules.
