# G5 multi-pile — state, the two walls, and the next three steps

*Session note — the current status of the G5 / Gate-6-A multi-pile thread
(`Shufflemath/FiniteDeck/`), written as the handoff after the 2026-11-25
qwen1125 candidate batch (10 Gate-6 K1 + GSR-segment theorems and the
`Shufflemath.FiniteDeck.Partition` module) was integrated and committed
(`10d9bef`, `ec58828`). F1–F5 and G1–G4 remain complete; Gate 6 (K1 core,
3-round headline, K1-swap oracle) is done. This is the **current** resume
point for the multi-pile gate.*

## What is green (committed, in the aggregator + `verify_next_phase.sh`)

- **`Shufflemath/FiniteDeck/Piles.lean`** (builds clean).  Defines the
  reusable `MultiFiber (N k) (posPile cardPile)` type (a deck realizing a
  `k`-pile allocation), the two-pile specializations `twoPilePos` /
  `twoPileCard`, and the **2-pile reduction**
  `twoPile_equivFiber : Nonempty (Equiv (MultiFiber N 2 …) (FibType N m hm A))`
  — a 2-pile fiber *is* the G2 fiber (a permutation's image is onto, so the
  left-image condition forces the right one).  The general-`k` capstone is the
  next rung.
- **`Shufflemath.FiniteDeck.Partition`** (from the 2026-11-25 batch):
  `glueBlocks` (rebuild a deck by reassigning each block's positions within
  its block) and `partitionSigmaEquiv` (`Π i, BlockBlock P i ≃ Fin k × Fin N`).
  These are the general-`k` gluing primitives a future multi-pile exchange
  builder (`B4` / `MultiExchange`) needs.

## What is WIP (untracked, does **not** build, not in aggregator/verify)

- **`Shufflemath/FiniteDeck/Histograms.lean`** — the B3 *lumping* core:
  `Histogram k c`, `lump`, `lump_pileTotal` (a row sums to the pile size),
  `coversDeck`, `lump_categoryTotal` (a column sums to the deck's category
  total), plus a concrete 3-pile/2-category example.  Mathematically complete;
  it only fails to **elaborate** because of the import wall below.  It is
  **untracked** (never committed) and **not** in the aggregator or
  `verify_next_phase.sh`, so its non-building state does **not** affect the
  green build.

## Wall 1 — `Histograms.lean`: `Finset` namespace import-exposure

This Mathlib version splits the `Finset` namespace across many modules
(`Insert.lean`, `Card.lean`, `Union.lean` / `Lattice/Union.lean`, `Disjoint.lean`,
`Pi.lean`, `Powerset.lean`, …), each with its own `@[expose] public section`.
Under the Lean-4 **module** system, `import Mathlib.Data.Finset.Basic` (and even
`…Card` / `…Union` / `…Powerset`) does **not** bring every `Finset.*` name into
reach.  `Histograms.lean` currently fails on exactly these names, in this order:

| name | used for | where it is `def`'d | status |
|---|---|---|---|
| `Finset.count` / `Finset.count_filter` / `Finset.card_filter` | per-category pile counts | `Card.lean` (the `card_filter_*` theorems are there; the base `count` is *not* in `Basic`) | **unresolved** after adding `Card` |
| `Finset.biUnion` / `Finset.card_biUnion` / `Finset.mem_biUnion` | union over the pile index | `Union.lean` / `Lattice/Union.lean` / `Powerset.lean` | **unresolved** after adding `Union`+`Powerset` |
| `Finset.insert` | the concrete example piles `{0,3}` etc. | `Insert.lean` | **unresolved** (needs `…Finset.Insert`) |
| `Finset.PairwiseDisjoint` | the disjointness hypotheses | not in `Basic`'s exposed set | **unresolved** (likely `…Finset.Disjoint`) |

**Diagnosis.** `Histograms.lean` is the **only** non-probe module in the repo
that uses `Finset.count`, so there is no in-repo working template to copy.  The
fix is to add the specific exposing module per name — most likely
`Mathlib.Data.Finset.Insert` (for `insert`), `Mathlib.Data.Finset.Disjoint`
(for `PairwiseDisjoint`), and the module that actually `expose`s the base
`count` (confirm by grepping each `Finset/*.lean` `@[expose]` section).  This is
a **bounded** fix (a handful of imports), not a mathematical wall.

**Next action (Wall 1).**  (1) grep each `Mathlib/Data/Finset/*.lean`
`@[expose]` section for `count` / `insert` / `PairwiseDisjoint` / `biUnion` and
add exactly the exposing modules; **or** (2) reformulate `lump` to avoid
`Finset.count` — e.g. `(cardPile i).card (fun x => color x = j)` via
`Finset.card`/`Finset.filter` if those are reachable — which sidesteps the
whole cluster.  Once it elaborates, add `Shufflemath.FiniteDeck.Histograms` to
the aggregator + `verify_next_phase.sh` and commit.

## Wall 2 — the general-`k` capstone needs a `Fintype`-instantiated product fiber

`twoPile_equivFiber` (k = 2) avoids a counting wall by being a **bijection** to
`FibType` (which *has* a `Fintype` instance) rather than a direct
`Fintype.card (MultiFiber …)` (which has **no** auto `Fintype` instance — the
same wall Gate 6 K1 and the batch-5b within-pile headline hit).  The general-`k`
capstone ("Generalize `twoPile_equivFiber` to arbitrary `k`", Option 2 in
`docs/planning/proof-strategies/g5-multipile-twoPile-reduction.md`) requires
first **constructing a product-fiber type with a `Fintype` instance**
(`≃ Π i, <single-pile fiber for pile i>`), then transferring the count
`∏_i |C i|` (or the multinomial `N! / ∏ h i!` for histograms) through the
bijection with `Fintype.card_congr`.  Until that product-fiber type (with its
`Fintype` instance) exists, the general-`k` fiber **count** is blocked the same
way the 2-pile numeric card-equality is (keep the bijection; transfer the number
at the call site with a local `letI` on the `FibType`-shaped side).

## Recommended order

1. **Wall 1** — resolve `Histograms.lean`'s `Finset` imports → lands B3 (lumping
   core) green and in the verify set.  Bounded, high-certainty.
2. **Wall 2** — build the general-`k` product-fiber type (with a `Fintype`
   instance) + its `Equiv (MultiFiber N k …)` → the G5 capstone (multinomial
   stationary law for arbitrary `k`).
3. **B4 / T5** — `MultiExchange` (a `k`-pile exchange built on `Partition.glueBlocks`)
   → multi-pile TV; and the category-preserving permutation-group **orbit**
   theorem (T5) using `Fintype.card_orbitOf` (the orbit lemma that worked for
   Gate 6 / the 2-pile fiber).
