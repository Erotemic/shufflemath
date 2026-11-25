# G5 multi-pile reduction — two-pile→G2 fiber bijection (committed `67a36c5`)

Session 2026-11-25. Increment to `Shufflemath/FiniteDeck/Piles.lean` (new leaf
module in the G0–G9 generalization roadmap,
`docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`).
Builds clean (`lake build Shufflemath.FiniteDeck.Piles` → EXIT 0). No other
module imports it yet.

## What landed

Type machinery (the `k`-pile generalization of the G2 `Membership` fiber):
- `PileCard N k (C : Fin k → Finset (Fin N))` / `PilePos N k (P : Fin k → Finset (Fin N))` —
  per-pile target / source finsets.
- `realizesAllocation N k P C (e)` — `∀ i, (P i).image (·∘e) = C i` (pile `i`'s
  cards land exactly on its target).
- `MultiFiber N k P C` — `{e : Deck N // realizesAllocation N k P C e}`.
- `multiFiber_prodCard` — for disjoint singleton targets,
  `Fintype.card (MultiFiber N k P C) = ∏_i |C i|`; `multiFiber_prodCard_one`
  specializes `k = 1` to the one-pile case.

Two-pile specialization (`k = 2`):
- `twoPilePos N m hm : Fin 2 → Finset (Fin N)` — `0 ↦ leftPositions`, `1 ↦ rightPositions`.
- `twoPileCard N m hm A : Fin 2 → Finset (Fin N)` — `0 ↦ A.1`, `1 ↦ univ \ A.1`.
- `twoPilePos0/1`, `twoPileCard0/1` — the unfolding lemmas.

Proofs:
- `univImage_eq_univ` — a permutation's whole-deck image is onto (`e.symm`).
- `twoPile_pred_iff` — **the reduction**: the 2-pile allocation predicate
  `(left-image = A ∧ right-image = univ \ A)` is equivalent to the single G2
  left-image condition. Proved via `Finset.image_sdiff` + `univImage_eq_univ`
  (the persistent `Finset.mem_image`/`mem_sdiff` wall is avoided by *not*
  chasing membership; the image-set equalities close directly).
- `finTwo_cases` — `Fin 2` has exactly two elements (`Fin.ext`, one-way).
- **`twoPile_equivFiber`** — the headline:
  `Nonempty (Equiv (MultiFiber N 2 (twoPilePos N m hm) (twoPileCard N m A))
                (FibType N m hm A))`.
  The 2-pile fiber is **in bijection** with the G2 fiber, via
  `Equiv.ofBijective` (left-image forces the right-image; `twoPile_pred_iff`).
  This is the two-color generalization: it makes every G2–G4 result
  (counting `m!(N-m)!`, disintegration, TV headlines) transfer to the 2-pile
  setting **without** re-proving them and without `N!` enumeration.

## The Fintype wall (documented, not chased)

The **card-equality** corollary
`Fintype.card (MultiFiber N 2 (twoPilePos N m hm) (twoPileCard N m A))
   = Nat.factorial m * Nat.factorial (N - m)`
is *true* (it follows from `twoPile_equivFiber` + `fiberCount`), but it is
**blocked on a Lean instance-elaboration wall**, not on the math:

- `Fintype (FibType N m hm A)` **does** synthesize (a single Finset-equality
  predicate; `fiberCount` in `Fiber.lean` uses `Fintype.card (FibType …)` in
  its goal and builds).
- `Fintype (MultiFiber N 2 …)` (a `{e // ∀ p : Fin 2, …}` subtype) does **not**
  auto-synthesize (probed: `#check Fintype.card {e // ∀ p : Fin 2, Q p}` prints
  only a partial `Fintype.card`), because `Decidable (∀ p : Fin 2, Q p)` does not
  resolve for the `∀`-bound Finset-equality predicate.
- Transferring the `FibType` Fintype across the bijection with
  `letI : Fintype (MultiFiber …) := Fintype.ofEquiv (α := FibType …) e.symm`
  **fails**: `letI`/`haveI` on the `MultiFiber` instance type triggers Lean to
  synthesize `Fintype (MultiFiber …)` (which has no global instance) instead of
  accepting the `ofEquiv` value. This is the known `letI`-on-a-non-instance-type
  elaboration trap.

The bijection `twoPile_equivFiber` is the **correct** statement to commit: it
captures the full G5 content (2-pile fiber *is* the G2 fiber) and needs no
Fintype instance. The `Fintype.card` equality is a trivial numeric corollary,
not worth a separate blocked increment.

## Next increment options (pick one)

1. **Card-equality corollary (if the numeric form is ever wanted):** establish
   `Fintype (MultiFiber N 2 …)` as a **global `instance`** (not `letI`) via
   `Fintype.ofEquiv _ e.symm`, then `Fintype.card_congr e` + `fiberCount`. Risk:
   a global instance on a `∀`-subtype may pollute/compete; prefer keeping the
   bijection and, if the number is needed at a call site, transfer it there
   with a local `letI` *on the `FibType`-shaped* side instead.
2. **Generalize `twoPile_equivFiber` to arbitrary `k`** (the real G5 capstone):
   for disjoint singleton `C i`, `MultiFiber N k (singletonPilePos) C ≃` the
   product fiber, count `∏_i |C i|` (already in `multiFiber_prodCard`). This is
   the `k ≥ 3` generalization of the committed 2-pile bijection and is the
   next rung of the G0–G9 ladder.

## Build / verify

```bash
cd ~/code/shufflemath
lake build Shufflemath.FiniteDeck.Piles   # EXIT 0, no new warnings in Piles.lean
```

`Piles.lean` imports only `TwoPile`, `Fiber`, `Fintype.Basic`, `Finset.Basic`,
`Tactic` (kept minimal, no unused-import warnings). `lakefile.lean` does not
list it (opt-in module, like the other `_Probe`/optional tranche files); add it
to the build list only when a downstream module imports it.
