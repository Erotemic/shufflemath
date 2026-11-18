# 47n — fiber-count probes (leftOrigSet → 50-set), status 2026-11-19

## What builds (in `Shufflemath/_Probe47n.lean`)
- `leftOrig50`: the 50 originally-left card-identities (0..49) as a 50-element
  `Finset (Fin 99)` (via `(Finset.univ : Finset (Fin 50)).image (Fin.castLE …)`).
- `leftOrigSet_eq_leftOrig50`: the 99-element filtered `leftOrigSet` from
  `CommanderFiberCount` is **definitionally equal** to `leftOrig50`. This is the
  key: the "99-filter" is really a 50-element set, so all counting avoids the
  99-element simp explosion.
- `leftOrig50_card50`: `leftOrig50` has 50 elements.
- `leftOrig50_mem_val (c : Fin 99) (hc50 : c ∈ leftOrig50) : c.val < 50`.
- `totalMarkedPos d := leftOrig50.image (d.symm)` and `totalMarkedPos_card50 d`:
  the positions holding an originally-left card form a 50-element set.
- `markedLeft_iff_inTotal (l : Fin 50)`: `l ∈ markedLeftPos d ↔
  leftPosition l ∈ totalMarkedPos d`.
- `markedRight_iff_inTotal (r : Fin 49)`: `r ∈ markedRightPos d ↔
  rightPosition r ∈ totalMarkedPos d`.
- `leftPos_iff_val (p : Fin 99)`: `p ∈ leftUniv50 ↔ p.val < 50`.
- `rightPos_iff_val (p : Fin 99)`: `p ∈ rightUniv49 ↔ 50 <= p.val`.
- `leftOriginalCount d` / `rightOriginalCount d` (= `markedLeftPos` /
  `markedRightPos`, matching `CommanderMembershipExchange`).

## The wall (next session)
`markedRightPos_card : (markedRightPos d).card = 50 - leftOriginalCount d`
is NOT in the probe. It requires a `hRpos` / `hUnion` showing the 50-element
`totalMarkedPos` splits as the disjoint union of the left and right marked
positions, then `#right = #total - #left` via `Finset.card_sdiff_of_subset` /
`Finset.card_union_of_disjoint` + `Nat.add_sub_cancel_left`. The blockers hit:
- `Fin.val_castAdd` does not reduce the `Fin` `property` proof, so `simp
  [rightPosition]` does NOT close `rightPosition r = p` — use `Fin.ext` +
  `omega` on the `val` field instead.
- The 99-element `leftOrigSet` filter causes `simp` to fully expand and time
  out; use `leftOrig50` (the 50-image) everywhere, bridging via
  `leftOrigSet_eq_leftOrig50`.
- `hDisjoint` (left ∩ right = ∅) needs `p.val < 50` vs `p.val >= 50`; extract
  the values via `Fin.val_castAdd` / `Fin.castLE` + `Fin.ext`.

## Route to the capstone (47n → F3 A3)
With `markedRightPos_card` in place, the F3 A3 count half is:
`membership_card` = `#(leftOrigSet ∩ d.symm '' (rightMarkedPos))` =
`50 - leftOriginalCount` (by `markedRightPos_card`), and the left half
`#(leftOrigSet ∩ d.symm '' (leftMarkedPos))` = `leftOriginalCount`
(by `markedLeft_iff_inTotal` + the 50-set count). Together they give the
fiber-count for `membership_card` in terms of `transitionNumerator 99 50 25`.

## Verified
`lake build Shufflemath._Probe47n` → green. `lake build Shufflemath.CommanderFiberCount
Shufflemath.CommanderMembershipKernels Shufflemath.BernoulliLaplace` → green.
`CommanderFiberCount.lean` was NOT modified this session (only probed).
