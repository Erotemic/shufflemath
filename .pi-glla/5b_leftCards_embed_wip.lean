-- WIP (session 83): wall-free route for the batch-5b support equivalence.
-- This file is NOT in the Shufflemath.lean aggregator (does not affect verify).
-- `leftCards_embed_eq_segLeft` is one line from done: bridge the 99-card
-- `leftPosition` to `Fin.castLE` via Fin.ext before the Finset.ext (see agent_handoff.md).
-- See docs/agent_handoff.md (session 83 note) for the full route + remaining step.

module

public import Shufflemath.GSRSegHeadline
public import Shufflemath.GSRSegMembership
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open scoped Nat

variable (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))

/-- The forward left-card fact (wall-free): `embed_m` (hence `roundEmbedMap`)
  relabels within the piles, so the set of cards in the left 50 positions is
  unchanged from the identity deck = the segregated left set. Uses
  `FiniteDeck.embed_m_left` + bijection image-invariance, never the
  `(fiberOrbit_equiv …).val` deck. -/
theorem leftCards_embed_eq_segLeft :
    CommanderPermutation.leftCards (FiniteDeck.embed_m 99 50 hm5099 pl pr) = segLeft := by
  dsimp only [CommanderPermutation.leftCards, CommanderPermutation.leftPosition,
              segLeft, FiniteDeck.leftPositions, FiniteDeck.leftPosition]
  apply Finset.ext
  intro x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    use pl i
    constructor
    · simp
    · simpa only [FiniteDeck.leftPosition] using
        (FiniteDeck.embed_m_left 99 50 hm5099 pl pr i).symm
  · rintro ⟨j, hj, rfl⟩
    use pl.symm j
    constructor
    · simp
    · simpa only [FiniteDeck.leftPosition, Equiv.apply_symm_apply] using
        FiniteDeck.embed_m_left 99 50 hm5099 pl pr (pl.symm j)
