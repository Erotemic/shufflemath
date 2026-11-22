module
public import Mathlib.Tactic
public import Shufflemath.GSRDeckRound
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.FiniteDeck.TwoPile

@[expose] public section

namespace Shufflemath

open Finset
open scoped Nat

theorem hm : 50 ≤ 99 := by norm_num

/-!
## The within-pile embedding preserves the segregated left-pile position set.

`roundEmbedMap 99 50 (pl, pr)` relabels the left 50 positions by `pl` and the right 49 by
`pr` (a permutation *within* each pile), so it maps the left-position set `{0..49}` onto
itself; in particular its left-pile card set is exactly the left-position set, unchanged.
This is the structural fact that lets the within-pile (finite-deck) round law sit over the
segregated membership fiber, and is the first step toward the
`rhoRoundIdeal = localLift (segregatedMembership)` bridge (see `docs/agent_handoff.md`).
-/

-- The 50 left-pile positions {0..49}.
def segregatedLeftSet : Finset (Fin 99) := FiniteDeck.leftPositions 99 50 hm

/-- A position is a left position iff it is the image of a `Fin 50` index under the
  left-position embedding. -/
theorem bridgeA_mem (p : Fin 99) :
    p ∈ FiniteDeck.leftPositions 99 50 hm ↔ ∃ i : Fin 50, p = FiniteDeck.leftPosition 99 50 hm i := by
  dsimp only [FiniteDeck.leftPositions, FiniteDeck.leftPosition]
  simp
  constructor
  · intro h
    simpa [eq_comm] using h
  · intro h
    simpa [eq_comm] using h

/- (A) The within-pile embedding's left-pile card set is the (unchanged) left-position set. -/
theorem bridgeA_leftCards
    (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    FiniteDeck.leftCards 99 50 hm (roundEmbedMap 99 50 hm (pl, pr)) = segregatedLeftSet := by
  dsimp only [roundEmbedMap, segregatedLeftSet]
  unfold FiniteDeck.leftCards
  apply Finset.ext
  intro c
  simp only [Finset.mem_image]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨i, rfl⟩ := (bridgeA_mem p).mp hp
    have hEq : (FiniteDeck.embed_m 99 50 hm pl pr) (FiniteDeck.leftPosition 99 50 hm i) =
        FiniteDeck.leftPosition 99 50 hm (pl i) := by
      simpa using FiniteDeck.embed_m_left 99 50 hm pl pr i
    simpa [hEq] using (bridgeA_mem (FiniteDeck.leftPosition 99 50 hm (pl i))).mpr ⟨pl i, rfl⟩
  · intro h
    obtain ⟨i, rfl⟩ := (bridgeA_mem c).mp h
    refine ⟨FiniteDeck.leftPosition 99 50 hm (pl.symm i), ?_, ?_⟩
    · exact (bridgeA_mem _).mpr ⟨pl.symm i, rfl⟩
    · have hEq : (FiniteDeck.embed_m 99 50 hm pl pr) (FiniteDeck.leftPosition 99 50 hm (pl.symm i)) =
          FiniteDeck.leftPosition 99 50 hm (pl (pl.symm i)) := by
        simpa using FiniteDeck.embed_m_left 99 50 hm pl pr (pl.symm i)
      simp [hEq, pl.apply_symm_apply i]

end Shufflemath
