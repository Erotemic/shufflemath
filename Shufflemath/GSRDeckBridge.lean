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

-- The within-pile embedding `embed_m` is injective in the pair of within-pile
-- permutations: two equal embeddings agree at every position, and at a left
-- (resp. right) position that identifies the left (resp. right) permutation
-- (`leftPosition = Fin.castLE` / `rightPosition i = ⟨m + i.val⟩`, both injective).
-- Proved at the apply level, so it never touches the `finSplit` internals.
theorem embed_m_injective (N m : Nat) (hm : m ≤ N) :
    Function.Injective (fun (p : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m))) =>
      FiniteDeck.embed_m N m hm p.1 p.2) := by
  intro p q h
  have hpl : p.1 = q.1 := by
    apply Equiv.ext
    intro i
    have hpos := congrArg (fun (e : Equiv.Perm (Fin N)) => e (FiniteDeck.leftPosition N m hm i)) h
    have heq : FiniteDeck.leftPosition N m hm (p.1 i) = FiniteDeck.leftPosition N m hm (q.1 i) := by
      simpa [FiniteDeck.embed_m_left, eq_comm] using hpos
    dsimp only [FiniteDeck.leftPosition] at heq
    exact Fin.castLE_injective hm heq
  have hpr : p.2 = q.2 := by
    apply Equiv.ext
    intro j
    have hpos := congrArg (fun (e : Equiv.Perm (Fin N)) => e (FiniteDeck.rightPosition N m hm j)) h
    have heq : FiniteDeck.rightPosition N m hm (p.2 j) = FiniteDeck.rightPosition N m hm (q.2 j) := by
      simpa [FiniteDeck.embed_m_right, eq_comm] using hpos
    apply Fin.ext
    simpa [FiniteDeck.rightPosition] using heq
  exact Prod.ext hpl hpr

end Shufflemath
