module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderMembershipKernels
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderLocalGSR

/-!
# Local (within-pile) shuffling and membership preservation (F4.2)

A *local* shuffle acts only *within* the two fixed working piles: it permutes
the 50 cards among the left-pile positions and the 49 cards among the right-pile
positions, and never moves a card between the piles. This file defines that
within-pile relabeling of deck positions and proves the central F4.2 fact:
**a local shuffle cannot change the membership state** (the set of named cards
in the left pile). The local-GSR *kernel* is the product of a GSR shuffle on
each pile applied through this mechanism; the deterministic pile-permutation
and its membership-preservation are established here.
-/

open CommanderPermutation

/-- A function on the 99 deck positions that permutes the *left* pile by `pl`
  and the *right* pile by `pr`, and never moves a card between the piles. A
  left position `leftPosition i` goes to `leftPosition (pl i)`; a right position
  `rightPosition j` goes to `rightPosition (pr j)`. -/
def pileRelabelFn (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (p : Fin 99) : Fin 99 :=
  if h : p.val < 50 then
    leftPosition (pl ⟨p.val, h⟩)
  else
    rightPosition (pr ⟨p.val - 50, by omega⟩)

/-- A left position stays a left position, permuted by `pl`. -/
theorem pileRelabelFn_left (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (i : Fin 50) :
    pileRelabelFn pl pr (leftPosition i) = leftPosition (pl i) := by
  simp [pileRelabelFn, leftPosition]
  <;> omega

/-- A right position stays a right position, permuted by `pr`. -/
theorem pileRelabelFn_right (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (j : Fin 49) :
    pileRelabelFn pl pr (rightPosition j) = rightPosition (pr j) := by
  simp [pileRelabelFn, rightPosition]
  <;> omega

/-- The 50 cards occupying the left pile of the deck `d` after the within-pile
  relabeling `pileRelabelFn pl pr`. -/
def permutedLeftCards (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image
    (fun i => d (pileRelabelFn pl pr (leftPosition i)))

-- A bijection on `Fin 50` leaves the image of `univ` under any `f` unchanged
-- (reindexing): `univ.image (f ∘ pl) = univ.image f`.
theorem univImage_reindex (f : Fin 50 → Fin 99) (pl : Equiv.Perm (Fin 50)) :
    (Finset.univ : Finset (Fin 50)).image (f ∘ pl) =
      (Finset.univ : Finset (Fin 50)).image f := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply]
  constructor
  · intro hX
    rcases hX with ⟨i, _, hfi⟩
    exact ⟨pl i, by simp, hfi⟩
  · intro hY
    rcases hY with ⟨i, _, hfi⟩
    have h : pl (pl.symm i) = i := pl.apply_symm_apply i
    exact ⟨pl.symm i, by simp, by simpa [h, hfi]⟩

/-- **F4.2 core.** A within-pile relabeling leaves the left-card set unchanged:
  it permutes the 50 left positions by a bijection, so the set of named cards in
  the left pile is the same. Hence the membership state is preserved. -/
theorem permutedLeftCards_eq (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    permutedLeftCards d pl pr = leftCards d := by
  unfold permutedLeftCards leftCards
  -- the permuted image equals the pl-reindexed image (pointwise the maps agree)
  have hg : (fun i : Fin 50 => d (pileRelabelFn pl pr (leftPosition i))) =
      (fun i : Fin 50 => d (leftPosition (pl i))) := by
    funext i
    simpa [pileRelabelFn_left]
  have hL : (Finset.univ : Finset (Fin 50)).image
        (fun i => d (pileRelabelFn pl pr (leftPosition i))) =
      (Finset.univ : Finset (Fin 50)).image
        (fun i => d (leftPosition (pl i))) := by
    simpa [hg]
  -- then reindex by the bijection pl
  exact hL.trans (univImage_reindex (fun i => d (leftPosition i)) pl)

-- Building blocks for the bijection proof: a left position maps to a left
-- position, and a right position maps to a right position. The `if` in
-- `pileRelabelFn` has a fresh binder, so the reduction is driven by `by_cases`
-- on the same condition (which `simp` then uses to close the `if`), not by the
-- hypothesis directly.

-- A left position (`p.val < 50`) maps to a left position.
theorem pileRelabelFn_leftVal (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))
    (p : Fin 99) (h : p.val < 50) : (pileRelabelFn pl pr p).val < 50 := by
  by_cases hlt : p.val < 50
  · dsimp only [pileRelabelFn]
    simp [hlt, leftPosition]
  · exfalso
    omega

-- A right position (`50 ≤ p.val`) maps to a right position.
theorem pileRelabelFn_rightVal (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))
    (p : Fin 99) (h : 50 ≤ p.val) : 50 ≤ (pileRelabelFn pl pr p).val := by
  by_cases hlt : p.val < 50
  · exfalso
    omega
  · dsimp only [pileRelabelFn]
    simp [hlt, rightPosition]


/-! ## The `Equiv`-based pile relabeling (F4.2, GPT-6 construction)

The within-pile relabeling as a full `Deck = Equiv.Perm (Fin 99)` *by
construction*: transport a left permutation and a right permutation through the
canonical `Fin 50 ⊕ Fin 49 ≃ Fin 99` equivalence. Bijectivity is inherited from
`Equiv` composition — no four-case injectivity/surjectivity proof. This is the
clean version of `pileRelabelFn` above (which keeps the explicit `if` for
compatibility).
-/

/-- The within-pile pile-relabeling as a `Deck` permutation by `Equiv`
  composition: `Fin 99 → (Fin 50 ⊕ Fin 49)`, apply `pl`/`pr` by
  `Equiv.sumCongr`, then back. -/
def pileRelabelEquiv (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) : Deck :=
  ((finSumFinEquiv (m := 50) (n := 49)).symm).trans
    ((Equiv.sumCongr pl pr).trans (finSumFinEquiv (m := 50) (n := 49)))

/-- A left position maps to the `pl`-image left position. -/
theorem pileRelabelEquiv_left (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (i : Fin 50) :
    pileRelabelEquiv pl pr (leftPosition i) = leftPosition (pl i) := by
  dsimp only [leftPosition]
  change (finSumFinEquiv (m := 50) (n := 49)
    (Sum.map (⇑pl) (⇑pr) (finSumFinEquiv (m := 50) (n := 49).symm (Fin.castAdd 49 i)))) =
    Fin.castAdd 49 (pl i)
  rw [finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]

/-- A right position maps to the `pr`-image right position. -/
theorem pileRelabelEquiv_right (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (j : Fin 49) :
    pileRelabelEquiv pl pr (rightPosition j) = rightPosition (pr j) := by
  dsimp only [rightPosition]
  change (finSumFinEquiv (m := 50) (n := 49)
    (Sum.map (⇑pl) (⇑pr) (finSumFinEquiv (m := 50) (n := 49).symm (Fin.natAdd 50 j)))) =
    Fin.natAdd 50 (pr j)
  rw [finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

/-- Reindex the deck positions by the pile-preserving permutation before
  reading cards. -/
def reorderedDeck (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) : Deck :=
  (pileRelabelEquiv pl pr).trans d

/-- The reordered deck has exactly the original left-card set: a local (within-
  pile) permutation cannot change which named cards sit in the left pile. -/
theorem reorderedDeck_leftCards (d : Deck) (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) :
    leftCards (reorderedDeck d pl pr) = leftCards d := by
  change (Finset.univ : Finset (Fin 50)).image
      (fun i => (reorderedDeck d pl pr) (leftPosition i)) =
    (Finset.univ : Finset (Fin 50)).image (fun i => d (leftPosition i))
  have hfun :
      (fun i : Fin 50 => (reorderedDeck d pl pr) (leftPosition i)) =
        (fun i : Fin 50 => d (leftPosition (pl i))) := by
    funext i
    simp only [reorderedDeck, Equiv.trans_apply, pileRelabelEquiv_left]
  rw [hfun]
  exact univImage_reindex (fun i => d (leftPosition i)) pl

end CommanderLocalGSR
end Shufflemath
end
