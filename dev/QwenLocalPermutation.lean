module

public import Shufflemath.CommanderLocalGSR
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderLocalGSR

open CommanderPermutation

/-!
# Isolated F4.2 construction candidate

Use the canonical `Fin 50 ⊕ Fin 49 ≃ Fin 99` equivalence to transport
independent pile permutations to a full-deck permutation. Injectivity and
surjectivity are guaranteed by `Equiv` composition rather than being proved
by four case splits. Compile independently before merging:

    lake env lean dev/QwenLocalPermutation.lean
-/

/-- A bijective 99-position map assembled from within-pile permutations. -/
def qwenPileRelabelEquiv (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) : Deck :=
  ((finSumFinEquiv (m := 50) (n := 49)).symm).trans
    ((Equiv.sumCongr pl pr).trans (finSumFinEquiv (m := 50) (n := 49)))

/-- The transported permutation agrees with the intended action on the left. -/
theorem qwenPileRelabelEquiv_left (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (i : Fin 50) :
    qwenPileRelabelEquiv pl pr (leftPosition i) = leftPosition (pl i) := by
  have hcast (j : Fin 50) : leftPosition j = Fin.castAdd 49 j := by
    apply Fin.ext
    rfl
  rw [hcast i, hcast (pl i)]
  simp [qwenPileRelabelEquiv, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply]

/-- The transported permutation agrees with the intended action on the right. -/
theorem qwenPileRelabelEquiv_right (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (j : Fin 49) :
    qwenPileRelabelEquiv pl pr (rightPosition j) = rightPosition (pr j) := by
  have hcast (t : Fin 49) : rightPosition t = Fin.natAdd 50 t := by
    apply Fin.ext
    rfl
  rw [hcast j, hcast (pr j)]
  simp [qwenPileRelabelEquiv, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply]

/-- Reindex positions by a pile-preserving permutation before reading cards. -/
def qwenReorderedDeck (d : Deck) (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) : Deck :=
  (qwenPileRelabelEquiv pl pr).trans d

/-- The new deck is valid and has exactly the original left-card set. -/
theorem qwenReorderedDeck_leftCards (d : Deck) (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) :
    leftCards (qwenReorderedDeck d pl pr) = leftCards d := by
  change (Finset.univ : Finset (Fin 50)).image
      (fun i => (qwenReorderedDeck d pl pr) (leftPosition i)) =
    (Finset.univ : Finset (Fin 50)).image (fun i => d (leftPosition i))
  have hfun :
      (fun i : Fin 50 => (qwenReorderedDeck d pl pr) (leftPosition i)) =
        (fun i : Fin 50 => d (leftPosition (pl i))) := by
    funext i
    simp only [qwenReorderedDeck, Equiv.trans_apply, qwenPileRelabelEquiv_left]
  rw [hfun]
  exact univImage_reindex (fun i => d (leftPosition i)) pl

end CommanderLocalGSR
end Shufflemath
end
