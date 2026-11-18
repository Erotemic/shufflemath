module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open FinsetCombinatorics
open Finset

variable (d : Deck)

namespace _Probe47t

/-!
# rightFilterGuarded — the `(c - a) + g = n` right-pile count, with guards

The one remaining conceptual piece for the per-deck Bernoulli-Laplace bridge.
Counting `R ∈ (Fin 49).powersetCard 25` with `(x - aL) + markedInRight d R = n`
(where `x = leftOriginalCount d`, `aL` a fixed `markedInLeft` value, and
`bR = n - (x - aL)`), the answer is the hypergeometric number
`choose (markedRightPos d).card bR * choose (49 - (markedRightPos d).card) (25 - bR)`
**exactly when the guards hold** (`x - aL ≤ n` and `bR ≤ 25`) and `0` otherwise.

The nested-`if` guard shape mirrors `transitionNumerator 99 50 25 x n`'s integrand
(`remaining := x - a` guarded by `remaining ≤ y`, then `b := y - remaining` guarded
by `b ≤ k`), so after the `#(markedRightPos d) = 50 - x` substitution this lemma's
RHS is term-for-term `transitionNumerator`'s right-hand factor.
-/

/-- `c ≤ n → (c + k = n ↔ k = n - c)` — the add-then-subtract equivalence the
    guarded right-pile count is built on. -/
private lemma haddSub (c n : Nat) (hc : c ≤ n) (k : Nat) : c + k = n ↔ k = n - c := by
  constructor <;> intro h <;> omega

theorem rightFilterGuarded (x aL n : Nat) :
    (((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => (x - aL) + markedInRight d R = n)).card =
      if x - aL ≤ n then
        (if n - (x - aL) ≤ 25 then
          Nat.choose (markedRightPos d).card (n - (x - aL)) *
            Nat.choose (49 - (markedRightPos d).card) (25 - (n - (x - aL)))
        else 0)
      else 0 := by
  let bR := n - (x - aL)
  by_cases h1 : x - aL ≤ n
  · -- x - aL ≤ n:  reduce the outer ite to its then-branch
    rw [if_pos h1]
    by_cases h2 : n - (x - aL) ≤ 25
    · -- h1 ∧ h2:  (x - aL) + markedInRight = n  <->  markedInRight = bR
      rw [if_pos h2]
      have hfin :
          ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
            (fun R => (x - aL) + markedInRight d R = n) =
            ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
            (fun R => markedInRight d R = bR) := by
        apply Finset.ext
        intro R
        simp only [Finset.mem_filter]
        have hequiv : ((x - aL) + markedInRight d R = n) ↔ (markedInRight d R = bR) :=
          haddSub (x - aL) n h1 (markedInRight d R)
        constructor
        · intro hp
          rcases hp with ⟨hmem, hcond⟩
          exact ⟨hmem, hequiv.mp hcond⟩
        · intro hp
          rcases hp with ⟨hmem, hmark⟩
          exact ⟨hmem, hequiv.mpr hmark⟩
      rw [hfin]
      simpa [markedInRight, bR, Finset.inter_comm, Finset.card_univ, Fintype.card_fin] using
        powersetCard_markedContent
          (U := (Finset.univ : Finset (Fin 49))) (M := markedRightPos d) (Finset.subset_univ _) 25 (n - (x - aL)) h2
    · -- h1 ∧ ¬h2 (bR > 25):  markedInRight ≤ 25 < bR, so no such R
      rw [if_neg h2]
      have hempty : ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
        (fun R => (x - aL) + markedInRight d R = n) = ∅ := by
        apply Finset.ext
        intro R
        have hnot : ¬R ∈ ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
          (fun R => (x - aL) + markedInRight d R = n) := by
          intro hmem
          rcases Finset.mem_filter.mp hmem with ⟨hmem2, hcond⟩
          have hmark : markedInRight d R = bR := (haddSub (x - aL) n h1 (markedInRight d R)).mp hcond
          have hR25 : R.card = 25 := (Finset.mem_powersetCard.mp hmem2).2
          have hcard : (markedRightPos d ∩ R).card ≤ 25 := by
            have hsub : markedRightPos d ∩ R ⊆ R := fun _ h => (Finset.mem_inter.mp h).2
            simpa [hR25] using Finset.card_mono hsub
          have hbR25 : bR ≤ 25 := by rw [← hmark]; simpa [markedInRight] using hcard
          exact h2 hbR25
        simp [hnot]
      rw [hempty]
      simp
  · -- ¬h1 (x - aL > n):  (x - aL) + markedInRight ≥ x - aL > n, so no such R
    rw [if_neg h1]
    have hempty : ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => (x - aL) + markedInRight d R = n) = ∅ := by
      apply Finset.ext
      intro R
      have hnot : ¬R ∈ ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
        (fun R => (x - aL) + markedInRight d R = n) := by
        intro hmem
        rcases Finset.mem_filter.mp hmem with ⟨_hmem2, hcond⟩
        have hlt : n < x - aL := Nat.not_le.mp h1
        have hge : x - aL ≤ (x - aL) + markedInRight d R := Nat.le_add_right _ _
        exact Nat.lt_irrefl n (by simpa [hcond] using Nat.lt_of_lt_of_le hlt hge)
      simp [hnot]
    rw [hempty]
    simp

end _Probe47t
end Shufflemath
