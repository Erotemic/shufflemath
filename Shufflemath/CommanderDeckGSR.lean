module

public import Shufflemath.CommanderLocalGSR
public import Shufflemath.CommanderPhysicalExchange
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation CommanderLocalGSR CommanderPhysicalExchange

/-!
# Deck-level (F4.2) GSR: within-pile relabeling as a `Deck` permutation

F4.2 lifts the pile-level GSR machinery (`gsrProductKernel` over
`List (Fin nL) × List (Fin nR)`) to the deck level, i.e. to distributions over
`Deck = Equiv.Perm (Fin 99)`.  The Fintype-free route (avoids the
`List.mem_bind`/`toMultiset` sub-wall) is: a *membership-preserving* deck
permutation is exactly a within-pile relabeling, i.e. a pair
`(pl : Equiv.Perm (Fin 50)) × (pr : Equiv.Perm (Fin 49))` transported to a
`Deck` by `pileRelabelEquiv`.  This file establishes the injectivity half of
that identification: the within-pile pair is recovered from its `Deck` action.
-/

/-- **F4.2 injectivity:** a within-pile relabeling (a
    `Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49)` pair) is determined by its
    action as a `Deck` permutation.  If two within-pile relabelings produce the
    same `Deck`, then their left and right components agree.  The left component
    is read off on the 50 left positions via `pileRelabelEquiv_left` +
    `leftPosition_injective`; the right component on the 49 right positions via
    `pileRelabelEquiv_right` + `rightPosition_injective`. -/
theorem pileRelabelEquiv_pairInjective
    (p p' : Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49))
    (h : pileRelabelEquiv p.1 p.2 = pileRelabelEquiv p'.1 p'.2) :
    p = p' := by
  have h1 : p.1 = p'.1 := by
    apply Equiv.ext
    intro i
    have hL : leftPosition (p.1 i) = leftPosition (p'.1 i) := by
      calc
        leftPosition (p.1 i) = pileRelabelEquiv p.1 p.2 (leftPosition i) :=
          (pileRelabelEquiv_left _ _ i).symm
        _ = pileRelabelEquiv p'.1 p'.2 (leftPosition i) := by rw [h]
        _ = leftPosition (p'.1 i) := pileRelabelEquiv_left _ _ i
    exact leftPosition_injective hL
  have h2 : p.2 = p'.2 := by
    apply Equiv.ext
    intro j
    have hR : rightPosition (p.2 j) = rightPosition (p'.2 j) := by
      calc
        rightPosition (p.2 j) = pileRelabelEquiv p.1 p.2 (rightPosition j) :=
          (pileRelabelEquiv_right _ _ j).symm
        _ = pileRelabelEquiv p'.1 p'.2 (rightPosition j) := by rw [h]
        _ = rightPosition (p'.2 j) := pileRelabelEquiv_right _ _ j
    exact rightPosition_injective hR
  exact Prod.ext h1 h2

/-! ## The image half: membership-preserving decks are exactly the within-pile relabelings. -/

/-- The left within-pile component of a deck permutation `σ` that preserves the
    left/right split: `leftPermOf σ hL i` is the index of the left position that
    `σ` sends the `i`-th left position to.  Defined with `leftIndex` (the inverse
    of `leftPosition` on the left half). -/
def leftPermOf (σ : Deck) (hL : ∀ i : Fin 50, (σ (leftPosition i)).val < 50)
    (i : Fin 50) : Fin 50 :=
  leftIndex (σ (leftPosition i)) (hL i)

/-- The right within-pile component, dual to `leftPermOf`. -/
def rightPermOf (σ : Deck)
    (hR : ∀ j : Fin 49, ¬ (σ (rightPosition j)).val < 50) (j : Fin 49) : Fin 49 :=
  rightIndex (σ (rightPosition j)) (hR j)

/-- Reading the `leftPermOf` index back through `leftPosition` recovers exactly the
    image `σ` places the `i`-th left position at. -/
theorem leftPos_leftPermOf (σ : Deck) (hL : ∀ i : Fin 50, (σ (leftPosition i)).val < 50)
    (i : Fin 50) : leftPosition (leftPermOf σ hL i) = σ (leftPosition i) := by
  simp only [leftPermOf]
  exact leftPosition_leftIndex (σ (leftPosition i)) (hL i)

/-- Dual of `leftPos_leftPermOf` on the right half. -/
theorem rightPos_rightPermOf (σ : Deck)
    (hR : ∀ j : Fin 49, ¬ (σ (rightPosition j)).val < 50) (j : Fin 49) :
    rightPosition (rightPermOf σ hR j) = σ (rightPosition j) := by
  simp only [rightPermOf]
  exact rightPosition_rightIndex (σ (rightPosition j)) (hR j)

/-- The left within-pile component of a pile-preserving deck permutation is
    injective: two distinct left positions land on distinct left positions
    (`σ` and `leftPosition` are both injective). -/
theorem leftPermOf_injective (σ : Deck)
    (hL : ∀ i : Fin 50, (σ (leftPosition i)).val < 50) :
    Function.Injective (leftPermOf σ hL) := by
  intro i i' h
  have heq : leftPosition (leftPermOf σ hL i) = leftPosition (leftPermOf σ hL i') := by rw [h]
  have hσ : σ (leftPosition i) = σ (leftPosition i') := by
    calc
      σ (leftPosition i) = leftPosition (leftPermOf σ hL i) := (leftPos_leftPermOf σ hL i).symm
      _ = leftPosition (leftPermOf σ hL i') := heq
      _ = σ (leftPosition i') := leftPos_leftPermOf σ hL i'
  exact leftPosition_injective (σ.injective hσ)

/-- Dual of `leftPermOf_injective` on the right half. -/
theorem rightPermOf_injective (σ : Deck)
    (hR : ∀ j : Fin 49, ¬ (σ (rightPosition j)).val < 50) :
    Function.Injective (rightPermOf σ hR) := by
  intro j j' h
  have heq : rightPosition (rightPermOf σ hR j) = rightPosition (rightPermOf σ hR j') := by rw [h]
  have hσ : σ (rightPosition j) = σ (rightPosition j') := by
    calc
      σ (rightPosition j) = rightPosition (rightPermOf σ hR j) := (rightPos_rightPermOf σ hR j).symm
      _ = rightPosition (rightPermOf σ hR j') := heq
      _ = σ (rightPosition j') := rightPos_rightPermOf σ hR j'
  exact rightPosition_injective (σ.injective hσ)
