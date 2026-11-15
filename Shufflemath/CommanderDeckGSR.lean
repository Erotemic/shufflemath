module

public import Shufflemath.CommanderLocalGSR
public import Shufflemath.CommanderPhysicalExchange
public import Mathlib.Logic.Equiv.Basic
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
