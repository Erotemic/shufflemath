module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplaceGeneral
open CommanderPermutation
open CommanderPhysicalExchange
open FinsetCombinatorics
open Finset

namespace _Probe47p

/-!
# Per-deck Bernoulli-Laplace bridge — building blocks (47o part 2)

For a fixed deck `d`, let `x = leftOriginalCount d` (originally-left cards
currently at left positions) and `xR = #(markedRightPos d) = 50 - x` (the
marked cards that crossed to the right).  A 25/25 exchange selects a 25-subset
`L` of the left positions and a 25-subset `R` of the right positions; the new
left-pile originally-left count is

  `newLeftOriginalCount d L R = (x - markedInLeft d L) + markedInRight d R`

(`newLeftOriginalCount_eq`).  This file builds the counting kernel that
discharges `hMembershipExchange` per deck: the number of `(L, R)` pairs with
new count `n` is the 4-fold Vandermonde sum, which equals
`transitionNumerator 99 50 50 25 x n` (r = 50 = the total originally-left /
"red" cards, k = 25).

Building blocks (proved below): the number of 25-subsets of a pile containing
exactly `a` of the marked positions is the hypergeometric number
`choose(#marked, a) * choose(#unmarked, 25 - a)` — the reusable
`powersetCard_markedContent`.
-/

variable (d : Deck) (n : Nat)

/-- The 25/25 selected-set pairs: a 25-subset of the 50 left positions times a
    25-subset of the 49 right positions. -/
noncomputable def leftRight25Pairs : Finset (Finset (Fin 50) × Finset (Fin 49)) :=
  (Finset.univ : Finset (Fin 50)).powersetCard 25 ×ˢ
    (Finset.univ : Finset (Fin 49)).powersetCard 25

/-- The number of 25-subsets `L` of the left pile holding exactly `aL`
    originally-left cards is the hypergeometric number
    `choose(x, aL) * choose(50 - x, 25 - aL)`. -/
theorem leftCountByMarked (aL : Nat) (ha : aL ≤ 25) :
    (((Finset.univ : Finset (Fin 50)).powersetCard 25).filter
      (fun L => markedInLeft d L = aL)).card =
      Nat.choose (leftOriginalCount d) aL * Nat.choose (50 - leftOriginalCount d) (25 - aL) := by
  have hsub : markedLeftPos d ⊆ (Finset.univ : Finset (Fin 50)) := Finset.subset_univ _
  simpa [markedInLeft, markedLeftPos_card d, Finset.inter_comm] using
    powersetCard_markedContent
      (U := (Finset.univ : Finset (Fin 50))) (M := markedLeftPos d) hsub 25 aL ha

/-- The number of 25-subsets `R` of the right pile holding exactly `bR`
    originally-left (crossed) cards is the hypergeometric number
    `choose(xR, bR) * choose(49 - xR, 25 - bR)`, where `xR = 50 - x`. -/
theorem rightCountByMarked (bR : Nat) (ha : bR ≤ 25) :
    (((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => markedInRight d R = bR)).card =
      Nat.choose (markedRightPos d).card bR *
        Nat.choose (49 - (markedRightPos d).card) (25 - bR) := by
  have hsub : markedRightPos d ⊆ (Finset.univ : Finset (Fin 49)) := Finset.subset_univ _
  simpa [markedInRight, Finset.inter_comm] using
    powersetCard_markedContent
      (U := (Finset.univ : Finset (Fin 49))) (M := markedRightPos d) hsub 25 bR ha

end _Probe47p
end Shufflemath
