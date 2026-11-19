module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic
public import Shufflemath.Finite
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open CommanderPhysicalExchange
open FiberDisintegration
open Finset
open Fintype

/-!
## A3 count-bridge machinery (home file)

The proper library home for the A3 count-bridge building blocks that live *below*
`CommanderMembershipExchange` in the dependency order, so that
`CommanderMembershipExchange` can import them (for the `hMembershipExchange`
capstone) without an import cycle.  This file must **not** import
`CommanderMembershipExchange`.

Currently relocated here:

* `exchangeChoice_card_eq_transitionDenominator` — `#exchangeChoice =
  transitionDenominator 99 50 25`, the cardinality bridge that `a3_countBridge`
  and the `mu_x_countFiberTotal` count-bridge need.  (Moved out of
  `CommanderMembershipExchange` to break the import cycle.)
-/

/-- The exchange-choice choice space has exactly `transitionDenominator 99 50 25`
    elements: it is the product of the 25-subsets-of-50 and 25-subsets-of-49,
    i.e. `choose 50 25 * choose 49 25 = transitionDenominator 99 50 25`.  This is
    the card fact that turns the `(1 / #exchangeChoice) · #{...}` count law into
    the `transitionWeight 99 50 25` normalization the A3 part-(i) assembly needs. -/
theorem exchangeChoice_card_eq_transitionDenominator :
    (Fintype.card exchangeChoice : Rat) =
      (transitionDenominator 99 50 25 : Rat) := by
  classical
  -- the product choice space
  have hProd : Fintype.card exchangeChoice =
      Fintype.card {L : Finset (Fin 50) // L ∈ leftChoices} *
      Fintype.card {R : Finset (Fin 49) // R ∈ rightChoices} := by
    unfold exchangeChoice
    simp only [Fintype.card_prod]
  -- the subtype cards are the finset cards
  have hSubL : Fintype.card {L : Finset (Fin 50) // L ∈ leftChoices} = (leftChoices).card := by
    simp [Fintype.card_subtype, leftChoices, Finset.mem_powersetCard]
  have hSubR : Fintype.card {R : Finset (Fin 49) // R ∈ rightChoices} = (rightChoices).card := by
    simp [Fintype.card_subtype, rightChoices, Finset.mem_powersetCard]
  -- each finset card is the corresponding binomial coefficient
  have hLc : (leftChoices).card = Nat.choose 50 25 := by
    unfold leftChoices
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hRc : (rightChoices).card = Nat.choose 49 25 := by
    unfold rightChoices
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- transitionDenominator 99 50 25 = choose 50 25 * choose (99-50) 25 = choose 50 25 * choose 49 25
  have hTd : (transitionDenominator 99 50 25 : Rat) =
      (Nat.choose 50 25 * Nat.choose 49 25 : Rat) := by
    unfold transitionDenominator
    norm_num
  rw [hProd, hSubL, hSubR, hLc, hRc, hTd]
  simp [Nat.cast_mul]

end Shufflemath
end
