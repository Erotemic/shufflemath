module

public import Shufflemath.FinsetCombinatorics
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderA3Kernel
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderPhysicalExchange
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open CommanderPhysicalExchange
open Finset

/-
## A3 capstone count bridge (68th-session diagnosis)

**Goal:** the count-level A3 equality `rawExchangeMembership_count` needs
    `#{j : exchangeChoice // membershipCount (newMembership d j ...) = c}
       = transitionNumerator 99 50 25 (leftOriginalCount d) c`
(the preimage-count → transitionNumerator bridge).  Chaining this with
`exchangeChoice_card_eq_transitionDenominator` turns the mass
(`rawExchange_membershipCount_mass`) into the `transitionWeight`, and
`newLeftCount_deckIndependent` gives the fiber-average collapse.

**Recursion diagnosis:**
- `Fintype.card {j : exchangeChoice // …}` (the *named* Fintype) compiles — proven in
  `rawExchange_membershipCount_mass`.
- `Finset.card (leftChoices ×ˢ rightChoices)` (the *concrete* Finset) compiles (Test 2).
- `Fintype.card {p : Finset (Fin 50) × Finset (Fin 49) // …}` (the *anonymous* huge
  product) recurses even at `maxRecDepth 4000`.  So the bridge must stay in the
  named-Fintype `exchangeChoice` and the concrete-Finset `leftChoices ×ˢ rightChoices`,
  never instantiating a Fintype on the anonymous product.  `newLeftCount_eq_transitionNumerator`
  already counts over `(leftChoices ×ˢ rightChoices).filter (…)` — the target domain.

**Chain (next session):** exchangeChoice ≃ ↑(leftChoices ×ˢ rightChoices) (via
exchangeChoice_equiv_lr + Finset.mem_prod, keeping the concrete-Finset side), then the
predicate bridge (membershipCount (newMembership d …) = (newLeftCards d … ∩ leftOrigSet).card,
via membershipCount_newMembership), then `newLeftCount_eq_transitionNumerator`.
-/

/-- Test 2 (compiled): the concrete Finset prod has a computable card. -/
theorem probe_prod_finset_card :
    Finset.card (leftChoices ×ˢ rightChoices) =
      Finset.card leftChoices * Finset.card rightChoices := by
  simp [Finset.card_product]

/-- The A3-capstone count bridge (WIP — `sorry` at the deep equiv/predicate crux). -/
theorem exchangeCount_preimage_eq_transitionNumerator (d : Deck) (c : Nat) :
    Fintype.card {j : exchangeChoice //
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c}
    = transitionNumerator 99 50 25 (leftOriginalCount d) c := by
  sorry

end Shufflemath
end
