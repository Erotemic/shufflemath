module

public import Shufflemath.FinsetCombinatorics
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderA3Kernel
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFiberCount
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
    `Fintype.card {j : exchangeChoice // membershipCount (newMembership d j ...) = c}
       = transitionNumerator 99 50 25 (leftOriginalCount d) c`
(the preimage-count → transitionNumerator bridge).  Chained with
`exchangeChoice_card_eq_transitionDenominator` it turns the mass
(`rawExchange_membershipCount_mass`) into the `transitionWeight`, and
`newLeftCount_deckIndependent` gives the fiber-average collapse.

**Recursion diagnosis (three walls, all at maxRecDepth 4000):**
1. `Fintype.card` of the *named* Fintype `exchangeChoice` and of the *concrete* Finset
   `leftChoices ×ˢ rightChoices` (their cards) elaborate fine — the target statement below
   COMPILES, and `newLeftCount_eq_transitionNumerator` counts over
   `(leftChoices ×ˢ rightChoices).filter …` in exactly this idiom.
2. `Fintype.card` of the *anonymous* product `{p : Finset (Fin 50) × Finset (Fin 49) // …}`
   recurses — so do NOT restate the count over the raw product.
3. **NEW:** even the *statement-legal* `Fintype.card {p : ↑(leftChoices ×ˢ rightChoices) // …}`
   (a Finset-subtype, whose `Fintype` comes from `Finset.fintype`) **recurses in the PROOF**
   (`unfold Fintype.card; simp [Fintype.card, Finset.fintype, …]`) — computing that subtype's
   card forces the anonymous-product reduction.  So the bridge must never instantiate a
   `Fintype` on `↑(leftChoices ×ˢ rightChoices)` in the proof either.

**Consequence / route:** keep BOTH ends concrete — (LHS) the named-Fintype `exchangeChoice`
as `Finset.card (Finset.univ (j : exchangeChoice) | …)`, (RHS) the concrete-Finset
`Finset.card ((leftChoices ×ˢ rightChoices).filter …)`, and bridge the two Finsets by the
bijection `exchangeChoice ≃ ↑(leftChoices ×ˢ rightChoices)` (via `exchangeChoice_equiv_lr` +
`Finset.mem_prod`), pushing the predicate `membershipCount (newMembership d L R) = c
↔ (newLeftCards d L R ∩ leftOrigSet).card = c` (`membershipCount_newMembership`).  The next
session's first probe should test whether
`Fintype.card {j : exchangeChoice // P j} = Finset.card (Finset.univ (j : exchangeChoice) | P j)`
is a NON-recursive bridge (it uses the named Fintype, so it should be) before pushing the
equiv to the concrete Finset.

**Imports that work:** `FinsetCombinatorics`, `BernoulliLaplace`, `CommanderPermutation`
(`leftOriginalCount`), `CommanderA3Kernel` (`newLeftCount_eq_transitionNumerator`,
`newLeftCount_deckIndependent`), `CommanderMembershipKernels` (`membershipCount`),
`CommanderMembershipExchange` (`membershipCount_newMembership`), `CommanderPhysicalExchange`
(`newMembership`, `newLeftCards`, `leftChoices`/`rightChoices`, `leftCard25`/`rightCard25`,
`exchangeChoice_equiv_lr` in CommanderA3ExchangePushforward), `CommanderFiberCount`
(`leftOrigSet`); all in `namespace Shufflemath`, `FinsetCombinatorics.*` qualified,
`Finset.card_product` (not `card_prod`) for the prod card.
-/

/-- (compiled, 68th-session) the concrete Finset prod has a computable card. -/
theorem probe_prod_finset_card :
    Finset.card (leftChoices ×ˢ rightChoices) =
      Finset.card leftChoices * Finset.card rightChoices := by
  simp [Finset.card_product]

/-- The A3-capstone count bridge (WIP — `sorry`; route + recursion walls above). -/
theorem exchangeCount_preimage_eq_transitionNumerator (d : Deck) (c : Nat) :
    Fintype.card {j : exchangeChoice //
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c}
    = transitionNumerator 99 50 25 (leftOriginalCount d) c := by
  sorry

end Shufflemath
end
