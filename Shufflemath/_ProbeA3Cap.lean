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
## A3 capstone count bridge (68th-session diagnosis — READY for next session)

**Goal lemma** (statement compiles, body `sorry`):
    `Fintype.card {j : exchangeChoice // membershipCount (newMembership d j.1.1 (leftCard25 j.1.2)
       j.2.1 (rightCard25 j.2.2)) = c}
       = transitionNumerator 99 50 25 (leftOriginalCount d) c`.
  Chained with `exchangeChoice_card_eq_transitionDenominator` it turns
  `rawExchange_membershipCount_mass`'s RHS into the `transitionWeight`; with
  `newLeftCount_deckIndependent` it gives the fiber-average collapse
  `rawExchangeMembership_count = commanderExchange25_countMass`, the A3 part-(i) count level.
  The target is the next step toward the A3 kernel capstone `hMembershipExchange`.

**Recursion walls (all at `maxRecDepth 4000`; the 99-card powerset types are too big for
Fintype-card computation):**
  1. `Fintype.card` of the *named* Fintype `exchangeChoice` and of the *concrete* Finset
     `leftChoices ×ˢ rightChoices` (their cards) elaborate fine — the target statement compiles,
     and `newLeftCount_eq_transitionNumerator` counts over `(leftChoices ×ˢ rightChoices).filter …`.
  2. `Fintype.card` of the **anonymous** product `{p : Finset (Fin 50) × Finset (Fin 49) // …}`
     recurses — never restate the count over the raw product.
  3. `Fintype.card` of the Finset-subtype `{p : ↑(leftChoices ×ˢ rightChoices) // …}` (whose
     `Fintype` comes from `Finset.fintype`) recurses in the PROOF (`unfold Fintype.card;
     simp [Finset.fintype, …]` forces the anonymous-product reduction).
  4. **Even the named-Fintype bridge** `Fintype.card {j : exchangeChoice // P j} =
     Finset.card (Finset.univ (j : exchangeChoice) | P j)` recurses under `simp [Fintype.card,
     Finset.fintype]` (simp over-expands `Fintype.univ`/`card_univ` of the powerset Fintype).

**The route that should work (next session):** all four walls are triggered by computing a
`Fintype.card` from an *elaborated* Fintype instance on a huge type.  The escape is to use
`Fintype/Card.lean`'s instance-specific lemmas directly, which state the card WITHOUT expanding
the default instance: `Fintype.card_subtype` / `Fintype.card_of_subtype` / `Fintype.card_ofFinset`
give `Fintype.card (ofFinset s H …) = Finset.card s` for `H : x ∈ s ↔ P x`.  So:
  - LHS `Fintype.card {j : exchangeChoice // P j}` = (instance-independence, `Fintype.card_unique`
    / the `ofFinset`-vs-`Subtype` bridge) `Fintype.card (ofFinset (Finset.univ.filter P)
    (mem_filter_univ))` = (card_ofFinset) `Finset.card (Finset.univ (j : exchangeChoice) | P j)`.
  - push that Finset by the bijection `exchangeChoice ≃ ↑(leftChoices ×ˢ rightChoices)`
    (`exchangeChoice_equiv_lr` + `Finset.mem_prod`) to
    `Finset.card ((leftChoices ×ˢ rightChoices).filter P')`, `P' p =
    (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = c` (`membershipCount_newMembership`);
  - = `transitionNumerator 99 50 25 (leftOriginalCount d) c` (`newLeftCount_eq_transitionNumerator`).
  The `ofFinset`-vs-default-instance bridge is the crux to test first (it must avoid expanding the
  powerset Fintype; `Fintype.card_unique`/`Fintype.card_eq` instance-independence may do it in one
  `rw` without `simp`).

**Imports that work** (all in `namespace Shufflemath`; `CommanderFiberCount` has NO sub-namespace,
so `leftOrigSet` is used unqualified; `FinsetCombinatorics.*` qualified; `Finset.card_product`,
NOT `card_prod`): `FinsetCombinatorics`, `BernoulliLaplace`, `CommanderPermutation`
(`leftOriginalCount`), `CommanderA3Kernel` (`newLeftCount_eq_transitionNumerator`,
`newLeftCount_deckIndependent`), `CommanderMembershipKernels` (`membershipCount`),
`CommanderMembershipExchange` (`membershipCount_newMembership`), `CommanderPhysicalExchange`
(`newMembership`, `newLeftCards`, `leftChoices`/`rightChoices`, `leftCard25`/`rightCard25`),
`CommanderA3ExchangePushforward` (`exchangeChoice_equiv_lr`), `CommanderFiberCount`
(`leftOrigSet`).
-/

/-- (compiled) the concrete Finset prod has a computable card. -/
theorem probe_prod_finset_card :
    Finset.card (leftChoices ×ˢ rightChoices) =
      Finset.card leftChoices * Finset.card rightChoices := by
  simp [Finset.card_product]

/-- The A3-capstone count bridge (WIP — `sorry`; 4 recursion walls + route above). -/
theorem exchangeCount_preimage_eq_transitionNumerator (d : Deck) (c : Nat) :
    Fintype.card {j : exchangeChoice //
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c}
    = transitionNumerator 99 50 25 (leftOriginalCount d) c := by
  sorry

end Shufflemath
end
