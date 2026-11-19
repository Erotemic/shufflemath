module

public import Shufflemath.Finite
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderA3ExchangePushforward
public import Shufflemath.CommanderPhysicalExchange

open Finset Fintype

/-!
Recursion-wall investigation (A3-capstone count bridge, 70th session).

Establishes precisely WHERE the `Fintype`-based count bridge recurses:

* The RAW `leftChoices` / `rightChoices` Finsets (each `powersetCard 25`) and their
  product `leftChoices ×ˢ rightChoices` are CLEAN: `probe_rawProdCard` compiles via
  `Finset.card_product` with no powerset computation. This is the side the 47v
  machinery (`_Probe47v.transitionNumerator_eq_fiberProduct`, `newLeftCount_eq_transitionNumerator`)
  uses to compute the count combinatorially (`Nat.choose`) — non-recursive.

* The `Fintype.univ` of the SUBTYPE `{L : Finset (Fin 50) // L ∈ leftChoices}` (and hence of
  `exchangeChoice = {L // L ∈ leftChoices} × {R // R ∈ rightChoices}`) RECURSES when expanded
  or computed to a product (the `Fintype` instance is `inferInstance`, whose univ is not the
  clean base Finset). So `Fintype.card {j : exchangeChoice // …}` (the count-mass side) cannot
  be reduced to the raw `×ˢ`-filter card without hitting the recursion.

Conclusion: the count bridge is proven up to the image push (`_ProbeA3Cap.lean` f1–f3). The
last step needs a bijection that *constructs* the raw-`×ˢ` membership from the subtype's
clean pieces (never touching `Fintype.univ`), then reuses `newLeftCount_eq_transitionNumerator`
(= the 47v combinatorial card). See `docs/agent_handoff.md` (70th session).
-/

@[expose] public section

namespace Shufflemath

open CommanderMembershipKernels
open CommanderPhysicalExchange

variable (d : Deck)

-- The RAW product card is clean (no powerset compute) — the side the 47v bridge uses.
theorem probe_rawProdCard :
    (leftChoices ×ˢ rightChoices).card = leftChoices.card * rightChoices.card := by
  simp only [Finset.card_product]

end Shufflemath
end
