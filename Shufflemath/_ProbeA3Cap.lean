module

public import Shufflemath.FinsetCombinatorics
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderA3Kernel
public import Shufflemath.CommanderA3ExchangePushforward
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
open CommanderMembershipExchange
open CommanderPhysicalExchange
open Finset

/-- **The 4 recursion walls are BROKEN (69th session).** The crux
    `Fintype.card {j : exchangeChoice // p j} = Finset.card (Finset.univ (j : exchangeChoice) | p)`
    closes non-recursively via `Fintype.card_of_subtype` (Mathlib `Data/Fintype/Card.lean`,
    proof `rw [← subtype_card s H]; congr!` — an *instance* bridge, never a `Fintype.univ` compute).
    This theorem chains `fintypeCard_subtypeCongr` (membership-count ↔ marked-count) then
    `Fintype.card_of_subtype` to reach the univ-filter **Finset** card.  The only remaining step
    is the equiv-push of that Finset to the `Fin 50 × Fin 49` product space (see handoff). -/
theorem probe_countBridge_preEquiv (d : Deck) (c : Nat) :
    Fintype.card {j : exchangeChoice //
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c}
    = Finset.card (Finset.univ.filter (fun j : exchangeChoice =>
      (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c)) := by
  let P : exchangeChoice → Prop := fun j =>
    membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c
  let Q (j : exchangeChoice) : Prop :=
    (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c
  change Fintype.card {j : exchangeChoice // P j}
      = Finset.card (Finset.univ.filter Q)
  -- P ch <-> Q ch  (membership-count = marked-count, pointwise)
  have hPQ (ch : exchangeChoice) : P ch ↔ Q ch := by
    dsimp only [P, Q]
    have h := count_exchangeChoice_eq_markedCount d ch
    constructor
    · intro hc; rw [h] at hc; exact hc
    · intro hc; rw [← h] at hc; exact hc
  calc
    Fintype.card {j : exchangeChoice // P j} = Fintype.card {j : exchangeChoice // Q j} :=
      FinsetCombinatorics.fintypeCard_subtypeCongr (P := P) (Q := Q) hPQ
    _ = Finset.card (Finset.univ.filter Q) :=
      Fintype.card_of_subtype (p := Q) (s := Finset.univ.filter Q)
        (H := fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end Shufflemath
end
