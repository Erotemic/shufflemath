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

/-
## PURE-FINSET equiv-push route (69th session, continued) — NO Fintype computation.

Goal:  Fintype.card {j : exchangeChoice // P j}  =  transitionNumerator 99 50 25 (leftOriginalCount d) c

Route (every step is wall-free: card_of_subtype is a structural congr; card_image_of_injOn needs
only DecidableEq; Finset.ext is pointwise — none of these ever compute a powerset cardinality):
  (f1) Fintype.card {j // P j} = Finset.card (Finset.univ (j : exchangeChoice) | P)          [Fintype.card_of_subtype]
  (f2) = Finset.card (Finset.univ (j : exchangeChoice) | Q)                                 [Finset.card_congr, P<->Q]
  (f3) = Finset.card ((Finset.univ (j : exchangeChoice) | Q).image f)                       [Finset.card_image_of_injOn]
  (f4) = Finset.card ((leftChoices ×ˢ rightChoices).filter (fun p => (newLeftCards ...) = c))
        where f j = (j.1.1, j.2.1) and the last equality is a Finset.ext (pointwise)          [Finset.ext]
  (f5) = transitionNumerator 99 50 25 (leftOriginalCount d) c                               [newLeftCount_eq_transitionNumerator]
-/

/-- The projection from the choice space to the flat `(L, R)` product. -/
def projLR (j : exchangeChoice) : Finset (Fin 50) × Finset (Fin 49) := (j.1.1, j.2.1)


/-! f1: Fintype.card of the P-subtype = Finset.card of the univ-filter (Fintype.card_of_subtype, non-recursive). -/
theorem probe_f1 (d : Deck) (c : Nat) :
    Fintype.card {j : exchangeChoice //
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c}
    = Finset.card (Finset.univ.filter (fun j : exchangeChoice =>
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c)) := by
  let P (j : exchangeChoice) : Prop :=
    membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c
  exact Fintype.card_of_subtype (p := P) (s := Finset.univ.filter P)
        (H := fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

/-! f2: the univ-filter card is unchanged under the (pointwise) P<->Q predicate equivalence. -/
theorem probe_f2 (d : Deck) (c : Nat) :
    Finset.card (Finset.univ.filter (fun j : exchangeChoice =>
      membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c))
    = Finset.card (Finset.univ.filter (fun j : exchangeChoice =>
      (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c)) := by
  let P (j : exchangeChoice) : Prop :=
    membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c
  let Q (j : exchangeChoice) : Prop :=
    (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c
  have hPQ (j : exchangeChoice) : P j ↔ Q j := by
    dsimp only [P, Q]
    have h := count_exchangeChoice_eq_markedCount d j
    constructor
    · intro hc; rw [h] at hc; exact hc
    · intro hc; rw [← h] at hc; exact hc
  have hEq : (Finset.univ.filter P : Finset exchangeChoice) = Finset.univ.filter Q := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hPQ x
  simpa [P, Q] using congrArg Finset.card hEq

/-! f3: pushing the univ-filter through the (injective) projection preserves the card (no Fintype needed). -/
theorem probe_f3 (d : Deck) (c : Nat) :
    Finset.card (Finset.univ.filter (fun j : exchangeChoice =>
      (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c))
    = Finset.card ((Finset.univ.filter (fun j : exchangeChoice =>
      (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c)).image projLR) := by
  let Q (j : exchangeChoice) : Prop :=
    (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c
  set s := (Finset.univ.filter Q : Finset exchangeChoice)
  classical
  have hInjOn : Set.InjOn projLR s := by
    intro a _ b _ h
    simp only [projLR, Prod.mk.injEq] at h
    apply Prod.ext <;> apply Subtype.ext <;>
      (try exact h.1) <;> (try exact h.2)
  simpa [s, projLR] using (Finset.card_image_of_injOn hInjOn).symm

/-!
NOTE (resumption point): the composition of f1 ∘ f2 ∘ f3
    Fintype.card {j // membershipCount = c} = Finset.card ((univ.filter markedCountPred).image projLR)
    recurses when written as a single `calc` (the `Fintype.card {j // ...}` and the image
    together force the exchangeChoice product Fintype univ computation). Each of f1/f2/f3
    compiles in ISOLATION. The next step (f4) — equating that image to
    `(leftChoices ×ˢ rightChoices).filter (newLeftCards-count = c)` (= transitionNumerator via
    `newLeftCount_eq_transitionNumerator`) — needs a pointwise Finset membership on the
    exchangeChoice side, which recurses on the ×ˢ-of-powersetCard univ; the 47v machinery
    computes the same card combinatorially (Nat.choose) instead. The count bridge is thus
    proven up to the image push (f1–f3); f4 is the last step. See docs/agent_handoff.md.
-/
end Shufflemath
end
