module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderA3ExchangePushforward
public import Shufflemath.FinsetCombinatorics
public import Shufflemath.BernoulliLaplace
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open CommanderMembershipKernels
open Finset
open Fintype

-- The deep `newMembership` / `Membership`-Finset structure pushes a few reductions to a
-- recursion depth of ~70 (measured: this file builds at `maxRecDepth` 70 but not 60).  That
-- is comfortably inside Lean's default cap (1000), so no local `maxRecDepth` bump is needed.
-- The 66th-session wall that an old 20000 backstop hedged is gone: the final fiber-card
-- bridge now uses the shallow, general `fintypeCard_subtypeCongr` (applied to `hP`) instead
-- of a Membership-context `Equiv`, whose `ext`/reduction was the actual recursion source.

/- 67th session — A3 part (i), the final 1B-bridge lemma: the  c-fiber  total mass of the
   raw-exchange-membership transition kernel equals the transition weight  (1 / #exchangeChoice)
   times the number of exchange-choices whose induced membership carries exactly  c  marked
   left-cards.

   This is the third and last of the three lemmas the 56th-session A3 plan calls the "1B bridge"
   (the other two,  exchangeChoice_card_eq_transition  and  uniformPushforward_eventMass, were the
   55th session's work).  Together they feed the uniform-pushforward / BernoulliLaplace-semantic
   discharge of the Commander membership-exchange contract.

   The proof is a calc chain: point-mass (rawExchangeMembership_pointMass) -> indicator -> fiber-sum
   (Finset.sum_filter) -> preimage-card (fiberSum_eq_preimageCard) ->  Fintype-card  bridge.  The final
   bridge uses the general, shallow  fintypeCard_subtypeCongr  (applied to  hP)  rather than a
   Membership-context  Equiv  (whose  ext/recursion was the 66th-session wall). -/
theorem rawExchange_membershipCount_mass (d : Deck) (c : Nat) :
    (∑ m : Membership,
       (if membershipCount m = c then (Dist.mass (rawExchangeMembership d) m) else 0)) =
      (Fintype.card exchangeChoice : Rat)⁻¹ *
        (Fintype.card {j : exchangeChoice //
           membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c} : Rat) := by
  classical
  set F : exchangeChoice → Membership := fun j =>
    newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)
  set S : Finset Membership := (Finset.univ : Finset Membership).filter (fun m => membershipCount m = c)
  set invEC : Rat := (Fintype.card exchangeChoice : Rat)⁻¹
  set Q : exchangeChoice → Prop := fun j =>
    membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c
  -- (1) Each membership's kernel mass, on its  c-fiber, is  (1/#EC)  times the card of its fiber
  --     {j // F j = m}  (point-mass formula + the fiber-card = preimage-ncard bridge).
  have hA (m : Membership) :
      (if membershipCount m = c then (Dist.mass (rawExchangeMembership d) m) else 0 : Rat) =
        invEC *
          (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0) := by
    by_cases hm : membershipCount m = c
    · simp only [hm, ite_true]
      rw [CommanderA3ExchangePushforward.rawExchangeMembership_pointMass d m]
      dsimp only [F]
      have h : (#{j ∈ (Finset.univ : Finset exchangeChoice) | F j = m} : Rat) =
          (Fintype.card {j : exchangeChoice // F j = m} : Rat) := by
        simp only [Fintype.card_subtype, Nat.cast_ite]
      rw [h]
    · simp only [hm, ite_false, mul_zero]
  calc
    (∑ m : Membership,
       (if membershipCount m = c then (Dist.mass (rawExchangeMembership d) m) else 0)) =
        (∑ m : Membership,
          invEC *
            (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0)) := by
      apply Finset.sum_congr rfl
      intro m _
      exact hA m
    -- (2) Factor the common  1/#EC  out of the sum.
    _ =
        invEC *
          (∑ m : Membership,
             (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0)) := by
      rw [← mul_sum]
    -- (3) The indicator restricts the sum to the  c-fiber  S  (Finset.sum_filter).
    _ =
        invEC * (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) := by
      have hSum :
          (∑ m : Membership,
             (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0)) =
            (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) := by
        rw [Finset.sum_filter]
      rw [hSum]
    -- (4) The fiber-sum over  S  is the  c-preimage  Fintype-card  (fiberSum_eq_preimageCard).
    _ =
        invEC * (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) := by
      have hNat : Fintype.card {j : exchangeChoice // F j ∈ S} =
          ∑ m ∈ S, Fintype.card {j : exchangeChoice // F j = m} :=
        FinsetCombinatorics.fiberSum_eq_preimageCard (X := exchangeChoice) (Y := Membership) F S
      calc
        invEC * (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) =
            invEC * (∑ m ∈ S, Fintype.card {j : exchangeChoice // F j = m} : Rat) := by
          simp only [Nat.cast_ite, ite_mul]
        _ = invEC * (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) := by
          rw [← Nat.cast_sum]
          rw [hNat]
    -- (5) The  c-fiber  predicate  F j ∈ S  is extensionally  Q j  (= c marked left-cards); the
    --     general  fintypeCard_subtypeCongr  bridges the two  Fintype-cards  (shallow — no
    --     Membership-context  Equiv).
    _ =
        (Fintype.card exchangeChoice : Rat)⁻¹ *
          (Fintype.card {j : exchangeChoice //
             membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c} : Rat) := by
      have hP (j : exchangeChoice) : F j ∈ S ↔ Q j := by
        simp only [S, Finset.mem_filter, Finset.mem_univ]
        dsimp only [F, Q]
        simp only [and_true, true_and]
      have hCard : Fintype.card {j : exchangeChoice // F j ∈ S} =
          Fintype.card {j : exchangeChoice // Q j} :=
        FinsetCombinatorics.fintypeCard_subtypeCongr (P := fun j => F j ∈ S) (Q := Q) hP
      have hXY : (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) =
          (Fintype.card {j : exchangeChoice // Q j} : Rat) :=
        congrArg (fun n : Nat => (n : Rat)) hCard
      rw [hXY]
      --  invEC  is definitionally  (Fintype.card exchangeChoice : Rat)⁻¹,  so  invEC * Y  =
      --  (Fintype.card exchangeChoice)⁻¹ * Y  (rfl after the rewrite above).

end Shufflemath
