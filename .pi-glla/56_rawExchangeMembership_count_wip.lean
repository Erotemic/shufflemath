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

-- ============================================================================
-- 56th-session WIP — A3 part (i) count-mass bridge
--   `rawExchange_membershipCount_mass`
-- ============================================================================
-- STATUS (56th session):  the (a)+(b) combinatorial core is DONE and the whole
-- `calc` chain is written; ONLY the final step (turn `F j ∈ S` into
-- `membershipCount (newMembership ...) = c`) is open.  Specifically:
--   (a)  point mass -> fiber count      [hA, uses CommanderA3ExchangePushforward.
--                                       rawExchangeMembership_pointMass +
--                                       `Fintype.card_subtype`]                      ✓ DONE
--       the `if count m = c` indicator -> the `c`-fiber S                         ✓ DONE
--       `← mul_sum`  (factor `1/#EC` out of the sum)                             ✓ DONE
--       `Finset.sum_filter`  (sum over univ with indicator = sum over S)          ✓ DONE
--   (b)  fiber sum = preimage          [FinsetCombinatorics.fiberSum_eq_preimageCard
--                                       + `Nat.cast_sum` / `congrArg`]            ✓ DONE
--   (c)  FINAL STEP:  `F j ∈ S` reduces to  `membershipCount (F j) = c`, and
--       `F j = newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)`,
--       so the two subtypes are the same.  BUT  `dsimp only [F, S, ...]; rfl`
--       hits `maximum recursion depth` because `F` = `newMembership` is a deep
--       definition (addMembership over `Finset.succImage` / `mem`).
--
-- NEXT (57th session — one focused fix):  do NOT fully unfold `F`/`newMembership`
-- in an `rfl`/`dsimp`.  Instead, at the final step, prove the PREDICATE equality
-- by `funext j; simp only [S, Finset.mem_filter, Finset.mem_univ]` (this reduces
-- `F j ∈ S` to `membershipCount (F j) = c` WITHOUT unfolding `newMembership`),
-- then bridge the two `Fintype.card`s with `congr 1` / `Fintype.card_congr` /
-- `congrArg (Fintype.card ·)`.  The predicate `membershipCount (F j) = c` vs
-- `membershipCount (newMembership ...) = c` differ only by the `set F` let-relation
-- (`F j` vs `newMembership ... j ...`), which is a shallow `dsimp [F]` (a `let`,
-- not a recursive def) — that shallow unfold does NOT recurse.  So the close is:
--   `congr 1`  →  `simp only [F, S, Finset.mem_filter, Finset.mem_univ]`  →  `rfl`
-- (the `rfl` now only has to confirm the two `let`-unfolded predicates, not
--  `newMembership`'s body).  If that still recurses, the fallback is
--  `have hP : (fun j => F j ∈ S) = (fun j => membershipCount (newMembership d ...) = c)
--   := by funext j; simp only [F, S, Finset.mem_filter, Finset.mem_univ]`
--  then `convert Fintype.card_congr hP` (a `Subtype.ext`/`congrArg` at the
--  `Fintype.card` level, never unfolding `newMembership`).
--
-- After this closes, the lemma extracts to `CommanderA3ExchangePushforward.lean`
-- (NOT `CommanderMembershipExchange.lean` — that would be an import cycle, since
-- `CommanderA3ExchangePushforward` already imports `CommanderMembershipExchange`).
-- It then plugs into step 2/3 of the 56th-session A3 part-(i) plan (the fiber
-- average over the `c`-fiber and its reconciliation with `transitionNumerator`).

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open CommanderMembershipKernels
open Finset
open Fintype

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
        rfl
      rw [h]
      simp only [ite_true]
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
    _ =
        invEC *
          (∑ m : Membership,
             (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0)) := by
      rw [← mul_sum]
    _ =
        invEC * (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) := by
      have hSum :
          (∑ m : Membership,
             (if membershipCount m = c then (Fintype.card {j : exchangeChoice // F j = m} : Rat) else 0)) =
            (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro m hm2
        simp only [S, Finset.mem_filter, Finset.mem_univ, hm2, ite_true]
      rw [hSum]
    _ =
        invEC * (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) := by
      have hNat : Fintype.card {j : exchangeChoice // F j ∈ S} =
          ∑ m ∈ S, Fintype.card {j : exchangeChoice // F j = m} :=
        FinsetCombinatorics.fiberSum_eq_preimageCard (X := exchangeChoice) (Y := Membership) F S
      calc
        invEC * (∑ m ∈ S, (Fintype.card {j : exchangeChoice // F j = m} : Rat)) =
            invEC * (∑ m ∈ S, Fintype.card {j : exchangeChoice // F j = m} : Rat) := by
          simp only [Nat.cast_ite, ite_mul]
          apply Finset.sum_congr rfl
          intro m _
          rfl
        _ = invEC * (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) := by
          have h := congrArg (fun (n : Nat) => (n : Rat)) hNat
          simpa [Nat.cast_sum] using h
    _ =
        (Fintype.card exchangeChoice : Rat)⁻¹ *
          (Fintype.card {j : exchangeChoice //
             membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c} : Rat) := by
      -- BLOCKED HERE (56th): `F j ∈ S` -> `membershipCount (F j) = c` -> `membershipCount (newMembership ...) = c`
      -- but `dsimp [F]; rfl` recurses (F = newMembership is deep).  See the banner's NEXT for the
      -- `congr 1` + `funext`/`simp` (shallow) close.
      dsimp only [F, S, Finset.mem_filter, Finset.mem_univ]
      rfl

end Shufflemath
