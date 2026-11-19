module

/-!
WIP — 67th-session continuation of the A3 count proof (66th-session file `55a_a3mass_wip.lean`'s follow-up).

STATUS (as of this session):
  (a) `exchangeChoice_card_eq_transition`  — DONE (55th).
  (b) `uniformPushforward_eventMass`       — DONE (55th).
  (c) THIS (the 3rd of the three 1B-bridge lemmas): `rawExchange_membershipCount_mass` — 95% done.
      All mathematical content is PROVED and compiles in this file:
        - the point-mass step `hA` (via `rawExchangeMembership_pointMass` + the `F` let),
        - the indicator → fiber-sum step (`Finset.sum_filter`),
        - the fiber-sum → preimage-card step via `fiberSum_eq_preimageCard` (hNat), and
        - the 4th calc step now CLOSES with targeted `rw [← Nat.cast_sum]; rw [hNat]` (the earlier
          `simpa [Nat.cast_sum]` recursed on the deep structure — a single `rw` does not).
        - `hP : F j ∈ S ↔ Q j` (the predicate equality, the whole substance) WORKS:
            `simp only [S, Finset.mem_filter, Finset.mem_univ]; dsimp [F]; simp only [and_true, true_and]`
            (reduces `F j ∈ S` to `True ∧ count (F j) = c`, then `Q j` — SHALLOW, no `newMembership` unfolding).
      The ONE remaining step is the final Fintype-card bridge:
          `(Fintype.card {j // F j ∈ S} : Rat) = (Fintype.card {j // Q j} : Rat)`
      where `F j ∈ S` and `Q j` are `Iff`-equal (`hP`) but NOT definitionally equal (the subtype predicate
      `F j ∈ (univ.filter (count·=c))` does not reduce to `count (newMembership ...) = c` by WHNF alone —
      it needs the `Finset.mem_filter`/`mem_univ` SIMPLIFICATION, which is not definitional). So no
      `rfl` / `congr` / `congrArg Fintype.card (Subtype.ext hP)` (type mismatch) / manual-Equiv +
      `Fintype.card_congr` (its injectivity `ext` leaves a deep `a✝ ∈ ↑(...).2` Membership-internal
      subgoal) closes it.

NEXT (clean fix — the general lemma):
  Prove ONCE, in `Shufflemath/FinsetCombinatorics.lean` (a shallow context, NOT the Membership-heavy A3
  file), the general bridge
      `Fintype.card {a : α // P a} = Fintype.card {a : α // Q a}`  from  `h : ∀ a, P a ↔ Q a`
  (first check whether Mathlib already has it — candidates: `Fintype.card_congr` from a subtype `Equiv`,
  or a `Finset.ncard`/`Finset.card_congr`-based formulation). Then apply it here with `hP` to close the
  5th calc step, and `rw [hXY]; rfl`. Then extract the whole lemma into `Shufflemath/CommanderA3Mass.lean`
  (new file; add to `Shufflemath.lean` module list, after `CommanderA3Count`), delete this probe, and
  `./dev/verify_next_phase.sh` must stay green.

  The `maxRecDepth 20000` option in this file is a LOCAL guard for the deep structure; the general-lemma
  route should let it go away once the bridge no longer reduces the Membership-internal Finset.
-/-

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

-- The deep `newMembership` / `Membership`-Finset structure pushes some reductions past the
-- default recursion cap; bump it for this file's proof only (local, not global).
set_option maxRecDepth 20000

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
          --  goal:  invEC * (∑ m ∈ S, (Fintype.card {j // F j = m} : Rat))  =  invEC * (Fintype.card {j // F j ∈ S} : Rat)
          --  (1) `rw [← Nat.cast_sum]`  turns the per-term-cast sum into the cast of the Nat sum (single rewrite, avoids `simpa` recursion).
          --  (2) `rw [hNat]`  replaces the Nat sum by the preimage Fintype-card (hNat: fiberSum = preimageCard).
          rw [← Nat.cast_sum]
          rw [hNat]
    _ =
        (Fintype.card exchangeChoice : Rat)⁻¹ *
          (Fintype.card {j : exchangeChoice //
             membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c} : Rat) := by
      -- AVOID `congr` (decomposing the product recurses on the deep structure).  Instead: the two
      -- Fintype-cards are equal because their subtypes are in bijection (hP gives the fiberwise `Iff`),
      -- bridged by an explicit `Equiv` + `Fintype.card_congr` (shallow: `hP`'s proof is a shallow
      -- simp; no `newMembership` unfolding).
      have hP (j : exchangeChoice) : F j ∈ S ↔
          membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c := by
        simp only [S, Finset.mem_filter, Finset.mem_univ]
        dsimp only [F]
        simp only [and_true, true_and]
      set Q : exchangeChoice → Prop := fun j =>
        membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c
      have heq : {j : exchangeChoice // F j ∈ S} ≃ {j : exchangeChoice // Q j} :=
        ⟨fun x => ⟨x.1, (hP x.1).mp x.2⟩,
         fun x => ⟨x.1, (hP x.1).mpr x.2⟩,
         fun x => by ext; rfl,
         fun x => by ext; rfl⟩
      have hXY : (Fintype.card {j : exchangeChoice // F j ∈ S} : Rat) =
          (Fintype.card {j : exchangeChoice // Q j} : Rat) := by
        rw [Nat.cast_inj]
        exact Fintype.card_congr heq
      rw [hXY]
      --  invEC * Y  =  (Fintype.card exchangeChoice)⁻¹ * Y   —  invEC is definitionally that factor
      rfl

end Shufflemath
