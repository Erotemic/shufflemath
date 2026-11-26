module

public import Shufflemath.CommanderA3ExchangeCard
public import Shufflemath.FiniteDeck.SubsetExchange
public import Shufflemath.Gate6K1Bridges
public import Shufflemath.FiniteDeck.Gate6ThreeRound

@[expose] public section

namespace Shufflemath

/-!
# Gate 6: membership row independence (M5a)

The 25/25 physical exchange law `rawExchangeMembership` depends only on the
initial membership — not on the initial internal ordering — for the
99-card commander deck.

* `choiceImage` — the post-exchange membership for a given `(L, R)` choice.
* `choiceImage_injective` — the map is injective (from `newLeftCards_injective`).
* `reachable25` — the `k = 25` reach set of the initial membership (the
  documented `FiniteDeck.ReachSet` of the 99! deck).
* `choiceImage_mem_reachable` — the post-exchange membership is reachable
  (the 25-overlap + 50-card-size arithmetic, via `Finset.card_sdiff`).
* `choice_card_nat` / `choice_card_reachable` — the choice space and the
  reach set have the same cardinal (`choose 50 25 * choose 49 25`).
* `choice_range` — the image of the choice map is exactly the reach set.
* `rawExchangeMembership_eq_of_membership` — **the M5a theorem**: two decks with
  the same membership derive the same physical exchange law. Purely kernel-level;
  used by the deterministic-start reset-absorption chain (M5b).

The injectivity/bijection argument never enumerates the ambient 99-card type:
the `Fintype`/`Finset` reasoning happens on the *choice* domain and on the two
50-card left sets, exactly as in the seed.
-/

open CommanderPermutation CommanderMembershipKernels CommanderPhysicalExchange

/-- The post-exchange membership for a specific `(L, R)` choice — the kernel
    map of `rawExchangeMembership` by name, so only this definition is ever
    unfolded. -/
def choiceImage (d : Deck) (c : exchangeChoice) : Membership :=
  newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)

theorem choiceImage_injective (d : Deck) : Function.Injective (choiceImage d) := by
  intro a b hab
  have hv : newLeftCards d a.1.1 a.2.1 = newLeftCards d b.1.1 b.2.1 :=
    congrArg Subtype.val hab
  obtain ⟨hL, hR⟩ := newLeftCards_injective d a.1.1 b.1.1 a.2.1 b.2.1 hv
  exact Prod.ext (Subtype.ext hL) (Subtype.ext hR)

/-- The `k = 25` reach set of a membership: every membership reachable from it
  by a 25-exchange, as a `Finset` (the documented `FiniteDeck.ReachSet`). -/
noncomputable def reachable25 (s : Membership) : Finset Membership :=
  FiniteDeck.ReachSet 99 50 25 (by decide) (by decide) (by decide) s

theorem choiceImage_mem_reachable (d : Deck) (c : exchangeChoice) :
    choiceImage d c ∈ reachable25 (membership d) := by
  classical
  have hO : ((membership d).1 ∩ (choiceImage d c).1).card = 25 :=
    newMembership_overlap_25 d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)
  have hL : (membership d).1.card = 50 := (membership d).property
  have hR : (choiceImage d c).1.card = 50 := (choiceImage d c).property
  have h1 : ((membership d).1 \ (choiceImage d c).1).card = 25 := by
    rw [Finset.card_sdiff, hL, Finset.inter_comm, hO]
  have h2 : ((choiceImage d c).1 \ (membership d).1).card = 25 := by
    rw [Finset.card_sdiff, hR, hO]
  unfold reachable25 FiniteDeck.ReachSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h1, h2⟩

theorem choice_card_nat : Fintype.card exchangeChoice = Nat.choose 50 25 * Nat.choose 49 25 := by
  have h := exchangeChoice_card_eq_transitionDenominator
  change (Fintype.card exchangeChoice : Rat) =
    ((Nat.choose 50 25 * Nat.choose 49 25 : Nat) : Rat) at h
  exact_mod_cast h

theorem choice_card_reachable (s : Membership) :
    Fintype.card exchangeChoice = (reachable25 s).card := by
  rw [choice_card_nat, reachable25, FiniteDeck.subsetExchangeCount]

theorem choice_range (d : Deck) (s : Membership) :
    (∃ c, choiceImage d c = s) ↔ s ∈ reachable25 (membership d) :=
  range_iff_mem_of_card_eq (choiceImage d) (reachable25 (membership d))
    (choiceImage_injective d) (choiceImage_mem_reachable d)
    (choice_card_reachable (membership d)) s

/-- **M5a: the membership row is independence.** Two decks with the same
  membership derive the same physical exchange law — the uniform-choice
  pushforward through `choiceImage` depends only on the membership. This is the
  membership-row factoring that the deterministic-start reset chain (M5b)
  factors through: `E = comp P (rowFactor …)`. -/
theorem rawExchangeMembership_eq_of_membership (d e : Deck)
    (h : membership d = membership e) :
    rawExchangeMembership d = rawExchangeMembership e := by
  change (GSR.uniformDist exchangeChoice).map (choiceImage d) =
    (GSR.uniformDist exchangeChoice).map (choiceImage e)
  apply uniform_same_image (choiceImage d) (choiceImage e)
    (choiceImage_injective d) (choiceImage_injective e)
  intro s
  rw [choice_range d s, choice_range e s, h]

/-! ## 2. The ideal-reset smoothing chain (M5b)

The ideal full-round kernel `E ; U` (exchange then perfect-local reset) is
factored through the membership observation by M5a, and the initial local reset
kernel `P ; U` is **absorbed** by it — geometrically: resetting a deck to its
membership and then running `E ; U` leaves the same law as running `E ; U`
from the reset deck (`H ; L = L`).
-/

/-- The true membership kernel of the exchange: the post-exchange membership
  law after reading the initial deck through `membership` — the factor of
  `rawExchangeMembership` through the observation (M5a). -/
noncomputable def idealMembershipKernel : FiniteKernel Membership Membership :=
  rowFactor membership membership_surjective rawExchangeMembership

/-- The correct-order ideal full-round kernel: the A3 exchange-then-local-reset
  law `comp rawExchangeMembership localLift` — the kernel that
  `K1_swapFirst_eq_exchangeLift` identifies with the correct-order ideal round
  `comp (PAK swapLaw) (PAK rho99Ideal)`. -/
noncomputable def idealFullRound : FiniteKernel Deck Deck :=
  FiniteKernel.comp rawExchangeMembership localLift

/-- The initial local reset kernel `P ; U` (read membership, resample uniformly
  in the fiber) — the kernel that `k1_idealKernel_eq_membershipLift` identifies
  with `PAK rho99Ideal`. -/
noncomputable def idealLocalReset : FiniteKernel Deck Deck :=
  FiniteKernel.comp (FiniteKernel.deterministic membership) localLift

/-- `rawExchangeMembership` factors through the membership observation (the
  M5a row factoring). -/
theorem rawExchangeMembership_eq_comp_rowFactor :
    rawExchangeMembership =
      FiniteKernel.comp (FiniteKernel.deterministic membership) idealMembershipKernel :=
  rowFactor_comp membership membership_surjective rawExchangeMembership
    rawExchangeMembership_eq_of_membership

/-- **M5b.** The initial local reset is absorbed by the ideal full-round kernel:
  `H ; L = L`. Both sides are the same kernel after the M5a factorization and
  the reset identity `U ; P = identity` (`localLift_preserves_membership`). -/
theorem idealLocalReset_absorption :
    FiniteKernel.comp idealLocalReset idealFullRound = idealFullRound := by
  have hL : idealFullRound =
      FiniteKernel.comp (FiniteKernel.deterministic membership)
        (FiniteKernel.comp idealMembershipKernel localLift) := by
    have h1 : rawExchangeMembership =
        FiniteKernel.comp (FiniteKernel.deterministic membership) idealMembershipKernel :=
      rawExchangeMembership_eq_comp_rowFactor
    unfold idealFullRound
    rw [h1, FiniteKernel.comp_assoc]
  unfold idealLocalReset
  rw [hL]
  exact reset_absorption (FiniteKernel.deterministic membership) localLift
    idealMembershipKernel localLift_preserves_membership

/-- **M5b (run form).** Running the ideal full round from the reset start
  `H(d)` equals running from the deterministic start `pointMass d`, for any
  positive number of rounds — the kernel-algebra content of the ideal-reset
  smoothing (used to certify the preliminary-local-reset protocol). -/
theorem ideal_reset_run_eq_point (d : Deck) (t : Nat) :
    FiniteKernel.run idealFullRound (t+1) (idealLocalReset d) =
      FiniteKernel.run idealFullRound (t+1) (Dist.pointMass d) :=
  run_from_reset_eq_point idealLocalReset idealFullRound idealLocalReset_absorption d t

/-- The ideal full-round kernel is the physical correct-order ideal round:
  the `q3` ideal side of the Gate-6 certificate (`K1_swapFirst_eq_exchangeLift`). -/
theorem idealFullRound_eq_physicalIdealRound :
    idealFullRound =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
  unfold idealFullRound
  exact K1_swapFirst_eq_exchangeLift.symm

end Shufflemath
