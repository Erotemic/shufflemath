module

public import Shufflemath.Gate6K1Bridges
public import Shufflemath.CommanderA3ExchangeCard
public import Shufflemath.FiniteDeck.SubsetExchange
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.InklingNov26

open CommanderPermutation CommanderMembershipKernels CommanderPhysicalExchange

/-! Proposed, not independently compiled. The ONLY new combinatorial fact
needed for deterministic-start smoothing: the membership row depends on the
initial membership, not on the initial internal order. Reuse the generic
ReachSet count and injectivity, not inverse selection witnesses. -/

def choiceImage (d : Deck) (c : exchangeChoice) : Membership :=
  newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)

theorem choiceImage_injective (d : Deck) : Function.Injective (choiceImage d) := by
  intro a b hab
  have hv : newLeftCards d a.1.1 a.2.1 = newLeftCards d b.1.1 b.2.1 :=
    congrArg Subtype.val hab
  obtain ⟨hL,hR⟩ := newLeftCards_injective d a.1.1 b.1.1 a.2.1 b.2.1 hv
  exact Prod.ext (Subtype.ext hL) (Subtype.ext hR)

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
    rw [Finset.card_sdiff, hL, hO]
  have h2 : ((choiceImage d c).1 \ (membership d).1).card = 25 := by
    rw [Finset.card_sdiff, Finset.inter_comm, hR, hO]
  unfold reachable25 FiniteDeck.ReachSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h1,h2⟩

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

theorem rawExchangeMembership_eq_of_membership (d e : Deck)
    (h : membership d = membership e) :
    rawExchangeMembership d = rawExchangeMembership e := by
  change (GSR.uniformDist exchangeChoice).map (choiceImage d) =
    (GSR.uniformDist exchangeChoice).map (choiceImage e)
  apply uniform_same_image (choiceImage d) (choiceImage e)
    (choiceImage_injective d) (choiceImage_injective e)
  intro s
  rw [choice_range d s, choice_range e s, h]

end Shufflemath.InklingNov26
