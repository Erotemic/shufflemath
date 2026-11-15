module

public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderFiberCount
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderMembershipKernels

/-!
# Membership-fiber basics (F3 part (ii), step A1 groundwork)

Part (ii) of the F3 item 3 kernel equality needs the physical-exchange
distribution to be uniform over the membership fiber of each target count; the
intended proof is a group-action one (the `leftOrigSet`-stabilizer acts
transitively on each fiber — see `docs/agent_handoff.md`, Spec A).  This module
records the clean, standalone groundwork: every valid membership has marked
count `k` in the well-typed range `1 ≤ k ≤ 50` (so all the fiber part-counts in
the orbit construction are valid).

`Membership = {S : Finset (Fin 99) // S.card = 50}`,
`membershipCount m = (m.1 ∩ leftOrigSet).card`,
`leftOrigSet = {c : Fin 99 : c.val < 50}` (50 cards),
`rightOrigSet = {c : Fin 99 : c.val ≥ 50}` (49 cards, the complement
`univ \ leftOrigSet`).
-/

/-! `leftOrigSet` and `rightOrigSet` (its complement in the 99 cards) are
    disjoint and their union is all 99 cards. -/
theorem leftRightOrig_cover :
    leftOrigSet ∪ rightOrigSet = (Finset.univ : Finset (Fin 99)) := by
  rw [rightOrigSet_sdiff]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  -- (x ∈ L ∨ x ∉ L) ↔ True, by excluded middle
  exact ⟨fun _ => trivial, fun _ => Classical.em _⟩

theorem leftRightOrig_disjoint : Disjoint leftOrigSet rightOrigSet := by
  rw [Finset.disjoint_iff_inter_eq_empty, rightOrigSet_sdiff]
  exact Finset.inter_sdiff_self leftOrigSet (Finset.univ : Finset (Fin 99))

/-! **Every valid membership has at least one marked card.**  A membership is a
    50-subset of the 99 cards; it splits into `k` cards in the 50-card
    `leftOrigSet` and `50 - k` cards in the 49-card `rightOrigSet`.  Since only
    49 right-orig cards exist, `50 - k ≤ 49`, so `k ≥ 1`. -/
theorem membershipCount_pos (m : Membership) : 0 < membershipCount m := by
  set k := membershipCount m with hk
  set A := m.1 ∩ leftOrigSet with hA
  set B := m.1 ∩ rightOrigSet with hB
  -- |A| = k (A is the marked part).
  have hkA : k = A.card := by
    dsimp only [k, A, membershipCount]
  -- The two pieces A, B are disjoint and cover m.1.
  have hLR : (leftOrigSet ∩ rightOrigSet : Finset (Fin 99)) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp leftRightOrig_disjoint
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    simp only [hA, hB, Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_right_comm, hLR, Finset.inter_empty]
  have hcover : A ∪ B = m.1 := by
    rw [hA, hB, ← Finset.inter_union_distrib_left, leftRightOrig_cover, Finset.inter_univ]
  -- |m.1| = |A| + |B| (disjoint union) = 50.
  have hsum : A.card + B.card = m.1.card := by
    calc
      A.card + B.card = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = m.1.card := by rw [hcover]
  have h50 : m.1.card = 50 := m.2
  have h50s : A.card + B.card = 50 := by rw [hsum, h50]
  -- |B| ≤ 49 (B ⊆ rightOrigSet, 49 cards).
  have hBsub : B ⊆ rightOrigSet := by rw [hB]; exact Finset.inter_subset_right
  have hB49 : B.card ≤ 49 := by
    calc
      B.card ≤ rightOrigSet.card := Finset.card_le_card hBsub
      _ = 49 := rightOrigSet_card
  -- A.card = 50 - B.card with B.card ≤ 49 forces A.card ≥ 1, hence k ≥ 1.
  have hAcard_pos : 0 < A.card := by
    by_contra h
    have hA0 : A.card = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h)
    rw [hA0] at h50s
    have hB50 : B.card = 50 := by simpa [Nat.zero_add] using h50s
    have hBlt : B.card ≤ 49 := hB49
    rw [hB50] at hBlt
    have hlt : 49 < 50 := by decide
    exact (Nat.not_le.mpr hlt) hBlt
  exact (hkA.symm ▸ hAcard_pos)

/-! The marked count of a membership is at most 50 (there are only 50
    left-orig cards).  Pairs with `membershipCount_pos` to give the valid
    range `1 ≤ k ≤ 50`. -/
theorem membershipCount_le_50 (m : Membership) : membershipCount m ≤ 50 := by
  set A := m.1 ∩ leftOrigSet with hA
  rw [membershipCount, ← hA]
  have hsub : A ⊆ leftOrigSet := Finset.inter_subset_right
  calc
    A.card ≤ leftOrigSet.card := Finset.card_le_card hsub
    _ = 50 := leftOrigSet_card

end Shufflemath
end
