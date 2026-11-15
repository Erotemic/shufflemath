module

public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderFiberCount
public import Mathlib.Data.Fintype.EquivFin
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
the orbit construction are valid), and the atomic bijection the orbit
construction is built from.

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

/-! **Equi-cardinal finite subsets of a finite type are bijective.**  If two
    finite sets have the same cardinality, their subtypes are in bijection
    (noncomputable, via the `Fintype` instances and `Fintype.equivFinOfCardEq`).
    This is the atomic step in the orbit-transitivity construction (Spec A1). -/
noncomputable def equiCardFinsets_bij {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (h : s.card = t.card) : {x : α // x ∈ s} ≃ {x : α // x ∈ t} := by
  classical
  let n := s.card
  have cs : Fintype.card {x : α // x ∈ s} = n := by
    calc
      Fintype.card {x : α // x ∈ s} = Fintype.card {x : α // x ∈ (↑s : Set α)} := rfl
      _ = s.card := Fintype.card_ofFinset _ (fun _ => Iff.rfl)
      _ = n := rfl
  have ct : Fintype.card {x : α // x ∈ t} = n := by
    calc
      Fintype.card {x : α // x ∈ t} = Fintype.card {x : α // x ∈ (↑t : Set α)} := rfl
      _ = t.card := Fintype.card_ofFinset _ (fun _ => Iff.rfl)
      _ = s.card := by rw [← h]
      _ = n := rfl
  have es : {x : α // x ∈ s} ≃ Fin n := Fintype.equivFinOfCardEq cs
  have et : {x : α // x ∈ t} ≃ Fin n := Fintype.equivFinOfCardEq ct
  exact es.trans et.symm


/-! ## F3 item 4 (part ii): orbit transitivity of the membership fibers. -/

/-- A bijection between the orbit of a membership state under the two-pile
    exchange and itself: when the two 50-subsets `A`/`A'` (the marked-card sets
    of two membership states) have equal cardinality, there is a permutation of
    the 99-card universe carrying `A` to `A'` (and its complement to its
    complement).  This is the algebraic skeleton of the orbit-transitivity claim:
    it exhibits an element of the deck permutation group sending one fiber point
    to another.  Built `Fintype`-free (no `List.mem_bind`/`toMultiset`): a
    `Fin 99`-sized `Finset` is bridged through `equiCardFinsets_bij`.  The map
    sends `A → A'` by the equi-cardinal bijection `eAB` and the complement
    `C = univ \ A → D = univ \ A'` by `eCD`, and is bijective. -/
noncomputable def finsetType_perm {s : Type*} [Fintype s] [DecidableEq s]
    (A A' : Finset s) (h : A.card = A'.card) : s ≃ s := by
  classical
  set C := (Finset.univ : Finset s) \ A with hC
  set D := (Finset.univ : Finset s) \ A' with hD
  have hc : C.card = (Finset.univ : Finset s).card - A.card := by
    rw [hC, Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _)]
  have hd : D.card = (Finset.univ : Finset s).card - A'.card := by
    rw [hD, Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _)]
  have hCA : C.card = D.card := by rw [hc, hd, h]
  have eAB : {x : s // x ∈ A} ≃ {x : s // x ∈ A'} := equiCardFinsets_bij h
  have eCD : {x : s // x ∈ C} ≃ {x : s // x ∈ D} := equiCardFinsets_bij hCA
  let hmemC (x : s) (hx : x ∉ A) : x ∈ C := by
    rw [hC, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ x, hx⟩
  let f (x : s) : s :=
      if hx : x ∈ A then (eAB ⟨x, hx⟩).val else (eCD ⟨x, hmemC x hx⟩).val
  refine Equiv.ofBijective f ?_
  constructor
  · -- injective: unfold f then split on both ites
    intro x y hxy
    dsimp only [f] at hxy
    split_ifs at hxy <;> rename_i hx hy
    · -- hx : x ∈ A, hy : y ∈ A
      simpa using (eAB.injective (Subtype.ext hxy))
    · -- hx : x ∈ A, hy : ¬y ∈ A
      have hv : (eAB ⟨x, hx⟩).val = (eCD ⟨y, hmemC y hy⟩).val := by simpa only [f] using hxy
      have hmem : (eAB ⟨x, hx⟩).val ∈ A' ∩ D := by
        rw [Finset.mem_inter]
        exact ⟨(eAB ⟨x, hx⟩).2, by rw [hv]; exact (eCD ⟨y, hmemC y hy⟩).2⟩
      have hdisj : Disjoint A' D := by
        rw [Finset.disjoint_iff_inter_eq_empty, hD]
        exact Finset.inter_sdiff_self A' (Finset.univ : Finset s)
      exact (False.elim ((Finset.not_disjoint_iff_nonempty_inter.mpr ⟨(eAB ⟨x, hx⟩).val, hmem⟩) hdisj))
    · -- hx : ¬x ∈ A, hy : y ∈ A
      have hv : (eCD ⟨x, hmemC x hx⟩).val = (eAB ⟨y, hy⟩).val := by simpa only [f] using hxy
      have hmem : (eCD ⟨x, hmemC x hx⟩).val ∈ A' ∩ D := by
        rw [Finset.mem_inter]
        exact ⟨by rw [hv]; exact (eAB ⟨y, hy⟩).2, (eCD ⟨x, hmemC x hx⟩).2⟩
      have hdisj : Disjoint A' D := by
        rw [Finset.disjoint_iff_inter_eq_empty, hD]
        exact Finset.inter_sdiff_self A' (Finset.univ : Finset s)
      exact (False.elim ((Finset.not_disjoint_iff_nonempty_inter.mpr ⟨(eCD ⟨x, hmemC x hx⟩).val, hmem⟩) hdisj))
    · -- hx : ¬x ∈ A, hy : ¬y ∈ A
      simpa using (eCD.injective (Subtype.ext hxy))
  -- surjective: every z ∈ univ lies in A' (lift through eAB) or in D (through eCD)
  · intro z
    by_cases hzA' : z ∈ A'
    · -- z ∈ A'
      let pre : {x : s // x ∈ A} := eAB.symm ⟨z, hzA'⟩
      use pre.val
      dsimp only [f]
      split_ifs with hx2
      · -- hx2 : pre.val ∈ A, the then-branch of f
        have hsub : ⟨pre.val, hx2⟩ = pre := Subtype.ext (by rfl)
        rw [hsub]
        dsimp only [pre]
        rw [Equiv.apply_symm_apply]
      · -- hx2 : ¬pre.val ∈ A, contradicts pre.2 (pre : {x // x ∈ A})
        exfalso
        exact hx2 pre.2
    · -- z ∉ A'
      have hzD : z ∈ D := by rw [hD, Finset.mem_sdiff]; exact ⟨Finset.mem_univ z, hzA'⟩
      let pre : {x : s // x ∈ C} := eCD.symm ⟨z, hzD⟩
      use pre.val
      dsimp only [f]
      split_ifs with hx2
      · -- hx2 : pre.val ∈ A contradicts pre.2 (pre.val ∈ C = univ \ A)
        exfalso
        have hmem' : pre.val ∈ (Finset.univ : Finset s) \ A := hC ▸ pre.2
        exact (Finset.mem_sdiff.mp hmem').2 hx2
      · -- hx2 : ¬pre.val ∈ A, the else-branch of f
        have hsub : ⟨pre.val, hmemC pre.val hx2⟩ = pre := Subtype.ext (by rfl)
        rw [hsub]
        dsimp only [pre]
        rw [Equiv.apply_symm_apply]

end Shufflemath
end
