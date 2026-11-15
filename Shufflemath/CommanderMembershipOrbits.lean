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


/-! ## Spec A1: the marked-card fiber is a single orbit under the pile-preserving deck group. -/

/-- The marked / unmarked split of a membership's 50-subset inside the two original piles. -/
abbrev partA (m : Membership) := m.1 ∩ leftOrigSet
abbrev partB (m : Membership) := m.1 ∩ rightOrigSet
abbrev partC (m : Membership) := leftOrigSet \ partA m
abbrev partD (m : Membership) := rightOrigSet \ partB m

/-- `m.1` (a 50-subset of the 99-card universe) decomposes as the disjoint union of its
    left-pile part and its right-pile part, so its cardinality splits additively. -/
theorem m1_decomp (m : Membership) :
    (m.1).card = (m.1 ∩ leftOrigSet).card + (m.1 ∩ rightOrigSet).card := by
  have hLRE : leftOrigSet ∩ rightOrigSet = ∅ := by
    rw [← Finset.disjoint_iff_inter_eq_empty]
    exact leftRightOrig_disjoint
  have hI : (m.1 ∩ leftOrigSet) ∩ (m.1 ∩ rightOrigSet) = ∅ := by
    apply Finset.ext
    intro c
    repeat rw [Finset.mem_inter]
    constructor
    · intro h
      rw [← hLRE, Finset.mem_inter]
      exact ⟨h.1.2, h.2.2⟩
    · intro hc
      cases hc
  have hU : (m.1 ∩ leftOrigSet) ∪ (m.1 ∩ rightOrigSet) = m.1 := by
    rw [← Finset.inter_union_distrib_left, leftRightOrig_cover, Finset.inter_univ]
  have hUcard : ((m.1 ∩ leftOrigSet) ∪ (m.1 ∩ rightOrigSet)).card = (m.1).card :=
    congrArg (fun s : Finset (Fin 99) => s.card) hU
  calc
    (m.1).card = ((m.1 ∩ leftOrigSet) ∪ (m.1 ∩ rightOrigSet)).card := hUcard.symm
    _ = (m.1 ∩ leftOrigSet).card + (m.1 ∩ rightOrigSet).card -
        ((m.1 ∩ leftOrigSet) ∩ (m.1 ∩ rightOrigSet)).card :=
      Finset.card_union (m.1 ∩ leftOrigSet) (m.1 ∩ rightOrigSet)
    _ = (m.1 ∩ leftOrigSet).card + (m.1 ∩ rightOrigSet).card := by
      rw [hI, Finset.card_empty]
      omega

/-- A 50-subset `S` splits as `(S ∩ left).card + (S ∩ right).card = 50`. -/
theorem m1_sum50 (m : Membership) :
    (m.1 ∩ leftOrigSet).card + (m.1 ∩ rightOrigSet).card = 50 :=
  (m1_decomp m).symm.trans m.2

/-- `S ∩ left` has at most 50 elements. -/
theorem m1_left_le (m : Membership) : (m.1 ∩ leftOrigSet).card ≤ 50 := by
  have hcard : (m.1 ∩ leftOrigSet).card ≤ (leftOrigSet).card :=
    Finset.card_le_card (Finset.inter_subset_right)
  rw [leftOrigSet_card] at hcard
  exact hcard

/-- **Spec A1 equi-cardinality (marked, left pile).**  `partA m` and `partA m'` have the
    same cardinality (both `= membershipCount`). -/
theorem partCard_eqA (m m' : Membership) (h : membershipCount m = membershipCount m') :
    (partA m).card = (partA m').card := by
  simpa [partA, membershipCount] using h

/-- **Spec A1 equi-cardinality (marked, right pile).**  `partB m` and `partB m'` have the
    same cardinality (both `= 50 - membershipCount`). -/
theorem partCard_eqB (m m' : Membership) (h : membershipCount m = membershipCount m') :
    (partB m).card = (partB m').card := by
  dsimp only [partB]
  have hb1 : (m.1 ∩ rightOrigSet).card = 50 - (m.1 ∩ leftOrigSet).card := by
    have hsum := m1_sum50 m
    have hle := m1_left_le m
    omega
  have hb2 : (m'.1 ∩ rightOrigSet).card = 50 - (m'.1 ∩ leftOrigSet).card := by
    have hsum := m1_sum50 m'
    have hle := m1_left_le m'
    omega
  rw [hb1, hb2]
  apply congrArg (fun x => 50 - x)
  simpa [membershipCount] using h

/-- **Spec A1 equi-cardinality (unmarked, left pile).**  `partC m` and `partC m'` have the
    same cardinality (both `= 50 - membershipCount`). -/
theorem partCard_eqC (m m' : Membership) (h : membershipCount m = membershipCount m') :
    (partC m).card = (partC m').card := by
  dsimp only [partC, partA]
  have hc1 : (leftOrigSet \ (m.1 ∩ leftOrigSet)).card = 50 - (m.1 ∩ leftOrigSet).card := by
    rw [Finset.card_sdiff_of_subset (Finset.inter_subset_right), leftOrigSet_card]
  have hc2 : (leftOrigSet \ (m'.1 ∩ leftOrigSet)).card = 50 - (m'.1 ∩ leftOrigSet).card := by
    rw [Finset.card_sdiff_of_subset (Finset.inter_subset_right), leftOrigSet_card]
  rw [hc1, hc2]
  apply congrArg (fun x => 50 - x)
  simpa [membershipCount] using h

/-- **Spec A1 equi-cardinality (unmarked, right pile).**  `partD m` and `partD m'` have the
    same cardinality (both `= membershipCount - 1`). -/
theorem partCard_eqD (m m' : Membership) (h : membershipCount m = membershipCount m') :
    (partD m).card = (partD m').card := by
  dsimp only [partD, partB]
  have hd1 : (rightOrigSet \ (m.1 ∩ rightOrigSet)).card = 49 - (m.1 ∩ rightOrigSet).card := by
    rw [Finset.card_sdiff_of_subset (Finset.inter_subset_right), rightOrigSet_card]
  have hd2 : (rightOrigSet \ (m'.1 ∩ rightOrigSet)).card = 49 - (m'.1 ∩ rightOrigSet).card := by
    rw [Finset.card_sdiff_of_subset (Finset.inter_subset_right), rightOrigSet_card]
  have hb1 : (m.1 ∩ rightOrigSet).card = 50 - (m.1 ∩ leftOrigSet).card := by
    have hsum := m1_sum50 m
    have hle := m1_left_le m
    omega
  have hb2 : (m'.1 ∩ rightOrigSet).card = 50 - (m'.1 ∩ leftOrigSet).card := by
    have hsum := m1_sum50 m'
    have hle := m1_left_le m'
    omega
  rw [hd1, hd2, hb1, hb2]
  apply congrArg (fun x => 49 - (50 - x))
  simpa [membershipCount] using h



/-! ## Spec A1 groundwork: the marked / unmarked pieces cover each original pile. -/

/-- The left pile splits as `marked-in-left ∪ unmarked-in-left` (the two left pieces). -/
theorem leftCoverPieces (m : Membership) : leftOrigSet = partA m ∪ partC m := by
  ext c
  dsimp only [partA, partC]
  rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · intro hcl
    by_cases hcm1 : c ∈ m.1
    · left; exact ⟨hcm1, hcl⟩
    · right; exact ⟨hcl, fun hc => hcm1 (Finset.mem_inter.mp hc).1⟩
  · intro h
    rcases h with h1 | h2
    · exact h1.2
    · exact h2.1

/-- The right pile splits as `marked-in-right ∪ unmarked-in-right` (the two right pieces). -/
theorem rightCoverPieces (m : Membership) : rightOrigSet = partB m ∪ partD m := by
  ext c
  dsimp only [partB, partD]
  rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · intro hcr
    by_cases hcm1 : c ∈ m.1
    · left; exact ⟨hcm1, hcr⟩
    · right; exact ⟨hcr, fun hc => hcm1 (Finset.mem_inter.mp hc).1⟩
  · intro h
    rcases h with h1 | h2
    · exact h1.2
    · exact h2.1



/-- The four piece-equivs transporting the four pieces of `m` to the corresponding pieces
    of `m'` (each a bijection between equal-cardinality subtypes). -/
noncomputable def orbitEquivA (m m' : Membership) (h : membershipCount m = membershipCount m') :
    {c : Fin 99 // c ∈ partA m} ≃ {c : Fin 99 // c ∈ partA m'} :=
  equiCardFinsets_bij (partCard_eqA m m' h)
noncomputable def orbitEquivB (m m' : Membership) (h : membershipCount m = membershipCount m') :
    {c : Fin 99 // c ∈ partB m} ≃ {c : Fin 99 // c ∈ partB m'} :=
  equiCardFinsets_bij (partCard_eqB m m' h)
noncomputable def orbitEquivC (m m' : Membership) (h : membershipCount m = membershipCount m') :
    {c : Fin 99 // c ∈ partC m} ≃ {c : Fin 99 // c ∈ partC m'} :=
  equiCardFinsets_bij (partCard_eqC m m' h)
noncomputable def orbitEquivD (m m' : Membership) (h : membershipCount m = membershipCount m') :
    {c : Fin 99 // c ∈ partD m} ≃ {c : Fin 99 // c ∈ partD m'} :=
  equiCardFinsets_bij (partCard_eqD m m' h)

/-- A card not in the left pieces (A, C) lies in the right pile. -/
theorem notLeftPieces_impliesRight (m : Membership) (c : Fin 99)
    (hA : c ∉ partA m) (hC : c ∉ partC m) : c ∈ rightOrigSet := by
  have hnotleft : c ∉ leftOrigSet := by
    have hnl : c ∉ (partA m ∪ partC m) := by
      rw [Finset.mem_union]
      exact not_or_intro hA hC
    rwa [← leftCoverPieces] at hnl
  by_contra hnr
  have hcover : c ∈ leftOrigSet ∪ rightOrigSet := by
    rw [leftRightOrig_cover]
    exact Finset.mem_univ c
  cases (Finset.mem_union.mp hcover) with
  | inl hcl => exact hnotleft hcl
  | inr hcr => exact hnr hcr

/-- The piecewise deck permutation: it transports each of the four pieces of `m` to the
    corresponding piece of `m'`.  The four pieces partition the 99-card universe, so this is
    a well-defined function on all cards. -/
noncomputable def orbitMap (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) : Fin 99 := by
  by_cases hA : c ∈ partA m
  · exact ((orbitEquivA m m' h) ⟨c, hA⟩).val
  by_cases hB : c ∈ partB m
  · exact ((orbitEquivB m m' h) ⟨c, hB⟩).val
  by_cases hC : c ∈ partC m
  · exact ((orbitEquivC m m' h) ⟨c, hC⟩).val
  · -- not in parts A, B, C, hence in part D = right \ (m.1 ∩ right)
    exact ((orbitEquivD m m' h) ⟨c, by
      dsimp only [partD, partB]
      rw [Finset.mem_sdiff]
      constructor
      · exact notLeftPieces_impliesRight m c hA hC
      · -- partB m = m.1 ∩ right, already excluded
        intro hc; exact hB hc
    ⟩).val



/-- `c` in part A (marked, left pile): `orbitMap` is exactly the A-equiv. -/
theorem orbitMap_apply_partA (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ partA m) :
    orbitMap m m' h c = ((orbitEquivA m m' h) ⟨c, hc⟩).val := by
  dsimp only [orbitMap]
  split_ifs
  · apply congrArg (fun x : {z : Fin 99 // z ∈ partA m} => ((orbitEquivA m m' h) x).val)
    apply Subtype.ext
    rfl

/-- part B (marked, right) is disjoint from part A (marked, left). -/
theorem partB_not_partA (m : Membership) (c : Fin 99) (hc : c ∈ partB m) : c ∉ partA m := by
  have hcR : c ∈ rightOrigSet := by rw [partB] at hc; exact (Finset.mem_inter.mp hc).2
  intro h
  have hL : c ∈ leftOrigSet := by rw [partA] at h; exact (Finset.mem_inter.mp h).2
  have hI : c ∈ leftOrigSet ∩ rightOrigSet := Finset.mem_inter.mpr ⟨hL, hcR⟩
  have hIe : leftOrigSet ∩ rightOrigSet = ∅ := Finset.disjoint_iff_inter_eq_empty.mp leftRightOrig_disjoint
  rw [hIe] at hI
  cases hI

/-- `c` in part B (marked, right pile): `orbitMap` is the B-equiv. -/
theorem orbitMap_apply_partB (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ partB m) :
    orbitMap m m' h c = ((orbitEquivB m m' h) ⟨c, hc⟩).val := by
  have hcA : c ∉ partA m := partB_not_partA m c hc
  dsimp only [orbitMap]
  split_ifs
  · apply congrArg (fun x : {z : Fin 99 // z ∈ partB m} => ((orbitEquivB m m' h) x).val)
    apply Subtype.ext
    rfl

/-- part C (left pile) is disjoint from part A. -/
theorem partC_not_partA (m : Membership) (c : Fin 99) (hc : c ∈ partC m) : c ∉ partA m := by
  rw [partC] at hc
  exact (Finset.mem_sdiff.mp hc).2

/-- part C (left pile) is disjoint from part B (right pile). -/
theorem partC_not_partB (m : Membership) (c : Fin 99) (hc : c ∈ partC m) : c ∉ partB m := by
  have hcL : c ∈ leftOrigSet := by rw [partC] at hc; exact (Finset.mem_sdiff.mp hc).1
  intro h
  have hR : c ∈ rightOrigSet := by rw [partB] at h; exact (Finset.mem_inter.mp h).2
  have hI : c ∈ leftOrigSet ∩ rightOrigSet := Finset.mem_inter.mpr ⟨hcL, hR⟩
  have hIe : leftOrigSet ∩ rightOrigSet = ∅ := Finset.disjoint_iff_inter_eq_empty.mp leftRightOrig_disjoint
  rw [hIe] at hI
  cases hI

/-- `c` in part C (unmarked, left pile): `orbitMap` is the C-equiv. -/
theorem orbitMap_apply_partC (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ partC m) :
    orbitMap m m' h c = ((orbitEquivC m m' h) ⟨c, hc⟩).val := by
  have hcA : c ∉ partA m := partC_not_partA m c hc
  have hcB : c ∉ partB m := partC_not_partB m c hc
  dsimp only [orbitMap]
  split_ifs
  · apply congrArg (fun x : {z : Fin 99 // z ∈ partC m} => ((orbitEquivC m m' h) x).val)
    apply Subtype.ext
    rfl

/-- part D (right pile) is disjoint from part A (left pile). -/
theorem partD_not_partA (m : Membership) (c : Fin 99) (hc : c ∈ partD m) : c ∉ partA m := by
  have hcR : c ∈ rightOrigSet := by rw [partD] at hc; exact (Finset.mem_sdiff.mp hc).1
  intro h
  have hL : c ∈ leftOrigSet := by rw [partA] at h; exact (Finset.mem_inter.mp h).2
  have hI : c ∈ leftOrigSet ∩ rightOrigSet := Finset.mem_inter.mpr ⟨hL, hcR⟩
  have hIe : leftOrigSet ∩ rightOrigSet = ∅ := Finset.disjoint_iff_inter_eq_empty.mp leftRightOrig_disjoint
  rw [hIe] at hI
  cases hI

/-- part D (right pile) is disjoint from part B. -/
theorem partD_not_partB (m : Membership) (c : Fin 99) (hc : c ∈ partD m) : c ∉ partB m := by
  rw [partD] at hc
  exact (Finset.mem_sdiff.mp hc).2

/-- part D (right pile) is disjoint from part C (left pile). -/
theorem partD_not_partC (m : Membership) (c : Fin 99) (hc : c ∈ partD m) : c ∉ partC m := by
  have hcR : c ∈ rightOrigSet := by rw [partD] at hc; exact (Finset.mem_sdiff.mp hc).1
  intro h
  have hL : c ∈ leftOrigSet := by rw [partC] at h; exact (Finset.mem_sdiff.mp h).1
  have hI : c ∈ leftOrigSet ∩ rightOrigSet := Finset.mem_inter.mpr ⟨hL, hcR⟩
  have hIe : leftOrigSet ∩ rightOrigSet = ∅ := Finset.disjoint_iff_inter_eq_empty.mp leftRightOrig_disjoint
  rw [hIe] at hI
  cases hI

/-- `c` in part D (unmarked, right pile): `orbitMap` is the D-equiv. -/
theorem orbitMap_apply_partD (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ partD m) :
    orbitMap m m' h c = ((orbitEquivD m m' h) ⟨c, hc⟩).val := by
  have hcA : c ∉ partA m := partD_not_partA m c hc
  have hcB : c ∉ partB m := partD_not_partB m c hc
  have hcC : c ∉ partC m := partD_not_partC m c hc
  dsimp only [orbitMap]
  split_ifs
  · apply congrArg (fun x : {z : Fin 99 // z ∈ partD m} => ((orbitEquivD m m' h) x).val)
    apply Subtype.ext
    rfl



/-- The four orbit pieces of a membership cover the whole deck. -/
theorem piecesCover (m : Membership) :
    partA m ∪ partB m ∪ partC m ∪ partD m = Finset.univ := by
  ext c
  constructor
  · -- c in the four-piece union is trivially in the whole deck
    intro _
    simp only [Finset.mem_univ]
  · -- every card is in some piece
    intro _
    simp only [Finset.mem_union]
    -- goal: (((c ∈ partA ∨ c ∈ partB) ∨ c ∈ partC) ∨ c ∈ partD)
    have hcover : c ∈ leftOrigSet ∪ rightOrigSet := by
      rw [leftRightOrig_cover]
      simp only [Finset.mem_univ]
    simp only [Finset.mem_union] at hcover
    rcases hcover with hlc | hrc
    · rw [leftCoverPieces m] at hlc
      simp only [Finset.mem_union] at hlc
      rcases hlc with hcA | hcC
      · exact Or.inl (Or.inl (Or.inl hcA))
      · exact Or.inl (Or.inr hcC)
    · rw [rightCoverPieces m] at hrc
      simp only [Finset.mem_union] at hrc
      rcases hrc with hcB | hcD
      · exact Or.inl (Or.inl (Or.inr hcB))
      · exact Or.inr hcD



/-- The marked set `m.1` is exactly part A (marked left) plus part B (marked right). -/
theorem markedPieces_cover (m : Membership) : partA m ∪ partB m = m.1 := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · intro h
    cases h with
    | inl hA => exact hA.1
    | inr hB => exact hB.1
  · intro hx
    have hLorR : x ∈ leftOrigSet ∨ x ∈ rightOrigSet := by
      have hLU : x ∈ leftOrigSet ∪ rightOrigSet := by
        rw [leftRightOrig_cover]
        simp only [Finset.mem_univ]
      rw [Finset.mem_union] at hLU
      exact hLU
    cases hLorR with
    | inl hL => left; exact ⟨hx, hL⟩
    | inr hR => right; exact ⟨hx, hR⟩

/-- `orbitMap` sends the left pile into the left pile. -/
theorem orbitMap_preservesLeft (m m' : Membership) (h : membershipCount m = membershipCount m')
    (a : Fin 99) (ha : a ∈ leftOrigSet) : orbitMap m m' h a ∈ leftOrigSet := by
  rw [leftCoverPieces m] at ha
  simp only [Finset.mem_union] at ha
  rcases ha with haA | haC
  · rw [orbitMap_apply_partA m m' h a haA]
    exact (Finset.mem_inter.mp ((orbitEquivA m m' h) ⟨a, haA⟩).2).2
  · rw [orbitMap_apply_partC m m' h a haC]
    exact (Finset.mem_sdiff.mp ((orbitEquivC m m' h) ⟨a, haC⟩).2).1

/-- `orbitMap` sends the marked set `m.1` into `m'.1`. -/
theorem orbitMap_mapsM1 (m m' : Membership) (h : membershipCount m = membershipCount m')
    (a : Fin 99) (ha : a ∈ m.1) : orbitMap m m' h a ∈ m'.1 := by
  rw [← markedPieces_cover m] at ha
  simp only [Finset.mem_union] at ha
  rcases ha with haA | haB
  · rw [orbitMap_apply_partA m m' h a haA]
    exact (Finset.mem_inter.mp ((orbitEquivA m m' h) ⟨a, haA⟩).2).1
  · rw [orbitMap_apply_partB m m' h a haB]
    exact (Finset.mem_inter.mp ((orbitEquivB m m' h) ⟨a, haB⟩).2).1



/-- Every card of the left pile of `m'` is hit by `orbitMap` from the left pile of `m`. -/
theorem left_subset_fimageLeft (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ leftOrigSet) : c ∈ (orbitMap m m' h) '' leftOrigSet := by
  rw [leftCoverPieces m'] at hc
  simp only [Finset.mem_union, Finset.mem_image] at hc ⊢
  rcases hc with hcA | hcC
  · let yc : {x : Fin 99 // x ∈ partA m'} := Subtype.mk c hcA
    rcases (orbitEquivA m m' h).surjective yc with ⟨a, hae⟩
    refine ⟨a.1, ?_, ?_⟩
    · exact (Finset.mem_inter.mp a.2).2
    · have hsub : (⟨a.1, a.2⟩ : {z : Fin 99 // z ∈ partA m}) = a := Subtype.ext rfl
      rw [orbitMap_apply_partA m m' h a.1 a.2, hsub, hae]
  · let yc : {x : Fin 99 // x ∈ partC m'} := Subtype.mk c hcC
    rcases (orbitEquivC m m' h).surjective yc with ⟨a, hae⟩
    refine ⟨a.1, ?_, ?_⟩
    · exact (Finset.mem_sdiff.mp a.2).1
    · have hsub : (⟨a.1, a.2⟩ : {z : Fin 99 // z ∈ partC m}) = a := Subtype.ext rfl
      rw [orbitMap_apply_partC m m' h a.1 a.2, hsub, hae]

/-- Every marked card of `m'` is hit by `orbitMap` from a marked card of `m`. -/
theorem m1p_subset_fimageM1 (m m' : Membership) (h : membershipCount m = membershipCount m')
    (c : Fin 99) (hc : c ∈ m'.1) : c ∈ (orbitMap m m' h) '' m.1 := by
  rw [← markedPieces_cover m'] at hc
  simp only [Finset.mem_union, Finset.mem_image] at hc ⊢
  rcases hc with hcA | hcB
  · let yc : {x : Fin 99 // x ∈ partA m'} := Subtype.mk c hcA
    rcases (orbitEquivA m m' h).surjective yc with ⟨a, hae⟩
    refine ⟨a.1, ?_, ?_⟩
    · exact (Finset.mem_inter.mp a.2).1
    · have hsub : (⟨a.1, a.2⟩ : {z : Fin 99 // z ∈ partA m}) = a := Subtype.ext rfl
      rw [orbitMap_apply_partA m m' h a.1 a.2, hsub, hae]
  · let yc : {x : Fin 99 // x ∈ partB m'} := Subtype.mk c hcB
    rcases (orbitEquivB m m' h).surjective yc with ⟨a, hae⟩
    refine ⟨a.1, ?_, ?_⟩
    · exact (Finset.mem_inter.mp a.2).1
    · have hsub : (⟨a.1, a.2⟩ : {z : Fin 99 // z ∈ partB m}) = a := Subtype.ext rfl
      rw [orbitMap_apply_partB m m' h a.1 a.2, hsub, hae]

end Shufflemath
end
