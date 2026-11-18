
/-- A subset `S ⊆ U` splits uniquely into its `M`-part `S ∩ M` and its
    `M`-complement `S \ M`: the two pieces are disjoint, recombine to `S`, and
    the `M`-complement lies in `U \ M` (when `M ⊆ U`). This is the `U`-
    generalization of the marked/unmarked split behind `countFiberMemb`. -/
theorem sdiff_inter_split {α : Type*} [DecidableEq α] (U M S : Finset α)
    (hM : M ⊆ U) (hS : S ⊆ U) :
    (S ∩ M) ∪ (S \ M) = S ∧ Disjoint (S ∩ M) (S \ M) ∧ S \ M ⊆ U \ M := by
  refine ⟨?_, ?_, ?_⟩
  · -- the two pieces recombine to `S`
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · -- the two pieces are disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.ext
    intro z
    apply Iff.intro
    · intro hz
      have hzM : z ∈ M := (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2
      have hznotM : z ∉ M := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz).2).2
      contradiction
    · intro hz
      exact False.elim (Finset.notMem_empty z hz)
  · -- the `M`-complement stays inside `U \ M`
    rintro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hz, hznotM⟩
    exact Finset.mem_sdiff.mpr ⟨hS hz, hznotM⟩

/- The counting kernel (F3 A3 pile counts): the `k`-subsets of `U` with exactly
   `a` marked elements (`∩ M`) biject with pairs `(A, B)` where `A` is an
   `a`-subset of `M` and `B` is a `(k - a)`-subset of `U \ M` — the disjoint
   union `S = (S ∩ M) ∪ (S \ M)` recovers both halves, and intersecting a
   recombined `A ∪ B` with the two parts recovers `A` and `B`. This generalizes
   the `Membership`-fiber bijection `countFiberMemb_equiv` to an arbitrary
   `(U, M)` with `M ⊆ U`. -/
def powersetCard_markedContent_equiv {α : Type*} [DecidableEq α]
    (U M : Finset α) (hM : M ⊆ U) (k a : Nat) (ha : a ≤ k) :
    {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} ≃
      {p : Finset α × Finset α //
        p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} := by
  let X := U \ M
  have hXsub : X ⊆ U := Finset.sdiff_subset
  have hMdisjX : M ∩ X = ∅ := by
    ext z
    simp only [X, Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty]
    tauto
  let f : {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} →
          {p : Finset α × Finset α //
            p.1 ∈ M.powersetCard a ∧ p.2 ∈ X.powersetCard (k - a)} :=
    fun S =>
      let sF := S.1
      have hSsub : sF ⊆ U := S.2.1
      have hScard : sF.card = k := S.2.2.1
      have hSmark : (sF ∩ M).card = a := S.2.2.2
      have hAsub : sF ∩ M ⊆ M := Finset.inter_subset_right
      have hBsub : sF \ M ⊆ X := (sdiff_inter_split U M sF hM hSsub).2.2
      have hBcard : (sF \ M).card = k - a := by
        rw [Finset.card_sdiff, Finset.inter_comm, hScard, hSmark]
      ⟨⟨sF ∩ M, sF \ M⟩,
        ⟨Finset.mem_powersetCard.mpr ⟨hAsub, hSmark⟩,
         Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩⟩⟩
  let g : {p : Finset α × Finset α //
            p.1 ∈ M.powersetCard a ∧ p.2 ∈ X.powersetCard (k - a)} →
          {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} :=
    fun p =>
      let A := p.1.1
      let B := p.1.2
      have hA : A ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hAcard : A.card = a := (Finset.mem_powersetCard.mp p.2.1).2
      have hB : B ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      have hBcard : B.card = k - a := (Finset.mem_powersetCard.mp p.2.2).2
      have hABsub : A ∪ B ⊆ U := by
        rintro z hz
        simp only [Finset.mem_union] at hz
        rcases hz with hz | hz
        · exact hM (hA hz)
        · exact hXsub (hB hz)
      have hDisAB : Disjoint A B := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.ext
        intro z
        apply Iff.intro
        · intro hz
          have hzM : z ∈ M := hA (Finset.mem_inter.mp hz).1
          have hzX : z ∈ X := hB (Finset.mem_inter.mp hz).2
          have hInX : z ∈ M ∩ X := Finset.mem_inter.mpr ⟨hzM, hzX⟩
          rw [hMdisjX] at hInX
          exact False.elim (Finset.notMem_empty z hInX)
        · intro hz
          exact False.elim (Finset.notMem_empty z hz)
      have hABcard : (A ∪ B).card = k := by
        have hEmpty : A ∩ B = ∅ := (Finset.disjoint_iff_inter_eq_empty A B).mpr hDisAB
        have hInter : (A ∩ B).card = 0 := by rw [hEmpty, Finset.card_empty]
        have hUnion : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
          Finset.card_union_add_card_inter A B
        rw [hInter, Nat.add_zero, hAcard, hBcard] at hUnion
        omega
      have hAM : (A ∪ B) ∩ M = A := (union_inter_parts M X A B hA hB hMdisjX).1
      have hAmark : ((A ∪ B) ∩ M).card = a := by rw [hAM, hAcard]
      ⟨A ∪ B, ⟨hABsub, hABcard, hAmark⟩⟩
  refine Equiv.mk f g ?_ ?_
  · -- `g ∘ f = id`: the split pieces recombine to `S`.
    intro S
    dsimp only [f, g]
    apply Subtype.ext
    exact (sdiff_inter_split U M S.1 hM S.2.1).1
  · -- `f ∘ g = id`: the recombined `A ∪ B` re-splits to `(A, B)`.
    intro p
    dsimp only [f, g]
    apply Subtype.ext
    apply Prod.ext
    · -- `(A ∪ B) ∩ M = A`
      have hA : p.1.1 ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hB : p.1.2 ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      exact (union_inter_parts M X p.1.1 p.1.2 hA hB hMdisjX).1
    · -- `(A ∪ B) \ M = B`
      have hA : p.1.1 ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hB : p.1.2 ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      have hSdiff : (p.1.1 ∪ p.1.2) \ M = p.1.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        apply Iff.intro
        · intro h
          have hznotM : z ∉ M := h.2
          rcases h.1 with hzA | hzB
          · have hzM : z ∈ M := hA hzA
            contradiction
          · exact hzB
        · intro hzB
          exact ⟨Or.inr hzB, (Finset.mem_sdiff.mp (hB hzB)).2⟩
      rw [hSdiff]
      rfl

/- The F3 A3 counting kernel: the number of `k`-subsets of `U` containing
   exactly `a` elements of the marked part `M ⊆ U` is the hypergeometric number
   `choose(M.card, a) · choose(U.card - M.card, k - a)`. This is the reusable
   foundation for the 25/25 exchange pile counts in the Commander A3 discharge. -/
theorem powersetCard_markedContent {α : Type*} [Fintype α] [DecidableEq α]
    (U M : Finset α) (hM : M ⊆ U) (k a : Nat) (ha : a ≤ k) :
    ((U.powersetCard k).filter (fun S => (S ∩ M).card = a)).card =
      Nat.choose M.card a * Nat.choose (U.card - M.card) (k - a) := by
  have hBridge :
      ((U.powersetCard k).filter (fun S => (S ∩ M).card = a)).card =
        Fintype.card {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} :=
    (Fintype.card_of_subtype
        (p := fun S => S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a)
        (s := (U.powersetCard k).filter (fun S => (S ∩ M).card = a))
        (H := fun z => by
          simp only [Finset.mem_filter, Finset.mem_powersetCard, and_assoc]
          tauto)).symm
  have hEquiv :
      Fintype.card {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} =
        Fintype.card {p : Finset α × Finset α //
          p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} :=
    Fintype.card_congr (powersetCard_markedContent_equiv U M hM k a ha)
  have hProd :
      Fintype.card {p : Finset α × Finset α //
        p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} =
        (M.powersetCard a ×ˢ (U \ M).powersetCard (k - a)).card :=
    (Fintype.card_of_subtype
        (p := fun p : Finset α × Finset α =>
          p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a))
        (s := M.powersetCard a ×ˢ (U \ M).powersetCard (k - a))
        (H := fun p => by simp only [Finset.mem_product])).symm
  rw [hBridge, hEquiv, hProd, Finset.card_product,
      Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hM]
  rfl
