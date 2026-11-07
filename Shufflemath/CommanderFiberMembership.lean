module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderFiberCount

@[expose] public section

namespace Shufflemath
open BernoulliLaplace
open CommanderPermutation
open Finset

/-- The 50-card membership sets that carry exactly `k` initially-left cards. -/
def fiberMembershipSets (k : Nat) : Finset (Finset (Fin 99)) :=
  (powersetCard 50 (univ : Finset (Fin 99))).filter (fun S => (S ∩ leftOrigSet).card = k)

/-- Pairs `(L, R)` with `L` a `k`-subset of the left cards and
  `R` a `(50 - k)`-subset of the right cards. -/
def leftRightPairs (k : Nat) : Finset (Finset (Fin 99) × Finset (Fin 99)) :=
  powersetCard k leftOrigSet ×ˢ powersetCard (50 - k) rightOrigSet

def unionMap (p : Finset (Fin 99) × Finset (Fin 99)) : Finset (Fin 99) := p.1 ∪ p.2

/-- A pair `(L, R)` with `L ⊆ left` (|L| = k) and `R ⊆ right` (|R| = 50 - k)
  has a disjoint union of 50 cards, k of which are initially-left. -/
theorem unionMap_mem_fiber (k : Nat) (p : Finset (Fin 99) × Finset (Fin 99))
    (hp : p ∈ leftRightPairs k) : unionMap p ∈ fiberMembershipSets k := by
  have hLmem : p.1 ∈ powersetCard k leftOrigSet := (mem_product.mp hp).1
  have hRmem : p.2 ∈ powersetCard (50 - k) rightOrigSet := (mem_product.mp hp).2
  have hLsub : p.1 ⊆ leftOrigSet := (mem_powersetCard.mp hLmem).1
  have hLcard : p.1.card = k := (mem_powersetCard.mp hLmem).2
  have hRsub : p.2 ⊆ rightOrigSet := (mem_powersetCard.mp hRmem).1
  have hRcard : p.2.card = 50 - k := (mem_powersetCard.mp hRmem).2
  simp only [fiberMembershipSets, mem_filter, mem_powersetCard, unionMap]
  have hdj : p.1 ∩ p.2 = ∅ := by
    apply subset_empty.mp
    refine (inter_subset_inter hLsub hRsub).trans ?_
    rw [leftOrigSet_disjoint_rightOrigSet]
  have hRinter : p.2 ∩ leftOrigSet = ∅ := by
    apply subset_empty.mp
    refine (inter_subset_inter hRsub Finset.Subset.rfl).trans ?_
    rw [inter_comm, leftOrigSet_disjoint_rightOrigSet]
  have hLinter : p.1 ∩ leftOrigSet = p.1 := by
    ext x
    constructor
    · rintro hx; exact (mem_inter.mp hx).1
    · intro hx; exact mem_inter.mpr ⟨hx, hLsub hx⟩
  constructor
  · constructor
    · intro x _; exact mem_univ x
    · have hk50 : k ≤ 50 := by
        rw [← hLcard]
        simpa [leftOrigSet_card] using card_le_card hLsub
      have hdisj : Disjoint p.1 p.2 := (disjoint_iff_inter_eq_empty).mpr hdj
      rw [card_union_of_disjoint hdisj, hLcard, hRcard]
      omega
  · rw [union_inter_distrib_right, hLinter, hRinter, union_empty]
    simpa using hLcard





/-- Every subset decomposes into its left and right parts
  (because the original piles partition the deck). -/
theorem S_decomp (S : Finset (Fin 99)) :
    S = (S ∩ leftOrigSet) ∪ (S ∩ rightOrigSet) := by
  calc
    S = S ∩ univ := (inter_univ S).symm
    _ = S ∩ (leftOrigSet ∪ rightOrigSet) := by rw [← leftOrigSet_univ_rightOrigSet]
    _ = S ∩ leftOrigSet ∪ S ∩ rightOrigSet := by rw [inter_union_distrib_left]

/-- The left and right parts of any subset are disjoint. -/
theorem S_decomp_disjoint (S : Finset (Fin 99)) :
    Disjoint (S ∩ leftOrigSet) (S ∩ rightOrigSet) := by
  have hL : S ∩ leftOrigSet ⊆ leftOrigSet := inter_subset_right
  have hR : S ∩ rightOrigSet ⊆ rightOrigSet := inter_subset_right
  rw [disjoint_iff_inter_eq_empty]
  apply subset_empty.mp
  refine (inter_subset_inter hL hR).trans ?_
  rw [leftOrigSet_disjoint_rightOrigSet]

/-- Backward: a 50-subset with `k` initially-left cards splits uniquely as
  `(S ∩ left, S ∩ right)` in the left-right pair set. -/
theorem fiberMem_to_pairs (k : Nat) (S : Finset (Fin 99))
    (hS : S ∈ fiberMembershipSets k) :
    (S ∩ leftOrigSet, S ∩ rightOrigSet) ∈ leftRightPairs k := by
  simp only [fiberMembershipSets, mem_filter] at hS
  have hScard : S.card = 50 := (mem_powersetCard.mp hS.1).2
  have hSk : (S ∩ leftOrigSet).card = k := hS.2
  have hL : S ∩ leftOrigSet ⊆ leftOrigSet := inter_subset_right
  have hR : S ∩ rightOrigSet ⊆ rightOrigSet := inter_subset_right
  simp only [leftRightPairs, mem_product, mem_powersetCard]
  constructor
  · constructor
    · exact hL
    · simpa using hSk
  · constructor
    · exact hR
    · have hdisj : Disjoint (S ∩ leftOrigSet) (S ∩ rightOrigSet) := S_decomp_disjoint S
      have hU : (S ∩ leftOrigSet).card + (S ∩ rightOrigSet).card =
          (S ∩ leftOrigSet ∪ S ∩ rightOrigSet).card := (card_union_of_disjoint hdisj).symm
      have hEq : (S ∩ leftOrigSet ∪ S ∩ rightOrigSet).card = S.card := by rw [← S_decomp]
      have hsum : (S ∩ leftOrigSet).card + (S ∩ rightOrigSet).card = 50 := by
        rw [hU, hEq, hScard]
      have hk50 : (S ∩ leftOrigSet).card ≤ 50 := by
        simpa [leftOrigSet_card] using (card_le_card hL)
      rw [← hSk]
      omega


/-- The left part of a left-right union is recovered by intersecting with the
  left cards (the right part contributes nothing there). -/
theorem leftPart_of_union (L R : Finset (Fin 99))
    (hL : L ⊆ leftOrigSet) (hR : R ⊆ rightOrigSet) :
    (L ∪ R) ∩ leftOrigSet = L := by
  rw [union_inter_distrib_right]
  have hLinter : L ∩ leftOrigSet = L := by
    ext x
    constructor
    · rintro hx; exact (mem_inter.mp hx).1
    · intro hx; exact mem_inter.mpr ⟨hx, hL hx⟩
  have hRinter : R ∩ leftOrigSet = ∅ := by
    apply subset_empty.mp
    refine (inter_subset_inter hR Finset.Subset.rfl).trans ?_
    rw [inter_comm, leftOrigSet_disjoint_rightOrigSet]
  rw [hLinter, hRinter, union_empty]

/-- The right part of a left-right union is recovered by intersecting with the
  right cards. -/
theorem rightPart_of_union (L R : Finset (Fin 99))
    (hL : L ⊆ leftOrigSet) (hR : R ⊆ rightOrigSet) :
    (L ∪ R) ∩ rightOrigSet = R := by
  rw [union_inter_distrib_right]
  have hLinter : L ∩ rightOrigSet = ∅ := by
    apply subset_empty.mp
    have h : L ∩ rightOrigSet ⊆ leftOrigSet ∩ rightOrigSet :=
      inter_subset_inter hL (Finset.Subset.rfl : rightOrigSet ⊆ rightOrigSet)
    refine h.trans ?_
    rw [leftOrigSet_disjoint_rightOrigSet]
  have hRinter : R ∩ rightOrigSet = R := by
    ext x
    constructor
    · rintro hx; exact (mem_inter.mp hx).1
    · intro hx; exact mem_inter.mpr ⟨hx, hR hx⟩
  rw [hLinter, hRinter]
  simp

/-- A left-right union determines its two parts, so the union map is injective
  on the left-right pairs. -/
theorem unionMap_injective (k : Nat)
    (p q : Finset (Fin 99) × Finset (Fin 99))
    (hp : p ∈ leftRightPairs k) (hq : q ∈ leftRightPairs k)
    (h : unionMap p = unionMap q) : p = q := by
  have hpL : p.1 ⊆ leftOrigSet := (mem_powersetCard.mp ((mem_product.mp hp).1)).1
  have hpR : p.2 ⊆ rightOrigSet := (mem_powersetCard.mp ((mem_product.mp hp).2)).1
  have hqL : q.1 ⊆ leftOrigSet := (mem_powersetCard.mp ((mem_product.mp hq).1)).1
  have hqR : q.2 ⊆ rightOrigSet := (mem_powersetCard.mp ((mem_product.mp hq).2)).1
  have hpLrec : p.1 = unionMap p ∩ leftOrigSet := by
    simp only [unionMap]
    exact (leftPart_of_union p.1 p.2 hpL hpR).symm
  have hqLrec : q.1 = unionMap q ∩ leftOrigSet := by
    simp only [unionMap]
    exact (leftPart_of_union q.1 q.2 hqL hqR).symm
  have hpRrec : p.2 = unionMap p ∩ rightOrigSet := by
    simp only [unionMap]
    exact (rightPart_of_union p.1 p.2 hpL hpR).symm
  have hqRrec : q.2 = unionMap q ∩ rightOrigSet := by
    simp only [unionMap]
    exact (rightPart_of_union q.1 q.2 hqL hqR).symm
  apply Prod.ext
  · rw [hpLrec, hqLrec, h]
  · rw [hpRrec, hqRrec, h]



/-- The 50-subsets carrying `k` initially-left cards are exactly the unions of
  the `(k, 50-k)` left-right pairs. -/
theorem fiberMembershipSets_eq_image (k : Nat) :
    fiberMembershipSets k = (leftRightPairs k).image unionMap := by
  ext S
  simp only [mem_image]
  constructor
  · intro hS
    refine ⟨(S ∩ leftOrigSet, S ∩ rightOrigSet), ?_, ?_⟩
    · exact fiberMem_to_pairs k S hS
    · simp only [unionMap]
      exact (S_decomp S).symm
  · rintro (⟨p, hp, rfl⟩)
    exact unionMap_mem_fiber k p hp

/-- **F1b count:** the number of 50-card membership sets carrying exactly
  `k` initially-left cards is the binomial product
  `choose 50 k * choose 49 (50 - k)`. -/
theorem fiberMembershipSets_card (k : Nat) :
    (fiberMembershipSets k).card = Nat.choose 50 k * Nat.choose 49 (50 - k) := by
  rw [fiberMembershipSets_eq_image]
  have hinj : Set.InjOn unionMap (↑(leftRightPairs k)) := by
    rintro p hp q hq h
    exact unionMap_injective k p q (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) h
  rw [card_image_of_injOn hinj]
  simp only [leftRightPairs]
  rw [card_product]
  rw [card_powersetCard, leftOrigSet_card, card_powersetCard, rightOrigSet_card]

end Shufflemath
end