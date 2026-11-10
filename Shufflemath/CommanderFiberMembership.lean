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

/-!
## Full fiber count (F1c)

Assembles F1a (decks per membership, `50! * 49!`) and F1b (membership count,
`choose 50 k * choose 49 (50 - k)`) into the fiber count. The fiber is handled
at the **Finset** level (a filter on `Finset.univ : Finset Deck`) rather than
as a dependent `Fintype` Sigma, which hit a kernel recursion-depth wall.

Every deck has exactly one left-pile membership set `leftCards d`, and
`leftOriginalCount d = k` holds exactly when that membership set carries
`k` originally-left cards (`leftOriginalCount_eq_leftCardsInter`).  The
section map `d ↦ (leftCards d, d)` is injective on the fiber because its
second component is the deck itself, so the fiber Finset has the same
cardinality as the fiber-sigma `(fiberMembershipSets k).sigma leftCardsFin`;
`Finset.card_sigma` (Fubini, which distinguishes the membership index) then
turns the sigma count into a sum over membership sets of the per-membership
deck count.
-/ 

/-- The decks in the macro fiber with exactly `k` originally-left cards in the
  left pile. -/
abbrev fiberFin (k : Nat) : Finset Deck :=
  (Finset.univ : Finset Deck).filter (fun d => leftOriginalCount d = k)

/-- The decks in the macro fiber whose left pile is exactly `S`. -/
abbrev leftCardsFin (S : Finset (Fin 99)) : Finset Deck :=
  (Finset.univ : Finset Deck).filter (fun d => leftCards d = S)

/-- The commander projection of `d` is `x` exactly when the left pile carries
  `commanderLeftCount x` originally-left cards. -/
theorem project_eq_iff_leftOriginalCount (d : Deck)
    (x : BernoulliLaplace.CommanderState) :
    project d = x ↔ leftOriginalCount d = commanderLeftCount x := by
  simp only [project, commanderLeftCount]
  constructor
  · intro h
    have h1 : (project d).val = leftOriginalCount d - 1 := by
      unfold project
      simp
    have h2 : (project d).val = x.val := congrArg (fun (a : Fin 50) => a.val) h
    rw [h1] at h2
    have hsub : leftOriginalCount d = leftOriginalCount d - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.succ_le_of_lt (leftOriginalCount_pos d))).symm
    rw [h2] at hsub
    exact hsub
  · intro h
    have hval : leftOriginalCount d - 1 = x.val := by
      rw [h, Nat.add_sub_cancel_right]
    exact Fin.ext hval

/-- The fiber of the commander projection at `x` is the macro fiber at its
count `commanderLeftCount x`. -/
theorem fiberFin_eq_fiberSet (x : BernoulliLaplace.CommanderState) :
    fiberFin (commanderLeftCount x) = FiberDisintegration.fiberSet project x := by
  unfold fiberFin FiberDisintegration.fiberSet
  apply Finset.ext
  intro d
  simp only [mem_filter, Finset.mem_univ]
  constructor
  · intro h
    exact ⟨trivial, (project_eq_iff_leftOriginalCount d x).symm.mp h.2⟩
  · intro h
    exact ⟨trivial, (project_eq_iff_leftOriginalCount d x).mp h.2⟩

/-- The macro fiber is the disjoint union of the fixed-membership fibers,
  taken over the membership sets that carry `k` originally-left cards. -/
theorem fiberFin_biUnion (k : Nat) :
    fiberFin k = (fiberMembershipSets k).biUnion (fun S => leftCardsFin S) := by
  apply Finset.ext
  intro d
  simp only [mem_biUnion, mem_filter, Finset.mem_univ]
  constructor
  · intro h
    refine ⟨leftCards d, ?_, ?_⟩
    · have hcard50 : (leftCards d).card = 50 := leftCards_card d
      have hcardk : (leftCards d ∩ leftOrigSet).card = k := by
        rw [← leftOriginalCount_eq_leftCardsInter d, h.2]
      simp only [fiberMembershipSets, mem_filter, mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, hcard50⟩, hcardk⟩
    · exact ⟨trivial, rfl⟩
  · rintro ⟨S, hmem, _, hL⟩
    have hcardk : (S ∩ leftOrigSet).card = k := (Finset.mem_filter.mp hmem).2
    rw [leftOriginalCount_eq_leftCardsInter d, hL, hcardk]
    exact ⟨trivial, rfl⟩

/-- Fixed-membership fibers are pairwise disjoint: every deck has exactly one
  left pile. -/
theorem leftCardsFin_disjoint (S T : Finset (Fin 99)) (h : S ≠ T) :
    Disjoint (leftCardsFin S) (leftCardsFin T) := by
  rw [Finset.disjoint_left]
  intro d hdS hT
  simp only [mem_filter, Finset.mem_univ] at hdS hT
  exact h (hdS.2.symm.trans hT.2)

/-- The macro count of `d` is `k` exactly when its left-pile membership set
  is one of the fiber membership sets. -/
theorem leftOriginalCount_eq_iff_fiberMembership (k : Nat) (d : Deck) :
    leftOriginalCount d = k ↔ leftCards d ∈ fiberMembershipSets k := by
  have h1 : leftOriginalCount d = k ↔ d ∈ fiberFin k := by
    unfold fiberFin
    simp only [mem_filter, Finset.mem_univ]
    constructor
    · intro h
      exact ⟨trivial, h⟩
    · intro h
      exact h.2
  have h2 : d ∈ fiberFin k ↔ leftCards d ∈ fiberMembershipSets k := by
    rw [fiberFin_biUnion k]
    simp only [mem_biUnion, mem_filter, Finset.mem_univ]
    constructor
    · intro h
      rcases h with ⟨S, hmem, _, rfl⟩
      exact hmem
    · intro hmem
      exact ⟨leftCards d, hmem, trivial, rfl⟩
  exact h1.trans h2

/-- The section map of the fiber-sigma: a deck maps to the pair
  `(leftCards d, d)` of its left-pile membership set with itself. -/
def fiberSigmaSection (d : Deck) : (_S : Finset (Fin 99)) × Deck :=
  ⟨leftCards d, d⟩

/-- Pushing the macro fiber forward by its section map gives exactly the
  fiber-sigma: a sigma pair `(S, d)` is present exactly when `d` lies in the
  fiber and its left pile is `S`. -/
theorem fiberFin_image_eq_sigma (k : Nat) :
    (fiberFin k).image fiberSigmaSection =
      (fiberMembershipSets k).sigma (fun S => leftCardsFin S) := by
  apply Finset.ext
  intro x
  simp only [mem_image, mem_sigma]
  constructor
  · intro h
    rcases h with ⟨d, hd, rfl⟩
    have hmem : leftCards d ∈ fiberMembershipSets k :=
      (leftOriginalCount_eq_iff_fiberMembership k d).mp (Finset.mem_filter.mp hd).2
    have hd2 : d ∈ leftCardsFin (leftCards d) := by
      unfold leftCardsFin
      simp only [mem_filter, Finset.mem_univ]
      exact ⟨trivial, trivial⟩
    exact ⟨hmem, hd2⟩
  · intro h
    rcases h with ⟨hmem, hd2⟩
    have hL : leftCards (x.2) = x.1 := (Finset.mem_filter.mp hd2).2
    have hmem' : leftCards (x.2) ∈ fiberMembershipSets k := by
      rw [hL]
      exact hmem
    have hk : leftOriginalCount (x.2) = k :=
      (leftOriginalCount_eq_iff_fiberMembership k (x.2)).mpr hmem'
    refine ⟨x.2, ?_, ?_⟩
    · unfold fiberFin
      simp only [mem_filter, Finset.mem_univ]
      exact ⟨trivial, hk⟩
    · apply Sigma.ext
      · exact hL
      · exact HEq.refl (x.2)

/-- The section map is injective on the fiber: the second component of the
  pair is the deck itself. -/
theorem sigmaSection_injOn (k : Nat) :
    Set.InjOn fiberSigmaSection (↑(fiberFin k)) := by
  rintro d hd d' hd' h
  exact congrArg (fun (x : (_S : Finset (Fin 99)) × Deck) => x.2) h

/-- **F1c:** the macro fiber at count `k` has exactly
  `#(fiberMembershipSets k) * 50! * 49!` decks — the F1b membership count
times the F1a deck count per membership. -/
theorem fiberFin_card (k : Nat) :
    (fiberFin k).card = (fiberMembershipSets k).card *
      (Nat.factorial 50 * Nat.factorial 49) := by
  have hbridge : ∀ S, S ∈ fiberMembershipSets k → (leftCardsFin S).card =
      Fintype.card (decksWithLeft S) := by
    intro S hS
    classical
    unfold leftCardsFin decksWithLeft
    let p := fun (d : Deck) => leftCards d = S
    have hT : Set.toFinset {d : Deck | p d} = Finset.filter p Finset.univ :=
      Set.toFinset_ofPred (p := p)
    have hH : ∀ d, d ∈ Set.toFinset {d : Deck | p d} ↔ p d :=
      fun d => by simp
    rw [← hT, ← (Fintype.card_of_subtype (s := Set.toFinset {d : Deck | p d})
        (p := p) hH)]
  have hcard : ∀ S, S ∈ fiberMembershipSets k → Fintype.card (decksWithLeft S) =
      Nat.factorial 50 * Nat.factorial 49 := by
    intro S hS
    have hscard : S.card = 50 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    exact decksWithLeft_card S hscard
  rw [← (Finset.card_image_of_injOn (sigmaSection_injOn k)),
      fiberFin_image_eq_sigma k,
      Finset.card_sigma]
  change ∑ S ∈ (fiberMembershipSets k), (leftCardsFin S).card =
    (fiberMembershipSets k).card * (Nat.factorial 50 * Nat.factorial 49)
  rw [Finset.sum_congr rfl (fun S hS => hbridge S hS),
      Finset.sum_congr rfl (fun S hS => hcard S hS),
      Finset.sum_const_nat (fun _ _ => rfl)]

/-- **F1c:** the macro fiber at count `k` has
  `choose 50 k * choose 49 (50 - k) * 50! * 49!` decks. -/
theorem fiberFin_count (k : Nat) :
    (fiberFin k).card =
      Nat.choose 50 k * Nat.choose 49 (50 - k) * Nat.factorial 50 * Nat.factorial 49 := by
  rw [fiberFin_card k, fiberMembershipSets_card k]
  ac_rfl

/-- **F1b × F1a:** the fiber of the commander projection at state `x` has
  exactly `choose 50 (x.val + 1) * choose 49 (50 - (x.val + 1)) * 50! * 49!`
decks. -/
theorem fiberSet_card (x : BernoulliLaplace.CommanderState) :
    (FiberDisintegration.fiberSet project x).card =
      Nat.choose 50 (commanderLeftCount x) * Nat.choose 49 (50 - commanderLeftCount x) *
        Nat.factorial 50 * Nat.factorial 49 := by
  rw [(fiberFin_eq_fiberSet x).symm]
  have hcount : (fiberFin (commanderLeftCount x)).card = (fiberFin (x.val + 1)).card := rfl
  rw [hcount, fiberFin_count (x.val + 1)]
  simp only [commanderLeftCount]
