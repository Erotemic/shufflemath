module

public import Shufflemath.FiniteDeck.Histograms
public import Shufflemath.FiniteDeck.Piles
public import Shufflemath.FiberDisintegration

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# Histogram-fiber count (two-pile / two-color, Route B)

The T2 roadmap atom (`docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`,
T2): for a two-pile/two-color allocation, the number of pile-0 sets realizing the
per-category pile-0 counts `X = (x_{0,c})_{c : Color}` is the product of the
per-category binomials `∏_c choose (r_c) (x_{0,c})`, where `r_c` is the total
category-`c` count.

This is the **allocation-level** histogram-fiber count — the honestly-scoped
first landing toward the full T2 disintegration (ordered decks = this number
times `∏_p n_p!`, times the per-pile ordering factor, which requires the
fiber-over-X Sigma-lumping wall documented in the G5 strategy doc).

Route: the same `Finset.card_bij'` pattern as the landed
`powersetCard_markedSplit` (BLRefinement.lean) — the histogram fiber is in
bijection with the product of per-category powersetCards (`X 0`-subsets of the
category-0 cards) × (`X 1`-subsets of the category-1 cards), and the count
follows by `Finset.card_powersetCard`.
-/

/-- The pile-0 sets consistent with per-category pile-0 counts `X`:
    subsets `S` of the card set whose category-`c` count is exactly `X c`. -/
def histFiber (N : Nat) (color : Fin N → Fin 2) (X : Fin 2 → Nat) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powerset.filter
    (fun S => ∀ c, (S.filter (fun x => color x = c)).card = X c)

/-- **Two-pile histogram-fiber count.** The number of pile-0 sets realizing the
    per-category pile-0 counts `X` (two categories) is the product of the two
    per-category binomials: `choose r_0 (X 0) * choose r_1 (X 1)`, where `r_c`
    is the total category-`c` count. -/
theorem twoHist_fiber_card (N : Nat) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    (histFiber N color X).card =
      Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
        Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1) := by
  classical
  let cat0 : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => color x = 0)
  let cat1 : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => color x = 1)
  let Lf := histFiber N color X
  let P := (Finset.powersetCard (X 0) cat0) ×ˢ (Finset.powersetCard (X 1) cat1)
  let i (S : Finset (Fin N)) (_hS : S ∈ Lf) : Finset (Fin N) × Finset (Fin N) :=
    (S.filter (fun x => color x = 0), S.filter (fun x => color x = 1))
  let j (p : Finset (Fin N) × Finset (Fin N)) (_hp : p ∈ P) : Finset (Fin N) := p.1 ∪ p.2
  have hDecomp : ∀ p : Finset (Fin N) × Finset (Fin N), p ∈ P →
      p.1 ⊆ cat0 ∧ p.1.card = X 0 ∧ p.2 ⊆ cat1 ∧ p.2.card = X 1 := by
    intro p hp
    rw [Finset.mem_product] at hp
    rcases hp with ⟨hL, hR⟩
    rw [Finset.mem_powersetCard] at hL hR
    exact ⟨hL.1, hL.2, hR.1, hR.2⟩
  have hInv0 : ∀ p, p ∈ P → (p.1 ∪ p.2).filter (fun x => color x = 0) = p.1 := by
    intro p hp
    rcases hDecomp p hp with ⟨hAsub, _, hBsub, _⟩
    rw [Finset.filter_union]
    have hleft : p.1.filter (fun x => color x = 0) = p.1 := by
      apply Finset.filter_true_of_mem
      intro z hz
      exact (Finset.mem_filter.mp (hAsub hz)).2
    have hright : p.2.filter (fun x => color x = 0) = ∅ := by
      apply Finset.filter_false_of_mem
      intro z hz
      have hzc : z ∈ cat1 := hBsub hz
      have hcol : color z = 1 := (Finset.mem_filter.mp hzc).2
      exact fun h0 => by
        have hcontra : (0 : Fin 2) = (1 : Fin 2) := h0.symm.trans hcol
        exact absurd hcontra (by decide)
    rw [hleft, hright, Finset.union_empty]
  have hInv1 : ∀ p, p ∈ P → (p.1 ∪ p.2).filter (fun x => color x = 1) = p.2 := by
    intro p hp
    rcases hDecomp p hp with ⟨hAsub, _, hBsub, _⟩
    rw [Finset.filter_union]
    have hleft : p.1.filter (fun x => color x = 1) = ∅ := by
      apply Finset.filter_false_of_mem
      intro z hz
      have hzc : z ∈ cat0 := hAsub hz
      have hcol : color z = 0 := (Finset.mem_filter.mp hzc).2
      exact fun h1 => by
        have hcontra : (0 : Fin 2) = (1 : Fin 2) := hcol.symm.trans h1
        exact absurd hcontra (by decide)
    have hright : p.2.filter (fun x => color x = 1) = p.2 := by
      apply Finset.filter_true_of_mem
      intro z hz
      have hzc : z ∈ cat1 := hBsub hz
      exact (Finset.mem_filter.mp hzc).2
    rw [hleft, hright, Finset.empty_union]
  have hbij : Lf.card = P.card := by
    refine Finset.card_bij' i j ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Lf, histFiber, Finset.mem_filter, Finset.mem_powerset] at hS
      dsimp only [i, P] at ⊢
      have h0 : (S.filter (fun x => color x = 0)).card = X 0 := hS.2 0
      have h1 : (S.filter (fun x => color x = 1)).card = X 1 := hS.2 1
      have hsub0 : S.filter (fun x => color x = 0) ⊆ cat0 := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨Finset.mem_univ z, hz.2⟩
      have hsub1 : S.filter (fun x => color x = 1) ⊆ cat1 := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨Finset.mem_univ z, hz.2⟩
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      exact ⟨⟨hsub0, h0⟩, ⟨hsub1, h1⟩⟩
    · intro p hp
      simp only [Lf, histFiber, Finset.mem_filter, Finset.mem_powerset] at ⊢
      dsimp only [P, j] at hp ⊢
      rcases hDecomp p hp with ⟨hAsub, hAcard, hBsub, hBcard⟩
      refine ⟨?_, ?_⟩
      · intro z hz
        exact Finset.mem_univ z
      · intro c
        rcases finTwo_cases c with hc0 | hc1
        · subst hc0
          rw [hInv0 p hp, hAcard]
        · subst hc1
          rw [hInv1 p hp, hBcard]
    · intro S _hS
      dsimp only [i, j] at ⊢
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hz | hz)
        · exact hz.1
        · exact hz.1
      · intro hz
        rcases finTwo_cases (color z) with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    · intro p hp
      exact Prod.ext (hInv0 p hp) (hInv1 p hp)
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]

/-- **Allocation-count corollary.** The number of pile-0 sets of size `n_0`
    (the valid two-pile allocations) is `choose N n_0`, by the landed
    `Finset.card_powersetCard`. -/
theorem allocFiberCount (N n_0 : Nat) :
    ((Finset.univ : Finset (Fin N)).powerset.filter (fun S => S.card = n_0)).card =
      Nat.choose N n_0 := by
  have hEq : (Finset.univ : Finset (Fin N)).powerset.filter (fun S => S.card = n_0) =
      Finset.powersetCard n_0 (Finset.univ : Finset (Fin N)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  rw [hEq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Allocation-level marginal law** (the T2 marginal-numerator shape at the
    allocation level): the relative mass of the histogram `X` at the allocation
    level is the fiber count divided by the number of all two-pile allocations
    of that size.  Composes `twoHist_fiber_card` with `allocFiberCount`; the
    deck-level marginal law (multiplying by the `∏_p n_p!` fiber size) is the
    documented Sigma-lumping wall. -/
theorem histMarginalNum (N : Nat) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
        Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1) : Rat) /
      (Nat.choose N (X 0 + X 1) : Rat) =
        (histFiber N color X).card / (Nat.choose N (X 0 + X 1) : Rat) := by
  rw [twoHist_fiber_card N color X, Nat.cast_mul]

/-- Bounded two-pile histogram value: per-category pile-0 counts, each in `Fin (N+1)`. -/
abbrev Hist2 (N : Nat) := Fin 2 → Fin (N + 1)

/-- The histogram observation over the full two-pile allocation space:
    for a pile-0 set `S`, its per-category pile-0 counts as `Fin (N+1)` values. -/
noncomputable def histObs (N : Nat) (color : Fin N → Fin 2) :
    Finset (Fin N) → Hist2 N :=
  fun S => fun c =>
    ⟨(S.filter (fun x : Fin N => color x = c)).card, by
      have h1 := Finset.card_filter_le S (fun x : Fin N => color x = c)
      have h2 := Finset.card_le_univ S
      rw [Fintype.card_fin] at h2
      exact Nat.lt_succ_of_le (h1.trans h2)⟩

/-- Fiber identity: the fiber of the histogram observation over `X` is exactly
    the histogram fiber of pile-0 sets with per-category counts `(X 0).val, (X 1).val`. -/
theorem fiberSet_histObs (N : Nat) (color : Fin N → Fin 2) (X : Hist2 N) :
    FiberDisintegration.fiberSet (histObs N color) X =
      histFiber N color fun c => (X c).val := by
  classical
  ext S
  simp only [FiberDisintegration.fiberSet, Finset.mem_filter, Finset.mem_univ, true_and,
    histFiber, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro h
    refine ⟨Finset.subset_univ _, ?_⟩
    intro c
    have heq := congrFun h c
    exact congrArg Fin.val heq
  · intro h
    funext c
    exact Fin.ext (h.2 c)

/-- **The allocation-level T2 marginal-mass identity**: over the full
    allocation space (uniform over all pile-0 sets, all sizes), the histogram
    `X` carries mass equal to the per-category binomial product divided by the
    total-allocation count `2 ^ N`. -/
theorem histMarginalLaw_mass (N : Nat) (color : Fin N → Fin 2) (X : Hist2 N) :
    Dist.mass (FiberDisintegration.marginalLaw (histObs N color)) X =
      (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0).val *
        Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1).val : Rat) /
        (2 ^ N : Rat) := by
  rw [FiberDisintegration.marginalLaw_mass, fiberSet_histObs, twoHist_fiber_card,
    Fintype.card_finset, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  rfl

/-- The size-`n` histogram fiber: pile-0 sets of size `n` consistent with the
    per-category counts `X` (two categories). -/
def sizeNHistFiber (N : Nat) (color : Fin N → Fin 2) (n : Nat) (X : Fin 2 → Nat) :
    Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powerset.filter
    (fun S => S.card = n ∧ ∀ c, (S.filter (fun x => color x = c)).card = X c)

/-- Card-split identity: the size of a pile-0 set is the sum of its
    per-category filtered card counts (two color classes). -/
theorem card_split (N : Nat) (color : Fin N → Fin 2) (S : Finset (Fin N)) :
    S.card = (S.filter (fun x : Fin N => color x = 0)).card +
      (S.filter (fun x : Fin N => color x = 1)).card := by
  have h : S.filter (fun x => color x = 0) ∪ S.filter (fun x => color x = 1) = S := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      rcases finTwo_cases (color x) with h0 | h1
      · exact Or.inl ⟨hx, h0⟩
      · exact Or.inr ⟨hx, h1⟩
  have hdisjoint : Disjoint (S.filter (fun x => color x = 0)) (S.filter (fun x => color x = 1)) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have ⟨_, hc0⟩ := Finset.mem_filter.mp hx0
    have ⟨_, hc1⟩ := Finset.mem_filter.mp hx1
    rw [hc0] at hc1
    exact absurd hc1 (by decide)
  have hcard := congrArg Finset.card h
  rw [Finset.card_union_eq_card_add_card.mpr hdisjoint] at hcard
  exact hcard.symm

/-- **The size-`n` histogram-fiber count** (T2 at the size-`n` allocation level):
    the number of size-`n` pile-0 sets consistent with the per-category counts
    `X` is the per-category binomial product when `X 0 + X 1 = n`, and `0`
    otherwise (the size constraint is forced to be consistent). -/
theorem sizeN_histFiber_card (N : Nat) (color : Fin N → Fin 2) (n : Nat) (X : Fin 2 → Nat) :
    (sizeNHistFiber N color n X).card =
      if X 0 + X 1 = n then
        Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
          Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1)
      else 0 := by
  by_cases h : X 0 + X 1 = n
  · simp only [if_pos h]
    have hEq : sizeNHistFiber N color n X = histFiber N color X := by
      ext S
      simp only [sizeNHistFiber, Finset.mem_filter, Finset.mem_powerset, histFiber,
        Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hsub, hcard, hhist⟩
        exact ⟨hsub, hhist⟩
      · rintro ⟨hsub, hhist⟩
        have hsum : S.card = X 0 + X 1 := by
          rw [card_split N color S, hhist 0, hhist 1]
        exact ⟨hsub, hsum.trans h, hhist⟩
    rw [hEq, twoHist_fiber_card]
  · simp only [if_neg h]
    have hempty : sizeNHistFiber N color n X = ∅ := by
      simp only [sizeNHistFiber, Finset.filter_eq_empty_iff]
      intro S _hS hp
      have hsum : S.card = X 0 + X 1 := by
        rw [card_split N color S, hp.2 0, hp.2 1]
      rw [hp.1] at hsum
      exact h (hsum.symm)
    rw [hempty, Finset.card_empty]

/-- **The T2 size-`n` marginal law** (allocation level): the conditional mass of
    histogram `X` over the size-`n` allocation space, as a `Rat` identity
    `#fiber(X) / #allocations(n)`.  This is the T2 law shape — the per-category
    binomial product over `choose N n` (the number of size-`n` pile-0 sets,
    landed as `allocFiberCount`). -/
theorem sizeN_marginal_law_mass (N : Nat) (color : Fin N → Fin 2) (n : Nat) (X : Fin 2 → Nat) :
    ((sizeNHistFiber N color n X).card : Rat) / (Nat.choose N n : Rat) =
      if X 0 + X 1 = n then
        (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
          Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1) : Rat) /
          (Nat.choose N n : Rat)
      else 0 := by
  rw [sizeN_histFiber_card]
  simp only [Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, ite_div, div_zero, zero_div]


/-- The deck-level histogram fiber: decks whose induced left-pile allocation
    has per-category counts `X`.  This is the honestly-scoped deck-level T2
    object — every deck whose left pile carries pile-0 categories with counts
    `X`, which is the honestly-scoped deck-level T2 object. -/
def deckFiber (N m : Nat) (hm : m ≤ N) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    Finset (Equiv.Perm (Fin N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun g => ∀ c,
      (((leftPositions N m hm).image (fun p => g p)).filter (fun x => color x = c)).card = X c)

/-- The deck-level histogram fiber equals the disjoint biUnion of the per-`C`
    fibers over the histogram fiber. -/
theorem deckFiber_eq_biUnion (N m : Nat) (hm : m ≤ N) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    deckFiber N m hm color X =
      (histFiber N color X).biUnion (fun C => fiberSetPile N m hm C) := by
  ext g
  constructor
  · intro h
    simp only [deckFiber, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp only [Finset.mem_biUnion]
    refine ⟨(leftPositions N m hm).image (fun p => g p), ?_, ?_⟩
    · simp only [histFiber, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
      exact ⟨Finset.subset_univ _, h⟩
    · dsimp only [fiberSetPile]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [Finset.mem_biUnion]
    rintro ⟨C, hCmem, hgC⟩
    simp only [histFiber, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and] at hCmem
    have hloc : (leftPositions N m hm).image (fun p => g p) = C := by
      dsimp only [fiberSetPile] at hgC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hgC
      exact hgC
    simp only [deckFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    intro c
    rw [hloc]
    exact hCmem.2 c

/-- The per-`C` fiber count (two-pile / G2 form): the number of decks realizing
    a fixed allocation `C` (card `m`) is `m! * (N - m)!` — the landed `fiberCount`,
    via `fiberSetPile`/`fiberSet`/`fiberCount`. -/
theorem fiberSetPile_card (N m : Nat) (hm : m ≤ N) (C : Finset (Fin N)) (hC : C.card = m) :
    (fiberSetPile N m hm C).card = Nat.factorial m * Nat.factorial (N - m) := by
  have h1 : fiberSetPile N m hm C = fiberSet N m hm ⟨C, hC⟩ :=
    (fiberSet_eq_pile N m hm ⟨C, hC⟩).symm
  rw [h1, fiberSet_card]
  exact fiberCount N m hm ⟨C, hC⟩

/-- **T2 deck-level identity.** The number of decks whose induced left-pile
    allocation has per-category counts `X` is the allocation-fiber count
    `∏_c choose (r_c, X c)` times the per-allocation deck count
    `m! * (N - m)!` — the T2 deck-level composition.  The `if X 0 + X 1 = m`
    guard is honest: a deck's left pile has exactly `m` cards, so every
    histogram consistent with a left-pile allocation has total `m`. -/
theorem deckFiber_card (N m : Nat) (hm : m ≤ N) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    (deckFiber N m hm color X).card =
      if X 0 + X 1 = m then
        (histFiber N color X).card * Nat.factorial m * Nat.factorial (N - m)
      else 0 := by
  by_cases h : X 0 + X 1 = m
  · have hhistCard : ∀ C ∈ histFiber N color X, C.card = m := by
      intro C hmem
      have hC' : ∀ c, (C.filter (fun x => color x = c)).card = X c := by
        have h := hmem
        simp only [histFiber, Finset.mem_filter, Finset.mem_powerset] at h
        exact h.2
      have hsplit := card_split N color C
      rw [hsplit, hC' 0, hC' 1]
      exact h
    have hdisj : ((histFiber N color X) : Set (Finset (Fin N))).PairwiseDisjoint
        (fun C => fiberSetPile N m hm C) := by
      intro C1 _ C2 _ hne
      change Disjoint (fiberSetPile N m hm C1) (fiberSetPile N m hm C2)
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb heq
      dsimp only [fiberSetPile] at ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hIm : (leftPositions N m hm).image (fun p => a p) =
          (leftPositions N m hm).image (fun p => b p) :=
        congrArg (fun x : Equiv.Perm (Fin N) => (leftPositions N m hm).image (fun p => x p)) heq
      exact hne (by rw [← ha, ← hb]; exact hIm)
    rw [deckFiber_eq_biUnion, Finset.card_biUnion hdisj]
    simp only [if_pos h]
    have hsum : (histFiber N color X).sum (fun C => (fiberSetPile N m hm C).card) =
        (histFiber N color X).card * (Nat.factorial m * Nat.factorial (N - m)) := by
      rw [Finset.sum_congr rfl (fun C hC => fiberSetPile_card N m hm C (hhistCard C hC)),
        Finset.sum_const]
      ring
    rw [hsum]
    ring
  · simp only [if_neg h]
    have hempty : deckFiber N m hm color X = ∅ := by
      ext g
      constructor
      · intro hg
        simp only [deckFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        have hcard : ((leftPositions N m hm).image (fun p => g p)).card = m :=
          leftImageIsMembership N m hm g
        have hsum : ((leftPositions N m hm).image (fun p => g p)).card = X 0 + X 1 := by
          have hsplit := card_split N color ((leftPositions N m hm).image (fun p => g p))
          rw [hsplit]
          have h0 : (((leftPositions N m hm).image (fun p => g p)).filter (fun x => color x = 0)).card = X 0 := hg 0
          have h1 : (((leftPositions N m hm).image (fun p => g p)).filter (fun x => color x = 1)).card = X 1 := hg 1
          rw [h0, h1]
        rw [hcard] at hsum
        exact absurd hsum.symm h
      · intro hg
        exact absurd hg (by simp)
    rw [hempty, Finset.card_empty]


/-- **Roadmap T2 π law (two-pile / two-color).** The uniform-deck probability
    of histogram `X` — the deck-level fiber count `#deckFiber(X) / N!` — equals
    the multivariate-hypergeometric numerator `∏_c choose (r_c, X c)` over
    `choose N m` (the size-`m` pile-0 allocation count).  This is the T2
    `π(X)` in its two-pile specialization, composed honestly from the landed
    `deckFiber_card` (the deck-level identity) and the `N! = choose N m * m! *
    (N - m)!` total-deck split. -/
theorem deckFiber_prob (N m : Nat) (hm : m ≤ N) (color : Fin N → Fin 2) (X : Fin 2 → Nat) :
    ((deckFiber N m hm color X).card : Rat) / (Nat.factorial N : Rat) =
      if X 0 + X 1 = m then
        (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
          Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1) : Rat) /
          (Nat.choose N m : Rat)
      else 0 := by
  by_cases h : X 0 + X 1 = m
  · -- Nat-level identity first: deckFiber.card * choose N m = (c0 * c1) * N!
    have hId : (deckFiber N m hm color X).card * (Nat.choose N m) =
        (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
          Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1)) *
          Nat.factorial N := by
      rw [deckFiber_card, if_pos h, twoHist_fiber_card,
        ← Nat.choose_mul_factorial_mul_factorial hm]
      ring
    have hRat : ((deckFiber N m hm color X).card : Rat) * (Nat.choose N m : Rat) =
        (Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 0)).card) (X 0) *
          Nat.choose ((Finset.univ.filter (fun x : Fin N => color x = 1)).card) (X 1) : Rat) *
          (Nat.factorial N : Rat) := by
      have h := hId
      exact_mod_cast h
    have hposF : (Nat.factorial N : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.factorial_pos N))
    have hposC : (Nat.choose N m : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos hm))
    rw [if_pos h, div_eq_div_iff hposF hposC]
    exact hRat
  · rw [deckFiber_card, if_neg h]
    simp only [Nat.cast_zero, zero_div, if_neg h]


/-! ## Size-`n` allocation-space marginal law (the T2 size-`n` marginal-law
object over the subtype-space) -/

/-- The size-`n` allocation space (reducible abbrev — a `def` wrapper would
    block `Fintype` instance synthesis on the subtype). -/
abbrev sizeNAllocSpace (N n : Nat) : Type :=
  {S : Finset (Fin N) // S.card = n}

/-- The size-`n` allocation space is inhabited when `n ≤ N`. -/
theorem sizeNAllocSpace_nonempty (N n : Nat) (hn : n ≤ N) :
    Nonempty (sizeNAllocSpace N n) := by
  classical
  have hc : (Finset.univ : Finset (Fin N)).powersetCard n ≠ ∅ := by
    have hpos : 0 < ((Finset.univ : Finset (Fin N)).powersetCard n).card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos hn
    intro h
    rw [h, Finset.card_empty] at hpos
    exact Nat.lt_irrefl 0 hpos
  obtain ⟨S, hS⟩ := Finset.nonempty_of_ne_empty hc
  exact ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩⟩

/-- The size-`n` allocation-space histogram observation: project the pile-0
    set, then observe the per-category counts. -/
noncomputable def sizeNObs (N : Nat) (color : Fin N → Fin 2) (n : Nat) :
    sizeNAllocSpace N n → Hist2 N :=
  fun S => histObs N color S.1

/-- The size-`n` marginal law: the uniform-over-size-`n`-allocations histogram
    law, as a genuine `Dist` object. -/
noncomputable def sizeNMarginalLaw (N : Nat) (color : Fin N → Fin 2) (n : Nat)
    (hn : n ≤ N) : Dist (Hist2 N) :=
  letI := sizeNAllocSpace_nonempty N n hn
  FiberDisintegration.marginalLaw (sizeNObs N color n)

/-- histObs equality unfolds to per-category counts (two categories). -/
theorem histObs_eq_iff (N : Nat) (color : Fin N → Fin 2) (S : Finset (Fin N)) (X : Hist2 N) :
    histObs N color S = X ↔ ∀ c, (S.filter (fun x : Fin N => color x = c)).card = (X c).val := by
  constructor
  · intro h
    intro c
    exact congrArg Fin.val (congrFun h c)
  · intro h
    funext c
    exact Fin.ext (h c)

/-- sizeNHistFiber membership unfolds to size-`n` + per-category counts. -/
theorem sizeNHistFiber_mem_iff (N : Nat) (color : Fin N → Fin 2) (n : Nat) (X : Fin 2 → Nat)
    (S : Finset (Fin N)) :
    S ∈ sizeNHistFiber N color n X ↔
      S.card = n ∧ ∀ c, (S.filter (fun x : Fin N => color x = c)).card = X c := by
  simp only [sizeNHistFiber, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2⟩
  · intro h
    exact ⟨Finset.subset_univ S, h.1, h.2⟩

/-- The size-`n` marginal law's mass: the honestly-scoped T2 size-`n` identity —
    `#fiber(X) / #allocations(n) = #sizeNHistFiber(X) / choose N n`. -/
theorem sizeNMarginalLaw_mass (N : Nat) (color : Fin N → Fin 2) (n : Nat)
    (hn : n ≤ N) (X : Hist2 N) :
    Dist.mass (sizeNMarginalLaw N color n hn) X =
      ((sizeNHistFiber N color n fun c => (X c).val).card : Rat) / (Nat.choose N n : Rat) := by
  classical
  haveI : Nonempty (sizeNAllocSpace N n) := sizeNAllocSpace_nonempty N n hn
  have hm := FiberDisintegration.marginalLaw_mass (sizeNObs N color n) X
  haveI : Fintype ↥(FiberDisintegration.fiberSet (sizeNObs N color n) X) := inferInstance
  haveI : Fintype ↥(sizeNHistFiber N color n fun c => (X c).val) := inferInstance
  have equiv : ↥(FiberDisintegration.fiberSet (sizeNObs N color n) X) ≃
      ↥(sizeNHistFiber N color n fun c => (X c).val) :=
    { toFun := fun ⟨⟨S, hS⟩, hmem⟩ =>
        ⟨S, by
          have hX : ∀ c, (S.filter (fun x : Fin N => color x = c)).card = (X c).val := by
            have hh : histObs N color S = X := by
              have h := (Finset.mem_filter.mp hmem).2
              exact h
            exact (histObs_eq_iff N color S X).mp hh
          rw [sizeNHistFiber_mem_iff]
          exact ⟨hS, hX⟩⟩
      invFun := fun ⟨S, hS⟩ =>
        ⟨⟨S, (sizeNHistFiber_mem_iff N color n (fun c => (X c).val) S).mp hS |>.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (histObs_eq_iff N color S X).mpr ((sizeNHistFiber_mem_iff N color n (fun c => (X c).val) S).mp hS |>.2)⟩⟩
      left_inv := fun ⟨⟨S, hS⟩, hmem⟩ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun ⟨S, hS⟩ => Subtype.ext rfl }
  have hcard := Fintype.card_congr equiv
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  have hsub : Fintype.card (sizeNAllocSpace N n) = Nat.choose N n :=
    membershipCount N n hn
  have hm' : Dist.mass (sizeNMarginalLaw N color n hn) X =
      ((FiberDisintegration.fiberSet (sizeNObs N color n) X).card : Rat) /
        (Fintype.card (sizeNAllocSpace N n) : Rat) := hm
  rw [hm', hcard, hsub]


/-! ## Size-`n` fiber law (the T2 size-`n` conditional law over the reachable
histogram subtype) -/

/-- The reachable histogram subtype over the size-`n` allocation space:
    histogram values realized by at least one size-`n` pile-0 set. -/
abbrev sizeNReachableHist (N : Nat) (color : Fin N → Fin 2) (n : Nat) : Type :=
  {X : Hist2 N // ∃ S : sizeNAllocSpace N n, histObs N color S = X}

/-- The observation over the reachable subtype: project to the histogram,
    bundle the witnessing allocation. -/
noncomputable def sizeNObsReachable (N : Nat) (color : Fin N → Fin 2) (n : Nat) :
    sizeNAllocSpace N n → sizeNReachableHist N color n :=
  fun S => ⟨histObs N color S, ⟨S, rfl⟩⟩

/-- The observation over the reachable subtype is surjective. -/
theorem sizeNObs_surjective_reachable (N : Nat) (color : Fin N → Fin 2) (n : Nat)
    (hn : n ≤ N) :
    Function.Surjective (sizeNObsReachable N color n) := by
  rintro ⟨X, ⟨S, hS⟩⟩
  subst hS
  exact ⟨S, rfl⟩

/-- The reachable-histogram fiberSet card: the fiber of the reachable
    observation is in bijection (via `S ↦ S.1`) with the size-`n` histogram
    fiber of the observed histogram's underlying value. -/
theorem fiberSet_reachable_card (N : Nat) (color : Fin N → Fin 2) (n : Nat)
    (hn : n ≤ N) (X : sizeNReachableHist N color n) :
    (FiberDisintegration.fiberSet (sizeNObsReachable N color n) X).card =
      (sizeNHistFiber N color n fun c => (X.1 c).val).card := by
  classical
  haveI : Fintype ↥(FiberDisintegration.fiberSet (sizeNObsReachable N color n) X) := inferInstance
  haveI : Fintype ↥(sizeNHistFiber N color n fun c => (X.1 c).val) := inferInstance
  have equiv : ↥(FiberDisintegration.fiberSet (sizeNObsReachable N color n) X) ≃
      ↥(sizeNHistFiber N color n fun c => (X.1 c).val) :=
    { toFun := fun ⟨⟨S, hS⟩, hmem⟩ =>
        ⟨S, by
          have hX : ∀ c, (S.filter (fun x : Fin N => color x = c)).card = (X.1 c).val := by
            have hh : histObs N color S = X.1 := by
              have h := (Finset.mem_filter.mp hmem).2
              exact Subtype.ext_iff.mp h
            exact (histObs_eq_iff N color S X.1).mp hh
          rw [sizeNHistFiber_mem_iff]
          exact ⟨hS, hX⟩⟩
      invFun := fun ⟨S, hS⟩ =>
        let hh := (sizeNHistFiber_mem_iff N color n (fun c => (X.1 c).val) S).mp hS
        ⟨⟨S, hh.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Subtype.ext_iff.mpr ((histObs_eq_iff N color S X.1).mpr hh.2)⟩⟩
      left_inv := fun ⟨⟨S, hS⟩, hmem⟩ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun ⟨S, hS⟩ => Subtype.ext rfl }
  have hcard := Fintype.card_congr equiv
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard

/-- The size-`n` fiber law: the uniform conditional law over the fiber of the
    observed reachable histogram — the size-`n` companion to the marginal law. -/
noncomputable def sizeNFiberLaw (N : Nat) (color : Fin N → Fin 2) (n : Nat) (hn : n ≤ N) :
    FiniteKernel (sizeNReachableHist N color n) (sizeNAllocSpace N n) :=
  letI := sizeNAllocSpace_nonempty N n hn
  FiberDisintegration.fiberLaw (sizeNObsReachable N color n) (sizeNObs_surjective_reachable N color n hn)

/-- Mass of the size-`n` fiber law: uniform over the size-`n` fiber. -/
theorem sizeNFiberLaw_mass (N : Nat) (color : Fin N → Fin 2) (n : Nat) (hn : n ≤ N)
    (X : sizeNReachableHist N color n) (b : sizeNAllocSpace N n) :
    Dist.mass (sizeNFiberLaw N color n hn X) b =
      (if (histObs N color b.1 = X.1) then
        ((sizeNHistFiber N color n fun c => (X.1 c).val).card : Rat)⁻¹ else 0) := by
  haveI : Nonempty (sizeNAllocSpace N n) := sizeNAllocSpace_nonempty N n hn
  rw [sizeNFiberLaw, FiberDisintegration.fiberLaw_mass]
  rw [fiberSet_reachable_card N color n hn X]
  -- the observation equality reduces to the projection equality
  have hsub : (sizeNObsReachable N color n b = X) ↔ histObs N color b.1 = X.1 := by
    constructor
    · intro h
      exact Subtype.ext_iff.mp h
    · intro h
      exact Subtype.ext_iff.mpr h
  simp only [hsub]

end FiniteDeck
end Shufflemath

