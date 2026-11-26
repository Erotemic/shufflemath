module

public import Shufflemath.FiniteDeck.Histograms
public import Shufflemath.FiniteDeck.Piles
public import Shufflemath.FiberDisintegration
public import Shufflemath.BernoulliLaplaceGeneral

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


/-! ## T2: the two-pile/two-color π law is exactly the BL stationary law

Roadmap T2: "Its two-pile/two-color specialization is exactly `blStationary N m r`
and the associated fiber count."  With category 0 = the `r` special cards, the
deck-level π law (`deckFiber_prob`) at the special-count macrostate is the BL
stationary mass — composed from the landed `deckFiber_prob` and
`BernoulliLaplaceGeneral.blStationary`, with the two-color bookkeeping
(`filter_card_twoColor`) discharged inline.  This is the T2 ↔ BL-law bridge: the
two two-pile/two-color laws now provably coincide, not merely resemble. -/

/-- Two-color bookkeeping: with two categories, the category-1 card count is the
    complement of the category-0 count. -/
theorem filter_card_twoColor (N : Nat) (color : Fin N → Fin 2) :
    (Finset.univ.filter (fun x : Fin N => color x = 1)).card =
      N - (Finset.univ.filter (fun x : Fin N => color x = 0)).card := by
  have hunion :
      (Finset.univ.filter (fun x : Fin N => color x = 0)) ∪
        (Finset.univ.filter (fun x : Fin N => color x = 1)) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      rcases finTwo_cases (color x) with h0 | h1
      · exact Or.inl h0
      · exact Or.inr h1
  have hdisj : Disjoint
      (Finset.univ.filter (fun x : Fin N => color x = 0))
      (Finset.univ.filter (fun x : Fin N => color x = 1)) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have ⟨_, hc0⟩ := Finset.mem_filter.mp hx0
    have ⟨_, hc1⟩ := Finset.mem_filter.mp hx1
    rw [hc0] at hc1
    exact absurd hc1 (by decide)
  have hcard : (Finset.univ.filter (fun x : Fin N => color x = 0)).card +
      (Finset.univ.filter (fun x : Fin N => color x = 1)).card = N := by
    have h := congrArg Finset.card hunion
    rw [Finset.card_union_eq_card_add_card.mpr hdisj, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  omega

/-- **T2 two-pile/two-color π law = the BL stationary law.**  For a two-color
    deck whose category-0 card count is `r`, the deck-level π law (uniform-deck
    probability of the histogram `X`) at the admissible special-count macrostate
    is exactly the BL stationary mass — composed from `deckFiber_prob` and
    `blStationary`.  The admissibility preconditions (`X 0 ≤ r`,
    `X 1 ≤ N - r`) are what put the state in the BL state space
    (`blLo ≤ X 0 ≤ blHi`). -/
theorem deckFiber_prob_eq_blStationary {N m r : Nat} (hm : m ≤ N) (hr : r ≤ N)
    (color : Fin N → Fin 2)
    (hr0 : (Finset.univ.filter (fun x : Fin N => color x = 0)).card = r)
    (X : Fin 2 → Nat) (hX : X 0 + X 1 = m)
    (hXr : X 0 ≤ r) (hXl : X 1 ≤ N - r) :
    ((deckFiber N m hm color X).card : Rat) / (Nat.factorial N : Rat) =
      BernoulliLaplaceGeneral.blStationary N m r ⟨X 0, by
        constructor
        · rw [BernoulliLaplaceGeneral.blLo_eq_tsub]
          have h1 : m - X 0 ≤ N - r := by omega
          omega
        · rw [BernoulliLaplaceGeneral.blHi_def]
          omega⟩ := by
  have hrest : (Finset.univ.filter (fun x : Fin N => color x = 1)).card = N - r := by
    rw [filter_card_twoColor N color, hr0]
  have hX1 : X 1 = m - X 0 := by omega
  rw [deckFiber_prob N m hm color X, if_pos hX, hr0, hrest, hX1]
  unfold BernoulliLaplaceGeneral.blStationary
  push_cast
  rfl

/-! ## The valid two-pile/two-color histogram state space (the πK = π
formalization design — honest first leg)

The πK = π stationary-law identity (roadmap T5 line 176) quantifies over the
space of valid histograms: total size `m` with per-category counts bounded by
the total category counts `r0` (category 0) and `r1` (category 1).  The honest
`Finset`-carrier abbrev route (the `sizeNAllocSpace`-style abbrev — a `def`
wrapper would block `Fintype` instance synthesis), Fintype-wall-free. -/

/-- The valid two-pile/two-color histogram state space as a `Finset` carrier:
the histograms with total size `m` and per-category bounds `r0`, `r1`. -/
def validHistSet (N m r0 r1 : Nat) : Finset (Hist2 N) :=
  (Finset.univ : Finset (Hist2 N)).filter
    (fun X => (X 0).val + (X 1).val = m ∧ (X 0).val ≤ r0 ∧ (X 1).val ≤ r1)

/-- The valid two-pile histogram state space is nonempty whenever the totals
are legal (`m ≤ N` and `r0 + r1 = N`): any admissible total `m` admits a
histogram — `x0 = min m r0`, `x1 = m - x0` — so the filter set is inhabited. -/
theorem validHistSet_nonempty (N m r0 r1 : Nat) (hm : m ≤ N) (hr : r0 + r1 = N) :
    ∃ X : Hist2 N, (X 0).val + (X 1).val = m ∧ (X 0).val ≤ r0 ∧ (X 1).val ≤ r1 := by
  rcases Nat.lt_or_ge m r0 with h | h
  · -- m < r0: x0 = m, x1 = 0
    exact ⟨![⟨m, by omega⟩, ⟨0, by omega⟩], by simp, by simp; omega, by simp⟩
  · -- r0 ≤ m: x0 = r0, x1 = m - r0 (m - r0 ≤ r1 ⟺ m ≤ r0 + r1 = N)
    exact ⟨![⟨r0, by omega⟩, ⟨m - r0, by omega⟩], by simp; omega, by simp, by simp; omega⟩

noncomputable def validHistPi (N m r0 r1 : Nat) (X : Hist2 N) : Rat :=
  ((Nat.choose r0 (X 0).val * Nat.choose r1 (X 1).val : Nat) : Rat) / (Nat.choose N m : Rat)

theorem validHistPi_mass (N m r0 r1 : Nat) (hm : m ≤ N) (hr : r0 + r1 = N) :
    ∑ X ∈ validHistSet N m r0 r1, validHistPi N m r0 r1 X = 1 := by
  simp only [validHistSet] at *
  have hinj : Set.InjOn (fun X : Hist2 N => (X 0).val) (validHistSet N m r0 r1 : Set (Hist2 N)) := by
    intro X hX Y hY heq
    have heq' : (X 0).val = (Y 0).val := heq
    clear heq
    have hmemX := Finset.mem_filter.mp hX
    have hmemY := Finset.mem_filter.mp hY
    have hsumX : (X 0).val + (X 1).val = m := hmemX.2.1
    have hsumY : (Y 0).val + (Y 1).val = m := hmemY.2.1
    have hX1 : (X 1).val = m - (X 0).val := by omega
    have hY1 : (Y 1).val = m - (Y 0).val := by omega
    have h1 : (X 1).val = (Y 1).val := by rw [hX1, hY1]; omega
    have hX01 : X 1 = Y 1 := Fin.ext h1
    have hX0 : X 0 = Y 0 := Fin.ext heq'
    funext c
    fin_cases c
    · simp [hX0]
    · simp [hX01]
  have hrewrite : ∑ X ∈ validHistSet N m r0 r1, validHistPi N m r0 r1 X =
      ∑ X ∈ validHistSet N m r0 r1, ((Nat.choose r0 (X 0).val * Nat.choose r1 (m - (X 0).val) : Nat) : Rat) / (Nat.choose N m : Rat) := by
    apply Finset.sum_congr rfl
    intro X hX
    have hmemX := Finset.mem_filter.mp hX
    have hsumX : (X 0).val + (X 1).val = m := hmemX.2.1
    have hX1 : (X 1).val = m - (X 0).val := by omega
    unfold validHistPi
    rw [hX1]
  have hbiject : ∑ X ∈ validHistSet N m r0 r1, ((Nat.choose r0 (X 0).val * Nat.choose r1 (m - (X 0).val) : Nat) : Rat) / (Nat.choose N m : Rat) =
      ∑ i ∈ (validHistSet N m r0 r1).image (fun X : Hist2 N => (X 0).val), ((Nat.choose r0 i * Nat.choose r1 (m - i) : Nat) : Rat) / (Nat.choose N m : Rat) := by
    rw [Finset.sum_image hinj]
  have himg : (validHistSet N m r0 r1).image (fun X : Hist2 N => (X 0).val) =
      (Finset.range (m + 1)).filter (fun i => i ≤ r0 ∧ m - i ≤ r1) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨X, hX, hxi⟩
      subst hxi
      have hmemX := Finset.mem_filter.mp hX
      have hsumX : (X 0).val + (X 1).val = m := hmemX.2.1
      have hlt : (X 0).val < m + 1 := by omega
      refine ⟨hlt, hmemX.2.2.1, ?_⟩
      have hX1 : (X 1).val = m - (X 0).val := by omega
      have hX1' := hmemX.2.2.2
      rw [hX1] at hX1'
      exact hX1'
    · rintro ⟨hi, hr0_i, hr1_i⟩
      refine ⟨![⟨i, by omega⟩, ⟨m - i, by omega⟩], ?_, rfl⟩
      simp only [validHistSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · simp; omega
      · simp; exact hr0_i
      · simp; omega
  have hvanish : ∀ i ∈ Finset.range (m + 1), ¬(i ≤ r0 ∧ m - i ≤ r1) →
      (Nat.choose r0 i * Nat.choose r1 (m - i) : Nat) = 0 := by
    intro i hi hneg
    rcases not_and_or.mp hneg with h0 | h0
    · have hlt : r0 < i := not_le.mp h0
      rw [Nat.choose_eq_zero_of_lt hlt]; simp
    · have hlt : r1 < m - i := not_le.mp h0
      rw [Nat.choose_eq_zero_of_lt hlt]; simp
  have hrange : ∑ i ∈ (Finset.range (m + 1)).filter (fun i => i ≤ r0 ∧ m - i ≤ r1),
      ((Nat.choose r0 i * Nat.choose r1 (m - i) : Nat) : Rat) =
      ((∑ i ∈ Finset.range (m + 1), (Nat.choose r0 i * Nat.choose r1 (m - i) : Nat)) : Rat) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hP : i ≤ r0 ∧ m - i ≤ r1
    · rw [if_pos hP]
    · rw [if_neg hP]
      have hv := hvanish i hi hP
      simp [hv]
  have H : ∑ i ∈ Finset.range (m + 1), (Nat.choose r0 i * Nat.choose r1 (m - i) : Nat) = Nat.choose N m := by
    have key := Nat.add_choose_eq r0 r1 m
    rw [hr] at key
    rw [Finset.Nat.antidiagonal_eq_image] at key
    have inj : Set.InjOn (fun i : Nat => (i, m - i)) ((Finset.range (m + 1)) : Set Nat) := by
      intro i _ j _ hij
      exact (Prod.mk.inj hij).1
    rw [Finset.sum_image inj] at key
    exact key.symm
  have hfinal : ∑ X ∈ validHistSet N m r0 r1, validHistPi N m r0 r1 X = 1 := by
    rw [hrewrite, hbiject, himg]
    rw [(Finset.sum_div _ _ _).symm]
    rw [hrange]
    rw [← Nat.cast_sum, H]
    have hpos : (Nat.choose N m : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos hm))
    rw [div_self hpos]
  exact hfinal

/-! ## The histogram-level kernel (πK = π design, step c)

The `∑_{a,b}`-over-preimages reduction of the landed `lumpedTransition`
(T5 two-pile transition) to the valid two-pile/two-color histogram state space:
a histogram `X'` is reached from `X` via a `k`-swap exactly when the removed
(`a`) and added (`b`) per-category counts (`a .1 + a .2 = b .1 + b .2 = k`)
satisfy `X'_0 = X_0 - a_0 + b_0` and `X'_1 = X_1 - a_1 + b_1` — each `(a, b)`
pair contributes the two-pile-exchange numerator
`choose(X_0, a_0)·choose(X_1, a_1)·choose(r_0 - X_0, b_0)·choose(r_1 - X_1, b_1)`
normalized by the universal denominator `choose(m, k)·choose(N - m, k)`.

**Status (landed, this session):** the **row-sum** half — `∑_{X'} K(X→X') = 1` —
is proved (see `histogramTransition_rowSum` below).  The **stationary-law**
half — `∑_{X} π(X)·K(X→X') = π(X')` (the T5-line-176 πK = π claim) — remains
the remaining T2 item; it is a harder, non-uniform-π refinement of this identity.
Numerically confirmed across 9 cases (see the strategy note). -/

/-- The histogram-level two-pile exchange kernel over the valid histogram
state space: for a valid `X` (total `m`, per-category bounds `r0`/`r1`), the
transition mass from `X` to `X'` via a `k`-swap, summed over every per-category
removed/added pair `(a, b)` with total `k` — values as `Nat`, no subtypes in
the sum.  The `Finset.antidiagonal k` carrier enumerates exactly the pairs
`(i, j)` with `i + j = k`. -/
noncomputable def histogramTransition (N m r0 r1 k : Nat) (X X' : Hist2 N) : Rat :=
  ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k,
    if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
    then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
          ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
    else 0

/-! ## The histogram-level row-sum identity

**Result (landed):** for a valid `X`, `∑_{X'} histogramTransition N m r0 r1 k X X' = 1` — the
histogram-level two-pile exchange kernel is a genuine probability kernel over the valid
histogram state space.  This settles the row-sum half of the T2/T5 kernel-landing target
(the πK = π stationary-law identity — T5 line 176 — remains the remaining T2 item; it is a
harder, non-uniform-π refinement of the identity `∑_X π(X)·K(X→X') = π(X')`).

Route: Fubini over `(X', a, b)` (the preimage re-indexing — `X' = X - a + b` is a bijection in
`X'` for fixed `(a, b)`), the per-(`a,b`) inner sum collapses to the single-term value
(`X' = H`, the one valid histogram determined by `X, a, b`), and the remaining `(a, b)`-sum
factors as `∑_a choose(X_0, a_0)·choose(X_1, a_1)` (over the antidiagonal `k`) = `choose(m, k)`
times `∑_b choose(r_0 - X_0, b_0)·choose(r_1 - X_1, b_1)` (the same shape with `r - X`) =
`choose(N - m, k)`, normalized by `choose(m, k)·choose(N - m, k)` = 1.

The `by_cases hw : ... = 0` split discharges the degenerate case where the per-`(a, b)`
target numerator vanishes; otherwise `X - a + b` is forced to be exactly the valid histogram
`H`, and the sum has a single survivor `X' = H`.  The `b ≤ k` bounds (`hb1`, `hb2`) and the
per-category bounds (`hX0le`/`hX1le` via the constraint `total(X) = m`) keep the `Nat.choose`
arguments in range. -/

/-- **Row-sum 1 for the histogram-level two-pile exchange kernel** over the valid histogram
state space `{X | total(X) = m, per-category bounds r0/r1}`. -/
theorem histogramTransition_rowSum (N m r0 r1 k : Nat)
    (hm : m ≤ N) (hr : r0 + r1 = N)
    (hk1 : k ≤ m) (hk2 : k ≤ N - m)
    (X : Hist2 N) (hX : X ∈ validHistSet N m r0 r1) :
    ∑ X' ∈ validHistSet N m r0 r1, histogramTransition N m r0 r1 k X X' = 1 := by
  rcases Finset.mem_filter.mp hX with ⟨_, hmem⟩
  have hsum : (X 0).val + (X 1).val = m := hmem.1
  have hX0 : (X 0).val ≤ r0 := hmem.2.1
  have hX1 : (X 1).val ≤ r1 := hmem.2.2
  have hD : (Nat.choose m k * Nat.choose (N - m) k : Nat) ≠ 0 := by
    refine Nat.mul_ne_zero ?_ ?_
    exact Nat.ne_of_gt (Nat.choose_pos hk1)
    exact Nat.ne_of_gt (Nat.choose_pos hk2)
  -- ===== Fubini =====
  simp only [histogramTransition]
  have hFubini : (∑ X' ∈ validHistSet N m r0 r1, ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k,
        if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
        then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
            ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
        else 0) =
      ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k, ∑ X' ∈ validHistSet N m r0 r1,
        if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
        then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
            ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
        else 0 := by
    rw [Finset.sum_comm (s := validHistSet N m r0 r1) (t := Finset.antidiagonal k)
          (f := fun X' a => ∑ b ∈ Finset.antidiagonal k,
            if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
            then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
                Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
                ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
            else 0)]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm (s := validHistSet N m r0 r1) (t := Finset.antidiagonal k)
          (f := fun X' b => if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
            then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
                Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
                ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
            else 0)]
  rw [hFubini]
  -- ===== inner sum: per (a,b), ∑ X' → W/D =====
  have hinner : ∀ a ∈ Finset.antidiagonal k, ∀ b ∈ Finset.antidiagonal k,
      (∑ X' ∈ validHistSet N m r0 r1,
        if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
        then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
            ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
        else 0) =
      ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
        Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) := by
    intro a ha b hb
    have haa := Finset.mem_antidiagonal.mp ha
    have hbb := Finset.mem_antidiagonal.mp hb
    have hb1 : b.1 ≤ k := by omega
    have hb2 : b.2 ≤ k := by omega
    by_cases hw : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
        Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 = 0
    · have hw0 : (Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
          Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat).cast = 0 := by simp [hw]
      have hpos : ∀ X' ∈ validHistSet N m r0 r1,
          (if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
           then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
               Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
               ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
           else 0) = 0 := by
        intro X' _
        by_cases hev : (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
        · rw [ite_eq_left hev]
          simp [hw]
        · rw [ite_eq_right hev]
      rw [Finset.sum_eq_zero hpos]
      simp [hw]
    · have hw' : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
          Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 ≠ 0 := hw
      have hA0 : a.1 ≤ (X 0).val := by
        by_contra h
        have hnot : (X 0).val < a.1 := by omega
        have hz := Nat.choose_eq_zero_of_lt hnot
        have hW : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 = 0 := by rw [hz]; simp
        exact hw' hW
      have hA1 : a.2 ≤ (X 1).val := by
        by_contra h
        have hnot : (X 1).val < a.2 := by omega
        have hz := Nat.choose_eq_zero_of_lt hnot
        have hW : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 = 0 := by rw [hz]; simp
        exact hw' hW
      have hB0 : b.1 ≤ r0 - (X 0).val := by
        by_contra h
        have hnot : r0 - (X 0).val < b.1 := by omega
        have hz := Nat.choose_eq_zero_of_lt hnot
        have hW : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 = 0 := by rw [hz]; simp
        exact hw' hW
      have hB1 : b.2 ≤ r1 - (X 1).val := by
        by_contra h
        have hnot : r1 - (X 1).val < b.2 := by omega
        have hz := Nat.choose_eq_zero_of_lt hnot
        have hW : Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 = 0 := by rw [hz]; simp
        exact hw' hW
      have shiftvalid : ∃ X' ∈ validHistSet N m r0 r1, (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2 := by
        refine ⟨![⟨(X 0).val - a.1 + b.1, by omega⟩, ⟨(X 1).val - a.2 + b.2, by omega⟩], ?_, rfl, rfl⟩
        simp only [validHistSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · simp; omega
        · simp; omega
        · simp; omega
      obtain ⟨H, hH, hv0, hv1⟩ := shiftvalid
      have key : ∀ X' ∈ validHistSet N m r0 r1,
          (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2 → X' = H := by
        intro X' _ hmatch
        have h0' : X' 0 = H 0 := Fin.ext (by rw [hmatch.1, hv0])
        have h1' : X' 1 = H 1 := Fin.ext (by rw [hmatch.2, hv1])
        funext c
        fin_cases c
        · simp [h0']
        · simp [h1']
      rw [Finset.sum_eq_single H (fun X' hS hdiff => by
            rw [ite_eq_right (fun hmatch => by
              have h := key X' hS hmatch
              exact hdiff h)])
          (fun h => absurd hH h)]
      have hh : (H 0).val = (X 0).val - a.1 + b.1 ∧ (H 1).val = (X 1).val - a.2 + b.2 := ⟨hv0, hv1⟩
      rw [ite_eq_left hh]
  -- rewrite the (a,b)-sum
  rw [show (∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k, ∑ X' ∈ validHistSet N m r0 r1,
        if (X' 0).val = (X 0).val - a.1 + b.1 ∧ (X' 1).val = (X 1).val - a.2 + b.2
        then ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
            Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
            ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
        else 0) =
      ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k,
        ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
        Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)
    from Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hinner a ha b hb))]
  -- ===== factorization =====
  have hinj_a : Set.InjOn (fun i : Nat => (i, k - i)) ((Finset.range (k + 1)) : Set Nat) := by
    intro i _ j _ hij
    exact congrArg Prod.fst hij
  have hc_nat : ∑ a ∈ Finset.antidiagonal k, (Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) =
      Nat.choose m k := by
    rw [Finset.Nat.antidiagonal_eq_image, Finset.sum_image hinj_a]
    have hv := Nat.add_choose_eq (X 0).val (X 1).val k
    rw [Finset.Nat.antidiagonal_eq_image, Finset.sum_image hinj_a] at hv
    rw [hsum] at hv
    exact hv.symm
  have hd_nat : ∑ b ∈ Finset.antidiagonal k, (Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) =
      Nat.choose (N - m) k := by
    rw [Finset.Nat.antidiagonal_eq_image, Finset.sum_image hinj_a]
    have hv := Nat.add_choose_eq (r0 - (X 0).val) (r1 - (X 1).val) k
    rw [Finset.Nat.antidiagonal_eq_image, Finset.sum_image hinj_a] at hv
    rw [show (r0 - (X 0).val) + (r1 - (X 1).val) = N - m from by omega] at hv
    exact hv.symm
  have hc_rat : (∑ a ∈ Finset.antidiagonal k, ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) : Rat)) = (Nat.choose m k : Rat) := by
    rw [← Nat.cast_sum, hc_nat]
  have hd_rat : (∑ b ∈ Finset.antidiagonal k, ((Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat)) = (Nat.choose (N - m) k : Rat) := by
    rw [← Nat.cast_sum, hd_nat]
  have step1 : ∀ a b : Nat × Nat, ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
        Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) =
      ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) : Rat) *
      ((Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
      ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) := by
    intro a b; push_cast; ring
  have hsplit : ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k, ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 *
        Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) =
      ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k,
        ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) : Rat) *
        ((Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact step1 a b
  rw [hsplit]
  have hfac : ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal k,
        ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) : Rat) *
        ((Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
        ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) =
      ∑ a ∈ Finset.antidiagonal k, ((Nat.choose (X 0).val a.1 * Nat.choose (X 1).val a.2 : Nat) : Rat) *
        (∑ b ∈ Finset.antidiagonal k, ((Nat.choose (r0 - (X 0).val) b.1 * Nat.choose (r1 - (X 1).val) b.2 : Nat) : Rat) /
          ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  rw [hfac, ← Finset.sum_mul, ← Finset.sum_div]
  rw [hc_rat, hd_rat]
  have e : (Nat.choose m k : Rat) * ((Nat.choose (N - m) k : Rat) / ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat)) =
      ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) / ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) := by
    push_cast
    ring
  rw [e]
  have hD' : ((Nat.choose m k * Nat.choose (N - m) k : Nat) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hD
  exact div_self hD'

end FiniteDeck
end Shufflemath

