module

public import Shufflemath.FiniteDeck.Histograms
public import Shufflemath.FiniteDeck.Piles

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

end FiniteDeck
end Shufflemath
