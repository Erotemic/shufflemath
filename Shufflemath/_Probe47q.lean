module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.BernoulliLaplaceGeneral
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open Finset

namespace _Probe47q

/-!
# pairCountBySum — count `(x, y) ∈ s ×ˢ t` by the value of `f x + g y`

The combinatorial engine for the per-deck Bernoulli-Laplace bridge.  The
filtered product set `{p | f p.1 + g p.2 = n}` is the big-union, over the
distinct values `a` taken by `f` on `s`, of the (subtraction-free) fibers
`s.filter(f = a) ×ˢ t.filter (a + g · = n)`; the fibers are pairwise disjoint,
so the count is `∑_{a ∈ s.image f} #(s.filter(f = a)) · #(t.filter (a + g · = n))`.

(Using `a + g y = n` rather than `g y = n - a` avoids a Nat-subtraction trap:
the two are equivalent only when `a ≤ n`.)
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The `a`-fiber: pairs whose first coordinate has `f`-value `a` and which
    satisfy `a + g (second) = n`. -/
def fiber (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (n a : Nat) :
    Finset (α × β) :=
  (s.filter (fun x => f x = a)) ×ˢ (t.filter (fun y => a + g y = n))

/-- The filtered product set equals the big-union of the fibers over `s.image f`. -/
theorem filter_eq_biUnion (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (n : Nat) :
    (s ×ˢ t).filter (fun p => f p.1 + g p.2 = n) =
      (s.image f).biUnion fun a => fiber s t f g n a := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rcases hp with ⟨⟨hx, hy⟩, hsum⟩
    refine Finset.mem_biUnion.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx, ?_⟩
    simp only [fiber, Finset.mem_product, Finset.mem_filter]
    simp [hx, hy, hsum]
  · intro hp
    have h : ∃ a, a ∈ s.image f ∧ p ∈ fiber s t f g n a := by
      simpa using Finset.mem_biUnion.mp hp
    rcases h with ⟨a, _hmem, hxy⟩
    have hpL : p.1 ∈ s.filter (fun x => f x = a) := (Finset.mem_product.mp hxy).1
    have hpR : p.2 ∈ t.filter (fun y => a + g y = n) := (Finset.mem_product.mp hxy).2
    have hx : p.1 ∈ s := (Finset.mem_filter.mp hpL).1
    have hfa : f p.1 = a := (Finset.mem_filter.mp hpL).2
    have hy : p.2 ∈ t := (Finset.mem_filter.mp hpR).1
    have hsum : a + g p.2 = n := (Finset.mem_filter.mp hpR).2
    have hprod : p ∈ s ×ˢ t := by simp only [Finset.mem_product]; exact ⟨hx, hy⟩
    have hcond : f p.1 + g p.2 = n := by rw [hfa]; exact hsum
    exact Finset.mem_filter.mpr ⟨hprod, hcond⟩

/-- The fibers are pairwise disjoint: different `a`-values give disjoint
    `s.filter(f = ·)` parts, and disjointness propagates through the product. -/
theorem fibers_pairwiseDisjoint (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (n : Nat) :
    ((s.image f) : Set Nat).PairwiseDisjoint fun a => fiber s t f g n a := by
  intro a _hmemA b _hmemB hne
  have hdisjL : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x = b)) := by
    rw [Finset.disjoint_left]
    intro x hx
    have hfx : f x = a := (Finset.mem_filter.mp hx).2
    intro hxb
    have hfxb : f x = b := (Finset.mem_filter.mp hxb).2
    exact hne (hfx.symm.trans hfxb)
  change Disjoint (fiber s t f g n a) (fiber s t f g n b)
  simp only [fiber]
  rw [Finset.disjoint_product]
  exact Or.inl hdisjL

/-- The count of `(x, y) ∈ s ×ˢ t` with `f x + g y = n`, decomposed over the
    distinct values of `f`. -/
theorem pairCountBySum (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (n : Nat) :
    ((s ×ˢ t).filter (fun p => f p.1 + g p.2 = n)).card =
      (s.image f).sum fun a =>
        (s.filter (fun x => f x = a)).card * (t.filter (fun y => a + g y = n)).card := by
  rw [filter_eq_biUnion]
  rw [Finset.card_biUnion (h := fibers_pairwiseDisjoint s t f g n)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiber, Finset.card_product]

end _Probe47q
end Shufflemath
