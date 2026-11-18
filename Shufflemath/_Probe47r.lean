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

namespace _Probe47r

/-!
# pairCountByAffine — count `(x, y) ∈ s ×ˢ t` by `g y = c + f x`

The combinatorial engine for the *per-deck* Bernoulli-Laplace bridge.  Unlike
`_Probe47q.pairCountBySum` (condition `f x + g y = n`), this handles the
**affine** condition `g y = c + f x`, which is what the per-deck target needs:
after the `newLeftOriginalCount_eq` bridge, counting `(L, R)` with
`(newLeftCards d L R ∩ leftOrig50).card = n` is counting those with
`markedInRight d R = (n - x) + markedInLeft d L` (where `x = leftOriginalCount d`).

The filtered set is the disjoint big-union, over `a` in `s.image f`, of the
fibers `s.filter(f = a) ×ˢ t.filter(g = c + a)`, so
`# = ∑_{a ∈ s.image f} #(s.filter(f = a)) · #(t.filter(g = c + a))`.
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The `a`-fiber: pairs whose first coordinate has `f`-value `a` and whose
    second coordinate has `g`-value `c + a`. -/
def fiberA (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (c a : Nat) :
    Finset (α × β) :=
  (s.filter (fun x => f x = a)) ×ˢ (t.filter (fun y => g y = c + a))

/-- The affine-filtered product set equals the big-union of the fibers. -/
theorem filterA_eq_biUnion (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c : Nat) :
    (s ×ˢ t).filter (fun p => g p.2 = c + f p.1) =
      (s.image f).biUnion fun a => fiberA s t f g c a := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rcases hp with ⟨⟨hx, hy⟩, hcond⟩
    refine Finset.mem_biUnion.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx, ?_⟩
    simp only [fiberA, Finset.mem_product, Finset.mem_filter]
    simp [hx, hy, hcond]
  · intro hp
    have h : ∃ a, a ∈ s.image f ∧ p ∈ fiberA s t f g c a := by
      simpa using Finset.mem_biUnion.mp hp
    rcases h with ⟨a, _hmem, hxy⟩
    have hpL : p.1 ∈ s.filter (fun x => f x = a) := (Finset.mem_product.mp hxy).1
    have hpR : p.2 ∈ t.filter (fun y => g y = c + a) := (Finset.mem_product.mp hxy).2
    have hx : p.1 ∈ s := (Finset.mem_filter.mp hpL).1
    have hfa : f p.1 = a := (Finset.mem_filter.mp hpL).2
    have hy : p.2 ∈ t := (Finset.mem_filter.mp hpR).1
    have hcond : g p.2 = c + a := (Finset.mem_filter.mp hpR).2
    have hprod : p ∈ s ×ˢ t := by simp only [Finset.mem_product]; exact ⟨hx, hy⟩
    have hgoal : g p.2 = c + f p.1 := by rw [hfa]; exact hcond
    exact Finset.mem_filter.mpr ⟨hprod, hgoal⟩

/-- The fibers are pairwise disjoint: different `a`-values give disjoint
    `s.filter(f = ·)` parts, and disjointness propagates through the product. -/
theorem fibersA_pairwiseDisjoint (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c : Nat) :
    ((s.image f) : Set Nat).PairwiseDisjoint fun a => fiberA s t f g c a := by
  intro a _hmemA b _hmemB hne
  have hdisjL : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x = b)) := by
    rw [Finset.disjoint_left]
    intro x hx
    have hfx : f x = a := (Finset.mem_filter.mp hx).2
    intro hxb
    have hfxb : f x = b := (Finset.mem_filter.mp hxb).2
    exact hne (hfx.symm.trans hfxb)
  change Disjoint (fiberA s t f g c a) (fiberA s t f g c b)
  simp only [fiberA]
  rw [Finset.disjoint_product]
  exact Or.inl hdisjL

/-- The count of `(x, y) ∈ s ×ˢ t` with `g y = c + f x`, decomposed over the
    distinct values of `f`. -/
theorem pairCountByAffine (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c : Nat) :
    ((s ×ˢ t).filter (fun p => g p.2 = c + f p.1)).card =
      (s.image f).sum fun a =>
        (s.filter (fun x => f x = a)).card * (t.filter (fun y => g y = c + a)).card := by
  rw [filterA_eq_biUnion]
  rw [Finset.card_biUnion (h := fibersA_pairwiseDisjoint s t f g c)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberA, Finset.card_product]

end _Probe47r
end Shufflemath
