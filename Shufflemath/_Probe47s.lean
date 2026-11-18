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

namespace _Probe47s

/-!
# pairCountByConstSub — count `(x, y) ∈ s ×ˢ t` with `(c - f x) + g y = n`

The combinatorial engine the **per-deck** Bernoulli-Laplace target actually
needs.  Via `newLeftOriginalCount_eq`, counting `(L, R)` with
`(newLeftCards d L R ∩ leftOrigSet).card = n` is counting those with
`(x - markedInLeft d L) + markedInRight d R = n` (where `x = leftOriginalCount d`),
which is exactly this `(c - f p.1) + g p.2 = n` form (with `c = x`).

The fiber is `s.filter(f = a) ×ˢ t.filter ((c - a) + g · = n)` — the `g`-condition
is kept as a raw filter (never *solved* for `g y`), so there is no
Nat-subtraction-solvability trap.  The filtered set is the disjoint big-union
over `a ∈ s.image f`, so
`# = ∑_{a ∈ s.image f} #(s.filter(f = a)) · #(t.filter ((c - a) + g · = n))`.
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The `a`-fiber: pairs whose first coordinate has `f`-value `a` and which
    satisfy `(c - a) + g (second) = n`. -/
def fiberCS (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (c n a : Nat) :
    Finset (α × β) :=
  (s.filter (fun x => f x = a)) ×ˢ (t.filter (fun y => (c - a) + g y = n))

/-- The `(c - f) + g = n`-filtered product set equals the big-union of the fibers. -/
theorem filterCS_eq_biUnion (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    (s ×ˢ t).filter (fun p => (c - f p.1) + g p.2 = n) =
      (s.image f).biUnion fun a => fiberCS s t f g c n a := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rcases hp with ⟨⟨hx, hy⟩, hcond⟩
    refine Finset.mem_biUnion.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx, ?_⟩
    simp only [fiberCS, Finset.mem_product, Finset.mem_filter]
    simp [hx, hy, hcond]
  · intro hp
    have h : ∃ a, a ∈ s.image f ∧ p ∈ fiberCS s t f g c n a := by
      simpa using Finset.mem_biUnion.mp hp
    rcases h with ⟨a, _hmem, hxy⟩
    have hpL : p.1 ∈ s.filter (fun x => f x = a) := (Finset.mem_product.mp hxy).1
    have hpR : p.2 ∈ t.filter (fun y => (c - a) + g y = n) := (Finset.mem_product.mp hxy).2
    have hx : p.1 ∈ s := (Finset.mem_filter.mp hpL).1
    have hfa : f p.1 = a := (Finset.mem_filter.mp hpL).2
    have hy : p.2 ∈ t := (Finset.mem_filter.mp hpR).1
    have hcond : (c - a) + g p.2 = n := (Finset.mem_filter.mp hpR).2
    have hprod : p ∈ s ×ˢ t := by simp only [Finset.mem_product]; exact ⟨hx, hy⟩
    have hgoal : (c - f p.1) + g p.2 = n := by rw [hfa]; exact hcond
    exact Finset.mem_filter.mpr ⟨hprod, hgoal⟩

/-- The fibers are pairwise disjoint: different `a`-values give disjoint
    `s.filter(f = ·)` parts, and disjointness propagates through the product. -/
theorem fibersCS_pairwiseDisjoint (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    ((s.image f) : Set Nat).PairwiseDisjoint fun a => fiberCS s t f g c n a := by
  intro a _hmemA b _hmemB hne
  have hdisjL : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x = b)) := by
    rw [Finset.disjoint_left]
    intro x hx
    have hfx : f x = a := (Finset.mem_filter.mp hx).2
    intro hxb
    have hfxb : f x = b := (Finset.mem_filter.mp hxb).2
    exact hne (hfx.symm.trans hfxb)
  change Disjoint (fiberCS s t f g c n a) (fiberCS s t f g c n b)
  simp only [fiberCS]
  rw [Finset.disjoint_product]
  exact Or.inl hdisjL

/-- The count of `(x, y) ∈ s ×ˢ t` with `(c - f x) + g y = n`, decomposed over
    the distinct values of `f`. -/
theorem pairCountByConstSub (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    ((s ×ˢ t).filter (fun p => (c - f p.1) + g p.2 = n)).card =
      (s.image f).sum fun a =>
        (s.filter (fun x => f x = a)).card * (t.filter (fun y => (c - a) + g y = n)).card := by
  rw [filterCS_eq_biUnion]
  rw [Finset.card_biUnion (h := fibersCS_pairwiseDisjoint s t f g c n)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberCS, Finset.card_product]

end _Probe47s
end Shufflemath
