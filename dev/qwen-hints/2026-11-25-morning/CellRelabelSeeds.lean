module

public import Shufflemath.FiniteDeck.Partition
public import Shufflemath.FiniteDeck.Histograms
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.FiniteDeck.QwenMorningHints

/-!
UNCOMPILED candidate: derive histogram-fiber transitivity by applying the
already-compiled partition gluing equivalence to (pile, category) CELLS.
No dependent Fintype on a product of permutation groups is needed here.
-/

/-- Refine a partition by its category map. -/
def cell {N p c : Nat} (C : Fin p → Finset (Fin N)) (color : Fin N → Fin c)
    (ij : Fin p × Fin c) : Finset (Fin N) :=
  (C ij.1).filter (fun x => color x = ij.2)

theorem cells_partition {N p c : Nat} (C : Fin p → Finset (Fin N))
    (color : Fin N → Fin c) (hC : IsPartition C) : IsPartition (cell C color) := by
  constructor
  · intro x
    obtain ⟨i, hi⟩ := hC.1 x
    exact ⟨(i, color x), Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  · intro a b x ha hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact Prod.ext (hC.2 a.1 b.1 x ha'.1 hb'.1) (ha'.2.symm.trans hb'.2)

/-- Same histogram implies equal cell cardinalities. Glue an arbitrary bijection
between each pair of equal-size cells to obtain a color-preserving relabeling. -/
noncomputable def cellEquiv {N p c : Nat} (C D : Fin p → Finset (Fin N))
    (color : Fin N → Fin c)
    (h : ∀ i j, lump C color i j = lump D color i j)
    (ij : Fin p × Fin c) : ↥(cell C color ij) ≃ ↥(cell D color ij) := by
  classical
  apply Fintype.equivOfCardEq
  simpa only [Fintype.card_coe, cell, lump] using h ij.1 ij.2

noncomputable def cellRelabel {N p c : Nat} (C D : Fin p → Finset (Fin N))
    (color : Fin N → Fin c) (hC : IsPartition C) (hD : IsPartition D)
    (h : ∀ i j, lump C color i j = lump D color i j) : Equiv.Perm (Fin N) :=
  glueBlocks (cell C color) (cell D color) (cells_partition C color hC)
    (cells_partition D color hD) (cellEquiv C D color h)

theorem cellRelabel_mem {N p c : Nat} (C D : Fin p → Finset (Fin N))
    (color : Fin N → Fin c) (hC : IsPartition C) (hD : IsPartition D)
    (h : ∀ i j, lump C color i j = lump D color i j)
    (i : Fin p) (x : Fin N) (hx : x ∈ C i) :
    cellRelabel C D color hC hD h x ∈ D i ∧
      color (cellRelabel C D color hC hD h x) = color x := by
  have hxcell : x ∈ cell C color (i, color x) := Finset.mem_filter.mpr ⟨hx, rfl⟩
  have heq : cellRelabel C D color hC hD h x =
      (cellEquiv C D color h (i, color x) ⟨x, hxcell⟩).val := by
    exact glueBlocks_apply_member (cell C color) (cell D color)
      (cells_partition C color hC) (cells_partition D color hD)
      (cellEquiv C D color h) (i, color x) x hxcell
  rw [heq]
  exact Finset.mem_filter.mp (cellEquiv C D color h (i, color x) ⟨x, hxcell⟩).property

theorem cellRelabel_color {N p c : Nat} (C D : Fin p → Finset (Fin N))
    (color : Fin N → Fin c) (hC : IsPartition C) (hD : IsPartition D)
    (h : ∀ i j, lump C color i j = lump D color i j) (x : Fin N) :
    color (cellRelabel C D color hC hD h x) = color x := by
  obtain ⟨i, hx⟩ := hC.1 x
  exact (cellRelabel_mem C D color hC hD h i x hx).2

theorem cellRelabel_image {N p c : Nat} (C D : Fin p → Finset (Fin N))
    (color : Fin N → Fin c) (hC : IsPartition C) (hD : IsPartition D)
    (h : ∀ i j, lump C color i j = lump D color i j) (i : Fin p) :
    (C i).image (cellRelabel C D color hC hD h) = D i := by
  let g := cellRelabel C D color hC hD h
  apply Finset.ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (cellRelabel_mem C D color hC hD h i x hx).1
  · intro hy
    obtain ⟨x, rfl⟩ := g.surjective y
    obtain ⟨j, hj⟩ := hC.1 x
    have hj' : g x ∈ D j := (cellRelabel_mem C D color hC hD h j x hj).1
    have hji := hD.2 j i (g x) hj' hy
    rw [hji] at hj
    exact Finset.mem_image.mpr ⟨x, hj, rfl⟩

end Shufflemath.FiniteDeck.QwenMorningHints
