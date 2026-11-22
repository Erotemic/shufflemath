module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.Dobrushin
public import Shufflemath.TotalVariation
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
namespace Shufflemath
namespace Dobrushin

theorem rowTV_le_one_sub_minMass
    [Fintype α] [DecidableEq α] [Fintype β] (K : FiniteKernel α β) (i j : α) (z : β) :
    rowTV K i j ≤ 1 - min (Dist.mass (K i) z) (Dist.mass (K j) z) := by
  have hnonneg : ∀ y, 0 ≤ min (Dist.mass (K i) y) (Dist.mass (K j) y) := by
    intro y
    exact le_min (Dist.mass_nonneg (K i) y) (Dist.mass_nonneg (K j) y)
  have hsum_ge : min (Dist.mass (K i) z) (Dist.mass (K j) z) ≤
      (Finset.univ : Finset β).sum (fun y => min (Dist.mass (K i) y) (Dist.mass (K j) y)) :=
    Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ z)
  calc
    rowTV K i j = 1 - (Finset.univ : Finset β).sum (fun y => min (Dist.mass (K i) y) (Dist.mass (K j) y)) := by
      rw [rowTV, Dist.tv_eq_one_sub_overlap]
    _ ≤ 1 - min (Dist.mass (K i) z) (Dist.mass (K j) z) := by
      apply sub_le_sub_left
      exact hsum_ge

end Dobrushin
end Shufflemath
