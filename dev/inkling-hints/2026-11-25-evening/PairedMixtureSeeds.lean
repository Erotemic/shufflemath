module

public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.InklingHints

/-! Uncompiled helper for the G8 adjacent-transposition coupling. Prove with
abstract finite carriers; the huge allocation/deck Fintype never enters the
proof. Do not make this helper a prerequisite for G5. -/

theorem pairedMixtureTV {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (μ : Dist X) (K L : FiniteKernel X Y) :
    Dist.tv (FiniteKernel.apply μ K) (FiniteKernel.apply μ L) ≤
      ∑ x : X, Dist.mass μ x * Dist.tv (K x) (L x) := by
  have hpoint (y : Y) :
      |Dist.mass (FiniteKernel.apply μ K) y - Dist.mass (FiniteKernel.apply μ L) y| ≤
        ∑ x : X, Dist.mass μ x * |Dist.mass (K x) y - Dist.mass (L x) y| := by
    rw [FiniteKernel.apply_mass, FiniteKernel.apply_mass, ← Finset.sum_sub_distrib]
    have heq : (∑ x : X, (Dist.mass μ x * Dist.mass (K x) y -
        Dist.mass μ x * Dist.mass (L x) y)) =
          ∑ x : X, Dist.mass μ x * (Dist.mass (K x) y - Dist.mass (L x) y) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq]
    calc
      _ ≤ ∑ x : X, |Dist.mass μ x * (Dist.mass (K x) y - Dist.mass (L x) y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [abs_mul, abs_of_nonneg (Dist.mass_nonneg μ x)]
  unfold Dist.tv vectorTV
  calc
    _ ≤ (1 / 2 : Rat) * ∑ y : Y,
        ∑ x : X, Dist.mass μ x * |Dist.mass (K x) y - Dist.mass (L x) y| := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => hpoint y))
      norm_num
    _ = (1 / 2 : Rat) * ∑ x : X,
        ∑ y : Y, Dist.mass μ x * |Dist.mass (K x) y - Dist.mass (L x) y| := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum]
      ring

/-- A generic pushforward equality expressed as application of a deterministic
kernel, useful for the coupled first-step representation. -/
theorem apply_map_kernel {X Y Z : Type*} (μ : Dist X) (f : X → Y) (K : FiniteKernel Y Z) :
    FiniteKernel.apply (μ.map f) K = FiniteKernel.apply μ (fun x => K (f x)) := by
  rw [← GSR.apply_deterministic, FiniteKernel.apply_comp, GSR.comp_deterministic_left]

end Shufflemath.InklingHints
