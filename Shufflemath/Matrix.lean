import Shufflemath.Finite
import Mathlib.LinearAlgebra.Matrix.Stochastic

namespace Shufflemath
namespace FiniteKernel

variable {alpha beta : Type*}

/-- Forget a finite kernel to its rational transition matrix. -/
def toMatrix (K : FiniteKernel alpha beta) : Matrix alpha beta Rat :=
  fun x y => Dist.mass (K x) y

/-- Every square finite kernel gives a row-stochastic matrix. -/
theorem toMatrix_mem_rowStochastic
    [Fintype alpha] [DecidableEq alpha]
    (K : FiniteKernel alpha alpha) :
    toMatrix K ∈ Matrix.rowStochastic Rat alpha := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    exact Dist.mass_nonneg (K i) j
  · intro i
    exact Dist.sum_mass (K i)

/-- Build a semantic finite kernel from a row-stochastic rational matrix.

The matrix remains the computational representation; this constructor packages
its row-normalization proof into `Dist`. -/
noncomputable def ofRowStochastic
    [Fintype alpha] [DecidableEq alpha]
    (P : Matrix alpha alpha Rat)
    (hP : P ∈ Matrix.rowStochastic Rat alpha) : FiniteKernel alpha alpha :=
  fun x => Dist.ofFun
    (fun y => P x y)
    (fun y => Matrix.nonneg_of_mem_rowStochastic hP (i := x) (j := y))
    (Matrix.sum_row_of_mem_rowStochastic hP x)

@[simp]
theorem toMatrix_ofRowStochastic
    [Fintype alpha] [DecidableEq alpha]
    (P : Matrix alpha alpha Rat)
    (hP : P ∈ Matrix.rowStochastic Rat alpha) :
    toMatrix (ofRowStochastic P hP) = P := by
  ext i j
  exact Dist.mass_ofFun
    (fun y => P i y)
    (fun y => Matrix.nonneg_of_mem_rowStochastic hP (i := i) (j := y))
    (Matrix.sum_row_of_mem_rowStochastic hP i)
    j

end FiniteKernel
end Shufflemath
