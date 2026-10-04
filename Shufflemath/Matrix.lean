import Shufflemath.Finite
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Algebra.Group.Monoid

namespace Shufflemath
namespace FiniteKernel

variable {alpha beta gamma : Type*}

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

/-- The matrix of a composite kernel is the product of the matrices:

`toMatrix (comp K L) = toMatrix K * toMatrix L`.

This makes matrix computations faithful to the kernel semantics: a protocol
of kernels has matrix `(toMatrix K₁) * … * (toMatrix Kₙ)` in execution
order, so `n`-fold products and powers of the matrix are exact statements
about the shuffled deck. The proof computes the mass of the joined
pushforward of `(K x)` at the `Finsupp` weights level: the `mapDomain`
pushforward is rearranged by `Finsupp.sum_mapDomain_index`, the evaluation
at `y` is pushed inside by `Finsupp.sum_apply`, and the support sum is
converted to the `Fintype` sum of `Matrix.mul_apply` by
`Finsupp.sum_fintype`. -/
@[simp]
theorem toMatrix_comp [Fintype beta]
    (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma) :
    toMatrix (comp K L) = toMatrix K * toMatrix L := by
  ext x y
  -- Bring the LHS to `Dist` level. (`unfold toMatrix` would also hit the
  -- RHS, whose `*` instance needs `Matrix`-typed arguments.)
  change Dist.mass (((K x).map L).join) y = (toMatrix K * toMatrix L) x y
  simp only [Dist.mass, Convexity.StdSimplex.join, Convexity.StdSimplex.map]
  -- LHS: ((K x).weights.mapDomain L).sum (fun d r => r • d.weights) y
  rw [Finsupp.sum_mapDomain_index (f := L) (s := (K x).weights)
      (h := fun d r => r • d.weights)
      (h_zero := fun b => zero_smul Rat b.weights)
      (h_add := fun _ _ _ => add_smul _ _ _)]
  -- LHS: (K x).weights.sum (fun z r => r • (L z).weights) y
  rw [Finsupp.sum_apply]
  -- Do the RHS next: `Matrix.mul_apply` needs `Matrix`-typed arguments, and
  -- the resulting plain sum keeps the target type-correct for `rw`.
  rw [Matrix.mul_apply]
  simp only [toMatrix, Dist.mass]
  -- RHS: ∑ z, (K x).weights z * (L z).weights y
  -- The remaining LHS summand `(b • (L a₁).weights) y` is definitionally
  -- `b • ((L a₁).weights y)` (`Finsupp.smul_apply` is `@[defeq]`), and in
  -- `Rat` scalar multiplication is ordinary multiplication, so the sums
  -- close by `rfl`.
  -- `change` (kernel defeq) normalises the summand; `rw` cannot cross the
  -- `@[defeq]` gap on its own.
  change (K x).weights.sum (fun z r => r • (L z).weights y) =
      (∑ j, (K x).weights j * (L j).weights y)
  rw [Finsupp.sum_fintype (f := (K x).weights) (g := fun z r => r • (L z).weights y)
      (h := fun _ => zero_smul Rat _)]
  -- LHS: ∑ z, (K x).weights z • (L z).weights y = RHS, by definitionality.
  rfl

/-- The identity kernel has the identity matrix. -/
@[simp]
theorem toMatrix_identity [DecidableEq alpha] : toMatrix (identity : FiniteKernel alpha alpha) = 1 := by
  ext x y
  change Dist.mass (identity x) y = (1 : Matrix alpha alpha Rat) x y
  simp only [identity, deterministic, Dist.pointMass, Dist.mass,
    Convexity.StdSimplex.single, Finsupp.single_apply, Matrix.one_apply, id]

/-- The matrix of the `n`-fold composite is the `n`-th power of the matrix
(the execution order of `compPow` matches `pow_succ`, so no commutativity
is needed): `toMatrix (compPow K n) = (toMatrix K) ^ n`. -/
@[simp]
theorem toMatrix_compPow [Fintype alpha] [DecidableEq alpha]
    (K : FiniteKernel alpha alpha) (n : Nat) :
    toMatrix (compPow K n) = (toMatrix K) ^ n := by
  induction n with
  | zero =>
      rw [compPow_zero, toMatrix_identity]
      rfl
  | succ n ih =>
      rw [compPow_succ, toMatrix_comp, ih, pow_succ]

/-- `run` is the vector–matrix product: the mass at `x` after `n`
applications of `K` is the distribution `mu` (as a row vector) against the
`n`-th power of the transition matrix:

`mass (run K n mu) x = (fun y => mass mu y) ᵥ* (toMatrix K ^ n) x`.

The proof is the same Finsupp weights-level computation as `toMatrix_comp`,
with the distribution `mu` in place of the point mass. -/
theorem toMatrix_run [Fintype alpha] [DecidableEq alpha]
    (K : FiniteKernel alpha alpha) (n : Nat) (mu : Dist alpha) (x : alpha) :
    Dist.mass (run K n mu) x =
      Matrix.vecMul (fun y => Dist.mass mu y) (toMatrix K ^ n) x := by
  set Kp := compPow K n
  rw [run_compPow]
  unfold apply
  -- LHS: Dist.mass ((mu.map Kp).join) x
  simp only [Dist.mass, Dist.join_sConvexComb, Convexity.StdSimplex.weights_sConvexComb,
    Convexity.StdSimplex.map]
  -- LHS: ((mu.weights.mapDomain Kp).sum (fun d r => r • d.weights)) x
  rw [Finsupp.sum_mapDomain_index (f := Kp) (s := mu.weights)
      (h := fun d r => r • d.weights)
      (h_zero := fun b => zero_smul Rat b.weights)
      (h_add := fun _ _ _ => add_smul _ _ _)]
  -- LHS: mu.weights.sum (fun y r => r • (Kp y).weights) x
  rw [Finsupp.sum_apply]
  -- LHS: mu.weights.sum (fun y r => (r • (Kp y).weights) x)
  -- Do the RHS next: `Matrix.vecMul_apply_eq_sum` needs `Matrix`-typed
  -- arguments, exactly as in `toMatrix_comp`.
  rw [Matrix.vecMul_apply_eq_sum]
  -- RHS: ∑ y, (mu.weights y) * (toMatrix K ^ n) y x
  -- (the `Dist.mass` in the row-vector lambda was already unfolded by `rw`)
  rw [← toMatrix_compPow]
  -- RHS: ∑ y, (mu.weights y) * (toMatrix Kp) y x
  -- `Finsupp.smul_apply` is `@[defeq]`, which `rw` cannot cross, and
  -- `toMatrix`'s equation theorem does not rewrite the dot-notation form
  -- here, so `change` (kernel defeq, which unfolds `toMatrix`) takes the
  -- goal to its final shape; in `Rat`, `•` is ordinary `*`.
  change mu.weights.sum (fun y r => r • (Kp y).weights x) =
      (∑ y, (mu.weights y) * (Kp y).weights x)
  rw [Finsupp.sum_fintype (f := mu.weights) (g := fun y r => r • (Kp y).weights x)
      (h := fun _ => zero_smul Rat _)]
  -- LHS: ∑ y, (mu.weights y) • (Kp y).weights x = RHS, by definitionality.
  rfl

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
