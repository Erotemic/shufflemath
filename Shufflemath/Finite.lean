import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Tactic

namespace Shufflemath

noncomputable section

/-- An exact finite probability distribution with rational weights.

`Convexity.StdSimplex` carries nonnegativity and total mass one in the type, so
there is no separate probability-validity predicate to keep synchronized. -/
abbrev Dist (alpha : Type*) := Convexity.StdSimplex Rat alpha

namespace Dist

variable {alpha beta : Type*}

/-- The rational mass assigned to a point. -/
def mass (mu : Dist alpha) (x : alpha) : Rat :=
  mu.weights x

@[simp]
theorem mass_nonneg (mu : Dist alpha) (x : alpha) : 0 <= mass mu x := by
  exact mu.weights_nonneg x

@[simp]
theorem sum_mass [Fintype alpha] (mu : Dist alpha) :
    Finset.sum Finset.univ (fun x => mass mu x) = 1 := by
  simp [mass]

/-- Construct an exact finite distribution from a normalized rational function.

This is the boundary used to turn a computational vector or stochastic-matrix row
into the semantic `Dist` representation. -/
noncomputable def ofFun [Fintype alpha]
    (f : alpha -> Rat)
    (hnonneg : forall x, 0 <= f x)
    (htotal : Finset.sum Finset.univ f = 1) : Dist alpha where
  weights := Finsupp.equivFunOnFinite.symm f
  nonneg x := by
    simpa using hnonneg x
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using htotal

@[simp]
theorem mass_ofFun [Fintype alpha]
    (f : alpha -> Rat)
    (hnonneg : forall x, 0 <= f x)
    (htotal : Finset.sum Finset.univ f = 1)
    (x : alpha) :
    mass (ofFun f hnonneg htotal) x = f x := by
  rfl

/-- Point mass at `x`. -/
def pointMass (x : alpha) : Dist alpha :=
  Convexity.StdSimplex.single x

@[simp]
theorem mass_pointMass [DecidableEq alpha] (x y : alpha) :
    mass (pointMass x) y = if y = x then 1 else 0 := by
  simp [mass, pointMass, Finsupp.single_apply, eq_comm]

end Dist

/-- A finite exact Markov kernel. Each row is a probability distribution by
construction. -/
abbrev FiniteKernel (alpha beta : Type*) := alpha -> Dist beta

namespace FiniteKernel

variable {alpha beta gamma : Type*}

/-- Kernel induced by a deterministic state transformation. -/
def deterministic (f : alpha -> beta) : FiniteKernel alpha beta :=
  fun x => Dist.pointMass (f x)

/-- Identity kernel. -/
def identity : FiniteKernel alpha alpha :=
  deterministic id

/-- Apply a finite kernel to an input distribution. -/
def apply (mu : Dist alpha) (K : FiniteKernel alpha beta) : Dist beta :=
  (mu.map K).join

/-- Compose kernels in execution order: first `K`, then `L`. -/
def comp (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma) :
    FiniteKernel alpha gamma :=
  fun x => ((K x).map L).join

/-- Repeatedly apply a homogeneous kernel. -/
def run (K : FiniteKernel alpha alpha) : Nat -> Dist alpha -> Dist alpha
  | 0, mu => mu
  | n + 1, mu => run K n (apply mu K)

@[simp]
theorem apply_pointMass (x : alpha) (K : FiniteKernel alpha beta) :
    apply (Dist.pointMass x) K = K x := by
  simp [apply, Dist.pointMass]

@[simp]
theorem deterministic_apply_pointMass (x : alpha) (f : alpha -> beta) :
    apply (Dist.pointMass x) (deterministic f) = Dist.pointMass (f x) := by
  simp [deterministic]

end FiniteKernel

end

end Shufflemath
