/-
Markov-chain theory for finite kernels: stationarity, detailed balance,
and self-adjointness of the row operator in the stationary-weighted form.

Abstract theory only — no concrete chain (the Commander chain lives in
`BernoulliLaplace.lean`; the general Bernoulli–Laplace theory lives in
`BernoulliLaplaceGeneral.lean`). Everything is exact rational arithmetic
over finite types.
-/
import Shufflemath.Finite
import Shufflemath.TotalVariation
import Mathlib.Tactic

namespace Shufflemath

variable {alpha : Type*} {beta : Type*}

/-- A distribution `mu` is stationary for the kernel `K` if one
application of `K` leaves it fixed. -/
abbrev Stationary (mu : Dist alpha) (K : FiniteKernel alpha alpha) :=
    FiniteKernel.apply mu K = mu

/-- Stationarity is preserved under iteration: if `mu` is fixed by one
application of `K`, it is fixed by any number of them. Downstream this
lets a stationary certificate be checked once, at the one-step level. -/
theorem stationary_run (n : Nat) (mu : Dist alpha) (K : FiniteKernel alpha alpha)
    (h : Stationary mu K) :
    FiniteKernel.run K n mu = mu := by
  induction n with
  | zero =>
    show FiniteKernel.run K 0 mu = mu
    rfl
  | succ n ih =>
    rw [FiniteKernel.run_succ, ih]
    exact h

/-- Detailed balance (reversibility): the one-step flow of the
stationary measure from `x` to `y` equals the flow from `y` to `x`. -/
abbrev DetailedBalance (mu : Dist alpha) (K : FiniteKernel alpha alpha) :=
    forall x y, Dist.mass mu x * Dist.mass (K x) y =
      Dist.mass mu y * Dist.mass (K y) x

/-- Detailed balance implies stationarity. Summing the balance equation
over `x` at a fixed `y` and using only that the `y`-row of `K` has total
mass `1` gives `mass (apply mu K) y = mass mu y` for every `y` (no
double-sum swap is needed: the swapped index is the one being summed). -/
theorem detailedBalance_implies_stationary
    [Fintype alpha] [DecidableEq alpha]
    (mu : Dist alpha) (K : FiniteKernel alpha alpha)
    (hdb : DetailedBalance mu K) (y : alpha) :
    Dist.mass (FiniteKernel.apply mu K) y = Dist.mass mu y := by
  have h0 : Dist.mass (FiniteKernel.apply mu K) y =
      Finset.sum (Finset.univ : Finset alpha)
        (fun x => Dist.mass mu x * Dist.mass (K x) y) :=
    FiniteKernel.apply_mass mu K y
  rw [h0]
  rw [Finset.sum_congr rfl fun x _ => hdb x y]
  rw [(Finset.mul_sum (Finset.univ : Finset alpha)
      (fun x => Dist.mass (K y) x) (Dist.mass mu y)).symm]
  rw [Dist.sum_mass]
  rw [mul_one]

/-- The row action of the kernel `K` on a function: at `x`, the `K x`
-weighted average of `f`. This is the adjoint-side companion of
`FiniteKernel.apply` (which acts on distributions). -/
def applyFn [Fintype alpha] [Fintype beta] (K : FiniteKernel alpha beta)
    (f : beta → Rat) (x : alpha) : Rat :=
  Finset.sum (Finset.univ : Finset beta) (fun y => Dist.mass (K x) y * f y)

/-- Bilinear form on functions weighted by the distribution `mu`:
`∑ x, mu x * f x * g x`. It is degenerate at states with `mu x = 0`,
so it is not an inner product in the strict sense (over `R`, on the
support of `mu`, it is positive-semidefinite). The name follows the
looser Markov-chain usage. -/
def weightedInner [Fintype alpha] (mu : Dist alpha) (f g : alpha → Rat) : Rat :=
  Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x * f x * g x)

/-- Under detailed balance, the row action of the kernel is
self-adjoint in the `mu`-weighted bilinear form:
`weightedInner mu f (K.applyFn g) = weightedInner mu g (K.applyFn f)`. This is the finite, exact
form of reversibility ⇒ self-adjointness. Note the algebraic scope: the
coefficients live in `Rat`, the weighted form is degenerate at points
with `mu x = 0`, and a rational self-adjoint operator need not be
diagonalizable over `Q` — the real spectral statement (orthogonal
eigenbasis in the stationary-weighted form) requires moving to `R` and
handling support/positivity, which is out of scope for this file. -/
theorem selfAdjoint_of_detailedBalance
    [Fintype alpha]
    (mu : Dist alpha) (K : FiniteKernel alpha alpha)
    (hdb : DetailedBalance mu K) (f g : alpha → Rat) :
    weightedInner mu f (applyFn K g) = weightedInner mu g (applyFn K f) := by
  -- Expand the left-hand weighted form to a double sum.
  have hL : weightedInner mu f (applyFn K g) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum (Finset.univ : Finset alpha)
          (fun y => (Dist.mass mu x * f x) * (Dist.mass (K x) y * g y))) := by
    rw [weightedInner]
    simp only [applyFn]
    rw [Finset.sum_congr rfl fun x _ =>
        Finset.mul_sum (Finset.univ : Finset alpha)
          (fun y => Dist.mass (K x) y * g y) (Dist.mass mu x * f x)]
  -- Expand the right-hand one the same way (index order y, x).
  have hR : weightedInner mu g (applyFn K f) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun y => Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu y * g y) * (Dist.mass (K y) x * f x))) := by
    rw [weightedInner]
    simp only [applyFn]
    rw [Finset.sum_congr rfl fun y _ =>
        Finset.mul_sum (Finset.univ : Finset alpha)
          (fun x => Dist.mass (K y) x * f x) (Dist.mass mu y * g y)]
  -- Swap the detailed-balance factors in the double sum.
  have hSwap : Finset.sum (Finset.univ : Finset alpha)
      (fun x => Finset.sum (Finset.univ : Finset alpha)
        (fun y => (Dist.mass mu x * f x) * (Dist.mass (K x) y * g y))) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum (Finset.univ : Finset alpha)
          (fun y => (Dist.mass mu y * Dist.mass (K y) x) * (f x * g y))) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    calc
      _ = (Dist.mass mu x * Dist.mass (K x) y) * f x * g y := by ring
      _ = (Dist.mass mu y * Dist.mass (K y) x) * f x * g y := by
        rw [hdb x y]
      _ = (Dist.mass mu y * Dist.mass (K y) x) * (f x * g y) := by ring
  -- Pull the y-factor out of the x-sum: Fubini in the reverse direction.
  have hPull : Finset.sum (Finset.univ : Finset alpha)
      (fun x => Finset.sum (Finset.univ : Finset alpha)
        (fun y => (Dist.mass mu y * Dist.mass (K y) x) * (f x * g y))) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun y => (Dist.mass mu y * g y) *
          Finset.sum (Finset.univ : Finset alpha)
            (fun x => Dist.mass (K y) x * f x)) := by
    have h1 : Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum (Finset.univ : Finset alpha)
          (fun y => (Dist.mass mu y * Dist.mass (K y) x) * (f x * g y))) =
        Finset.sum (Finset.univ : Finset alpha)
          (fun x => Finset.sum (Finset.univ : Finset alpha)
            (fun y => (Dist.mass mu y * g y) * (Dist.mass (K y) x * f x))) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [h1]
    rw [Dist.double_sum_pullout (a := fun y => Dist.mass mu y * g y)
        (b := fun x y => Dist.mass (K y) x * f x)]
  calc
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum (Finset.univ : Finset alpha)
          (fun y => (Dist.mass mu x * f x) * (Dist.mass (K x) y * g y))) :=
      hL
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum (Finset.univ : Finset alpha)
          (fun y => (Dist.mass mu y * Dist.mass (K y) x) * (f x * g y))) :=
      hSwap
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun y => (Dist.mass mu y * g y) *
          Finset.sum (Finset.univ : Finset alpha)
            (fun x => Dist.mass (K y) x * f x)) :=
      hPull
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun y => Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu y * g y) * (Dist.mass (K y) x * f x))) := by
      rw [Finset.sum_congr rfl fun y _ =>
          Finset.mul_sum (Finset.univ : Finset alpha)
            (fun x => Dist.mass (K y) x * f x) (Dist.mass mu y * g y)]
    _ = weightedInner mu g (applyFn K f) := hR.symm

/-- Detailed balance implies stationarity, as a `Stationary` certificate. -/
theorem stationary_of_detailedBalance
    [Fintype alpha] [DecidableEq alpha]
    (mu : Dist alpha) (K : FiniteKernel alpha alpha)
    (hdb : DetailedBalance mu K) : Stationary mu K := by
  unfold Stationary
  ext x
  exact detailedBalance_implies_stationary mu K hdb x

end Shufflemath
