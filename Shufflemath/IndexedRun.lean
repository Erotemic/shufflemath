module

public import Shufflemath.Finite

@[expose] public section

/-!
# Time-indexed heterogeneous runs

A nonhomogeneous typed run of kernels: at each time `t` the carrier may change to its
successor carrier.  This replaces the parked capacity-vector inductive whose parameter
position put the capacity vector in the wrong part of the family — a schedule is data,
not a recursive subtype of allocations.

The run is defined by ordinary `Nat` recursion over the step sequence, so the generic
theory carries no concrete capacities or `Fintype` requirements at all.  `indexedRun`
is the first-class object, `indexedRun_zero`/`indexedRun_succ` are the defining
recursor equations, and `indexedRun_reference` is the workhorse — a *reference family*
`ref t : Dist (X t)` invariant under each step (`apply (ref t) (step t) = ref (succ t)`)
is preserved by the run from its seed.  `indexedKernel` extracts the heterogeneous
composite as an ordinary kernel by running from a point mass.

Source: `dev/inkling-hints/2026-11-26-evening/IndexedRunSeeds.lean`
-/

namespace Shufflemath

universe u

/-- A nonhomogeneous typed run.  At each time the carrier may change. -/
noncomputable def indexedRun {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t)))
    (mu : Dist (X 0)) (t : Nat) : Dist (X t) :=
  @Nat.rec (fun s => Dist (X s)) mu
    (fun s prev => FiniteKernel.apply prev (step s)) t

@[simp] theorem indexedRun_zero {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t))) (mu : Dist (X 0)) :
    indexedRun step mu 0 = mu := rfl

@[simp] theorem indexedRun_succ {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t))) (mu : Dist (X 0))
    (t : Nat) : indexedRun step mu (Nat.succ t) =
      FiniteKernel.apply (indexedRun step mu t) (step t) := rfl

/-- If the caller wants the heterogeneous composite as a kernel, do not build
another recursive object: run from a point mass. -/
noncomputable def indexedKernel {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t))) (t : Nat) :
    FiniteKernel (X 0) (X t) := fun x => indexedRun step (Dist.pointMass x) t

/-- A transported reference family, not just a fixed-space stationary law: if each step
transports the reference at time `t` to the reference at time `t + 1`, then the run from
the seed `ref 0` is exactly the reference family along the whole schedule. -/
theorem indexedRun_reference {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t)))
    (ref : (t : Nat) → Dist (X t))
    (hstep : ∀ t, FiniteKernel.apply (ref t) (step t) = ref (Nat.succ t))
    (t : Nat) : indexedRun step (ref 0) t = ref t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [indexedRun_succ, ih, hstep t]

end Shufflemath
