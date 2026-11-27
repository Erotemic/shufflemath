module

public import Shufflemath.Finite

@[expose] public section

namespace Shufflemath.FinishHints

/-! Proposed, uncompiled. Do not define an inductive with capacity vector as
an invariant parameter. This is induction on time, not on allocations. -/

universe u

/-- A nonhomogeneous typed run. At each time the carrier may change. -/
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

/-- A transported reference family, not just a fixed-space stationary law. -/
theorem indexedRun_reference {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t)))
    (ref : (t : Nat) → Dist (X t))
    (hstep : ∀ t, FiniteKernel.apply (ref t) (step t) = ref (Nat.succ t))
    (t : Nat) : indexedRun step (ref 0) t = ref t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [indexedRun_succ, ih, hstep t]

/-- If the caller wants the heterogeneous composite as a kernel, do not build
another recursive object: run from a point mass. -/
noncomputable def indexedKernel {X : Nat → Type u}
    (step : (t : Nat) → FiniteKernel (X t) (X (Nat.succ t))) (t : Nat) :
    FiniteKernel (X 0) (X t) := fun x => indexedRun step (Dist.pointMass x) t

end Shufflemath.FinishHints
