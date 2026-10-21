import Shufflemath.TotalVariation

namespace Shufflemath

/-!
# Exact total variation under a recoverable refinement

A coarse state `α` may be refined into a microscopic state `β` by a
conditional kernel `lift`. If a deterministic observation recovers the
coarse state almost surely, applying the *same* conditional kernel to two
coarse distributions preserves their TV distance exactly.

This theorem does not assume equal-sized fibers, or uniform conditional
laws. In the shuffle application the conditional law will be uniform on
each permutation fiber, but uniformity is a separate, substantive hypothesis
needed to identify the lifted stationary law with the full-deck uniform law.
No claim about the Commander exchange kernel is made in this generic file.
-/

namespace FiberLifting

variable {α β γ : Type*}

/-- A kernel with a stochastic left inverse preserves total variation.
The upper bound is data processing under `lift`; the reverse inequality is
data processing under `recover`. -/
theorem tv_apply_eq_of_leftInverse
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (lift : FiniteKernel α β) (recover : FiniteKernel β α)
    (hrecover : FiniteKernel.comp lift recover = FiniteKernel.identity)
    (p q : Dist α) :
    Dist.tv (FiniteKernel.apply p lift) (FiniteKernel.apply q lift) =
      Dist.tv p q := by
  apply le_antisymm
  · exact Dist.kernel_contraction lift p q
  · have h := Dist.kernel_contraction recover
        (FiniteKernel.apply p lift) (FiniteKernel.apply q lift)
    rw [FiniteKernel.apply_comp, FiniteKernel.apply_comp, hrecover,
      FiniteKernel.apply_id_left, FiniteKernel.apply_id_left] at h
    exact h

/-- A projection from microscopic to macroscopic states supplies the left
inverse. The premise says the conditional law `lift x` is supported in the
fiber over `x`, expressed using existing `FiniteKernel` semantics. -/
theorem tv_apply_eq_of_projection
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (lift : FiniteKernel α β) (project : β → α)
    (hproject : ∀ x : α,
      FiniteKernel.apply (lift x) (FiniteKernel.deterministic project) =
        Dist.pointMass x)
    (p q : Dist α) :
    Dist.tv (FiniteKernel.apply p lift) (FiniteKernel.apply q lift) =
      Dist.tv p q := by
  have hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity := by
    funext x
    change FiniteKernel.apply (lift x) (FiniteKernel.deterministic project) =
      Dist.pointMass x
    exact hproject x
  exact tv_apply_eq_of_leftInverse lift
    (FiniteKernel.deterministic project) hrecover p q

/-- The useful form for a mixing certificate: if the same recoverable
conditional refinement is applied to both the current macroscopic law and the
stationary macroscopic law, their distances are identical. -/
theorem tv_to_lifted_stationary
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (lift : FiniteKernel α β) (recover : FiniteKernel β α)
    (hrecover : FiniteKernel.comp lift recover = FiniteKernel.identity)
    (current stationary : Dist α) :
    Dist.tv (FiniteKernel.apply current lift)
      (FiniteKernel.apply stationary lift) = Dist.tv current stationary :=
  tv_apply_eq_of_leftInverse lift recover hrecover current stationary

/-- Intertwining condition for an exact microscopic/macroscopic model:
refine a macroscopic state and then take a microscopic step, or take the
macroscopic step and refine, and obtain the same distribution. -/
theorem run_intertwining
    (lift : FiniteKernel α β)
    (macroK : FiniteKernel α α) (micro : FiniteKernel β β)
    (hintertwine : FiniteKernel.comp lift micro =
      FiniteKernel.comp macroK lift)
    (p : Dist α) (n : Nat) :
    FiniteKernel.run micro n (FiniteKernel.apply p lift) =
      FiniteKernel.apply (FiniteKernel.run macroK n p) lift := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteKernel.run_succ, FiniteKernel.run_succ, ih]
      calc
        FiniteKernel.apply
            (FiniteKernel.apply (FiniteKernel.run macroK n p) lift) micro =
          FiniteKernel.apply (FiniteKernel.run macroK n p)
            (FiniteKernel.comp lift micro) :=
          FiniteKernel.apply_comp _ _ _
        _ = FiniteKernel.apply (FiniteKernel.run macroK n p)
            (FiniteKernel.comp macroK lift) := by rw [hintertwine]
        _ = FiniteKernel.apply
            (FiniteKernel.apply (FiniteKernel.run macroK n p) macroK) lift :=
          (FiniteKernel.apply_comp _ _ _).symm

/-- Full-deck mixing certificate from a recoverable refinement and a proved
kernel intertwining. This separates the abstract TV argument from the
substantive task of constructing a fiber-uniform lifting kernel and proving
it commutes with a concrete microscopic shuffle operation. -/
theorem run_tv_eq_macro
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (lift : FiniteKernel α β) (recover : FiniteKernel β α)
    (macroK : FiniteKernel α α) (micro : FiniteKernel β β)
    (hrecover : FiniteKernel.comp lift recover = FiniteKernel.identity)
    (hintertwine : FiniteKernel.comp lift micro =
      FiniteKernel.comp macroK lift)
    (start stationary : Dist α) (n : Nat) :
    Dist.tv (FiniteKernel.run micro n (FiniteKernel.apply start lift))
      (FiniteKernel.apply stationary lift) =
        Dist.tv (FiniteKernel.run macroK n start) stationary := by
  rw [run_intertwining lift macroK micro hintertwine start n]
  exact tv_apply_eq_of_leftInverse lift recover hrecover
    (FiniteKernel.run macroK n start) stationary

end FiberLifting
end Shufflemath
