import Shufflemath.Perturbation
import Shufflemath.Cost

namespace Shufflemath

/-!
# Target-relative protocol certificates

The existing `weightedTelescope` theorem bounds the discrepancy between an
actual and a reference schedule. Here we add the final triangle inequality
that turns that discrepancy into a bound against an arbitrary target law.
No approximation is substituted for an exact rational TV distance.
-/

namespace ProtocolCertificate

variable {α : Type*}

/-- The exact symbolic right-hand side of the weighted telescope bound. -/
noncomputable def errorBudget [Fintype α] [DecidableEq α] [Nonempty α]
    (actual ideal : List (FiniteKernel α α)) : Rat :=
  weightedTelescopeBound
    (List.map (fun (pair : FiniteKernel α α × FiniteKernel α α) =>
      kernelDiscrepancy pair.1 pair.2) (actual.zip ideal))
    (List.map Dobrushin.dobrushinCoeff (ideal.drop 1))

/-- Operational certificate: true terminal error is at most the ideal
reference error plus the exact weighted perturbation budget. -/
theorem terminalTV_le_reference_add_budget
    [Fintype α] [DecidableEq α] [Nonempty α]
    (actual ideal : List (FiniteKernel α α))
    (hlen : actual.length = ideal.length)
    (start target : Dist α) :
    Dist.tv (FiniteKernel.apply start (compList actual)) target ≤
      errorBudget actual ideal +
        Dist.tv (FiniteKernel.apply start (compList ideal)) target := by
  -- Expose only the budget wrapper before composing the two inequalities.
  -- Leaving it opaque forces elaboration to normalize the full weighted
  -- telescope term while matching the last `calc` step.
  unfold errorBudget
  have htriangle := Dist.tv_triangle
    (FiniteKernel.apply start (compList actual))
    (FiniteKernel.apply start (compList ideal)) target
  have hweighted := weightedTelescope actual ideal hlen start
  exact htriangle.trans
    (add_le_add_left hweighted
      (Dist.tv (FiniteKernel.apply start (compList ideal)) target))

/-- The semantics of a costed schedule reuse `compList` directly; no
second composition convention or source of kernel authority is needed. -/
noncomputable def kernelOfCosted (ops : List (CostedKernel α)) :
    FiniteKernel α α :=
  compList (ops.map CostedKernel.step)

@[simp]
theorem kernelOfCosted_nil :
    kernelOfCosted ([] : List (CostedKernel α)) = FiniteKernel.identity := by
  simp [kernelOfCosted]

@[simp]
theorem kernelOfCosted_cons (op : CostedKernel α) (ops : List (CostedKernel α)) :
    kernelOfCosted (op :: ops) =
      FiniteKernel.comp op.step (kernelOfCosted ops) := by
  simp [kernelOfCosted]

end ProtocolCertificate
end Shufflemath
