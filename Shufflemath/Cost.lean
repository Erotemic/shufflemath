import Shufflemath.Finite

namespace Shufflemath

/-- A state transition paired with a nonnegative physical cost. The cost unit is left
abstract: seconds, normalized local-shuffle units, or an exact symbolic calibration
can be layered on later. -/
structure CostedKernel (α : Type*) where
  step : Kernel α α
  cost : ℚ
  cost_nonneg : 0 ≤ cost

namespace CostedKernel

variable {α : Type*}

/-- Total additive cost of a finite protocol. -/
def protocolCost (ops : List (CostedKernel α)) : ℚ :=
  (ops.map CostedKernel.cost).sum

@[simp]
theorem protocolCost_nil : protocolCost ([] : List (CostedKernel α)) = 0 := by
  rfl

@[simp]
theorem protocolCost_cons (op : CostedKernel α) (ops : List (CostedKernel α)) :
    protocolCost (op :: ops) = op.cost + protocolCost ops := by
  simp [protocolCost]

@[simp]
theorem protocolCost_append (xs ys : List (CostedKernel α)) :
    protocolCost (xs ++ ys) = protocolCost xs + protocolCost ys := by
  simp [protocolCost]

end CostedKernel

end Shufflemath
