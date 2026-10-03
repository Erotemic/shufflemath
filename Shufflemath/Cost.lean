import Shufflemath.Finite

namespace Shufflemath

/-- A state transition paired with a nonnegative physical cost. The cost unit is
left abstract: seconds, normalized local-shuffle units, or an exact symbolic
calibration can be layered on later. -/
structure CostedKernel (alpha : Type*) where
  step : FiniteKernel alpha alpha
  cost : Rat
  cost_nonneg : 0 <= cost

namespace CostedKernel

variable {alpha : Type*}

/-- Total additive cost of a finite protocol. -/
def protocolCost (ops : List (CostedKernel alpha)) : Rat :=
  (ops.map CostedKernel.cost).sum

@[simp]
theorem protocolCost_nil : protocolCost ([] : List (CostedKernel alpha)) = 0 := by
  rfl

@[simp]
theorem protocolCost_cons (op : CostedKernel alpha) (ops : List (CostedKernel alpha)) :
    protocolCost (op :: ops) = op.cost + protocolCost ops := by
  simp [protocolCost]

@[simp]
theorem protocolCost_append (xs ys : List (CostedKernel alpha)) :
    protocolCost (xs ++ ys) = protocolCost xs + protocolCost ys := by
  simp [protocolCost]

end CostedKernel
end Shufflemath
