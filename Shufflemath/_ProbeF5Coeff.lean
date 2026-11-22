module

public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceCommanderBridge
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open BernoulliLaplaceGeneral

/-- Computable transition weight (no Dist / no blExchangeKernel). -/
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y

/-- Computable row-TV between the two macrostates `i` and `j` (sum over the 50
admissible states `1..50`). -/
def rowTV50 (i j : Nat) : Rat :=
  (1 / 2 : Rat) * (Finset.Icc 1 50).sum (fun z => |w50 i z - w50 j z|)

/-- The Dobrushin coefficient, computable: max over all 50x50 ordered pairs. -/
def coeff50 : Rat :=
  (Finset.Icc 1 50 ×ˢ Finset.Icc 1 50).fold (0 : Rat)
    fun p m => max m (rowTV50 p.1 p.2)

#eval coeff50
#eval (1 - w50 25 25)
#eval (coeff50 ^ 41 < (1 : Rat) / 1000)

end Shufflemath
