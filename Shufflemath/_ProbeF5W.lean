module
public import Mathlib
public meta import Shufflemath.BernoulliLaplaceGeneral
@[expose] public section
namespace Shufflemath
open BernoulliLaplaceGeneral

example : (transitionWeight 99 50 50 25 25 25 : Rat) = 997540809461453561581 / 6330095096149974879912 := by native_decide
example : (transitionWeight 99 50 50 25 25 25 : Rat) ≤ (transitionWeight 99 50 50 25 50 25 : Rat) := by native_decide
example : ((1 : Rat) - transitionWeight 99 50 50 25 25 25) ^ 41 < (1 : Rat) / 1000 := by native_decide

end Shufflemath
