module
public import Mathlib
public import Shufflemath.BernoulliLaplaceGeneral
public meta import Shufflemath.BernoulliLaplaceGeneral
@[expose] public section
namespace Shufflemath
open BernoulliLaplaceGeneral
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y
def reach25 (x : Nat) : Rat := w50 x 25
-- min over the 50 states, via a range fold (reduces cleanly)
def minReach25 : Rat :=
  (Finset.range 50).fold (reach25 1) fun idx m => min m (reach25 (idx + 1))

example : minReach25 = (transitionWeight 99 50 50 25 25 25 : Rat) := by native_decide
example : ((1 : Rat) - transitionWeight 99 50 50 25 25 25) ^ 41 < (1 : Rat) / 1000 := by native_decide

end Shufflemath
