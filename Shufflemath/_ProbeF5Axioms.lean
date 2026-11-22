module

public import Shufflemath.BernoulliLaplaceGeneral
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open BernoulliLaplaceGeneral

def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y
def rowTV50 (i j : Nat) : Rat :=
  (1 / 2 : Rat) * (Finset.Icc (1 : ℕ) 50).sum (fun z => |w50 i z - w50 j z|)

#check w50 25 25
#check rowTV50 25 50
#print axioms w50
#print axioms rowTV50

end Shufflemath
