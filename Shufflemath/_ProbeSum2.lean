module
public import Mathlib
public import Shufflemath.BernoulliLaplaceGeneral
public meta import Shufflemath.BernoulliLaplaceGeneral
@[expose] public section
namespace Shufflemath
open BernoulliLaplaceGeneral
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y

-- exact form from Dec4 (Icc + bound vars + (1/2)*):
def a (i j : Nat) : Rat := (1 / 2 : Rat) * (Finset.Icc (1 : ℕ) 50).sum (fun z => |w50 i z - w50 j z|)
-- same but range:
def b (i j : Nat) : Rat := (1 / 2 : Rat) * (Finset.range 50).sum (fun z => |w50 i (z + 1) - w50 j (z + 1)|)

#check a
#check b
end Shufflemath
