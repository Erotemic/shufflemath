module
public import Mathlib
public import Shufflemath.BernoulliLaplaceGeneral
public meta import Shufflemath.BernoulliLaplaceGeneral
@[expose] public section
namespace Shufflemath
open BernoulliLaplaceGeneral
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y

def t1 : Rat := (Finset.range 50).sum (fun z : ℕ => w50 25 (z + 1))
def t2 : Rat := (Finset.range 50).sum (fun z : ℕ => w50 25 (z + 1) - w50 50 (z + 1))
def t3 : Rat := (Finset.range 50).sum (fun z : ℕ => |w50 25 (z + 1) - w50 50 (z + 1)|)
def t4 : Rat := (Finset.range 50).sum (fun z : ℕ => max (w50 25 (z + 1) - w50 50 (z + 1)) (w50 50 (z + 1) - w50 25 (z + 1)))

#check t1
#check t2
#check t3
#check t4

end Shufflemath
