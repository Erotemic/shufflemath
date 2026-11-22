module
public import Mathlib
public import Shufflemath.BernoulliLaplaceGeneral
public meta import Shufflemath.BernoulliLaplaceGeneral
@[expose] public section
namespace Shufflemath
open BernoulliLaplaceGeneral

def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y
def rowTV50 (i j : Nat) : Rat :=
  (1 / 2 : Rat) * (Finset.Icc (1 : ℕ) 50).sum (fun z => |w50 i z - w50 j z|)
def coeff50 : Rat :=
  (Finset.range 2500).fold (0 : Rat) fun idx m =>
    max m (rowTV50 (idx / 50 + 1) (idx % 50 + 1))

example : coeff50 = 5332554286688521318331 / 6330095096149974879912 := by native_decide
example : coeff50 ^ 41 < (1 : Rat) / 1000 := by native_decide

end Shufflemath
