module

public import Shufflemath.BernoulliLaplaceGeneral
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open BernoulliLaplaceGeneral
open Finset

-- (A) Does native_decide work on a plain Rat inequality at all?
example : (3 : Rat) / 4 < 1 := by native_decide

-- (B) Does it work on a concrete rational power?
example : ((3 : Rat) / 4) ^ 20 < 1 / 1000 := by native_decide

-- (C) computable 50x50 coefficient
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y
def rowTV50 (i j : Nat) : Rat :=
  (1 / 2 : Rat) * (Icc (1 : ℕ) 50).sum (fun z => |w50 i z - w50 j z|)
def coeff50 : Rat :=
  (Icc (1 : ℕ) 50 ×ˢ Icc (1 : ℕ) 50).fold (0 : Rat) fun p m => max m (rowTV50 p.1 p.2)

-- (D) the headline: does native_decide prove coeff50^41 < 1/1000 ?
example : coeff50 ^ 41 < (1 : Rat) / 1000 := by native_decide

end Shufflemath
