module
public import Mathlib
@[expose] public section
namespace Shufflemath
-- List.foldl : f init l ; f : elem -> acc -> acc
def lf : Nat := (List.range 5).foldl (fun idx acc => acc + idx) 100
-- Finset.fold : ???
def f1 : Nat := (Finset.range 5).fold (fun x acc => acc + x) 100
def f2 : Nat := (Finset.range 5).fold 100 (fun x acc => acc + x)
#check lf
#check f1
#check f2
example : lf = 105 := by decide
end Shufflemath
