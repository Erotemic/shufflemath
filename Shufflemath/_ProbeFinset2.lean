module
public import Mathlib
@[expose] public section
namespace Shufflemath

example : (Finset.range 50).sum (fun x => x) = 1225 := by decide
example : ((Finset.univ : Finset (Fin 50))).sum (fun x => x.val) = 1225 := by decide
example : (Finset.Ico (0 : ℕ) 50).sum (fun x => x) = 1225 := by decide
example : (Finset.range 50).fold (0 : Nat) fun x a => a + x = 1225 := by decide

end Shufflemath
