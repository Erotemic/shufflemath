module
public import Mathlib
@[expose] public section
namespace Shufflemath

example : (Finset.Icc (1 : ℕ) 50).sum (fun x => x) = 1275 := by decide
example : (Finset.Icc (1 : ℕ) 50).fold (0 : Nat) fun x a => a + x = 1275 := by decide
example : (Finset.Icc (1 : ℕ) 50 ×ˢ Finset.Icc (1 : ℕ) 50).card = 2500 := by decide
example : (Finset.univ : Finset (Fin 50)).card = 50 := by decide

end Shufflemath
