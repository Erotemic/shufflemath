import Shufflemath
import Mathlib
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm

open Shufflemath

variable (n a : Nat) (ha : 0 < a)

def Ω2 (n a : Nat) := (Fin n → Fin a) × Equiv.Perm (Fin n)

example : Fintype (Ω2 n a) := by infer_instance
