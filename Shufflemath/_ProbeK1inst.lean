module
public import Mathlib

@[expose]

public section

#check Equiv.refl_apply
#check (1 : Equiv.Perm (Fin 3))
example (n : Nat) (s : Finset (Fin n)) : s.image (1 : Equiv.Perm (Fin n)) = s := by
  simp
example (n : Nat) (g h : Equiv.Perm (Fin n)) (s : Finset (Fin n)) : (s.image h).image g = s.image (g * h) := by
  ext x
  simp [Equiv.trans_apply, Finset.mem_image]
  <;> aesop

end
