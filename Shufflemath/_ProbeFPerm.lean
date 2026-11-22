module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic

@[expose]
public section

#check Equiv.instFintype
#check fintypePerm
example : Fintype (Fin 3 ≃ Fin 3) := by infer_instance
#check Equiv.fintypePerm
