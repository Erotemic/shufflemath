module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

variable (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) (x : Fin 99)

-- P1: rw [mem_union] at (x ∈ newLeftCards d L R) — FAILS on the def;
--     dsimp first (the finding; cf. K1h P1: newLeftCards *is* defeq its body,
--     but rw does not delta-reduce defs — only dsimp does).
example : x ∈ CommanderPhysicalExchange.newLeftCards d L R → True := by
  intro hx
  dsimp only [CommanderPhysicalExchange.newLeftCards] at hx
  rw [Finset.mem_union] at hx
  cases hx
  · exact True.intro
  · exact True.intro

-- P2: simp only [newLeftCards, mem_union] at hx
example : x ∈ CommanderPhysicalExchange.newLeftCards d L R → True := by
  intro hx
  simp only [CommanderPhysicalExchange.newLeftCards, Finset.mem_union] at hx
  cases hx
  · exact True.intro
  · exact True.intro

end Shufflemath
