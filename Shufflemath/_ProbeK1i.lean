module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

variable (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) (x : Fin 99)

-- S1b: membership side via unfold + change + rw [mem_image] + rcases
example : x ∈ (CommanderMembershipKernels.membership d : Finset (Fin 99)) → True := by
  intro hx
  unfold CommanderMembershipKernels.membership at hx
  change x ∈ leftCards d at hx
  -- finding: rw [mem_image] does NOT fire on `leftCards d` (def is not a
  -- simp/rw unfold target); a bare `dsimp` first makes it fire:
  dsimp only [leftCards] at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨i, _, _⟩
  exact True.intro

-- S2b: newLeftCards side via unfold + rw [mem_union] + rcases + rw [mem_image] + rcases
example : x ∈ CommanderPhysicalExchange.newLeftCards d L R → True := by
  intro hx
  unfold CommanderPhysicalExchange.newLeftCards at hx
  rw [Finset.mem_union] at hx
  rcases hx with hLft | hRgt
  · rw [Finset.mem_image] at hLft
    rcases hLft with ⟨l, _, _⟩
    exact True.intro
  · rw [Finset.mem_image] at hRgt
    rcases hRgt with ⟨r, _, _⟩
    exact True.intro

-- (the S3 membership-transport goal shape is superseded by the proven
-- `K1a_stmt_only` in `Shufflemath/_ProbeK1b.lean`; the direct set-level
-- transport is false for arbitrary (L, R), so it is not a probe target.)
