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

variable (d : Deck) (x : Fin 99)

-- T1: after unfold membership, is `x ∈ leftCards d` reachable by change?
example : x ∈ (CommanderMembershipKernels.membership d : Finset (Fin 99)) → True := by
  intro hx
  unfold CommanderMembershipKernels.membership at hx
  change x ∈ leftCards d at hx
  exact True.intro

-- T2: `show` takes no `at` (syntax error) — the `at`-form is `change`;
--     T1 documents the positive result.
example : x ∈ (CommanderMembershipKernels.membership d : Finset (Fin 99)) → True := by
  intro hx
  unfold CommanderMembershipKernels.membership at hx
  change x ∈ leftCards d at hx
  exact True.intro

-- T3: does dsimp only [leftCards] at hx fire?
example : x ∈ (CommanderMembershipKernels.membership d : Finset (Fin 99)) → True := by
  intro hx
  unfold CommanderMembershipKernels.membership at hx
  dsimp only [leftCards] at hx
  exact True.intro

end Shufflemath
