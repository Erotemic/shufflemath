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

-- P1: is newLeftCards definitionally its explicit union-of-images body?
--     (if rfl closes, kernel delta-reduces it; if not, it's opaque)
example : x ∈ CommanderPhysicalExchange.newLeftCards d L R ↔
    x ∈ (Finset.image (fun (l : Fin 50) => d (leftPosition l))
          ((Finset.univ : Finset (Fin 50)) \ L)
        ∪ Finset.image (fun (r : Fin 49) => d (rightPosition r)) R) := by
  exact Iff.intro (fun h => h) (fun h => h)

-- P2: does rw [mem_union, mem_image, mem_image] fire on the explicit union form?
example : (x ∈ (Finset.image (fun (l : Fin 50) => d (leftPosition l))
          ((Finset.univ : Finset (Fin 50)) \ L)
        ∪ Finset.image (fun (r : Fin 49) => d (rightPosition r)) R)) → True := by
  intro hx
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  cases hx
  · exact True.intro
  · exact True.intro

-- P3: membership is a Subtype (no Membership typeclass instance) — the
--     `x ∈` form needs the Finset coercion, and the carried set is
--     `leftCards d` only propositionally (membership_leftCards), not defeq.
example : x ∈ (CommanderMembershipKernels.membership d : Finset (Fin 99)) ↔
    x ∈ leftCards d := by
  rw [CommanderMembershipKernels.membership_leftCards d]

end Shufflemath
