module

public import Shufflemath.FiniteDeck.Fiber
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic

@[expose] public section
open Classical

namespace Shufflemath
namespace FiniteDeck

-- G2 / T1: the image of the left pile under any permutation is again an
-- m-pile (it has m distinct cards), so it is a valid membership.
theorem leftImageIsMembership (N m : Nat) (hm : m ≤ N) (g : Equiv.Perm (Fin N)) :
    ((leftPositions N m hm).image (fun p => g p)).card = m := by
  have hInjOn : Set.InjOn (fun p => g p) (↑(leftPositions N m hm)) := by
    intro a ha b hb hab
    have h1 : g.symm (g a) = a := Equiv.symm_apply_apply g a
    have h2 : g.symm (g b) = b := Equiv.symm_apply_apply g b
    have h3 : g.symm (g a) = g.symm (g b) := congrArg (fun w => g.symm w) hab
    simpa [h1, h2] using h3
  rw [Finset.card_image_of_injOn hInjOn, leftPositions_card N m hm]

-- G2 / T1: a permutation sends the left pile to a UNIQUE pile, so it lies in
-- at most one membership fiber (the disjointness half of the partition).
theorem fibersUnique (N m : Nat) (hm : m ≤ N) (A B : Membership N m) (g : Equiv.Perm (Fin N)) :
    (leftPositions N m hm).image (fun p => g p) = A.1 →
    (leftPositions N m hm).image (fun p => g p) = B.1 →
    A.1 = B.1 := by
  intro hgA hgB
  simpa [hgA] using hgB
end FiniteDeck
end Shufflemath
