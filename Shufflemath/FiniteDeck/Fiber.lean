module

public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

-- The generic two-pile `k`-exchange fiber machinery (roadmap item G2/T1).
-- A deck `Deck N` is a bijection of `Fin N`; for a left pile `A : Membership N m`
-- its fiber is the decks sending the left positions onto `A`. Restricting such a
-- deck to the left (resp. right) positions gives a bijection to `A` (resp. to the
-- complement of `A`). This module proves the left-restriction bijection; the
-- right-restriction bijection and the fiber count follow.
@[expose] public section

namespace Shufflemath
namespace FiniteDeck

def FibType (N m : Nat) (hm : m ≤ N) (A : Membership N m) :=
  {e : Equiv.Perm (Fin N) // (leftPositions N m hm).image (fun p => e p) = A.1}
def LType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (leftPositions N m hm)}
def RType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (rightPositions N m hm)}
def AAType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ A.1}
def BBType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ (Finset.univ \ A.1)}

-- The restriction of a fiber permutation to the left pile is a bijection L ≃ A.
noncomputable def fiberRestrictL (N m : Nat) (hm : m ≤ N) (A : Membership N m) (e : FibType N m hm A) :
    LType N m hm ≃ AAType N m hm A := by
  have hmem : ∀ (l : LType N m hm), e.1 (l.1) ∈ A.1 := by
    intro l
    simpa [e.2, Finset.mem_image] using (Finset.mem_image_of_mem (fun p => e.1 p) l.2)
  apply Equiv.ofBijective (fun l => ⟨e.1 (l.1), hmem l⟩)
  · constructor
    · -- injective: e is a bijection, so it is injective on the left positions
      intro l₁ l₂ h
      have hEq : e.1 (l₁.1) = e.1 (l₂.1) := by
        simpa using (congrArg (fun (z : AAType N m hm A) => z.1) h)
      exact Subtype.ext ((Equiv.injective (e.1)) hEq)
    · -- surjective: e's left-image is exactly A, so every a ∈ A is e p for a left p
      intro a
      have hA : ∃ p ∈ (leftPositions N m hm), e.1 p = a.1 := by
        rw [← Finset.mem_image]
        rw [e.2]
        exact a.2
      rcases hA with ⟨p, hp, heq⟩
      exact ⟨⟨p, hp⟩, Subtype.ext heq⟩
end FiniteDeck
end Shufflemath
