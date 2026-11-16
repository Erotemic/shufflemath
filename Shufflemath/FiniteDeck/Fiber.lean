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

-- The restriction of a fiber permutation to the right positions is a bijection
-- to the complement of the left pile `A`: the right-image of a fiber deck is
-- exactly `univ \ A`, because the deck is a bijection and its left-image is `A`.
noncomputable def fiberRestrictR (N m : Nat) (hm : m ≤ N) (A : Membership N m) (e : FibType N m hm A) :
    RType N m hm ≃ BBType N m hm A := by
  have hmem : ∀ (r : RType N m hm), e.1 (r.1) ∈ (Finset.univ \ A.1) := by
    intro r
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · -- e.1 (r.1) ∉ A.1: if it were, its left-preimage would equal r.1, a left position
      intro h
      have hImg : e.1 (r.1) ∈ (leftPositions N m hm).image (fun p => e.1 p) := by
        simpa [e.2] using h
      rcases Finset.mem_image.mp hImg with ⟨p, hp, heq⟩
      have hInj : p = r.1 := (Equiv.injective (e.1)) heq
      have hLeft : r.1 ∈ leftPositions N m hm := by
        simpa [hInj] using hp
      have hNotLeft : r.1 ∉ leftPositions N m hm := by
        have hr2 : r.1 ∈ rightPositions N m hm := r.2
        dsimp only [rightPositions] at hr2
        rw [Finset.mem_sdiff] at hr2
        exact hr2.2
      exact hNotLeft hLeft
  apply Equiv.ofBijective (fun r => ⟨e.1 (r.1), hmem r⟩)
  · constructor
    · intro r₁ r₂ h
      have hEq : e.1 (r₁.1) = e.1 (r₂.1) := by
        simpa using (congrArg (fun (z : BBType N m hm A) => z.1) h)
      exact Subtype.ext ((Equiv.injective (e.1)) hEq)
    · -- surjective: b.1 ∉ A.1, so its unique preimage under the bijection e.1 is a right position
      intro b
      let q := (e.1).symm (b.1)
      have hq : e.1 q = b.1 := Equiv.apply_symm_apply (e.1) (b.1)
      have hNotLeft : q ∉ leftPositions N m hm := by
        intro h
        have hImg : e.1 q ∈ (leftPositions N m hm).image (fun p => e.1 p) := by
          simpa [Finset.mem_image] using h
        have hInA : e.1 q ∈ A.1 := by
          simpa [e.2] using hImg
        have hb2 : b.1 ∈ Finset.univ \ A.1 := b.2
        rw [Finset.mem_sdiff] at hb2
        exact hb2.2 (by simpa [hq] using hInA)
      have hRight : q ∈ rightPositions N m hm := by
        rw [rightPositions, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hNotLeft⟩
      exact ⟨⟨q, hRight⟩, Subtype.ext hq⟩
end FiniteDeck
end Shufflemath
