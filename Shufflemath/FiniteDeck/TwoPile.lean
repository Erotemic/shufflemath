module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G1: a finite deck of `N` cards with a two-pile split

The foundational object of the shufflemath generalization is a **finite labeled
card universe** `Fin N` together with a partition of the deck *positions* into a
left pile (the first `m` positions) and a right pile (the remaining `N - m`).
The 99-card Commander deck is the specialization `N = 99`, `m = 50`.

Everything here is parametrized by `N` and `m` (with `m ≤ N`) and imports no
`Commander*` module.  A `Deck N` is a permutation of the `N` positions; its
`Membership N m` is the `Finset` of cards occupying the left pile.  The left /
right positional finsets (which cover the deck disjointly and have sizes `m`
and `N - m`) are the structural lemma the counting (G2) and exchange (G3)
layers build on.
-/

/-- A deck of `N` named cards: a bijection of the `N` positions. -/
abbrev Deck (N : Nat) := Equiv.Perm (Fin N)

/-- The set of cards in the left pile: a `Finset` of `m` of the `N` cards. -/
abbrev Membership (N m : Nat) := {S : Finset (Fin N) // S.card = m}

/-- The `m` left-deck positions, as a finset of positions of the whole deck. -/
def leftPositions (N m : Nat) (hm : m ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin m)).image (Fin.castLE hm)

/-- The `N - m` right-deck positions: the complement of the left positions. -/
def rightPositions (N m : Nat) (hm : m ≤ N) : Finset (Fin N) :=
  Finset.univ \ leftPositions N m hm

theorem leftPositions_card (N m : Nat) (hm : m ≤ N) : (leftPositions N m hm).card = m := by
  unfold leftPositions
  rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) (Fin.castLE_injective hm),
    Finset.card_univ, Fintype.card_fin]

theorem rightPositions_card (N m : Nat) (hm : m ≤ N) : (rightPositions N m hm).card = N - m := by
  unfold rightPositions
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (leftPositions N m hm)), leftPositions_card,
    Finset.card_univ, Fintype.card_fin]

theorem leftRight_cover (N m : Nat) (hm : m ≤ N) :
    leftPositions N m hm ∪ rightPositions N m hm = Finset.univ := by
  unfold rightPositions
  rw [Finset.union_comm, Finset.sdiff_union_of_subset (Finset.subset_univ (leftPositions N m hm))]

theorem leftRight_disjoint (N m : Nat) (hm : m ≤ N) :
    Disjoint (leftPositions N m hm) (rightPositions N m hm) := by
  unfold rightPositions
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.ext
  intro i
  simp

/-- The cards a deck puts in the left pile. -/
def leftCards (N m : Nat) (hm : m ≤ N) (d : Deck N) : Finset (Fin N) :=
  (leftPositions N m hm).image (fun p => d p)

theorem leftCards_card (N m : Nat) (hm : m ≤ N) (d : Deck N) : (leftCards N m hm d).card = m := by
  unfold leftCards
  rw [Finset.card_image_of_injective (leftPositions N m hm) d.injective]
  exact leftPositions_card N m hm

/-- The membership (left pile) carried by a deck. -/
def membership (N m : Nat) (hm : m ≤ N) (d : Deck N) : Membership N m :=
  ⟨leftCards N m hm d, leftCards_card N m hm d⟩

/-- At least one membership exists: the left positions themselves. -/
theorem membership_nonempty (N m : Nat) (hm : m ≤ N) : Nonempty (Membership N m) :=
  ⟨⟨leftPositions N m hm, leftPositions_card N m hm⟩⟩
end FiniteDeck
end Shufflemath
