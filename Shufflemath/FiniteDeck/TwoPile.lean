module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
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

/-- The finset of all `m`-element piles of the `N`-card deck (the concrete state
  space for the pile-level theory; a `Membership N m` is exactly such a pile with
  its size proof). -/
def pileSet (N m : Nat) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard m

/-- Embed a left-pile index (of the `m` left positions) into a deck position
  `0, 1, ..., m-1` (the same `Fin.castLE` embedding that `leftPositions` uses). -/
def leftPosition (N m : Nat) (hm : m ≤ N) (i : Fin m) : Fin N :=
  Fin.castLE hm i

/-- Embed a right-pile index (of the `N - m` right positions) into a deck position
  `m, m+1, ..., N-1`. -/
def rightPosition (N m : Nat) (hm : m ≤ N) (i : Fin (N - m)) : Fin N :=
  ⟨m + i.val, by
    have hlt : i.val + m < (N - m) + m := Nat.add_lt_add_right i.isLt m
    have hsum : (N - m) + m = N := Nat.sub_add_cancel hm
    omega⟩

theorem leftPosition_injective (N m : Nat) (hm : m ≤ N) : Function.Injective (leftPosition N m hm) :=
  Fin.castLE_injective hm

theorem rightPosition_injective (N m : Nat) (hm : m ≤ N) : Function.Injective (rightPosition N m hm) := by
  intro a b hab
  have hval : m + a.val = m + b.val := by
    have h0 : (rightPosition N m hm a).val = (rightPosition N m hm b).val := congrArg Fin.val hab
    simpa [rightPosition] using h0
  exact Fin.ext (Nat.add_left_cancel_iff.mp hval)

theorem leftPosition_memLeft (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    leftPosition N m hm i ∈ leftPositions N m hm := by
  dsimp only [leftPosition, leftPositions]
  exact Finset.mem_image_of_mem (Fin.castLE hm) (Finset.mem_univ i)

theorem rightPosition_memRight (N m : Nat) (hm : m ≤ N) (i : Fin (N - m)) :
    rightPosition N m hm i ∈ rightPositions N m hm := by
  unfold rightPositions
  rw [Finset.mem_sdiff]
  constructor
  · exact Finset.mem_univ _
  · intro h
    have hmem : rightPosition N m hm i ∈ (Finset.univ : Finset (Fin m)).image (Fin.castLE hm) := by
      dsimp only [leftPositions] at h
      exact h
    rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
    have hval : j.val = m + i.val := by
      have h0 : (Fin.castLE hm j).val = (rightPosition N m hm i).val := congrArg Fin.val heq
      have h1 : (Fin.castLE hm j).val = j.val := by dsimp only [Fin.castLE]
      have h2 : (rightPosition N m hm i).val = m + i.val := by dsimp only [rightPosition]
      omega
    have hjlt : j.val < m := j.isLt
    omega

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
