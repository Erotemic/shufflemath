module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# Pile histograms (B3 lumping)

This module defines the lumped histogram: given a `k`-pile allocation
`cardPile : Fin k → Finset (Fin N)` and a category map `color : Fin N → Fin c`,
`lump` counts how many cards of category `j` sit in pile `i`.  It then proves
the row-total fact: summing the `j`-counts over all categories recovers the
pile's card count (the color filters partition a pile).

This is the reusable arbitrary-finite-deck core that B4 (multi-pile exchange)
and T5 (within-pile orbit) build on.  It generalizes `Fiber.lean`'s
`swapFiber` (k = 2, categories = the two piles).

## Note on this Mathlib's `Finset` API

The classic spellings `Finset.count` and `Finset.PairwiseDisjoint` are not
available in this Mathlib version: `count` has been refactored away (use
`filter … |>.card`) and `PairwiseDisjoint` lives at the `Set` level
(coerce a `Finset` with `(s : Set ι)`).  This file is written against that
API, mirroring the `fiberDisjoint` / `fiberCard` / `Finset.card_biUnion`
idiom already in `FiniteDeck/Fiber.lean`.

### Column total

`lump_categoryTotal` — summing the `i`-counts over all piles equals the deck's
category-`j` count — additionally needs the piles to be **pairwise disjoint**
(a valid allocation); with a `hPiles : ∀ i j, i ≠ j → Disjoint (cardPile i)
(cardPile j)` hypothesis it goes through by `Finset.card_biUnion` on the
filtered piles plus `Finset.filter_biUnion`.  Proved below.
-/

/-- The lumped count of category-`j` cards inside pile `i`.
    Uses `filter … |>.card` (this Mathlib has no `Finset.count`). -/
def lump (cardPile : Fin k → Finset (Fin N)) (color : Fin N → Fin c)
    (i : Fin k) (j : Fin c) : ℕ :=
  (cardPile i).filter (fun x => color x = j) |>.card

/-- Row-sum: summing the `j`-counts over all categories gives the pile's
    total card count.  The color filters of a fixed pile partition that pile
    (every card has exactly one color), so their disjoint union is the pile. -/
theorem lump_pileTotal (cardPile : Fin k → Finset (Fin N)) (color : Fin N → Fin c)
    (i : Fin k) :
    (Finset.univ : Finset (Fin c)).sum (fun j => lump cardPile color i j) =
      (cardPile i).card := by
  let hf (j : Fin c) := (cardPile i).filter (fun x : Fin N => color x = j)
  -- Unfold `lump` to the `hf`-indexed card counts.
  have hLump : (Finset.univ : Finset (Fin c)).sum (fun j => lump cardPile color i j) =
      (Finset.univ : Finset (Fin c)).sum (fun j => (hf j).card) := by
    simp only [lump, hf]
  rw [hLump]
  -- Disjointness: two different color filters of the same pile share no card
  -- (a card has one color).  Mirrors `FiniteDeck.Fiber.fiberDisjoint`.
  have hDisj : ((Finset.univ : Finset (Fin c)) : Set (Fin c)).PairwiseDisjoint hf := by
    intros a _ b _ hne
    change Disjoint (hf a) (hf b)
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    subst y
    simp only [hf, Finset.mem_filter] at hx hy
    exact hne (hx.2.symm.trans hy.2)
  -- Cover: the color filters of the pile union to the pile itself.
  have hCover : ((Finset.univ : Finset (Fin c)).biUnion hf) = (cardPile i) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hf, Finset.mem_filter]
    by_cases hxc : x ∈ cardPile i
    · constructor
      · rintro ⟨_, ⟨hxc', _⟩⟩; exact hxc'
      · intro _; exact ⟨color x, ⟨hxc, rfl⟩⟩
    · constructor
      · rintro ⟨_, ⟨hxc', _⟩⟩; exact hxc'
      · intro h; exact (hxc h).elim
  calc (Finset.univ : Finset (Fin c)).sum (fun j => (hf j).card)
      = (((Finset.univ : Finset (Fin c)).biUnion hf)).card := (Finset.card_biUnion hDisj).symm
    _ = (cardPile i).card := congrArg Finset.card hCover

/-- Column-sum: summing the `i`-counts over all piles equals the number of
    category-`j` cards in the union of the piles.  The piles are assumed
    pairwise disjoint (a valid allocation); disjoint piles make the filtered
    (category-`j`) sub-piles disjoint, so their `card`s sum to the `card` of
    their `biUnion`, which (by `Finset.filter_biUnion`) is the filter of the
    piles' `biUnion`.  When the piles partition the whole deck, the right side
    is the deck's category-`j` count. -/
theorem lump_categoryTotal
    (cardPile : Fin k → Finset (Fin N)) (color : Fin N → Fin c)
    (hPiles : ∀ i j, i ≠ j → Disjoint (cardPile i) (cardPile j))
    (j : Fin c) :
    (Finset.univ : Finset (Fin k)).sum (fun i => lump cardPile color i j) =
      (((Finset.univ : Finset (Fin k)).biUnion cardPile).filter (fun x => color x = j)).card := by
  let p (x : Fin N) : Prop := color x = j
  let hf (i : Fin k) := (cardPile i).filter p
  -- Unfold `lump` to the filtered sub-pile card counts.
  have hLump : (Finset.univ : Finset (Fin k)).sum (fun i => lump cardPile color i j) =
      (Finset.univ : Finset (Fin k)).sum (fun i => (hf i).card) := by
    simp only [lump, hf, p]
  -- The filtered sub-piles are disjoint: a card common to two of them would be
  -- in two disjoint piles.  Mirrors the disjointness step of `lump_pileTotal`.
  have hDisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint hf := by
    intros a _ b _ hne
    change Disjoint (hf a) (hf b)
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [hf, p, Finset.mem_filter] at hx hy
    have hPD := Finset.disjoint_iff_ne.mp (hPiles a b hne)
    exact (hPD x hx.1 y hy.1) hxy
  -- Sum the disjoint sub-pile cards to the `biUnion`'s card, then commute the
  -- `filter` across the `biUnion`.
  calc (Finset.univ : Finset (Fin k)).sum (fun i => (hf i).card)
      = (((Finset.univ : Finset (Fin k)).biUnion hf)).card := (Finset.card_biUnion hDisj).symm
    _ = (((Finset.univ : Finset (Fin k)).biUnion cardPile).filter p).card := by
        simp only [Finset.filter_biUnion, hf, p]

end FiniteDeck
end Shufflemath
