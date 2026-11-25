module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.Fiber
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G5: multi-pile algebra — the pile-partition type definitions

Generalizes the two-pile fiber theory (G2) from a left/right split to an
arbitrary number `k` of piles.  A **pile partition** is a family
`posPile : Fin k → Finset (Fin N)` of pairwise-disjoint position sets covering
the deck; a **card allocation** `cardPile : Fin k → Finset (Fin N)` is the
analogous partition of the card universe.  A deck `d` **realizes** the
allocation when each pile's positions map onto the corresponding card pile.

This file establishes the reusable multi-pile type (`MultiFiber`) together
with the **two-pile instantiation** (`twoPilePos`, `twoPileCard`), whose pile
`0` / pile `1` are exactly the G2 left and right piles.  The two-pile/two-color
reduction (a two-pile allocation's fiber equals the G2 `FibType`) and the
general-`k` product-factorial fiber count are the next increments; this
increment fixes the shared type definitions they build on.
-/

/-- A deck `d` **realizes** the card allocation `cardPile` relative to the
    positional partition `posPile` when every pile's positions map onto the
    corresponding card pile. -/
def realizesAllocation (N k : Nat)
    (posPile cardPile : Fin k → Finset (Fin N)) (d : Deck N) : Prop :=
  ∀ p, (posPile p).image (fun q => d q) = cardPile p

/-- The **fiber** over a card allocation: all decks realizing it. -/
abbrev MultiFiber (N k : Nat) (posPile cardPile : Fin k → Finset (Fin N)) : Type :=
  {d : Deck N // realizesAllocation N k posPile cardPile d}

variable (N m : Nat) (hm : m ≤ N)

/-- The two-pile positional partition: pile `0` is the left pile, pile `1`
    the right pile. -/
noncomputable def twoPilePos (N m : Nat) (hm : m ≤ N) : Fin 2 → Finset (Fin N) :=
  fun p => if p.val = 0 then leftPositions N m hm else rightPositions N m hm

/-- The two-pile card allocation: pile `0` is the card set `A`, pile `1` its
    complement. -/
noncomputable def twoPileCard (N m : Nat) (A : Membership N m) : Fin 2 → Finset (Fin N) :=
  fun p => if p.val = 0 then A.1 else Finset.univ \ A.1

/-- Pile `0` is the left pile. -/
theorem twoPilePos0 (N m : Nat) (hm : m ≤ N) : twoPilePos N m hm 0 = leftPositions N m hm := by
  simp [twoPilePos]

/-- Pile `1` is the right pile. -/
theorem twoPilePos1 (N m : Nat) (hm : m ≤ N) : twoPilePos N m hm 1 = rightPositions N m hm := by
  simp [twoPilePos]

/-- Pile `0` of the card allocation is the card set `A`. -/
theorem twoPileCard0 (N m : Nat) (A : Membership N m) : twoPileCard N m A 0 = A.1 := by
  simp [twoPileCard]

/-- Pile `1` of the card allocation is the complement of `A`. -/
theorem twoPileCard1 (N m : Nat) (A : Membership N m) : twoPileCard N m A 1 = Finset.univ \ A.1 := by
  simp [twoPileCard]

end FiniteDeck
end Shufflemath
