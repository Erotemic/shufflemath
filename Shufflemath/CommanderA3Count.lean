module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFiberCount
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderA3Count

/-!
# A3 count half: the originally-right cards in the left pile

F3 A3 (the membership-exchange law) splits into a *count* half and a
*measure* half.  This module proves the count half for a single
physical-perfect exchange.

Let `e` be a deck (an `Equiv (Fin 99) (Fin 99)`).  A *marked* card is one
that began in the left pile; `leftOriginalCount e` is the number of the 50
left-pile positions holding a marked card (see
`Shufflemath.CommanderPermutation`).  During a physical-perfect exchange the
50 left-pile positions are refilled: `leftOriginalCount e` of them hold a
marked card that stayed put and the rest hold an *unmarked* card that came
from the right pile.  This module pins down that rest: it is exactly
`50 − leftOriginalCount e`.

Concretely, `leftIdxFinset e` is the 50 left-pile indices holding a marked
card and `rightIdxFinset e` is its complement in the 50 left-pile indices
(the originally-right cards that landed in the left pile).  The main result,
`leftUnmarkedCardCount`, gives `#rightIdxFinset e = 50 − leftOriginalCount e`
directly from `Finset.card_sdiff_of_subset`.
-/


open Shufflemath.CommanderPermutation
open Shufflemath.CommanderPhysicalExchange

variable (e : CommanderPermutation.Deck)

/-- A left-pile index `i` is *marked* iff the card now sitting at the
  corresponding left position is one of the 50 originally-left cards, i.e.
  `(e (leftPosition i)) ∈ leftOrigSet`. -/
@[reducible] def leftMarked (e : CommanderPermutation.Deck) (i : Fin 50) : Prop :=
  (e (leftPosition i)).val < 50

/-- The 50 left-pile indices holding a marked (originally-left) card. -/
noncomputable def leftIdxFinset (e : CommanderPermutation.Deck) : Finset (Fin 50) :=
  (Finset.univ : Finset (Fin 50)).filter (fun i => leftMarked e i)

/-- The 50 left-pile indices holding an *unmarked* (originally-right) card —
  the originally-right cards that moved into the left pile during the
  exchange. -/
noncomputable def rightIdxFinset (e : CommanderPermutation.Deck) : Finset (Fin 50) :=
  (Finset.univ : Finset (Fin 50)) \ leftIdxFinset e

/-- The marked count in the left pile equals `leftOriginalCount`: both
  `leftIdxFinset` and `markedLeftPos` are the filter of the 50 left indices by
  the same marked predicate, so their cardinalities agree, and
  `markedLeftPos_card` identifies the latter with `leftOriginalCount`. -/
theorem leftIdxFinset_card (e : CommanderPermutation.Deck) :
    (leftIdxFinset e).card = leftOriginalCount e := by
  unfold leftIdxFinset
  change (CommanderPhysicalExchange.markedLeftPos e).card = leftOriginalCount e
  exact CommanderPhysicalExchange.markedLeftPos_card e

/-- **A3 count half.**  Of the 50 left-pile positions, exactly
  `leftOriginalCount e` hold a card that began in the left pile and the rest,
  `50 − leftOriginalCount e`, hold a card that began in the right pile.  In
  other words, the number of originally-right cards that landed in the left
  pile during a physical-perfect exchange is `50 − leftOriginalCount e`. -/
theorem leftUnmarkedCardCount (e : CommanderPermutation.Deck) :
    (rightIdxFinset e).card = 50 - leftOriginalCount e := by
  unfold rightIdxFinset
  -- leftIdxFinset ⊆ univ  (a filter of univ)
  have hSub : leftIdxFinset e ⊆ (Finset.univ : Finset (Fin 50)) :=
    Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hSub]
  -- #univ (Fin 50) = 50
  have hUniv : (Finset.univ : Finset (Fin 50)).card = 50 := by decide
  rw [hUniv]
  rw [leftIdxFinset_card e]

end CommanderA3Count
end Shufflemath
