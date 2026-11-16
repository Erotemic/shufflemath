module
public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic
@[expose] public section
namespace Shufflemath
namespace FiniteDeck

/-!
The Bernoulli--Laplace refinement of the two-pile subset exchange: the *macro*
state of a deck is the number of marked (initially-left) cards in the left pile.
This module builds the marked-set / count-fiber infrastructure and the count of
each count-fiber, the foundation for the G4 macro-intertwining theorem
(uniform count-fiber ⊳ subsetExchange = blExchange ⊳ uniform count-fiber) and the
discharge of the Commander A3 by specialization at `(99, 50, 50, 25)`.
-/


def markedSet (N r : Nat) (hr : r ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin r)).image (Fin.castLE hr)

theorem markedSet_card (N r : Nat) (hr : r ≤ N) : (markedSet N r hr).card = r := by
  unfold markedSet
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective hr), Finset.card_univ, Fintype.card_fin]

def markedComp (N r : Nat) (hr : r ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)) \ markedSet N r hr

theorem markedComp_card (N r : Nat) (hr : r ≤ N) : (markedComp N r hr).card = N - r := by
  unfold markedComp
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), markedSet_card, Finset.card_univ, Fintype.card_fin]

theorem markedDisjoint (N r : Nat) (hr : r ≤ N) : Disjoint (markedSet N r hr) (markedComp N r hr) := by
  unfold markedComp
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_sdiff_self]

theorem markedCover (N r : Nat) (hr : r ≤ N) :
    (markedSet N r hr) ∪ (markedComp N r hr) = (Finset.univ : Finset (Fin N)) := by
  unfold markedComp
  exact Finset.union_sdiff_of_subset (Finset.subset_univ (markedSet N r hr))

def countFiber (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) : Finset (Finset (Fin N)) :=
  (pileSet N m).filter (fun S => (S ∩ markedSet N r hr).card = x)

theorem countFiber_subset (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) :
    countFiber N m r hm hr x ⊆ pileSet N m := by
  rw [countFiber]
  intro U hU
  exact (Finset.mem_filter.mp hU).1

end FiniteDeck
end Shufflemath
