module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipKernels
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace _Probe47ad

open Finset
open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace

/-!
# The 50+49 position partition of a deck

The 50 left-position cards and the 49 right-position cards of a deck partition
the 99 cards.  Proved by cardinality: the union is a subset of the 99 univ with
`50 + 49 - 0 = 99` cards, so it is the whole univ.  (A pure per-element
`Equiv.Perm` surjectivity argument triggers WHNF timeouts on the `Fin 99`
image machinery, so the size argument is the robust route.)  These facts are
the geometric backbone of the F3 A3 point-mass argument: the post-exchange left
pile is a 25-card slice of the left image plus a 25-card slice of the right
image, and together they span the full deck.
-/

variable (d : Deck)

/-- The right-position cards of a deck: the image of the 49 right positions. -/
abbrev rightCards (d : Deck) : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 49)).image (fun r => d (rightPosition r))

/-- The 50 left-position cards and the 49 right-position cards of a deck
    partition the 99 cards. -/
theorem leftCards_union_rightCards_univ (d : Deck) :
    leftCards d ∪ rightCards d = (Finset.univ : Finset (Fin 99)) := by
  classical
  -- the union is a subset of the 99 univ (both images live in Fin 99).
  have hsub : leftCards d ∪ rightCards d ⊆ (Finset.univ : Finset (Fin 99)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hL | hR
    · rcases Finset.mem_image.mp hL with ⟨_, _, rfl⟩
      exact Finset.mem_univ _
    · rcases Finset.mem_image.mp hR with ⟨_, _, rfl⟩
      exact Finset.mem_univ _
  -- the left image has 50 distinct cards.
  have hL : (leftCards d).card = 50 := leftCards_card d
  -- the right image has 49 distinct cards (d is injective, right positions disjoint).
  have hR : (rightCards d).card = 49 := by
    unfold rightCards
    have hinj : Function.Injective (fun r : Fin 49 => d (rightPosition r)) :=
      d.injective.comp rightPosition_injective
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin 49)) hinj, Finset.card_univ]
    norm_num
  -- the two position images are disjoint.
  have hdisj : Disjoint (leftCards d) (rightCards d) := by
    unfold rightCards
    exact leftCards_disjoint_rightCards d
  -- their intersection therefore has 0 cards.
  have hI : (leftCards d ∩ rightCards d).card = 0 := by
    have hempty : leftCards d ∩ rightCards d = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    rw [hempty, Finset.card_empty]
  -- a disjoint union has additive cardinality: 50 + 49 = 99, the size of the univ.
  have hcard : (leftCards d ∪ rightCards d).card = 99 := by
    rw [Finset.card_union_of_disjoint hdisj, hL, hR]
  -- a subset of the univ with the univ's cardinality is the univ:
  -- `univ \ union` has `99 - 99 = 0` cards, hence is empty, hence `univ ⊆ union`.
  have hsdiff : ((Finset.univ : Finset (Fin 99)) \ (leftCards d ∪ rightCards d)).card = 0 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, hcard]
    norm_num
  have hempty : (Finset.univ : Finset (Fin 99)) \ (leftCards d ∪ rightCards d) = ∅ :=
    Finset.card_eq_zero.mp hsdiff
  have hsup : (Finset.univ : Finset (Fin 99)) ⊆ leftCards d ∪ rightCards d :=
    Finset.sdiff_eq_empty_iff_subset.mp hempty
  exact Finset.Subset.antisymm hsub hsup

/-- The left-position and right-position card sets of a deck are disjoint. -/
theorem leftCards_disjoint_rightCards' (d : Deck) :
    Disjoint (leftCards d) (rightCards d) := by
  simpa [rightCards] using leftCards_disjoint_rightCards d

/-- The complement of the left-position cards is exactly the right-position
    cards (the 50+49 partition): a card that is not a left-position card is a
    right-position card. -/
theorem univ_sdiff_leftCards_eq_rightCards (d : Deck) :
    (Finset.univ : Finset (Fin 99)) \ leftCards d = rightCards d := by
  have hU : leftCards d ∪ rightCards d = (Finset.univ : Finset (Fin 99)) :=
    leftCards_union_rightCards_univ d
  have hdisj : Disjoint (leftCards d) (rightCards d) := leftCards_disjoint_rightCards' d
  apply Finset.ext
  intro x
  constructor
  · -- `x ∈ univ \ leftCards` ⇒ `x ∈ rightCards`: `x ∉ leftCards` and `x` is in the
    -- partition `leftCards ∪ rightCards = univ`, so it must be in `rightCards`.
    intro hpre
    rcases Finset.mem_sdiff.mp hpre with ⟨_, hxnL⟩
    have hxU : x ∈ leftCards d ∪ rightCards d := by
      rw [hU]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxU with hxL | hxR
    · exact False.elim (hxnL hxL)
    · exact hxR
  · -- `x ∈ rightCards` ⇒ `x ∈ univ \ leftCards`: `x` is a card (in univ) and is
    -- not a left-position card (the two images are disjoint).
    intro hxR
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hxnL
    have hmem : x ∈ leftCards d ∩ rightCards d := Finset.mem_inter.mpr ⟨hxnL, hxR⟩
    simpa [Finset.disjoint_iff_inter_eq_empty.mp hdisj] using hmem

end _Probe47ad
end Shufflemath
