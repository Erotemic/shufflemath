module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.BernoulliLaplace
public import Shufflemath.GSR
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderPhysicalExchange

/-!
# The 25-position physical exchange, at the membership level (F3)

A physical perfect-local exchange between the 50- and 49-card piles picks
25 distinct positions from each pile and swaps the selected positions under
a *fixed* bijective pairing (randomness is in the chosen subsets, not in the
pairing). The exact ordering of the cards after the swap depends on the
pairing, but the *membership* — which named cards end up in the left pile —
depends only on the two selected subsets, because a swap only moves the
selected left cards out and the selected right cards in.

This module defines that membership-level transition `newLeftCards` and its
basic invariants. The macro-count transition it induces (the counting
content of the `hMembershipExchange` premise) is the next item.
-/

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open Finset

/-- The 25-card exchange size. -/
def exchangeSize : Nat := 25

/-- `rightPosition` embeds the 49 right positions at `Fin 99` values 50–98
  and is therefore injective (the mirror of `leftPosition_injective`). -/
theorem rightPosition_injective : Function.Injective rightPosition := by
  intro a b hab
  have hval : (rightPosition a).val = (rightPosition b).val := congrArg Fin.val hab
  have ha : a.val = b.val := by
    rw [rightPosition, rightPosition] at hval
    exact Nat.add_left_cancel_iff.mp hval
  exact Fin.ext ha

/-- The card identities occupying the left pile *after* the selected left
  positions `L` (a subset of the 50 left positions) and selected right
  positions `R` (a subset of the 49 right positions) are exchanged: the
  unselected left positions keep their cards, and the selected right
  positions' cards move in. This is the post-exchange left-pile *content*,
  independent of the ordering of the cards within the pile. -/
def newLeftCards (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) : Finset (Fin 99) :=

  Finset.image (fun (l : Fin 50) => d (leftPosition l)) ((univ : Finset (Fin 50)) \ L) ∪
    Finset.image (fun (r : Fin 49) => d (rightPosition r)) R

/-- The two parts of `newLeftCards` — the unselected left cards and the
  selected right cards — occupy disjoint positions, so their images under the
  injective deck map are disjoint. -/
theorem newLeftCards_parts_disjoint (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    Disjoint (Finset.image (fun (l : Fin 50) => d (leftPosition l)) ((univ : Finset (Fin 50)) \ L))
      (Finset.image (fun (r : Fin 49) => d (rightPosition r)) R) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.ext
  intro card
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨hL, hR⟩
    rcases Finset.mem_image.mp hL with ⟨l, _, heqL⟩
    rcases Finset.mem_image.mp hR with ⟨r, _, heqR⟩
    -- heqL : d (leftPosition l) = card; heqR : d (rightPosition r) = card
    have heq : d (leftPosition l) = d (rightPosition r) := heqL.trans heqR.symm
    have hne : leftPosition l ≠ rightPosition r := by
      intro heq2
      have hval : (leftPosition l).val = (rightPosition r).val := congrArg Fin.val heq2
      have hL : (leftPosition l).val < 50 := by simp [leftPosition]
      have hR : 50 ≤ (rightPosition r).val := by simp [rightPosition]
      omega
    -- d is injective, so distinct positions give distinct cards
    have hdinj : Function.Injective d := d.injective
    have hne' : d (leftPosition l) ≠ d (rightPosition r) := fun heq3 => hne (hdinj heq3)
    exact False.elim (hne' heq)
  · intro h
    have hne : ¬ card ∈ (∅ : Finset (Fin 99)) := by simp
    exact False.elim (hne h)

/-- Exchanging 25 positions from each pile leaves the left pile with exactly
  50 cards: the 25 unselected left cards plus the 25 selected right cards. -/
theorem newLeftCards_card (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49))
    (hL : L.card = 25) (hR : R.card = 25) : (newLeftCards d L R).card = 50 := by
  classical
  unfold newLeftCards
  have hdisj := newLeftCards_parts_disjoint d L R
  rw [Finset.card_union_of_disjoint hdisj]
  have hinjL : Function.Injective (fun (l : Fin 50) => d (leftPosition l)) :=
    d.injective.comp leftPosition_injective
  have hinjR : Function.Injective (fun (r : Fin 49) => d (rightPosition r)) :=
    d.injective.comp rightPosition_injective
  rw [Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]
  -- goal: (univ \ L).card + R.card = 50
  have hLsub : L ⊆ univ := Finset.subset_univ _
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hLsub, hL, hR]
  norm_num


/-- **Spec A2 core: stabilizer-invariance of the exchange, pointwise.** Relabeling the
    cards by a permutation `f` commutes with `newLeftCards`: the post-exchange left
    pile of the relabeled deck `d.trans f` is exactly the `f`-image of the original
    post-exchange left pile.  Holds for any permutation `f`, a fortiori the
    `leftOrigSet`-preserving bijections of `membershipFiber_transitive`. -/
theorem newLeftCards_conjugate (f d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    newLeftCards (d.trans f) L R = (newLeftCards d L R).image f := by
  unfold newLeftCards at *
  apply Finset.ext
  intro c
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.trans, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    rcases h with hL | hR
    · rcases hL with ⟨l, hl, hcl⟩
      refine ⟨d (leftPosition l), ⟨Or.inl ⟨l, hl, rfl⟩, hcl⟩⟩
    · rcases hR with ⟨r, hr, hcr⟩
      refine ⟨d (rightPosition r), ⟨Or.inr ⟨r, hr, rfl⟩, hcr⟩⟩
  · intro h
    rcases h with ⟨a, ha, hac⟩
    rcases ha with hL | hR
    · rcases hL with ⟨l, hl, hal⟩
      refine Or.inl ⟨l, hl, ?_⟩
      simpa [hal] using hac
    · rcases hR with ⟨r, hr, har⟩
      refine Or.inr ⟨r, hr, ?_⟩
      simpa [har] using hac

