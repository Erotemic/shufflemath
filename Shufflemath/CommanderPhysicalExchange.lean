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

/-- The original left pile is disjoint from the selected-right-card part of the
    post-exchange pile: a left-position card can never coincide with a right-position
    card under a bijective deck map.  (Same argument as `newLeftCards_parts_disjoint`,
    but with the whole left image rather than the unselected part.) -/
theorem leftCards_disjoint_rightImage (d : Deck) (R : Finset (Fin 49)) :
    Disjoint (leftCards d)
      (Finset.image (fun (r : Fin 49) => d (rightPosition r)) R) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.ext
  intro c
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨hL, hR⟩
    rcases Finset.mem_image.mp hL with ⟨l, _hl, hcl⟩
    rcases Finset.mem_image.mp hR with ⟨r, _hr, hcr⟩
    have heq : d (leftPosition l) = d (rightPosition r) := hcl.trans hcr.symm
    have hne : leftPosition l ≠ rightPosition r := by
      intro heq2
      have hval : (leftPosition l).val = (rightPosition r).val := congrArg Fin.val heq2
      have hL : (leftPosition l).val < 50 := by simp [leftPosition]
      have hR : 50 ≤ (rightPosition r).val := by simp [rightPosition]
      omega
    exact False.elim (hne (d.injective heq))
  · intro h
    have hne' : ¬ c ∈ (∅ : Finset (Fin 99)) := by simp
    exact False.elim (hne' h)

/-- The left-position cards and the right-position cards of a deck are disjoint:
    a card sits at exactly one position (the deck is a bijection), and the left
    position set `{0,…,49}` is disjoint from the right position set `{50,…,98}`. -/
theorem leftCards_disjoint_rightCards (d : Deck) :
    Disjoint (leftCards d) ((univ : Finset (Fin 49)).image (fun r => d (rightPosition r))) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.ext
  intro c
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨hL, hR⟩
    rcases Finset.mem_image.mp hL with ⟨l, _hl, hcl⟩
    rcases Finset.mem_image.mp hR with ⟨r, _hr, hcr⟩
    have heq : d (leftPosition l) = d (rightPosition r) := hcl.trans hcr.symm
    have hne : leftPosition l ≠ rightPosition r := by
      intro heq2
      have hval : (leftPosition l).val = (rightPosition r).val := congrArg Fin.val heq2
      have hL : (leftPosition l).val < 50 := by simp [leftPosition]
      have hR : 50 ≤ (rightPosition r).val := by simp [rightPosition]
      omega
    exact False.elim (hne (d.injective heq))
  · intro h
    have hne' : ¬ c ∈ (∅ : Finset (Fin 99)) := by simp
    exact False.elim (hne' h)

/-- The post-exchange left pile shares exactly the unselected left cards with the
    original left pile: `newLeftCards`'s left-not-in-`L` image sits inside `leftCards`,
    and its right-card image is disjoint from `leftCards`, so the intersection is the
    unselected-left part. -/
theorem newLeftCards_inter_leftCards (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    leftCards d ∩ newLeftCards d L R =
      Finset.image (fun (l : Fin 50) => d (leftPosition l))
        ((univ : Finset (Fin 50)) \ L) := by
  classical
  have hA_sub : Finset.image (fun (l : Fin 50) => d (leftPosition l))
      ((univ : Finset (Fin 50)) \ L) ⊆ leftCards d := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨l, hl, hcl⟩
    have hl_univ : l ∈ (univ : Finset (Fin 50)) := (Finset.mem_sdiff.mp hl).1
    simpa [leftCards] using Finset.mem_image.mpr ⟨l, hl_univ, hcl⟩
  have hB_empty : leftCards d ∩
      Finset.image (fun (r : Fin 49) => d (rightPosition r)) R = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (leftCards_disjoint_rightImage d R)
  rw [newLeftCards, Finset.inter_union_distrib_left,
      Finset.inter_eq_right.mpr hA_sub, hB_empty]
  simp

/-- **25-overlap preservation (the structural core of a 25/25 exchange).** Exchanging
    25 positions out of each pile leaves the post-exchange left pile sharing exactly
    25 cards with the original left pile: the 25 unselected left cards stay, and the
    25 selected right cards are all new cards.  This is the membership-level statement
    underlying the Bernoulli-Laplace `25`-card swap and a building block for both the
    count-transition and within-count-uniformity halves of the A3 membership-exchange
    discharge. -/
theorem newMembership_overlap_25 (d : Deck) (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (_hR : R.card = 25) :
    ((membership d).1 ∩ newLeftCards d L R).card = 25 := by
  classical
  have hm1 : (membership d).1 = leftCards d := membership_leftCards d
  rw [hm1, newLeftCards_inter_leftCards d L R]
  have hinj : Function.Injective (fun (l : Fin 50) => d (leftPosition l)) :=
    d.injective.comp leftPosition_injective
  have hLsub : L ⊆ (univ : Finset (Fin 50)) := Finset.subset_univ _
  rw [Finset.card_image_of_injective _ hinj, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hLsub, hL]
  have huniv : (univ : Finset (Fin 50)).card = 50 := by simp
  simp [huniv]

/-! ## Step 2 — the deck-level position-choice map is injective

For a *fixed* deck `d`, a position choice `(L, R)` is recoverable from the
post-exchange left pile: the pile splits uniquely into its left-position cards
(and its right-position cards), each part lying in a disjoint region, so equal
piles force equal choices.  These lemmas are the "unique half" of the
`deck-level (L,R) → T` bijection (5-step plan, step 2); they reuse the 47g
disjointness facts.
-/ 

/-- For an injective map, equal images of two finite sets force the sets equal:
    every element is recovered from its unique image. -/
theorem image_injective_eq {α β} [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) {A B : Finset α}
    (h : Finset.image f A = Finset.image f B) : A = B := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hfa : f a ∈ Finset.image f A := Finset.mem_image_of_mem f ha
    rw [h] at hfa
    rcases Finset.mem_image.mp hfa with ⟨b, hb, hfb⟩
    exact (hf hfb) ▸ hb
  · intro ha
    have hfa : f a ∈ Finset.image f B := Finset.mem_image_of_mem f ha
    rw [← h] at hfa
    rcases Finset.mem_image.mp hfa with ⟨b, hb, hfb⟩
    exact (hf hfb) ▸ hb

/-- The left-position part of the post-exchange pile is exactly the part lying
    inside the original left pile: the selected-right part is disjoint from it, and
    the unselected-left part sits inside it. -/
theorem newLeftCards_leftPart (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    ((univ : Finset (Fin 50)) \ L).image (fun (l : Fin 50) => d (leftPosition l)) =
      newLeftCards d L R ∩ leftCards d := by
  classical
  unfold newLeftCards
  rw [Finset.inter_comm, Finset.inter_union_distrib_left]
  have hAsub :
      ((univ : Finset (Fin 50)) \ L).image (fun (l : Fin 50) => d (leftPosition l)) ⊆ leftCards d := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨l, hl, hcl⟩
    have hlU : l ∈ (univ : Finset (Fin 50)) := (Finset.mem_sdiff.mp hl).1
    simpa [leftCards] using Finset.mem_image.mpr ⟨l, hlU, hcl⟩
  have hBempty : leftCards d ∩ R.image (fun (r : Fin 49) => d (rightPosition r)) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (leftCards_disjoint_rightImage d R)
  rw [Finset.inter_eq_right.mpr hAsub, hBempty]
  simp

/-- The right-position part of the post-exchange pile is exactly the part lying
    inside the *selected* right-position cards: the unselected-left part is
    disjoint from it, and the selected-right part is the whole intersection.
    (Intersecting with the selected part, rather than the full right image,
    keeps the disjointness reference light.  Since the selected part is itself a
    subset of the pile, the intersection recovers it exactly.) -/
theorem newLeftCards_rightPart (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    R.image (fun (r : Fin 49) => d (rightPosition r)) =
      newLeftCards d L R ∩ R.image (fun (r : Fin 49) => d (rightPosition r)) := by
  have hAemptyL : R.image (fun (r : Fin 49) => d (rightPosition r)) ∩
      ((univ : Finset (Fin 50)) \ L).image (fun (l : Fin 50) => d (leftPosition l)) = ∅ := by
    rw [Finset.inter_comm]
    exact Finset.disjoint_iff_inter_eq_empty.mp (newLeftCards_parts_disjoint d L R)
  unfold newLeftCards
  rw [Finset.inter_comm, Finset.inter_union_distrib_left, hAemptyL]
  simp

/-- For a fixed deck `d`, the *left*-position choice `L` is recovered from the
    post-exchange left pile: two choices giving the same pile have the same `L`
    (the pile's left-position part is exactly `leftCards d`, which `d` labels
    bijectively over the unselected left positions, so equal piles force equal
    unselected-left sets, hence equal `L`).  The symmetric `R`-recovery, and the
    full `(L, R) → T` injectivity, are the next steps (they need the deck-only
    right-region disjointness). -/
theorem newLeftCards_injective_L (d : Deck) (L L' : Finset (Fin 50)) (R R' : Finset (Fin 49)) :
    newLeftCards d L R = newLeftCards d L' R' → L = L' := by
  intro h
  have hinjL : Function.Injective (fun (l : Fin 50) => d (leftPosition l)) :=
    d.injective.comp leftPosition_injective
  -- the left-position parts of the two piles coincide
  have hLpart :
      ((univ : Finset (Fin 50)) \ L).image (fun (l : Fin 50) => d (leftPosition l)) =
        ((univ : Finset (Fin 50)) \ L').image (fun (l : Fin 50) => d (leftPosition l)) := by
    rw [newLeftCards_leftPart d L R, h, ← newLeftCards_leftPart d L' R']
  have hUL : ((univ : Finset (Fin 50)) \ L) = ((univ : Finset (Fin 50)) \ L') :=
    image_injective_eq (fun (l : Fin 50) => d (leftPosition l)) hinjL hLpart
  have hL : L = L' := by
    apply Finset.ext
    intro x
    have hULx : (x ∈ ((univ : Finset (Fin 50)) \ L)) ↔ (x ∈ ((univ : Finset (Fin 50)) \ L')) := by
      constructor
      · intro hx; exact hUL ▸ hx
      · intro hx; exact hUL.symm ▸ hx
    have h1 : (x ∈ ((univ : Finset (Fin 50)) \ L)) ↔ ¬ (x ∈ L) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    have h2 : (x ∈ ((univ : Finset (Fin 50)) \ L')) ↔ ¬ (x ∈ L') := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · -- x ∈ L → x ∈ L'
      intro hxL
      by_contra hxnotL'
      have hnotUL : ¬ (x ∈ ((univ : Finset (Fin 50)) \ L)) := fun h => (h1.mp h) hxL
      have hnotUL' : ¬ (x ∈ ((univ : Finset (Fin 50)) \ L')) := fun h => hnotUL (hULx.mpr h)
      exact hnotUL' (h2.mpr hxnotL')
    · -- x ∈ L' → x ∈ L
      intro hxL'
      by_contra hxnotL
      have hnotUL' : ¬ (x ∈ ((univ : Finset (Fin 50)) \ L')) := fun h => (h2.mp h) hxL'
      have hnotUL : ¬ (x ∈ ((univ : Finset (Fin 50)) \ L)) := fun h => hnotUL' (hULx.mp h)
      exact hnotUL (h1.mpr hxnotL)
  exact hL

/-- The unselected-left part of the post-exchange pile is disjoint from the deck's full
    right-position card set: the left part sits in `leftCards d`, which is disjoint from
    the right positions. -/
theorem leftImg_disjoint_rightFull (d : Deck) (L : Finset (Fin 50)) :
    ((univ : Finset (Fin 50)) \ L).image (fun l => d (leftPosition l)) ∩
      (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) = ∅ := by
  have hsub : ((univ : Finset (Fin 50)) \ L).image (fun l => d (leftPosition l)) ⊆ leftCards d := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨l, hl, hcl⟩
    have hlU : l ∈ (univ : Finset (Fin 50)) := (Finset.mem_sdiff.mp hl).1
    simpa [leftCards] using Finset.mem_image.mpr ⟨l, hlU, hcl⟩
  have hdis : leftCards d ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (leftCards_disjoint_rightCards d)
  apply Finset.ext
  intro c
  constructor
  · intro hc
    rcases Finset.mem_inter.mp hc with ⟨hcL, hcR⟩
    have hcLeftCards : c ∈ leftCards d := hsub hcL
    have hboth : c ∈ leftCards d ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) :=
      Finset.mem_inter.mpr ⟨hcLeftCards, hcR⟩
    exact hdis ▸ hboth
  · intro hc
    exact absurd hc (by simp : ¬ c ∈ (∅ : Finset (Fin 99)))

/-- The selected-right image is recoverable from the post-exchange left pile by
    intersecting with the deck's full right-position card set (the left part is
    disjoint from that set; the selected-right part already sits inside it). -/
theorem newLeftCards_rightPart_deck (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    R.image (fun r => d (rightPosition r)) =
      newLeftCards d L R ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) := by
  have hAempty := leftImg_disjoint_rightFull d L
  have hAemptyR : (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) ∩
      ((univ : Finset (Fin 50)) \ L).image (fun l => d (leftPosition l)) = ∅ :=
    (Finset.inter_comm _ _).symm.trans hAempty
  have hrightSub : R.image (fun r => d (rightPosition r)) ⊆
      (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨r, hr, hcr⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hcr⟩
  unfold newLeftCards
  rw [Finset.inter_comm, Finset.inter_union_distrib_left, hAemptyR, Finset.empty_union]
  exact (Finset.ext fun c => Iff.intro
    (fun hc => Finset.mem_inter.mpr ⟨hrightSub hc, hc⟩)
    (fun hc => (Finset.mem_inter.mp hc).2))

/-- **Step 2 (unique half, full):** the map `(L, R) ↦ newLeftCards d L R` is injective
    for a fixed deck `d`: equal post-exchange left piles force equal `L` and equal `R`.
    This is the uniqueness half of the (L,R)↦T bijection of the physical exchange. -/
theorem newLeftCards_injective (d : Deck) (L L' : Finset (Fin 50)) (R R' : Finset (Fin 49))
    (h : newLeftCards d L R = newLeftCards d L' R') : L = L' ∧ R = R' := by
  have hL : L = L' := newLeftCards_injective_L d L L' R R' h
  have h2 : newLeftCards d L R = newLeftCards d L R' := by simpa [← hL] using h
  have hpartR : R.image (fun r => d (rightPosition r)) =
      newLeftCards d L R ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) :=
    newLeftCards_rightPart_deck d L R
  have hpartR' : R'.image (fun r => d (rightPosition r)) =
      newLeftCards d L R' ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) :=
    newLeftCards_rightPart_deck d L R'
  have himg : R.image (fun r => d (rightPosition r)) = R'.image (fun r => d (rightPosition r)) := by
    calc
      _ = newLeftCards d L R ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) := hpartR
      _ = newLeftCards d L R' ∩ (univ : Finset (Fin 49)).image (fun r => d (rightPosition r)) := by rw [h2]
      _ = R'.image (fun r => d (rightPosition r)) := hpartR'.symm
  have hR : R = R' :=
    image_injective_eq (fun r => d (rightPosition r)) (by
      intro r r' h
      have hval : (rightPosition r).val = (rightPosition r').val := congrArg Fin.val (d.injective h)
      have hrv : r.val = r'.val := by simp [rightPosition] at hval ⊢; omega
      exact Fin.val_injective hrv) himg
  exact ⟨hL, hR⟩

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

/-!
## The macro-count transition

The macro state of a deck is how many *initially-left* (marked) cards sit in
the left pile, `leftOriginalCount`. Exchanging the selected positions moves
the marked cards at the selected left positions out and the marked cards at
the selected right positions in, so the new marked count is the old count
minus what left plus what came in. This is the count content of the
`hMembershipExchange` premise, stated at the level of the selected sets.
-/ 

/-- The initially-left (marked) positions among the 50 left positions. Its
  cardinality is exactly the macro count `leftOriginalCount`. -/
def markedLeftPos (d : Deck) : Finset (Fin 50) :=
  Finset.filter (fun (l : Fin 50) => (d (leftPosition l)).val < 50) (univ : Finset (Fin 50))

/-- `markedLeftPos` counts the marked cards in the left pile. -/
theorem markedLeftPos_card (d : Deck) : (markedLeftPos d).card = leftOriginalCount d := by
  unfold markedLeftPos
  simp only [leftOriginalCount]

/-- The initially-left (marked) positions among the 49 right positions. -/
def markedRightPos (d : Deck) : Finset (Fin 49) :=
  Finset.filter (fun (r : Fin 49) => (d (rightPosition r)).val < 50) (univ : Finset (Fin 49))

/-- The number of marked cards currently sitting at the selected left positions. -/
def markedInLeft (d : Deck) (L : Finset (Fin 50)) : Nat := (markedLeftPos d ∩ L).card

/-- The number of marked cards currently sitting at the selected right positions. -/
def markedInRight (d : Deck) (R : Finset (Fin 49)) : Nat := (markedRightPos d ∩ R).card

/-- The *left* part of the post-exchange left pile, restricted to the marked
  cards, is exactly the image of the *marked unselected* left positions: a card
  is a marked unselected-left card iff it sits at a marked position that was not
  selected for exchange. -/
theorem newLeftCards_leftPart_marked (d : Deck) (L : Finset (Fin 50)) :
    Finset.image (fun (l : Fin 50) => d (leftPosition l)) ((univ : Finset (Fin 50)) \ L) ∩ leftOrigSet
      = Finset.image (fun (l : Fin 50) => d (leftPosition l)) (markedLeftPos d \ L) := by
  let fL : Fin 50 → Fin 99 := fun (l : Fin 50) => d (leftPosition l)
  ext c
  constructor
  · -- forward: a marked card in the unselected left part sits at a marked unselected position
    intro hc
    rcases Finset.mem_inter.mp hc with ⟨hcA, hcM⟩
    rcases Finset.mem_image.mp hcA with ⟨l, hl, rfl⟩
    rcases Finset.mem_sdiff.mp hl with ⟨hlU, hlN⟩
    have hval : (fL l).val < 50 := by
      simp only [leftOrigSet, Finset.mem_filter, Finset.mem_univ] at hcM
      exact hcM.2
    apply Finset.mem_image.mpr
    refine ⟨l, ?_, rfl⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp only [markedLeftPos, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hval⟩
    · exact hlN
  · -- backward: the image of a marked unselected position is a marked unselected-left card
    intro hc
    rcases Finset.mem_image.mp hc with ⟨l, hl, rfl⟩
    rcases Finset.mem_sdiff.mp hl with ⟨hlM, hlN⟩
    simp only [markedLeftPos, Finset.mem_filter] at hlM
    rcases hlM with ⟨hlU, hlMval⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨l, ?_, rfl⟩
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ _, hlN⟩
    · simp only [leftOrigSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hlMval⟩

/-- The *right* part of the post-exchange left pile, restricted to the marked
  cards, is exactly the image of the *marked selected* right positions. -/
theorem newLeftCards_rightPart_marked (d : Deck) (R : Finset (Fin 49)) :
    Finset.image (fun (r : Fin 49) => d (rightPosition r)) R ∩ leftOrigSet
      = Finset.image (fun (r : Fin 49) => d (rightPosition r)) (markedRightPos d ∩ R) := by
  let fR : Fin 49 → Fin 99 := fun (r : Fin 49) => d (rightPosition r)
  ext c
  constructor
  · intro hc
    rcases Finset.mem_inter.mp hc with ⟨hcB, hcM⟩
    rcases Finset.mem_image.mp hcB with ⟨r, hr, rfl⟩
    have hval : (fR r).val < 50 := by
      simp only [leftOrigSet, Finset.mem_filter, Finset.mem_univ] at hcM
      exact hcM.2
    apply Finset.mem_image.mpr
    refine ⟨r, ?_, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · simp only [markedRightPos, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hval⟩
    · exact hr
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨r, hr, rfl⟩
    rcases Finset.mem_inter.mp hr with ⟨hrM, hrR⟩
    simp only [markedRightPos, Finset.mem_filter] at hrM
    rcases hrM with ⟨hrU, hrMval⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨r, ?_, rfl⟩
      exact hrR
    · simp only [leftOrigSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hrMval⟩

/-- **F3b:** the post-exchange macro count. The number of marked (initially-
  left) cards in the new left pile equals the old count minus the marked cards
  that left (at the selected left positions) plus the marked cards that came in
  (at the selected right positions). This is the counting content of the
  `hMembershipExchange` premise: it says exactly how the 25-position exchange
  moves the marked-card count, at the level of the selected sets. -/
theorem newLeftOriginalCount_eq (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    (newLeftCards d L R ∩ leftOrigSet).card =
      (leftOriginalCount d - markedInLeft d L) + markedInRight d R := by
  classical
  let fL : Fin 50 → Fin 99 := fun (l : Fin 50) => d (leftPosition l)
  let fR : Fin 49 → Fin 99 := fun (r : Fin 49) => d (rightPosition r)
  let leftPart : Finset (Fin 99) := Finset.image fL (univ \ L)
  let rightPart : Finset (Fin 99) := Finset.image fR R
  let mLeft : Finset (Fin 99) := Finset.image fL (markedLeftPos d \ L)
  let mRight : Finset (Fin 99) := Finset.image fR (markedRightPos d ∩ R)
  have hinjL : Function.Injective fL := d.injective.comp leftPosition_injective
  have hinjR : Function.Injective fR := d.injective.comp rightPosition_injective
  have hA : leftPart ∩ leftOrigSet = mLeft := by simpa using newLeftCards_leftPart_marked d L
  have hB : rightPart ∩ leftOrigSet = mRight := by simpa using newLeftCards_rightPart_marked d R
  -- the marked left and right parts sit at disjoint positions, so the two image
  -- sets are disjoint (the same argument as newLeftCards_parts_disjoint)
  have hdisjM : Disjoint mLeft mRight := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.ext
    intro c
    constructor
    · intro hc
      rcases Finset.mem_inter.mp hc with ⟨hcL, hcR⟩
      rcases Finset.mem_image.mp hcL with ⟨l, _, heqL⟩
      rcases Finset.mem_image.mp hcR with ⟨r, _, heqR⟩
      -- heqL : fL l = c; heqR : fR r = c, so fL l = fR r
      have heq : fL l = fR r := heqL.trans heqR.symm
      have hne : leftPosition l ≠ rightPosition r := by
        intro heq2
        have hval : (leftPosition l).val = (rightPosition r).val := congrArg Fin.val heq2
        have hL : (leftPosition l).val < 50 := by simp [leftPosition]
        have hR : 50 ≤ (rightPosition r).val := by simp [rightPosition]
        omega
      have hne' : fL l ≠ fR r := fun heq3 => hne (d.injective heq3)
      exact False.elim (hne' heq)
    · intro hc
      have hne : ¬ c ∈ (∅ : Finset (Fin 99)) := by simp
      exact False.elim (hne hc)
  calc
    (newLeftCards d L R ∩ leftOrigSet).card
        = ((leftPart ∪ rightPart) ∩ leftOrigSet).card := by rfl
    _ = (mLeft ∪ mRight).card := by
          rw [Finset.union_inter_distrib_right, hA, hB]
    _ = mLeft.card + mRight.card := by rw [Finset.card_union_of_disjoint hdisjM]
    _ = (Finset.image fL (markedLeftPos d \ L)).card +
        (Finset.image fR (markedRightPos d ∩ R)).card := by
          simp only [mLeft, mRight]
    _ = (markedLeftPos d \ L).card + (markedRightPos d ∩ R).card := by
          rw [Finset.card_image_of_injective _ hinjL,
              Finset.card_image_of_injective _ hinjR]
    _ = ((markedLeftPos d).card - (L ∩ markedLeftPos d).card) + (markedRightPos d ∩ R).card := by
          rw [Finset.card_sdiff]
    _ = (leftOriginalCount d - markedInLeft d L) + markedInRight d R := by
          rw [markedLeftPos_card, markedInLeft, markedInRight]
          simp only [Finset.inter_comm]

/-! ## The deck-level exchange kernel (F3 item 2)

The physical exchange as a `FiniteKernel Deck Deck`: pick 25 of the 50 left
positions and 25 of the 49 right positions uniformly, then swap the selected
positions under a *fixed* (size-independent) bijective pairing. The post-exchange
left-pile membership is exactly `newLeftCards d L R` (proved below), independent
of the particular pairing, so the macro/membership law is pairing-independent.

We build the kernel by composition: the *membership-level* exchange law
(`rawExchangeMembership`, the pushforward of a uniform `(L,R)` choice to its
post-exchange membership) followed by the uniform membership-fiber lift
(`localLift`). Because resampling inside a membership fiber does not change the
membership (`localLift_preserves_membership`), the resulting `Deck`-level kernel
has the *same membership push-through* as the physical swap, which is exactly
what the `hMembershipExchange` intertwining law needs.
-/ 

-- The 25-element selected position sets, and the type of uniform (L,R) choices.
abbrev leftChoices := powersetCard (25 : Nat) (univ : Finset (Fin 50))
abbrev rightChoices := powersetCard (25 : Nat) (univ : Finset (Fin 49))
abbrev exchangeChoice :=
  {L : Finset (Fin 50) // L ∈ leftChoices} × {R : Finset (Fin 49) // R ∈ rightChoices}

instance : Fintype exchangeChoice := inferInstance

-- Two explicit 25-element subsets, witnesses that the choice types are nonempty.
def left25 : Finset (Fin 50) :=
  (univ : Finset (Fin 25)).image (Fin.castLEEmb (by omega))
def right25 : Finset (Fin 49) :=
  (univ : Finset (Fin 25)).image (Fin.castLEEmb (by omega))

theorem left25_card : left25.card = 25 := by
  unfold left25
  rw [Finset.card_image_of_injective]
  · simp
  · exact (Fin.castLEEmb (by omega)).injective

theorem right25_card : right25.card = 25 := by
  unfold right25
  rw [Finset.card_image_of_injective]
  · simp
  · exact (Fin.castLEEmb (by omega)).injective

theorem hNonemptyLeft : Nonempty {L : Finset (Fin 50) // L ∈ leftChoices} :=
  ⟨⟨left25, by simpa [Finset.mem_powersetCard] using left25_card⟩⟩

theorem hNonemptyRight : Nonempty {R : Finset (Fin 49) // R ∈ rightChoices} :=
  ⟨⟨right25, by simpa [Finset.mem_powersetCard] using right25_card⟩⟩

instance : Nonempty exchangeChoice := by
  exact ⟨⟨⟨left25, by simpa [Finset.mem_powersetCard] using left25_card⟩,
        ⟨right25, by simpa [Finset.mem_powersetCard] using right25_card⟩⟩⟩

-- Extract the `card = 25` fact from a membership in `leftChoices`/`rightChoices`
-- (the powersetCard membership is `s ⊆ univ ∧ s.card = n`, so the card is `.2`).
theorem leftCard25 {L : Finset (Fin 50)} (h : L ∈ leftChoices) : L.card = 25 := by
  simp only [leftChoices] at h
  exact (Finset.mem_powersetCard).mp h |>.2
theorem rightCard25 {R : Finset (Fin 49)} (h : R ∈ rightChoices) : R.card = 25 := by
  simp only [rightChoices] at h
  exact (Finset.mem_powersetCard).mp h |>.2

-- The post-exchange left-pile membership for a chosen (L,R).
def newMembership (d : Deck) (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25) : Membership :=
  ⟨newLeftCards d L R, newLeftCards_card d L R hL hR⟩

-- The membership-level exchange law: pushforward of a uniform (L,R) choice to
-- its post-exchange membership.
noncomputable def rawExchangeMembership : FiniteKernel Deck Membership := by
  intro d
  exact (GSR.uniformDist exchangeChoice).map
    (fun c => newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2))

-- The deck-level exchange kernel: membership-level exchange followed by the
-- uniform membership-fiber lift.
noncomputable def rawExchange : FiniteKernel Deck Deck :=
  FiniteKernel.comp rawExchangeMembership localLift

-- The membership push-through of the exchange is the membership-level law:
-- resampling inside the membership fiber does not change the membership.
theorem rawExchange_membership_pushforward : 
    FiniteKernel.comp rawExchange (FiniteKernel.deterministic membership) =
      rawExchangeMembership := by
  classical
  change FiniteKernel.comp (FiniteKernel.comp rawExchangeMembership localLift)
    (FiniteKernel.deterministic membership) = rawExchangeMembership
  simp only [FiniteKernel.comp_assoc, localLift_preserves_membership,
      FiniteKernel.comp_id_right]

/-! ## The `hMembershipExchange` intertwining law (F3 item 3)

The `hMembershipExchange` premise of the physical-exchange reduction:
starting from the two-layer (membership-then-deck) lift and reading the
membership after the physical exchange equals applying the macro count exchange
and then lifting uniformly to a membership. The left-hand side reduces, by the
F2 capstone (`membershipLift_localLift_eq_fiberLaw`) and the exchange's
membership push-through, to pushing the uniform *project-fiber* deck law through
the membership-level exchange.
-/ 

-- The left-hand side of the `hMembershipExchange` premise is the uniform
-- project-fiber deck law pushed through the membership-level exchange.
theorem hMembershipExchange_lhs_reduces :
    FiniteKernel.comp (FiniteKernel.comp (FiniteKernel.comp membershipLift localLift) rawExchange)
      (FiniteKernel.deterministic membership) =
      FiniteKernel.comp (FiberDisintegration.fiberLaw project project_surjective)
        rawExchangeMembership := by
  simp only [FiniteKernel.comp_assoc, rawExchange_membership_pushforward,
      membershipLift_localLift_eq_fiberLaw]

  /- 47i — first step of F3 item 3, item 1 (deck-independence): the post-exchange left
     pile `newLeftCards d L R` depends on the deck `d` only through `leftCards d` (the
     membership's left pile) and the two chosen card-sets. The unselected-left part is
     the deck's left pile minus the selected-left cards (`image_sdiff` via deck
     injectivity); the selected-right part is unchanged. -/
  theorem newLeftCards_as_sdiff_union (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
      newLeftCards d L R = (leftCards d \ L.image (fun l => d (leftPosition l))) ∪
        R.image (fun r => d (rightPosition r)) := by
    unfold newLeftCards
    unfold leftCards
    rw [Finset.image_sdiff (f := fun l => d (leftPosition l)) _ _
        (d.injective.comp leftPosition_injective)]

  /- 47x — deck-independence, unique half (left and right). The deck is a permutation
     of the 99 cards, so the left positions map the 50 left positions bijectively onto
     the left pile `leftCards d` and the right positions onto the right pile (the
     complement). An injective map's image determines its source set (`image_injective_eq`),
     so the card-set at the selected positions determines the position-set. This lets the
     exchange be reparameterized by card-sets rather than positions, making the post-
     exchange membership a function of the source membership (the left pile) alone. -/

  /-- The selected-left card-set determines the selected-left positions: the left pile
      is `leftCards d`, and two 25-position choices give the same selected-left cards
      only if they are the same positions. -/
  theorem leftPosCard_image_injective (d : Deck) (L L' : Finset (Fin 50))
      (h : L.image (fun l => d (leftPosition l)) = L'.image (fun l => d (leftPosition l))) :
      L = L' :=
    image_injective_eq (fun l => d (leftPosition l)) (d.injective.comp leftPosition_injective) h

  /-- The selected-right card-set determines the selected-right positions: the right
      pile is the complement of `leftCards d`, and two 25-position choices give the same
      selected-right cards only if they are the same positions. -/
  theorem rightPosCard_image_injective (d : Deck) (R R' : Finset (Fin 49))
      (h : R.image (fun r => d (rightPosition r)) = R'.image (fun r => d (rightPosition r))) :
      R = R' :=
    image_injective_eq (fun r => d (rightPosition r)) (d.injective.comp rightPosition_injective) h

  /-- The selected-left cards sit in the left pile, so the post-exchange membership
      `(leftCards d \ Lc) ∪ Rc` (from `newLeftCards_as_sdiff_union`) is built purely from
      the source membership `leftCards d` and the chosen card-sets — never from the
      deck's position arrangement. The selected-right cards are disjoint from the left
      pile (`leftImg_disjoint_rightFull`). -/
  theorem newLeftCards_leftPart_in_leftPile (d : Deck) (L : Finset (Fin 50)) :
      L.image (fun l => d (leftPosition l)) ⊆ leftCards d := by
    unfold leftCards
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨l, hl, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨l, Finset.mem_univ l, rfl⟩


end CommanderPhysicalExchange
end Shufflemath
end
