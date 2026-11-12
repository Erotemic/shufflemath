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
abbrev leftChoices := powersetCard (25 : Nat) (Finset.univ : Finset (Fin 50))
abbrev rightChoices := powersetCard (25 : Nat) (Finset.univ : Finset (Fin 49))
abbrev exchangeChoice :=
  {L : Finset (Fin 50) // L ∈ leftChoices} × {R : Finset (Fin 49) // R ∈ rightChoices}

instance : Fintype exchangeChoice := inferInstance

-- Two explicit 25-element subsets, witnesses that the choice types are nonempty.
def left25 : Finset (Fin 50) :=
  (Finset.univ : Finset (Fin 25)).image (Fin.castLEEmb (by omega))
def right25 : Finset (Fin 49) :=
  (Finset.univ : Finset (Fin 25)).image (Fin.castLEEmb (by omega))

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

end CommanderPhysicalExchange
end Shufflemath
end
