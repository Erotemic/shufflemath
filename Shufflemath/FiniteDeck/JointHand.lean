module

public import Shufflemath.FiniteDeck.HandSecrecy
public import Shufflemath.FiniteDeck.Partition

@[expose] public section

/-!
# Joint hand + next-block law

The marginal hand law (`HandSecrecy.handSet_uniform_law`) says the hand's card set is
uniform over the `h`-subsets.  This module adds the **joint** law of the hand
(positions `0, …, h-1`) and the *next block* (positions `h, …, h+t-1`), which is the
conditional statement behind the "residual cards are uniform given the hand" guarantee:
for a known hand set `S`, the next-block set `T` is uniform over the `t`-subsets of the
complement of `S`, with conditional mass `1 / Nat.choose (N - h) t`.

The construction mirrors `HandSecrecy`:
1. `blockPositions` / `deckBlockSet` — the `t` positions after the hand and the cards
   at those positions;
2. `jointBlockPartition` — the three-block partition of the card universe
   (hand / next block / remainder);
3. `jointTransitive` — a single transposition sending a joint pair `(S, T)` to a
   matching joint pair `(S', T')` (glued block bijections via `glueBlocks`);
4. `jointFiber_card` — the fibers of the joint observation for every valid pair are
   equal (the `d ↦ d.trans σ` bijection);
5. `jointHand_uniform_law` — the joint uniform law: every valid joint pair carries mass
   `1 / (Nat.choose N h * Nat.choose (N - h) t)`;
6. `jointHand_conditional_law` — dividing by the hand marginal gives the conditional
   mass `1 / Nat.choose (N - h) t`.

No `Equiv.Perm` types are enumerated; everything is structural.
-/

namespace Shufflemath.FiniteDeck

open Classical

/-! ## Block positions and block sets -/

/-- The `t` deck positions starting at `h` (when `h + t ≤ N`). -/
def blockPositions (N h t : Nat) (hh : h + t ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin t)).image
    (fun i => (⟨h + i.val, by
      have := Fin.isLt i
      omega⟩ : Fin N))

theorem blockPositions_card (N h t : Nat) (hh : h + t ≤ N) :
    (blockPositions N h t hh).card = t := by
  have hinj : Function.Injective
      (fun i : Fin t => (⟨h + i.val, by have := Fin.isLt i; omega⟩ : Fin N)) := by
    intro i j hij
    have e := hij
    rw [Fin.mk.injEq] at e
    have hnat : i.val = j.val := by omega
    exact Fin.ext hnat
  rw [blockPositions, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

/-- The card set at the `t` positions starting at `h`: `h, …, h+t-1`. -/
def deckBlockSet (N h t : Nat) (hh : h + t ≤ N) (d : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  (blockPositions N h t hh).image d

theorem deckBlockSet_card (N h t : Nat) (hh : h + t ≤ N) (d : Equiv.Perm (Fin N)) :
    (deckBlockSet N h t hh d).card = t := by
  rw [deckBlockSet, Finset.card_image_of_injective _ (Equiv.injective d), blockPositions_card]

/-- Transcomposition acts on the block set by the permutation. -/
theorem deckBlockSet_trans (N h t : Nat) (hh : h + t ≤ N)
    (d : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin N)) :
    deckBlockSet N h t hh (d.trans τ) = (deckBlockSet N h t hh d).image (fun a => τ a) := by
  rw [deckBlockSet, deckBlockSet]
  exact img_comp N τ d (blockPositions N h t hh)

/-- The first-block positions and the next-block positions are disjoint. -/
theorem handPositions_blockPositions_disjoint (N h t : Nat) (hh : h + t ≤ N) :
    Disjoint (handPositions N h (by omega)) (blockPositions N h t hh) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
  have hv : i.val = h + j.val := by
    have h0 : Fin.val a = Fin.val b := congrArg Fin.val hab
    rw [← hia, ← hjb] at h0
    simp only [Fin.val_castLE] at h0
    exact h0
  have hiLt : i.val < h := Fin.isLt i
  have hjGe : j.val ≥ 0 := Nat.zero_le j.val
  omega

/-- The hand set and the next-block set are disjoint: the first blocks and the next
blocks occupy disjoint position sets, and the deck is injective. -/
theorem handSet_blockSet_disjoint (N h t : Nat) (hh : h + t ≤ N)
    (d : Equiv.Perm (Fin N)) :
    Disjoint (handSet N h (by omega) d) (deckBlockSet N h t hh d) := by
  rw [handSet, deckBlockSet, Finset.disjoint_image d.injective]
  exact handPositions_blockPositions_disjoint N h t hh

/-! ## The three-block partition and the joint transposition -/

/-- The three-block partition of the card universe: the hand block `S`, the
next-block block `T`, and the remainder (the complement of their union). -/
def jointBlocks (S T : Finset (Fin N)) (i : Fin 3) : Finset (Fin N) :=
  match i with
  | 0 => S
  | 1 => T
  | _ => Finset.univ \ (S ∪ T)

/-- Membership in the three-block partition. -/
theorem jointBlocks_mem (S T : Finset (Fin N)) (i : Fin 3) (x : Fin N) :
    x ∈ jointBlocks S T i ↔
      (i = 0 ∧ x ∈ S) ∨ (i = 1 ∧ x ∈ T) ∨ (i = 2 ∧ x ∉ (S ∪ T)) := by
  fin_cases i <;> simp [jointBlocks, Finset.mem_sdiff, Finset.mem_union]

/-- The three-block partition is a partition when `S` and `T` are disjoint. -/
theorem jointBlocks_isPartition (S T : Finset (Fin N)) (hdisjoint : Disjoint S T) :
    IsPartition (jointBlocks S T) := by
  constructor
  · intro x
    by_cases hxS : x ∈ S
    · exact ⟨0, by simp [jointBlocks, hxS]⟩
    · by_cases hxT : x ∈ T
      · exact ⟨1, by simp [jointBlocks, hxT]⟩
      · have hxnot : x ∉ (S ∪ T) := by
          rw [Finset.mem_union]
          tauto
        exact ⟨2, by simp [jointBlocks, hxnot]⟩
  · intro i j x hx hj
    have hnd := Finset.disjoint_iff_ne.mp hdisjoint
    fin_cases i <;> fin_cases j <;>
      simp_all [jointBlocks, Finset.mem_sdiff, Finset.mem_union]

/-! ## The remainder block card and the joint transposition -/

/-- The complement block of the three-block partition holds exactly `N - h - t` cards. -/
theorem jointComplement_card (N h t : Nat) (S T : Finset (Fin N))
    (hdisjoint : Disjoint S T) (hS : S.card = h) (hT : T.card = t) :
    Fintype.card {x : Fin N // x ∈ Finset.univ \ (S ∪ T)} = N - h - t := by
  have hunion : (S ∪ T).card = h + t := by
    rw [Finset.card_union_of_disjoint hdisjoint, hS, hT]
  have hcard : Fintype.card {x : Fin N // x ∈ Finset.univ \ (S ∪ T)} =
      (Finset.univ \ (S ∪ T)).card := by
    rw [Fintype.card_subtype]
    congr 1
    apply Finset.ext
    intro x
    simp [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ]
  rw [hcard, Finset.card_sdiff, Finset.inter_univ, hunion, Finset.card_univ, Fintype.card_fin]
  omega

/-- The per-block equivalences between the three-block partition of `(S, T)` and of
`(S', T')` (same hand size `h` and next-block size `t`, both disjoint): the hand block,
the next block, and the remainder region. -/
noncomputable def jointBlockEquivs (N h t : Nat) (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    ∀ i : Fin 3, {x : Fin N // x ∈ jointBlocks S T i} ≃ {y : Fin N // y ∈ jointBlocks S' T' i} :=
  fun i => match i with
    | 0 => Fintype.equivOfCardEq (by
        simp [jointBlocks]
        rw [hS, hS'])
    | 1 => Fintype.equivOfCardEq (by
        simp [jointBlocks]
        rw [hT, hT'])
    | 2 => Fintype.equivOfCardEq (by
        simp only [jointBlocks]
        rw [Fintype.card_coe, Fintype.card_coe, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, Fintype.card_fin]
        have hunion : (S ∪ T).card = h + t := by
          rw [Finset.card_union_of_disjoint hdisjoint, hS, hT]
        have hunion' : (S' ∪ T').card = h + t := by
          rw [Finset.card_union_of_disjoint hdisjoint', hS', hT']
        rw [hunion]
        rw [Finset.card_sdiff, Finset.inter_univ, hunion', Finset.card_univ, Fintype.card_fin])

/-- The joint transposition: a single deck permutation sending the joint pair
`(S, T)` to `(S', T')`, glued from the per-block bijections. -/
noncomputable def jointTransitive (N h t : Nat) (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    Equiv.Perm (Fin N) :=
  glueBlocks (jointBlocks S T) (jointBlocks S' T')
    (jointBlocks_isPartition S T hdisjoint)
    (jointBlocks_isPartition S' T' hdisjoint')
    (jointBlockEquivs N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')

/-- The hand image of the joint transposition is the target hand set. -/
theorem jointHand_image_trans (N h t : Nat) (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    S.image (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) = S' := by
  have hinj : Function.Injective
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) :=
    (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').injective
  have hsubset : S.image
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) ⊆ S' := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have htx : jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a = x := hax
    rw [← htx]
    have hprop := (jointBlockEquivs N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' 0 ⟨a, ha⟩).property
    simp only [jointBlocks] at hprop
    have hMember := glueBlocks_apply_member (jointBlocks S T) (jointBlocks S' T')
      (jointBlocks_isPartition S T hdisjoint) (jointBlocks_isPartition S' T' hdisjoint')
      (jointBlockEquivs N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')
      0 a ha
    simp only [jointTransitive]
    rw [hMember]
    exact hprop
  have hcardimage : (S.image
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a)).card = h := by
    rw [Finset.card_image_of_injective _ hinj, hS]
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hS', hcardimage]



/-- The next-block image of the joint transposition is the target next-block set. -/
theorem jointBlock_image_trans (N h t : Nat) (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    T.image (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) = T' := by
  have hinj : Function.Injective
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) :=
    (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').injective
  have hsubset : T.image
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) ⊆ T' := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have htx : jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a = x := hax
    rw [← htx]
    simp only [jointTransitive]
    have hMember := glueBlocks_apply_member (jointBlocks S T) (jointBlocks S' T')
      (jointBlocks_isPartition S T hdisjoint) (jointBlocks_isPartition S' T' hdisjoint')
      (jointBlockEquivs N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')
      1 a ha
    rw [hMember]
    have hprop := (jointBlockEquivs N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' 1 ⟨a, ha⟩).property
    simp only [jointBlocks] at hprop
    exact hprop
  have hcardimage : (T.image
      (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a)).card = t := by
    rw [Finset.card_image_of_injective _ hinj, hT]
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hT', hcardimage]

/-- The joint observation: the hand block set and the next-block set. -/
def jointObs (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N) (d : Equiv.Perm (Fin N)) :
    Finset (Fin N) × Finset (Fin N) :=
  (handSet N h hk d, deckBlockSet N h t hh d)

/-- The fiber of the joint observation for a pair: the decks whose hand set and
next-block set are exactly the given pair. -/
def jointFiber (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N) (S T : Finset (Fin N)) :
    Finset (Equiv.Perm (Fin N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => jointObs N h t hh hk d = (S, T))

/-- Transporting a joint-fiber deck by the joint transposition stays in the target
joint fiber. -/
theorem jointFiber_trans_fwd (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T')
    (d : Equiv.Perm (Fin N))
    (hd : jointObs N h t hh hk d = (S, T)) :
    jointObs N h t hh hk (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')) =
      (S', T') := by
  rw [jointObs] at hd ⊢
  rw [Prod.mk.injEq] at hd
  obtain ⟨hdS, hdT⟩ := hd
  rw [Prod.mk.injEq]
  constructor
  · have h1 : handSet N h hk (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'))
        = (handSet N h hk d).image
            (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) :=
      handSet_trans N h hk d
        (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')
    rw [h1]
    rw [hdS]
    exact jointHand_image_trans N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'
  · have h2 : deckBlockSet N h t hh (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'))
        = (deckBlockSet N h t hh d).image
            (fun a => jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint' a) :=
      deckBlockSet_trans N h t hh d
        (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')
    rw [h2]
    rw [hdT]
    exact jointBlock_image_trans N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'


/-- Reverse transport: a target-fiber deck transported by the inverse joint
transposition stays in the source joint fiber. -/
theorem jointFiber_trans_bwd (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T')
    (d : Equiv.Perm (Fin N))
    (hd : jointObs N h t hh hk d = (S', T')) :
    jointObs N h t hh hk (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm) =
      (S, T) := by
  rw [jointObs] at hd ⊢
  rw [Prod.mk.injEq] at hd
  obtain ⟨hdS, hdT⟩ := hd
  rw [Prod.mk.injEq]
  constructor
  · have h1 : handSet N h hk (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm)
        = (handSet N h hk d).image
            (fun a => (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm a) :=
      handSet_trans N h hk d
        (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm
    rw [h1]
    rw [hdS]
    simpa [jointHand_image_trans N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'] using
      img_symm_img N (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint') S
  · have h2 : deckBlockSet N h t hh (d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm)
        = (deckBlockSet N h t hh d).image
            (fun a => (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm a) :=
      deckBlockSet_trans N h t hh d
        (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm
    rw [h2]
    rw [hdT]
    simpa [jointBlock_image_trans N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint'] using
      img_symm_img N (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint') T

/-- Transporting the source joint fiber by the joint transposition gives the target
joint fiber. -/
theorem jointFiber_image_eq (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T S' T' : Finset (Fin N))
    (hS : S.card = h) (hT : T.card = t) (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => jointObs N h t hh hk d = (S, T))).image
        (fun d => d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')) =
    (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => jointObs N h t hh hk d = (S', T')) := by
  ext e2
  constructor
  · intro he2
    rw [Finset.mem_image] at he2
    obtain ⟨d, hd, hd0⟩ := he2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hd0]
    exact jointFiber_trans_fwd N h t hh hk S T S' T' hS hT hS' hT' hdisjoint hdisjoint' d hd
  · intro he0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he0
    rw [Finset.mem_image]
    refine ⟨e2.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint').symm, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact jointFiber_trans_bwd N h t hh hk S T S' T' hS hT hS' hT' hdisjoint hdisjoint' e2 he0
    · ext x
      simp [Equiv.trans_apply]

/-- All valid joint fibers have the same cardinality: the joint transposition with
its inverse witnesses the bijection. -/
theorem jointFiber_card (N h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T S' T' : Finset (Fin N)) (hS : S.card = h) (hT : T.card = t)
    (hS' : S'.card = h) (hT' : T'.card = t)
    (hdisjoint : Disjoint S T) (hdisjoint' : Disjoint S' T') :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => jointObs N h t hh hk d = (S, T))).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => jointObs N h t hh hk d = (S', T'))).card := by
  have himg := jointFiber_image_eq N h t hh hk S T S' T' hS hT hS' hT' hdisjoint hdisjoint'
  have hind : Function.Injective
      (fun d : Equiv.Perm (Fin N) =>
        d.trans (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint')) := by
    intro a b hEq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun f => f x) hEq
    rw [Equiv.trans_apply, Equiv.trans_apply] at hx
    exact Equiv.injective (jointTransitive N h t S T S' T' hS hT hS' hT' hdisjoint hdisjoint') hx
  rw [← himg, Finset.card_image_of_injective _ hind]

/-- The complement of `S` (as a finset of the universe) is the disjointness witness:
`T ⊆ univ \ S ↔ Disjoint S T`. -/
theorem subset_compl_iff_disjoint (N : Nat) (S T : Finset (Fin N)) :
    (T ⊆ (Finset.univ \ S)) ↔ Disjoint S T := by
  rw [Finset.disjoint_iff_ne]
  constructor
  · intro hsub a ha b hb
    by_contra hab
    rw [hab] at ha
    have hbSub : b ∈ Finset.univ \ S := hsub hb
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hbSub
    exact hbSub ha
  · intro hdisj x hxT
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by
      by_contra hxS
      exact (hdisj x hxS x hxT) rfl⟩

/-- The number of valid joint pairs is the number of `h`-subsets of the hand plus,
for each hand, the number of `t`-subsets of the complement. -/
theorem validPairs_card (N h t : Nat) (_hh : h + t ≤ N) :
    ((Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
      (fun p => p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2)).card =
      Nat.choose N h * Nat.choose (N - h) t := by
  have hInner : ∀ S : Finset (Fin N),
      (∑ T ∈ Finset.univ, if (S.card = h ∧ T.card = t ∧ Disjoint S T) then (1 : ℕ) else 0) =
      if S.card = h then Nat.choose (N - h) t else 0 := by
    intro S
    by_cases hS : S.card = h
    · have h2 : (∑ T ∈ Finset.univ, if (S.card = h ∧ T.card = t ∧ Disjoint S T) then (1 : ℕ) else 0) =
          (Finset.univ.filter (fun T => T.card = t ∧ Disjoint S T)).card := by
        rw [← Finset.sum_filter]
        have hC : (Finset.univ : Finset (Finset (Fin N))).filter
            (fun T => S.card = h ∧ T.card = t ∧ Disjoint S T) =
            (Finset.univ : Finset (Finset (Fin N))).filter (fun T => T.card = t ∧ Disjoint S T) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro h
          · exact h.2
          · exact ⟨hS, h⟩
        rw [hC, Finset.card_eq_sum_ones]
      have h3 : (Finset.univ.filter (fun T => T.card = t ∧ Disjoint S T)).card = Nat.choose (N - h) t := by
        have hEq : (Finset.univ : Finset (Finset (Fin N))).filter
            (fun T => T.card = t ∧ Disjoint S T) = Finset.powersetCard t (Finset.univ \ S) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
            subset_compl_iff_disjoint N S T]
          tauto
        rw [hEq, Finset.card_powersetCard]
        have hcard : (Finset.univ \ S).card = N - h := by
          rw [Finset.card_sdiff, Finset.inter_univ, hS, Finset.card_univ, Fintype.card_fin]
        rw [hcard]
      rw [h2, h3, ite_eq_left hS]
    · rw [ite_eq_right hS]
      apply Finset.sum_eq_zero
      intro T _
      rw [ite_eq_right (by intro h; exact hS (h.1))]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  have hprod : (∑ p : Finset (Fin N) × Finset (Fin N),
      if p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2 then (1 : ℕ) else 0) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))),
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin N))),
          if S.card = h ∧ T.card = t ∧ Disjoint S T then (1 : ℕ) else 0 := by
    rw [← Finset.univ_product_univ]
    exact Finset.sum_product' (Finset.univ : Finset (Finset (Fin N)))
      (Finset.univ : Finset (Finset (Fin N)))
      (fun c c' => if c.card = h ∧ c'.card = t ∧ Disjoint c c' then (1 : ℕ) else 0)
  rw [hprod]
  rw [Finset.sum_congr rfl (fun S _ => hInner S)]
  rw [← Finset.sum_filter]
  have hcard_filter : (Finset.univ : Finset (Finset (Fin N))).filter
      (fun S => S.card = h) = Finset.powersetCard h (Finset.univ : Finset (Fin N)) := by
    ext S
    simp [Finset.mem_powersetCard, Finset.subset_univ]
  rw [Finset.sum_const, hcard_filter, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul]

/-- **Joint hand + next-block law.**  Under the uniform deck law, the pair of card
sets at the first `h` and `h+t` positions is uniform over the valid joint pairs —
every valid pair carries mass `1 / (Nat.choose N h * Nat.choose (N - h) t)`. -/
theorem jointHand_uniform_law (N : Nat) [Nonempty (Equiv.Perm (Fin N))]
    (h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T : Finset (Fin N)) (hS : S.card = h) (hT : T.card = t) (hdisjoint : Disjoint S T) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
      (fun d => jointObs N h t hh hk d)) (S, T) =
      (1 : Rat) / (Nat.choose N h * Nat.choose (N - h) t : Rat) := by
  set K := ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => jointObs N h t hh hk d = (S, T))).card with hK
  -- The sum over all pairs is the total deck count N!.
  have hsumExact : (∑ p : Finset (Fin N) × Finset (Fin N),
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => jointObs N h t hh hk d = p)).card) = Nat.factorial N := by
    have h := Shufflemath.FiberDisintegration.sum_fiber_card
      (fun d : Equiv.Perm (Fin N) => jointObs N h t hh hk d)
    have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [hcard_eq] at h
    exact_mod_cast h
  -- Invalid pairs have empty fibers.
  have hEmpty : ∀ p : Finset (Fin N) × Finset (Fin N),
      ¬ (p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2) →
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => jointObs N h t hh hk d = p)).card = 0 := by
    intro p hp
    have hempty : (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => jointObs N h t hh hk d = p) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro d _ hd
      rw [jointObs, Prod.mk.injEq] at hd
      obtain ⟨hdS, hdT⟩ := hd
      have hcard1 : p.1.card = h := by
        have hcard := congrArg Finset.card hdS
        rw [handSet_card N h hk d] at hcard
        exact hcard.symm
      have hcard2 : p.2.card = t := by
        have hcard := congrArg Finset.card hdT
        rw [deckBlockSet_card] at hcard
        exact hcard.symm
      have hdisj : Disjoint p.1 p.2 := by
        have hnd := handSet_blockSet_disjoint N h t hh d
        rw [hdS, hdT] at hnd
        exact hnd
      exact hp ⟨hcard1, hcard2, hdisj⟩
    rw [hempty, Finset.card_empty]
  -- The sum over pairs is the sum over valid pairs of the common K.
  have hsumN : (∑ p : Finset (Fin N) × Finset (Fin N),
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => jointObs N h t hh hk d = p)).card) =
      Nat.choose N h * Nat.choose (N - h) t * K := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : Finset (Fin N) × Finset (Fin N) => p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2)]
    have hNot : ∑ p ∈ Finset.univ.filter
        (fun p : Finset (Fin N) × Finset (Fin N) => ¬ (p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2)),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => jointObs N h t hh hk d = p)).card = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact hEmpty p (Finset.mem_filter.mp hp).2
    rw [hNot, add_zero]
    have hPer : ∑ p ∈ Finset.univ.filter
        (fun p : Finset (Fin N) × Finset (Fin N) => p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => jointObs N h t hh hk d = p)).card =
        ∑ p ∈ Finset.univ.filter
        (fun p : Finset (Fin N) × Finset (Fin N) => p.1.card = h ∧ p.2.card = t ∧ Disjoint p.1 p.2), K := by
      apply Finset.sum_congr rfl
      intro p hp
      have h' := Finset.mem_filter.mp hp
      have hcard' := jointFiber_card N h t hh hk p.1 p.2 S T
        h'.2.1 h'.2.2.1 hS hT h'.2.2.2 hdisjoint
      have hKK : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => jointObs N h t hh hk d = (S, T))).card = K := hK.symm
      rw [hKK] at hcard'
      exact hcard'
    rw [hPer, Finset.sum_const, validPairs_card N h t hh]
    ring
  -- N! = choose N h * choose (N-h) t * K — the common fiber cardinality.
  have hfactN : Nat.factorial N = Nat.choose N h * Nat.choose (N - h) t * K := hsumExact.symm.trans hsumN
  have hchoose_pos : 0 < Nat.choose N h := Nat.choose_pos hk
  have hchoose_pos_t : 0 < Nat.choose (N - h) t := Nat.choose_pos (by omega)
  have hKpos : 0 < K := by
    by_contra h
    have hK0 : K = 0 := by omega
    have hzero : Nat.factorial N = 0 := by
      rw [hfactN, hK0, mul_zero]
    have hNfact : 0 < Nat.factorial N := Nat.factorial_pos N
    omega
  -- The mass formula.
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hfactRat : (Nat.factorial N : Rat) =
      (Nat.choose N h : Rat) * (Nat.choose (N - h) t : Rat) * (K : Rat) := by
    exact_mod_cast hfactN
  have hK_ne : (K : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  have hchoose_ne : (Nat.choose N h : Rat) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hchoose_ne_t : (Nat.choose (N - h) t : Rat) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [hcard_eq, hfactRat, ← hK]
  field_simp [hchoose_ne, hchoose_ne_t, hK_ne]

/-- The conditional next-block law: the joint mass divided by the hand marginal mass
is `1 / Nat.choose (N - h) t` — the next-block set at positions `h, …, h+t-1` is
uniform over the `t`-subsets of the complement of the hand set. -/
theorem jointHand_conditional_mass (N : Nat) [Nonempty (Equiv.Perm (Fin N))]
    (h t : Nat) (hh : h + t ≤ N) (hk : h ≤ N)
    (S T : Finset (Fin N)) (hS : S.card = h) (hT : T.card = t) (hdisjoint : Disjoint S T) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
      (fun d => jointObs N h t hh hk d)) (S, T) /
      Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
        (fun d => handSet N h hk d)) S =
      (1 : Rat) / (Nat.choose (N - h) t : Rat) := by
  rw [jointHand_uniform_law N h t hh hk S T hS hT hdisjoint,
    handSet_uniform_law N h hk S hS]
  have hchoose_ne : (Nat.choose N h : Rat) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hchoose_ne_t : (Nat.choose (N - h) t : Rat) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp [hchoose_ne, hchoose_ne_t]

end Shufflemath.FiniteDeck
