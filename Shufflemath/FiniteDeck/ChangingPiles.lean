module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic
public import Shufflemath.GSR
public import Shufflemath.FiberDisintegration
public import Shufflemath.FiniteDeck.HistogramKernel

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G7: moving capacities — the transfer-one-card action

This is the first genuinely new mathematical object in the G7 gate
(`docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`,
T7 / the G7 acceptance row — *Transfer-one-card action and conditional-uniform
law; conservation and update of capacity*).

The toy is a three-pile capacity state — an **ordered draw pile** (head = the
top card), an **ordered hand**, and an **ordered discard pile** — for the `N`
cards.  The transfer-one-card action (the *draw*) moves the top card out of
the draw pile into the hand: the draw pile shrinks by one, the hand grows by
one, the discard is unchanged.  Three distinct facts are proved, as the roadmap
requires:

1. **Conservation of named cards** — the union finset stays the whole deck
   (the draw preserves the set of cards and moves nothing in or out).
2. **Exact mapping of capacities** — draw pile length drops by one, hand
   length increases by one, the total is unchanged.
3. **The conditional-uniform law** — the sound statement is *the top card of a
   uniformly shuffled deck is uniform over the card universe* (the uniform
   pushforward fact), which is exactly the uniformity hypothesis needed to
   draw soundly: the draw pile must be uniform, *not* an arbitrary ordered
   list.  A draw from a *nonuniformly ordered* deck does **not** produce a
   uniform sample.

The toy uses three piles (draw / hand / discard), which satisfies the G7
acceptance row's "3+ piles" requirement.
-/

/-- A three-pile capacity state for the `N`-card deck: an ordered draw pile
(head = top card), an ordered hand, and an ordered discard pile.  The piles
are pairwise disjoint, internally distinct, and together cover the whole deck
(each card exactly once). -/
structure CapacityState (N : Nat) where
  /-- The ordered draw pile (head = the top card). -/
  drawPile : List (Fin N)
  /-- The ordered hand of the player. -/
  hand : List (Fin N)
  /-- The ordered discard pile. -/
  discard : List (Fin N)
  /-- The piles are pairwise disjoint and internally distinct. -/
  nodup : (drawPile ++ hand ++ discard).Nodup
  /-- The piles cover the whole deck: every card appears exactly once. -/
  cover : (drawPile ++ hand ++ discard).toFinset = Finset.univ

/-- The drawn card of a state: the head of its draw pile (the top card). -/
def drawnCard (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) : Fin N :=
  st.drawPile.head (List.ne_nil_of_length_pos h)

/-- The transfer-one-card (draw) action: the top card of the draw pile leaves
the pile and is placed on top of the hand; the draw pile is the rest of the
old pile; the discard is unchanged. -/
def draw (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) : CapacityState N where
  drawPile := st.drawPile.tail
  hand := st.drawPile.head (List.ne_nil_of_length_pos h) :: st.hand
  discard := st.discard
  nodup := by
    set head := st.drawPile.head (List.ne_nil_of_length_pos h) with hHead
    set tail := st.drawPile.tail with hTail
    have hgf : st.drawPile = head :: tail := (List.cons_head_tail (List.ne_nil_of_length_pos h)).symm
    have hnodup : (st.drawPile ++ st.hand ++ st.discard).Nodup := st.nodup
    rw [hgf] at hnodup
    -- hnodup : ((head :: tail) ++ hand) ++ discard).Nodup
    obtain ⟨hInner, hDiscNodup, hInnerDisjoint⟩ := List.nodup_append'.1 hnodup
    -- hInner : ((head :: tail) ++ hand).Nodup
    obtain ⟨hHeadTailNodup, hHandNodup, hHeadTailHand⟩ := List.nodup_append'.1 hInner
    -- hInnerDisjoint : ((head :: tail) ++ hand).Disjoint discard
    have hHeadTailDisc : (head :: tail).Disjoint st.discard :=
      (List.disjoint_append_left.1 hInnerDisjoint).1
    have hHandDiscard : st.hand.Disjoint st.discard :=
      (List.disjoint_append_left.1 hInnerDisjoint).2
    -- head ∉ tail ; tail.Nodup
    have hHeadTail : head ∉ tail := List.Nodup.notMem hHeadTailNodup
    have hTailNodup : tail.Nodup := List.Nodup.of_cons hHeadTailNodup
    -- head ∉ hand / discard ; tail.Disjoint hand / discard
    have hHeadHand : head ∉ st.hand := by
      intro hmem
      have hne := (List.disjoint_iff_ne.1 hHeadTailHand) head (by exact List.mem_cons_self) head
      exact hne hmem rfl
    have hTailHand : tail.Disjoint st.hand := by
      rw [List.disjoint_iff_ne]
      intro a ha b hb
      exact (List.disjoint_iff_ne.1 hHeadTailHand) a (List.mem_cons_of_mem _ ha) b hb
    have hHeadDiscard : head ∉ st.discard := by
      intro hmem
      have hne := (List.disjoint_iff_ne.1 hHeadTailDisc) head (by exact List.mem_cons_self) head
      exact hne hmem rfl
    have hTailDiscard : tail.Disjoint st.discard := by
      rw [List.disjoint_iff_ne]
      intro a ha b hb
      exact (List.disjoint_iff_ne.1 hHeadTailDisc) a (List.mem_cons_of_mem _ ha) b hb
    -- (head :: hand).Nodup
    have hHeadHand_nodup : (head :: st.hand).Nodup := List.Nodup.cons hHeadHand hHandNodup
    -- tail.Disjoint (head :: hand)
    have hTailHead : tail.Disjoint [head] := by
      rw [List.disjoint_iff_ne]
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hbc
      rw [hbc] at ha
      exact hHeadTail ha
    have hTailHeadHand : tail.Disjoint (head :: st.hand) := by
      rw [← List.singleton_append, List.disjoint_append_right]
      exact ⟨hTailHead, hTailHand⟩
    -- assemble inner nodup: tail ++ (head :: hand)
    have hInnerNodup : (tail ++ (head :: st.hand)).Nodup :=
      List.Nodup.append hTailNodup hHeadHand_nodup hTailHeadHand
    -- (tail ++ (head :: hand)).Disjoint discard
    have hOuterDisjoint : (tail ++ (head :: st.hand)).Disjoint st.discard := by
      rw [List.disjoint_append_left]
      constructor
      · exact hTailDiscard
      · rw [List.disjoint_iff_ne]
        intro a ha b hb
        rcases List.mem_cons.1 ha with rfl | ha
        · intro hbc
          rw [← hbc] at hb
          exact hHeadDiscard hb
        · exact List.disjoint_iff_ne.1 hHandDiscard a ha b hb
    exact List.Nodup.append hInnerNodup hDiscNodup hOuterDisjoint
  cover := by
    have hgf : st.drawPile = st.drawPile.head (List.ne_nil_of_length_pos h) :: st.drawPile.tail :=
      (List.cons_head_tail (List.ne_nil_of_length_pos h)).symm
    have hcover : (st.drawPile ++ st.hand ++ st.discard).toFinset = Finset.univ := st.cover
    rw [hgf] at hcover
    -- new union == old union, then hcover closes
    have hnew : (st.drawPile.tail ++ (st.drawPile.head (List.ne_nil_of_length_pos h) :: st.hand) ++ st.discard).toFinset =
        ((st.drawPile.head (List.ne_nil_of_length_pos h) :: st.drawPile.tail) ++ st.hand ++ st.discard).toFinset := by
      simp only [List.toFinset_append, List.toFinset_cons, Finset.insert_union, Finset.union_insert, Finset.union_assoc]
    rw [hnew]
    exact hcover

/-- **Conservation of named cards under the draw action.** The union finset of
the new state is unchanged — every card still appears exactly once. -/
theorem draw_cover (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) :
    ((draw N st h).drawPile ++ (draw N st h).hand ++ (draw N st h).discard).toFinset =
      Finset.univ :=
  (draw N st h).cover

/-- **Capacity mapping — the draw pile shrinks by one.** -/
theorem draw_drawPile_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) :
    (draw N st h).drawPile.length = st.drawPile.length - 1 := by
  simp [draw, List.length_tail]

/-- **Capacity mapping — the hand grows by one.** -/
theorem draw_hand_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) :
    (draw N st h).hand.length = st.hand.length + 1 := by
  simp [draw, List.length_cons]

/-- **Capacity mapping — the total number of cards is unchanged.** -/
theorem draw_total_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) :
    (draw N st h).drawPile.length + (draw N st h).hand.length + (draw N st h).discard.length =
    st.drawPile.length + st.hand.length + st.discard.length := by
  rw [draw_drawPile_length, draw_hand_length]
  have : (draw N st h).discard.length = st.discard.length := rfl
  rw [this]
  have hlt : (draw N st h).hand.length = st.hand.length + 1 := rfl
  omega

/-- The drawn card is the head of the new hand: the top card left the draw pile
and was placed on top of the hand. -/
theorem drawnCard_eq_hand_head (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length) :
    drawnCard N st h =
      (draw N st h).hand.head (List.ne_nil_of_length_pos (by
        rw [draw_hand_length]; exact Nat.succ_pos _)) := by
  rfl

/-! ## The conditional-uniform law for the drawn card

Under the uniform law on all decks, the card at any fixed position — the top
card of the draw pile, hence the card drawn by the transfer-one-card action —
is uniform over the card universe.  This is the sound conditional-uniform fact
that the toy draw relies on, and it is exactly the hypothesis that must hold:
the deck must be uniformly shuffled.  A draw from a *nonuniformly ordered*
deck does **not** produce a uniform sample, so this is the only uniformity
assumption the physical story needs. -/

/-- The fibers of the position-`p` observation are all of the same cardinality:
postcomposing with the card-swap `swap c c'` (an involution) is a bijection
between any two fibers. -/
theorem fiber_top_positions_card_eq (N : Nat) (p : Fin N) (c c' : Fin N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c')).card := by
  have hind : Function.Injective (fun d : Equiv.Perm (Fin N) => d.trans (Equiv.swap c c')) := by
    intro a b h
    apply Equiv.ext
    intro x
    have hx := congrArg (fun f => f x) h
    rw [Equiv.trans_apply, Equiv.trans_apply] at hx
    exact Equiv.injective _ hx
  have himg : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).image
      (fun d => d.trans (Equiv.swap c c')) =
      (Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c') := by
    ext e2
    constructor
    · intro he2
      rw [Finset.mem_image] at he2
      rcases he2 with ⟨d, hd, hd0⟩
      rw [← hd0]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Equiv.trans_apply]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      rw [hd]
      exact Equiv.swap_apply_left _ _
    · intro he0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he0
      rw [Finset.mem_image]
      refine ⟨e2.trans (Equiv.swap c c'), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Equiv.trans_apply, he0]
        exact Equiv.swap_apply_right _ _
      · ext x
        rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.swap_apply_self]
  rw [← himg, Finset.card_image_of_injective _ hind]

/-- **The card at position `p` of a uniform deck is uniform over the card
universe.**  The pushforward of the uniform law on all decks through the
position-`p` observation is the uniform law on the card universe — the sound
conditional-uniform fact for the transfer-one-card action (the precise
uniformity hypothesis: the deck is uniform; a draw from a nonuniformly ordered
deck is not uniform). -/
theorem topCard_uniform_law (N : Nat) (hN : 0 < N) [Nonempty (Equiv.Perm (Fin N))]
    (p : Fin N) (c : Fin N) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => d p)) c = (1 : Rat) / N := by
  -- The fibers of the position-`p` observation partition the deck space.
  have hsumExact : (∑ x : Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = x)).card : Rat) =
      (Fintype.card (Equiv.Perm (Fin N)) : Rat) :=
    Shufflemath.FiberDisintegration.sum_fiber_card (fun d : Equiv.Perm (Fin N) => d p)
  have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [hcard_eq] at hsumExact
  -- All fibers have the same cardinality.
  have hEq : ∀ x : Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = x)).card =
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card :=
    fun x => fiber_top_positions_card_eq N p x c
  -- The sum over the card universe is the common fiber card times N.
  have hsum_const : (∑ x : Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = x)).card : Rat) =
      (N : Rat) * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [hEq x])]
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum_const] at hsumExact
  -- The mass is the common fiber card over the total.
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card, hcard_eq]
  have hk0 : 0 < ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.swap p c, by simp [Equiv.swap_apply_left]⟩
  have hNne : (N : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hkRat : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk0)
  have hNk : (Nat.factorial N : Rat) = (N : Rat) * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun d => d p = c)).card := by
    exact hsumExact.symm
  rw [hNk]
  field_simp [hNne, hkRat]

/-- **The drawn card is uniform under the uniform deck law.**  Specializing
the position-`p` fact to the top position: the card drawn (the card at the
draw-pile top, i.e. position `⟨0, hN⟩`) of a uniform deck is uniform — the
sound conditional-uniform fact for the transfer-one-card action. -/
theorem drawnCard_uniform_law (N : Nat) (hN : 0 < N) [Nonempty (Equiv.Perm (Fin N))]
    (c : Fin N) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => d ⟨0, hN⟩)) c = (1 : Rat) / N :=
  topCard_uniform_law N hN ⟨0, hN⟩ c

end FiniteDeck
end Shufflemath
