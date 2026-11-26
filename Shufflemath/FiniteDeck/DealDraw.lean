module

public import Shufflemath.FiniteDeck.ChangingPiles
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G7: moving capacities — the discard action

The second typed action on the three-pile capacity state of the draw-pile /
hand / discard toy — the roadmap's "move it to a player's hand **or discard**"
half (`docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`,
T7 / the G7 acceptance row; the draw action and its sound conditional-uniform
law landed in `Shufflemath/FiniteDeck/ChangingPiles.lean`).

The discard action moves the **top card of the hand** into the **discard
pile** (on top of it — the same "head = most recent" convention as the hand):
the hand shrinks by one, the discard grows by one, the draw pile is unchanged.

Three distinct facts are proved, as the roadmap requires, mirroring the draw
action's three-part structure:

1. **Conservation of named cards** — `discard_cover`: the union finset is
   unchanged, every card still appears exactly once.
2. **Exact mapping of capacities** — `discard_hand_length` (hand shrinks by
   one), `discard_discard_length` (discard grows by one), `discard_total_length`
   (total unchanged), and `discardedCard_eq_discard_head` (the discarded card
   is the head of the new discard pile).
3. **The conditional-uniform law** — `discardedCard_uniform_law`: the card
   the discard action moves off the hand is, in the deck model, the card at a
   fixed position of the deck — under the uniform deck law it is uniform over
   the card universe (the sound conditional-uniform hypothesis for the toy:
   the deck must be uniform, *not* a nonuniformly ordered list).
-/

/-- The card discarded by the discard action: the head of the hand. -/
def discardedCard (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) : Fin N :=
  st.hand.head (List.ne_nil_of_length_pos h)

/-- The discard action: the top card of the hand is placed on top of the
discard pile; the hand is the rest of the old pile; the draw pile is unchanged. -/
def discard (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) : CapacityState N where
  drawPile := st.drawPile
  hand := st.hand.tail
  discard := st.hand.head (List.ne_nil_of_length_pos h) :: st.discard
  nodup := by
    set head := st.hand.head (List.ne_nil_of_length_pos h) with hHead
    set tail := st.hand.tail with hTail
    have hgf : st.hand = head :: tail := (List.cons_head_tail (List.ne_nil_of_length_pos h)).symm
    have hnodup : (st.drawPile ++ st.hand ++ st.discard).Nodup := st.nodup
    rw [hgf] at hnodup
    -- hnodup : (drawPile ++ (head :: tail)) ++ discard).Nodup
    obtain ⟨hInner, hDiscNodup, hInnerDisjoint⟩ := List.nodup_append'.1 hnodup
    -- hInner : (drawPile ++ (head :: tail)).Nodup
    obtain ⟨hDrawPileNodup, hHeadTailNodup, hDrawPileHeadTail⟩ := List.nodup_append'.1 hInner
    -- hInnerDisjoint : (drawPile ++ (head :: tail)).Disjoint discard
    have hDrawPileDiscard : st.drawPile.Disjoint st.discard :=
      (List.disjoint_append_left.1 hInnerDisjoint).1
    have hHeadTailDiscard : (head :: tail).Disjoint st.discard :=
      (List.disjoint_append_left.1 hInnerDisjoint).2
    -- facts from (head :: tail).Nodup
    have hHeadTail : head ∉ tail := List.Nodup.notMem hHeadTailNodup
    have hTailNodup : tail.Nodup := List.Nodup.of_cons hHeadTailNodup
    -- facts from (head :: tail).Disjoint discard
    have hHeadDiscard : head ∉ st.discard := by
      intro hmem
      have hne := (List.disjoint_iff_ne.1 hHeadTailDiscard) head (by exact List.mem_cons_self) head
      exact hne hmem rfl
    have hTailDiscard : tail.Disjoint st.discard := by
      rw [List.disjoint_iff_ne]
      intro a ha b hb
      exact (List.disjoint_iff_ne.1 hHeadTailDiscard) a (List.mem_cons_of_mem _ ha) b hb
    -- facts from drawPile.Disjoint (head :: tail)
    rw [← List.singleton_append] at hDrawPileHeadTail
    rw [List.disjoint_append_right] at hDrawPileHeadTail
    obtain ⟨hDrawPileHead, hDrawPileTail⟩ := hDrawPileHeadTail
    -- tail.Disjoint [head] (from head ∉ tail)
    have hTailHead : tail.Disjoint [head] := by
      rw [List.disjoint_iff_ne]
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hbc
      rw [hbc] at ha
      exact hHeadTail ha
    -- (drawPile ++ tail).Nodup
    have hInnerNodup : (st.drawPile ++ tail).Nodup :=
      List.Nodup.append hDrawPileNodup hTailNodup hDrawPileTail
    -- (head :: discard).Nodup
    have hHeadDiscardNodup : (head :: st.discard).Nodup :=
      List.Nodup.cons hHeadDiscard hDiscNodup
    -- (drawPile ++ tail).Disjoint (head :: discard)
    have hOuterDisjoint : (st.drawPile ++ tail).Disjoint (head :: st.discard) := by
      rw [List.disjoint_append_left]
      constructor
      · rw [← List.singleton_append, List.disjoint_append_right]
        exact ⟨hDrawPileHead, hDrawPileDiscard⟩
      · rw [← List.singleton_append, List.disjoint_append_right]
        exact ⟨hTailHead, hTailDiscard⟩
    exact List.Nodup.append hInnerNodup hHeadDiscardNodup hOuterDisjoint
  cover := by
    have hgf : st.hand = st.hand.head (List.ne_nil_of_length_pos h) :: st.hand.tail :=
      (List.cons_head_tail (List.ne_nil_of_length_pos h)).symm
    have hcover : (st.drawPile ++ st.hand ++ st.discard).toFinset = Finset.univ := st.cover
    rw [hgf] at hcover
    -- new union == old union, then hcover closes
    have hnew : (st.drawPile ++ st.hand.tail ++ (st.hand.head (List.ne_nil_of_length_pos h) :: st.discard)).toFinset =
        ((st.drawPile ++ (st.hand.head (List.ne_nil_of_length_pos h) :: st.hand.tail) ++ st.discard)).toFinset := by
      simp only [List.toFinset_append, List.toFinset_cons, Finset.insert_union, Finset.union_insert, Finset.union_assoc]
    rw [hnew]
    exact hcover

/-- **Conservation of named cards under the discard action.** The union finset
of the new state is unchanged — every card still appears exactly once. -/
theorem discard_cover (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    ((discard N st h).drawPile ++ (discard N st h).hand ++ (discard N st h).discard).toFinset =
      Finset.univ :=
  (discard N st h).cover

/-- **Capacity mapping — the draw pile is unchanged.** -/
theorem discard_drawPile_length (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    (discard N st h).drawPile.length = st.drawPile.length :=
  rfl

/-- **Capacity mapping — the hand shrinks by one.** -/
theorem discard_hand_length (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    (discard N st h).hand.length = st.hand.length - 1 := by
  simp [discard, List.length_tail]

/-- **Capacity mapping — the discard pile grows by one.** -/
theorem discard_discard_length (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    (discard N st h).discard.length = st.discard.length + 1 := by
  simp [discard, List.length_cons]

/-- **Capacity mapping — the total number of cards is unchanged.** -/
theorem discard_total_length (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    (discard N st h).drawPile.length + (discard N st h).hand.length + (discard N st h).discard.length =
    st.drawPile.length + st.hand.length + st.discard.length := by
  rw [discard_drawPile_length, discard_hand_length, discard_discard_length]
  omega

/-- The discarded card is the head of the new discard pile: the top card of
the hand left the hand and was placed on top of the discard pile. -/
theorem discardedCard_eq_discard_head (N : Nat) (st : CapacityState N) (h : 0 < st.hand.length) :
    discardedCard N st h =
      (discard N st h).discard.head (List.ne_nil_of_length_pos (by
        rw [discard_discard_length]; exact Nat.succ_pos _)) := by
  rfl

/-- **The discarded card is uniform under the uniform deck law.**  The card
the discard action moves off the hand is the deck's card at the position the
hand top corresponds to — in the deck model, position `⟨k, hk⟩` for the
`k`-th card drawn.  Under the uniform deck law, that card is uniform over the
card universe (`1 / N`) — the sound conditional-uniform fact this toy relies
on: the deck must be uniform, *not* a nonuniformly ordered list. -/
theorem discardedCard_uniform_law (N : Nat) (hN : 0 < N) [Nonempty (Equiv.Perm (Fin N))]
    (c : Fin N) (k : Nat) (hk : k < N) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => d ⟨k, hk⟩)) c = (1 : Rat) / N :=
  topCard_uniform_law N hN ⟨k, hk⟩ c

end FiniteDeck
end Shufflemath
