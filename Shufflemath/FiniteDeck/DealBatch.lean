module

public import Shufflemath.FiniteDeck.ChangingPiles
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G7: moving capacities — the batch deal (variable counts)

The roadmap's next T7 step after the single-card actions landed in
`Shufflemath/FiniteDeck/ChangingPiles.lean` (`draw`) and
`Shufflemath/FiniteDeck/DealDraw.lean` (`discard`): **generalize to variable
counts** — a batch deal moves the first `k` cards of the draw pile into the
hand in one typed action.  The physical story: the `k` cards on top of the
draw pile (positions `0`, …, `k - 1` of the draw pile) are dealt to the
hand, most-recently-dealt card on top — so the new hand is `(take k
drawPile).reverse ++ hand` — the draw pile is the rest (`drop k drawPile`),
and the discard pile is unchanged.

The logical structure mirrors the single-card actions:

1. **Conservation of named cards** — `deal_cover`: the union finset is
   unchanged, every card still appears exactly once.
2. **Exact mapping of capacities** — `deal_drawPile_length` (draw pile
   shrinks by `k`), `deal_hand_length` (hand grows by `k`), `deal_discard_length`
   (discard unchanged), `deal_total_length` (total unchanged), and
   `deal_new_hand_head` (the top card of the new hand is the `k`-th card of
   the old draw pile — the card that was dealt last).
3. **The conditional-uniform law** — `deal_first_remaining_uniform_law`: the
   card at deck position `⟨k, hk⟩` — the first card remaining in the draw pile
   after the deal — is uniform over the card universe (`1 / N`) under the
   uniform deck law — the sound conditional-uniform hypothesis for the batch
   deal: the deck must be **uniform**, not a nonuniformly ordered list.
-/

/-- The batch deal action: the first `k` cards of the draw pile are dealt to
the hand (most-recently-dealt card on top); the draw pile is the rest; the
discard pile is unchanged. -/
def deal (N : Nat) (st : CapacityState N) (_h : 0 < st.drawPile.length) (k : Nat)
    (_hk : k ≤ st.drawPile.length) : CapacityState N where
  drawPile := st.drawPile.drop k
  hand := (st.drawPile.take k).reverse ++ st.hand
  discard := st.discard
  nodup := by
    have hInner2 : (st.drawPile ++ st.hand).Nodup := (List.nodup_append'.1 st.nodup).1
    have hDiscNodup : st.discard.Nodup := (List.nodup_append'.1 st.nodup).2.1
    have hOuterDisjoint : (st.drawPile ++ st.hand).Disjoint st.discard := (List.nodup_append'.1 st.nodup).2.2
    obtain ⟨hDrawPileNodup, hHandNodup, hDrawPileHand⟩ := List.nodup_append'.1 hInner2
    have hDrawPileDiscard : st.drawPile.Disjoint st.discard := (List.disjoint_append_left.1 hOuterDisjoint).1
    have hHandDiscard : st.hand.Disjoint st.discard := (List.disjoint_append_left.1 hOuterDisjoint).2
    -- take/drop nodups
    have hTakeNodup : (st.drawPile.take k).Nodup := List.Nodup.sublist (List.take_sublist k st.drawPile) hDrawPileNodup
    have hDropNodup : (st.drawPile.drop k).Nodup := List.Nodup.sublist (List.drop_sublist k st.drawPile) hDrawPileNodup
    have hTakeReverseNodup : (st.drawPile.take k).reverse.Nodup := List.nodup_reverse.2 hTakeNodup
    -- hand disjointness with take/drop
    have hHandDisjointTake : (st.drawPile.take k).Disjoint st.hand := by
      rw [List.disjoint_iff_ne]
      intro x hx y hy
      exact (List.disjoint_iff_ne.1 hDrawPileHand) x (List.Sublist.mem hx (List.take_sublist k st.drawPile)) y hy
    have hHandDisjointDrop : (st.drawPile.drop k).Disjoint st.hand := by
      rw [List.disjoint_iff_ne]
      intro x hx y hy
      exact (List.disjoint_iff_ne.1 hDrawPileHand) x (List.Sublist.mem hx (List.drop_sublist k st.drawPile)) y hy
    have hHandDisjointTakeReverse : (st.drawPile.take k).reverse.Disjoint st.hand :=
      List.disjoint_reverse_left.2 hHandDisjointTake
    -- take/drop disjointness vs discard
    have hTakeDiscard : (st.drawPile.take k).Disjoint st.discard := by
      rw [List.disjoint_iff_ne]
      intro x hx y hy
      exact (List.disjoint_iff_ne.1 hDrawPileDiscard) x (List.Sublist.mem hx (List.take_sublist k st.drawPile)) y hy
    have hDropDiscard : (st.drawPile.drop k).Disjoint st.discard := by
      rw [List.disjoint_iff_ne]
      intro x hx y hy
      exact (List.disjoint_iff_ne.1 hDrawPileDiscard) x (List.Sublist.mem hx (List.drop_sublist k st.drawPile)) y hy
    have hTakeReverseDiscard : (st.drawPile.take k).reverse.Disjoint st.discard :=
      List.disjoint_reverse_left.2 hTakeDiscard
    -- drop/take disjointness
    have hDropTakeReverse : (st.drawPile.drop k).Disjoint (st.drawPile.take k).reverse :=
      List.disjoint_reverse_right.2 (List.disjoint_comm.2 (List.disjoint_take_drop hDrawPileNodup (by omega)))
    -- inner hand
    have hInnerHandNodup : ((st.drawPile.take k).reverse ++ st.hand).Nodup :=
      List.Nodup.append hTakeReverseNodup hHandNodup hHandDisjointTakeReverse
    have hInnerDisjointDrop : (st.drawPile.drop k).Disjoint ((st.drawPile.take k).reverse ++ st.hand) := by
      rw [List.disjoint_append_right]
      exact ⟨hDropTakeReverse, hHandDisjointDrop⟩
    have hInnerNodup : (st.drawPile.drop k ++ ((st.drawPile.take k).reverse ++ st.hand)).Nodup :=
      List.Nodup.append hDropNodup hInnerHandNodup hInnerDisjointDrop
    -- outer disjointness
    have hInnerDisjointDiscard : (st.drawPile.drop k ++ ((st.drawPile.take k).reverse ++ st.hand)).Disjoint st.discard := by
      rw [List.disjoint_append_left]
      constructor
      · exact hDropDiscard
      · rw [List.disjoint_append_left]
        exact ⟨hTakeReverseDiscard, hHandDiscard⟩
    exact List.Nodup.append hInnerNodup hDiscNodup hInnerDisjointDiscard
  cover := by
    have hcover : (st.drawPile ++ st.hand ++ st.discard).toFinset = Finset.univ := st.cover
    have htakedrop : (st.drawPile.drop k).toFinset ∪ (st.drawPile.take k).toFinset = st.drawPile.toFinset := by
      have h := congrArg List.toFinset (List.take_append_drop k st.drawPile)
      rw [List.toFinset_append] at h
      rw [Finset.union_comm] at h
      exact h
    have htakedrop2 : (st.drawPile.drop k).toFinset ∪ ((st.drawPile.take k).toFinset ∪ st.hand.toFinset) =
        st.drawPile.toFinset ∪ st.hand.toFinset := by
      rw [← htakedrop]
      rw [Finset.union_assoc]
    have hnew : (st.drawPile.drop k ++ ((st.drawPile.take k).reverse ++ st.hand) ++ st.discard).toFinset =
        (st.drawPile ++ st.hand ++ st.discard).toFinset := by
      rw [List.toFinset_append, List.toFinset_append, List.toFinset_append, List.toFinset_reverse]
      rw [htakedrop2]
      rw [List.toFinset_append, List.toFinset_append]
    rw [hnew]
    exact hcover

/-- **Conservation of named cards under the batch deal.** The union finset of
the new state is unchanged — every card still appears exactly once. -/
theorem deal_cover (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : k ≤ st.drawPile.length) :
    ((deal N st h k hk).drawPile ++ (deal N st h k hk).hand ++ (deal N st h k hk).discard).toFinset =
      Finset.univ :=
  (deal N st h k hk).cover

/-- **Capacity mapping — the draw pile shrinks by `k`.** -/
theorem deal_drawPile_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : k ≤ st.drawPile.length) :
    (deal N st h k hk).drawPile.length = st.drawPile.length - k := by
  simp [deal, List.length_drop]

/-- **Capacity mapping — the hand grows by `k`.** -/
theorem deal_hand_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : k ≤ st.drawPile.length) :
    (deal N st h k hk).hand.length = st.hand.length + k := by
  simp [deal, List.length_reverse, List.length_append, List.length_take, min_eq_left hk]
  omega

/-- **Capacity mapping — the discard pile is unchanged.** -/
theorem deal_discard_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : k ≤ st.drawPile.length) :
    (deal N st h k hk).discard.length = st.discard.length :=
  rfl

/-- **Capacity mapping — the total number of cards is unchanged.** -/
theorem deal_total_length (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : k ≤ st.drawPile.length) :
    (deal N st h k hk).drawPile.length + (deal N st h k hk).hand.length + (deal N st h k hk).discard.length =
      st.drawPile.length + st.hand.length + st.discard.length := by
  rw [deal_drawPile_length, deal_hand_length, deal_discard_length]
  omega

/-- **The top card of the new hand is the `k`-th card of the old draw pile** —
the card that was dealt last. -/
theorem deal_new_hand_head (N : Nat) (st : CapacityState N) (h : 0 < st.drawPile.length)
    (k : Nat) (hk : 1 ≤ k) (hk2 : k ≤ st.drawPile.length) :
    (deal N st h k hk2).hand.head (List.ne_nil_of_length_pos (by
      have hlen : (deal N st h k hk2).hand.length = st.hand.length + k := deal_hand_length N st h k hk2
      rw [hlen]
      omega)) = st.drawPile[k - 1]' (by omega) := by
  simp only [deal]
  have hlen_k : (st.drawPile.take k).length = k := by
    rw [List.length_take, min_eq_left hk2]
  have hne2 : (st.drawPile.take k).reverse ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_reverse, hlen_k]
    omega
  rw [List.head_append_of_ne_nil hne2]
  rw [List.head_reverse hne2]
  simp only [List.getLast_eq_getElem, hlen_k]
  exact List.getElem_take

/-- **The first card remaining in the draw pile (deck position `k`) is uniform
under the uniform deck law.**  The card at position `⟨k, hk⟩` is the head of the
remaining draw pile — under the uniform deck law it is uniform over the card
universe (`1 / N`) — the sound conditional-uniform hypothesis the batch deal
relies on: the deck must be **uniform**, not a nonuniformly ordered list. -/
theorem deal_first_remaining_uniform_law (N : Nat) (hN : 0 < N) [Nonempty (Equiv.Perm (Fin N))]
    (c : Fin N) (k : Nat) (hk : k < N) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => d ⟨k, hk⟩)) c = (1 : Rat) / N :=
  topCard_uniform_law N hN ⟨k, hk⟩ c

end FiniteDeck
end Shufflemath
