module
public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Tactic
@[expose] public section
namespace Shufflemath
namespace FiniteDeck

/-!
The literal physical exchange, generalized to an arbitrary `N`-card deck split into
an `m`-card left pile and an `(N-m)`-card right pile.

A **swap** selects `k` left positions and `k` right positions and exchanges the
cards between them.  The post-swap left *pile* (as a set of cards) depends only on
which positions were selected, not on how the selected positions are paired — so the
membership (fiber) pushforward is well-defined and pairing-independent.  This module
gives the concrete post-swap left pile `newLeftCards`, its size, and the
stabilizer-invariance (conjugation) law that is the general-N/m analog of the
Commander A2 core `newLeftCards_conjugate`.
-/

/-- The card-set of the left pile *after* exchanging the selected left positions
  `L` and selected right positions `R`: the unselected left positions keep their
  cards, and the selected right positions' cards move in.  This is the post-swap
  left-pile content, independent of the ordering (and of the `L`-`R` pairing).
  General-N/m analog of `CommanderPhysicalExchange.newLeftCards`. -/
def newLeftCards (N m : Nat) (hm : m ≤ N) (d : Deck N)
    (L : Finset (Fin m)) (R : Finset (Fin (N - m))) : Finset (Fin N) :=
  ((Finset.univ : Finset (Fin m)) \ L).image (fun l => d (leftPosition N m hm l)) ∪
    R.image (fun r => d (rightPosition N m hm r))

theorem newLeftCards_parts_disjoint (N m : Nat) (hm : m ≤ N) (d : Deck N)
    (L : Finset (Fin m)) (R : Finset (Fin (N - m))) :
    Disjoint (((Finset.univ : Finset (Fin m)) \ L).image (fun l => d (leftPosition N m hm l)))
      (R.image (fun r => d (rightPosition N m hm r))) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.eq_empty_of_forall_notMem
  intro c hc
  rw [Finset.mem_inter] at hc
  rcases hc with ⟨hA, hB⟩
  rcases Finset.mem_image.mp hA with ⟨l, hl, heqL⟩
  rcases Finset.mem_image.mp hB with ⟨r, hr, heqR⟩
  have heq : d (leftPosition N m hm l) = d (rightPosition N m hm r) := heqL.trans heqR.symm
  have hne : leftPosition N m hm l ≠ rightPosition N m hm r := by
    intro heq2
    have hval : (leftPosition N m hm l).val = (rightPosition N m hm r).val := congrArg Fin.val heq2
    have hL : (leftPosition N m hm l).val < m := by
      dsimp only [leftPosition, Fin.castLE]
      simpa using l.isLt
    have hR : m ≤ (rightPosition N m hm r).val := by
      dsimp only [rightPosition]
      omega
    omega
  have hdinj : Function.Injective d := d.injective
  have hne' : d (leftPosition N m hm l) ≠ d (rightPosition N m hm r) := fun h3 => hne (hdinj h3)
  exact False.elim (hne' heq)

/-- Exchanging `k` positions from each pile leaves the left pile with exactly `m`
  cards: the `m - k` unselected left cards plus the `k` selected right cards. -/
theorem newLeftCards_card (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m) (d : Deck N)
    (L : Finset (Fin m)) (hL : L.card = k) (R : Finset (Fin (N - m))) (hR : R.card = k) :
    (newLeftCards N m hm d L R).card = m := by
  classical
  unfold newLeftCards
  have hdisj := newLeftCards_parts_disjoint N m hm d L R
  rw [Finset.card_union_of_disjoint hdisj]
  have hinjL : Function.Injective (fun (l : Fin m) => d (leftPosition N m hm l)) :=
    d.injective.comp (leftPosition_injective N m hm)
  have hinjR : Function.Injective (fun (r : Fin (N - m)) => d (rightPosition N m hm r)) :=
    d.injective.comp (rightPosition_injective N m hm)
  rw [Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]
  have hLsub : L ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hLsub, hL, hR]
  simpa using Nat.sub_add_cancel hk

/-- The membership (left pile) resulting from the swap: the post-swap left pile has
  `m` cards, so it is a valid membership.  This is **pairing-independent** by
  construction — `newLeftCards` depends only on the selected position sets `L` and
  `R`, not on any bijection pairing the two.  General-N/m analog of
  `CommanderPhysicalExchange.newMembership`. -/
def literalSwapMembership (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m) (d : Deck N)
    (L : Finset (Fin m)) (hL : L.card = k) (R : Finset (Fin (N - m))) (hR : R.card = k) :
    Membership N m :=
  ⟨newLeftCards N m hm d L R, newLeftCards_card N m k hm hk hkm d L hL R hR⟩

/-- **General-N/m A2 core: stabilizer-invariance of the swap, pointwise.** Relabeling
  the cards by a permutation `f` commutes with the swap: the post-swap left pile of
  the relabeled deck `d.trans f` is exactly the `f`-image of the original post-swap
  left pile.  General analog of `CommanderPhysicalExchange.newLeftCards_conjugate`. -/
theorem newLeftCards_conjugate (N m : Nat) (hm : m ≤ N) (f d : Deck N)
    (L : Finset (Fin m)) (R : Finset (Fin (N - m))) :
    newLeftCards N m hm (d.trans f) L R = (newLeftCards N m hm d L R).image f := by
  unfold newLeftCards at *
  apply Finset.ext
  intro c
  simp only [Function.comp_apply, Equiv.trans_apply, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    rcases h with hL | hR
    · rcases hL with ⟨l, hl, hcl⟩
      refine ⟨d (leftPosition N m hm l), ⟨Or.inl ⟨l, hl, rfl⟩, hcl⟩⟩
    · rcases hR with ⟨r, hr, hcr⟩
      refine ⟨d (rightPosition N m hm r), ⟨Or.inr ⟨r, hr, rfl⟩, hcr⟩⟩
  · intro h
    rcases h with ⟨a, ha, hac⟩
    rcases ha with hL | hR
    · rcases hL with ⟨l, hl, hal⟩
      refine Or.inl ⟨l, hl, ?_⟩
      simpa [hal] using hac
    · rcases hR with ⟨r, hr, har⟩
      refine Or.inr ⟨r, hr, ?_⟩
      simpa [har] using hac

end FiniteDeck
end Shufflemath
