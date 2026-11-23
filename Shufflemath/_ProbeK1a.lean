module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

theorem h50le99 : 50 ≤ 99 := by
  norm_num

/-- **K1a.** The *literal* 25/25 position swap and the *membership-level*
  post-exchange bookkeeping agree: after pushing the deck `d` by the literal
  swap permutation `swapPerm 99 50 h50le99 L R b` (the 25 left positions in `L`
  exchange with the 25 right positions in `R` according to the pairing `b`,
  everything else fixed), the left-pile membership of the resulting deck is
  exactly `newMembership d L R` — the 25 unselected left cards plus the 25
  selected right cards. Independent of the pairing `b`. This is the
  membership-level bridge between the `GSRDeckRound` canonical swap and the
  commander `rawExchange` post-exchange membership (the `GSRDeckBridge`
  segregated special case generalized to an arbitrary deck). -/
theorem K1a_swapPerm_membership
    (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    CommanderMembershipKernels.membership ((FiniteDeck.swapPerm 99 50 h50le99 L R b).trans d) =
      CommanderPhysicalExchange.newMembership d L hL R hR := by
  let hm := h50le99
  set S := FiniteDeck.swapPerm 99 50 hm L R b with hS
  apply Subtype.ext
  -- The subtype bridge needed below (Lean 4.34: `Fin` is not unifiable as
  --   a bare `Subtype`, so `Subtype.ext` does not apply to it; `Fin.ext` +
  --   `dsimp` does, since `(Fin.castLE hm i).val` reduces to `i.val`).
  have hbr (i : Fin 50) (hxl : (FiniteDeck.leftPosition 99 50 hm i).val < 50) :
      (⟨(FiniteDeck.leftPosition 99 50 hm i).val, hxl⟩ : Fin 50) = i := by
    apply Fin.ext
    dsimp only [FiniteDeck.leftPosition, Fin.castLE]
  -- The outer subtype bridge: `⟨⟨x.val, hxl⟩, hsel⟩` and `⟨i, hi⟩` agree on
  --   `.val`, so they are equal subtypes.
  have hsubL (i : Fin 50) (hxl : (FiniteDeck.leftPosition 99 50 hm i).val < 50)
      (hi : i ∈ L) :
      (⟨⟨(FiniteDeck.leftPosition 99 50 hm i).val, hxl⟩, hi⟩ : {i : Fin 50 // i ∈ L}) =
        ⟨i, hi⟩ := by
    apply Subtype.ext
    exact hbr i hxl
  -- Selected left position: sent to its paired right position.
  have hsel (i : Fin 50) (hi : i ∈ L) :
      S (FiniteDeck.leftPosition 99 50 hm i) =
        FiniteDeck.rightPosition 99 50 hm ((b ⟨i, hi⟩).val) := by
    dsimp only [S]
    change (FiniteDeck.swapFn 99 50 hm L R b) (FiniteDeck.leftPosition 99 50 hm i) =
      FiniteDeck.rightPosition 99 50 hm ((b ⟨i, hi⟩).val)
    have hxl : (FiniteDeck.leftPosition 99 50 hm i).val < 50 := by
      dsimp only [FiniteDeck.leftPosition]
      exact i.isLt
    have h1 := FiniteDeck.swapFn_selectedLeft 99 50 hm L R b
      (FiniteDeck.leftPosition 99 50 hm i) hxl hi
    convert h1
    -- goal: ⟨i, hi⟩ = ⟨⟨(leftPosition i).val, hxl⟩, hi⟩
    exact (hsubL i hxl hi).symm
  -- Unselected left position: fixed.
  have huns (i : Fin 50) (hi : i ∉ L) :
      S (FiniteDeck.leftPosition 99 50 hm i) = FiniteDeck.leftPosition 99 50 hm i := by
    dsimp only [S]
    change (FiniteDeck.swapFn 99 50 hm L R b) (FiniteDeck.leftPosition 99 50 hm i) =
      FiniteDeck.leftPosition 99 50 hm i
    have hxl : (FiniteDeck.leftPosition 99 50 hm i).val < 50 := by
      dsimp only [FiniteDeck.leftPosition]
      exact i.isLt
    have hi' : (⟨(FiniteDeck.leftPosition 99 50 hm i).val, hxl⟩ : Fin 50) ∉ L := by
      simpa [hbr i hxl] using hi
    exact (FiniteDeck.swapFn_unselectedLeft 99 50 hm L R b
      (FiniteDeck.leftPosition 99 50 hm i) hxl hi')
  -- The left-pile cards of the swapped deck.
  apply Finset.ext
  intro x
  constructor
  · -- LHS ⊆ RHS: a card sitting at a left position after the swap came
    --   either from an unselected left position (fixed) or from a selected
    --   right position (the paired one).
    intro hx
    unfold CommanderMembershipKernels.membership at hx
    change x ∈ leftCards (S.trans d) at hx
    change x ∈ (Finset.univ : Finset (Fin 50)).image
      (fun (i : Fin 50) => (S.trans d) (FiniteDeck.leftPosition 99 50 hm i)) at hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, _, hEq⟩
    have hX : x = d (S (FiniteDeck.leftPosition 99 50 hm i)) := by
      simpa [← hEq] using (Equiv.trans_apply S d (FiniteDeck.leftPosition 99 50 hm i))
    change x ∈ (Finset.image (fun (l : Fin 50) => d (FiniteDeck.leftPosition 99 50 hm l))
        ((Finset.univ : Finset (Fin 50)) \ L)
      ∪ Finset.image (fun (r : Fin 49) => d (FiniteDeck.rightPosition 99 50 hm r)) R)
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases hiL : i ∈ L
    · rw [hX, hsel i hiL]
      refine Or.inr ⟨((b ⟨i, hiL⟩).val), ?_, rfl⟩
      exact (b ⟨i, hiL⟩).property
    · rw [hX, huns i hiL]
      refine Or.inl ⟨i, ?_, rfl⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ i, hiL⟩
  · -- RHS ⊆ LHS: a card in the post-exchange left pile is either at an
    --   unselected left position (fixed by the swap) or at a selected right
    --   position, which the swap sends to its paired left position.
    intro hx
    change x ∈ CommanderPhysicalExchange.newLeftCards d L R at hx
    change x ∈ (Finset.image (fun (l : Fin 50) => d (FiniteDeck.leftPosition 99 50 hm l))
        ((Finset.univ : Finset (Fin 50)) \ L)
      ∪ Finset.image (fun (r : Fin 49) => d (FiniteDeck.rightPosition 99 50 hm r)) R) at hx
    rw [Finset.mem_union] at hx
    rcases hx with hLft | hRgt
    · -- x = d (leftPosition l), l ∈ univ \ L
      rw [Finset.mem_image] at hLft
      rcases hLft with ⟨l, hlMem, hEq⟩
      rw [Finset.mem_sdiff] at hlMem
      have hNotL := hlMem.2
      unfold CommanderMembershipKernels.membership
      change x ∈ leftCards (S.trans d)
      change x ∈ (Finset.univ : Finset (Fin 50)).image
        (fun (i : Fin 50) => (S.trans d) (FiniteDeck.leftPosition 99 50 hm i))
      rw [Finset.mem_image]
      refine ⟨l, ?_, ?_⟩
      · exact Finset.mem_univ l
      · have hT : (S.trans d) (FiniteDeck.leftPosition 99 50 hm l) =
              d (S (FiniteDeck.leftPosition 99 50 hm l)) :=
            Equiv.trans_apply S d (FiniteDeck.leftPosition 99 50 hm l)
        rw [huns l hNotL] at hT
        rw [hT]
        exact hEq
    · -- x = d (rightPosition r), r ∈ R: witness the paired left position
      rw [Finset.mem_image] at hRgt
      rcases hRgt with ⟨r, hr, hEq⟩
      let iw := (b.symm ⟨r, hr⟩).val
      have hIw : ⟨iw, (b.symm ⟨r, hr⟩).property⟩ = (b.symm ⟨r, hr⟩) := by
        apply Subtype.ext
        rfl
      have hS' : S (FiniteDeck.leftPosition 99 50 hm iw) =
          FiniteDeck.rightPosition 99 50 hm r := by
        simpa [hsel iw (b.symm ⟨r, hr⟩).property, hIw,
               Equiv.apply_symm_apply b ⟨r, hr⟩] using
          hsel iw (b.symm ⟨r, hr⟩).property
      unfold CommanderMembershipKernels.membership
      change x ∈ leftCards (S.trans d)
      change x ∈ (Finset.univ : Finset (Fin 50)).image
        (fun (i : Fin 50) => (S.trans d) (FiniteDeck.leftPosition 99 50 hm i))
      rw [Finset.mem_image]
      refine ⟨iw, ?_, ?_⟩
      · exact Finset.mem_univ iw
      · have hT : (S.trans d) (FiniteDeck.leftPosition 99 50 hm iw) =
              d (S (FiniteDeck.leftPosition 99 50 hm iw)) :=
            Equiv.trans_apply S d (FiniteDeck.leftPosition 99 50 hm iw)
        rw [hS'] at hT
        rw [hT]
        exact hEq

end Shufflemath
