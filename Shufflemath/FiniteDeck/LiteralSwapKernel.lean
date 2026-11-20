module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PhysicalSwap
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G3 (B1): the literal two-pile swap as a deck permutation

The `PhysicalSwap` module computed, by `Finset` bookkeeping, the *membership*
(the left pile) a literal two-pile swap produces: `newLeftCards` keeps the
unselected left cards and collects the selected right cards, independently of
which selected right card is paired to which selected left slot.

This module makes that same swap an **actual deck permutation**
`swapPerm : Equiv.Perm (Fin N)`: it transposes each selected left *global*
position `leftPosition l` with the paired selected right position
`rightPosition (b l)` and fixes every other position.  Because it is a genuine
permutation of positions, it acts on any deck by composition, and the headline
result (later in this file) is the pointwise identity
`membership (swapPerm ∘ d) = literalSwapMembership d`, i.e. the permutation and
the finset bookkeeping agree — with **no** dependence on the pairing `b`.

The 99-card special case is `N = 99`, `m = 50`, `k = 25`, `L ⊆ Fin 50`,
`R ⊆ Fin 49`, both of cardinality `25`.
-/

/-- A left-pile index embeds to a deck position whose `Fin.val` is unchanged. -/
theorem leftPosition_val (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    (leftPosition N m hm i).val = i.val := by
  dsimp only [leftPosition, Fin.castLE]

/-- A right-pile index embeds to deck position `m + i.val`. -/
theorem rightPosition_val (N m : Nat) (hm : m ≤ N) (i : Fin (N - m)) :
    (rightPosition N m hm i).val = m + i.val := by
  dsimp only [rightPosition]

/-- The right-index bound: if `x` is a right position (`m ≤ x.val`), then
  `x.val - m` is a valid `Fin (N - m)` value. -/
def rightBound (N m : Nat) (hm : m ≤ N) (x : Fin N) (hmle : m ≤ x.val) : x.val - m < N - m := by
  have hxN : x.val < N := x.isLt
  omega

/-- The literal swap, as a bare function on deck positions.

  A position `x` is a left position exactly when `x.val < m`.  Selected left
  positions (`⟨x.val,_⟩ ∈ L`) are sent to their paired selected right position;
  selected right positions (`⟨x.val-m,_⟩ ∈ R`) to the paired selected left
  position; everything else is fixed.  This is the raw function behind the
  `swapPerm` permutation. -/
def swapFn (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N) : Fin N :=
  if hl : x.val < m then
    if hLmem : (⟨x.val, hl⟩ : Fin m) ∈ L then
      rightPosition N m hm (b ⟨⟨x.val, hl⟩, hLmem⟩).val
    else x
  else
    if hRmem : (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hl)⟩ : Fin (N - m)) ∈ R then
      leftPosition N m hm (b.symm
        ⟨⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hl)⟩, hRmem⟩).val
    else x

/-- Selected left: a left position `x` with `⟨x.val,_⟩ ∈ L` is sent to the paired
  selected right position.  `split_ifs` uses the context hypotheses to collapse to
  the single live branch, whose fresh membership sits on the same `Fin` as `hsel`,
  so the branch's subtype is fixed by its first field. -/
theorem swapFn_selectedLeft (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N)
    (hxl : x.val < m) (hsel : (⟨x.val, hxl⟩ : Fin m) ∈ L) :
    swapFn N m hm L R b x = rightPosition N m hm (b ⟨⟨x.val, hxl⟩, hsel⟩).val := by
  unfold swapFn
  split_ifs
  · apply congrArg (fun (e : {i : Fin m // i ∈ L}) => rightPosition N m hm ((b e).val))
    apply Subtype.ext
    rfl

/-- Unselected left: a left position `x` with `⟨x.val,_⟩ ∉ L` is fixed. -/
theorem swapFn_unselectedLeft (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N)
    (hxl : x.val < m) (huns : ¬(⟨x.val, hxl⟩ : Fin m) ∈ L) :
    swapFn N m hm L R b x = x := by
  unfold swapFn
  split_ifs
  · rfl

/-- Selected right: a right position `x` with `⟨x.val - m,_⟩ ∈ R` is sent to the
  paired selected left position. -/
theorem swapFn_selectedRight (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N)
    (hxr : ¬x.val < m)
    (hsel : (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxr)⟩ : Fin (N - m)) ∈ R) :
    swapFn N m hm L R b x =
      leftPosition N m hm (b.symm
        ⟨⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxr)⟩, hsel⟩).val := by
  unfold swapFn
  split_ifs
  · apply congrArg (fun (e : {j : Fin (N - m) // j ∈ R}) => leftPosition N m hm ((b.symm e).val))
    apply Subtype.ext
    rfl

/-- Unselected right: a right position `x` with `⟨x.val - m,_⟩ ∉ R` is fixed. -/
theorem swapFn_unselectedRight (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N)
    (hxr : ¬x.val < m)
    (huns : ¬(⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxr)⟩ : Fin (N - m)) ∈ R) :
    swapFn N m hm L R b x = x := by
  unfold swapFn
  split_ifs
  · rfl

-- WIP (next session): `leftPosition_self` / `rightPosition_self` pile-position
-- self-lemmas, then `swapFn_involution` (the four-subcase involution via the
-- region lemmas above), `swapFn_bijective`, the `Equiv.Perm` packaging, and
-- `swapPerm_involution`.  Full WIP saved to /tmp/lsw_k_wip.lean.
end FiniteDeck
end Shufflemath
