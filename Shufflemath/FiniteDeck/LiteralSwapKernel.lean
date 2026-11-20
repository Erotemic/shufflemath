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

Status: the raw function `swapFn`, its four region lemmas, the self/index
lemmas, the **involution** `swapFn_involution`, the **bijectivity**
`swapFn_bijective`, the resulting permutation `swapPerm : Equiv.Perm (Fin N)`,
and the **pairing-bijection image** lemma `selectedRight_image_eq` are all proved
in this file.  The headline pointwise identity
`membership (swapPerm ∘ d) = literalSwapMembership d` (permutation ↔ finset
bookkeeping agree on the left pile, pairing-independent) is the remaining step;
`selectedRight_image_eq` is the crux it reduces to.
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
theorem rightBound (N m : Nat) (hm : m ≤ N) (x : Fin N) (hmle : m ≤ x.val) : x.val - m < N - m := by
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

theorem leftPosition_self (N m : ℕ) (hm : m ≤ N) (x : Fin N) (hxl : x.val < m) :
    leftPosition N m hm (⟨x.val, hxl⟩) = x := by
  apply Fin.ext
  have hxN : x.val < N := x.isLt
  simp [leftPosition_val]

theorem rightPosition_self (N m : ℕ) (hm : m ≤ N) (x : Fin N) (hxr : ¬x.val < m) :
    rightPosition N m hm (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxr)⟩) = x := by
  apply Fin.ext
  have hle : m ≤ x.val := Nat.le_of_not_lt hxr
  have hxN : x.val < N := x.isLt
  rw [rightPosition_val]
  simpa using Nat.add_sub_of_le hle

theorem rightPosition_index (N m : ℕ) (hm : m ≤ N) (i : Fin (N - m))
    (hxr : ¬(rightPosition N m hm i).val < m) :
    (⟨(rightPosition N m hm i).val - m, rightBound N m hm (rightPosition N m hm i) (Nat.le_of_not_lt hxr)⟩ : Fin (N - m)) = i := by
  ext
  simp [rightPosition_val]

theorem leftPosition_index (N m : ℕ) (hm : m ≤ N) (i : Fin m) :
    (⟨(leftPosition N m hm i).val, i.isLt⟩ : Fin m) = i := by
  ext
  rw [leftPosition_val]

theorem swapFn_involution (N m : ℕ) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N) :
    swapFn N m hm L R b (swapFn N m hm L R b x) = x := by
  by_cases hxl : x.val < m
  · by_cases hsel : (⟨x.val, hxl⟩ : Fin m) ∈ L
    · let i := (⟨x.val, hxl⟩ : Fin m)
      let j := b ⟨i, hsel⟩
      have h1 : swapFn N m hm L R b x = rightPosition N m hm j.val := by simpa [i, j] using swapFn_selectedLeft N m hm L R b x hxl hsel
      rw [h1]
      have hxr : ¬(rightPosition N m hm j.val).val < m := by rw [rightPosition_val]; omega
      have hselR : (⟨(rightPosition N m hm j.val).val - m, rightBound N m hm (rightPosition N m hm j.val) (Nat.le_of_not_lt hxr)⟩ : Fin (N - m)) ∈ R := by
        simpa [rightPosition_index N m hm j.val hxr] using j.2
      let rj : {j : Fin (N - m) // j ∈ R} := ⟨⟨(rightPosition N m hm j.val).val - m, rightBound N m hm (rightPosition N m hm j.val) (Nat.le_of_not_lt hxr)⟩, hselR⟩
      have h2 : swapFn N m hm L R b (rightPosition N m hm j.val) = leftPosition N m hm (b.symm rj).val :=
        by simpa [rj] using swapFn_selectedRight N m hm L R b (rightPosition N m hm j.val) hxr hselR
      rw [h2]
      have hsub : rj = (j : {j : Fin (N - m) // j ∈ R}) := by
        refine Subtype.ext ?_
        simpa [rj, j] using rightPosition_index N m hm j.val hxr
      have hback : b.symm rj = (b.symm j : {i : Fin m // i ∈ L}) := by simpa [hsub]
      have hleft : (b.symm j : {i : Fin m // i ∈ L}) = ⟨i, hsel⟩ := by simpa [j] using Equiv.symm_apply_apply b ⟨i, hsel⟩
      simpa [hback, hleft, i] using leftPosition_self N m hm x hxl
    · have h1 : swapFn N m hm L R b x = x := by simpa using swapFn_unselectedLeft N m hm L R b x hxl hsel
      rw [h1, h1]
  · let rIdx := (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxl)⟩ : Fin (N - m))
    by_cases hsel : rIdx ∈ R
    · let j := rIdx
      let i := b.symm ⟨j, hsel⟩
      have h1 : swapFn N m hm L R b x = leftPosition N m hm i.val := by simpa [j] using swapFn_selectedRight N m hm L R b x hxl hsel
      rw [h1]
      have hxl2 : (leftPosition N m hm i.val).val < m := by rw [leftPosition_val]; exact i.val.isLt
      have hselL : (⟨(leftPosition N m hm i.val).val, hxl2⟩ : Fin m) ∈ L := by
        simpa [leftPosition_index N m hm i.val] using i.2
      let li : {i : Fin m // i ∈ L} := ⟨⟨(leftPosition N m hm i.val).val, hxl2⟩, hselL⟩
      have h2 : swapFn N m hm L R b (leftPosition N m hm i.val) = rightPosition N m hm (b li).val :=
        by simpa [li] using swapFn_selectedLeft N m hm L R b (leftPosition N m hm i.val) hxl2 hselL
      rw [h2]
      have hsub : li = (i : {i : Fin m // i ∈ L}) := by
        refine Subtype.ext ?_
        simpa [li, i] using leftPosition_index N m hm i.val
      have hback : b li = (b i : {j : Fin (N - m) // j ∈ R}) := by simpa [hsub]
      have hright : (b i : {j : Fin (N - m) // j ∈ R}) = ⟨j, hsel⟩ := by simpa [i] using Equiv.apply_symm_apply b ⟨j, hsel⟩
      simpa [hback, hright, j] using rightPosition_self N m hm x hxl
    · have h1 : swapFn N m hm L R b x = x := by simpa using swapFn_unselectedRight N m hm L R b x hxl hsel
      rw [h1, h1]

theorem swapFn_bijective (N m : ℕ) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) :
    Function.Bijective (swapFn N m hm L R b) := by
  constructor
  · intro u v huv
    have h := congrArg (swapFn N m hm L R b) huv
    rwa [swapFn_involution N m hm L R b u, swapFn_involution N m hm L R b v] at h
  · intro y
    exact ⟨swapFn N m hm L R b y, swapFn_involution N m hm L R b y⟩



noncomputable def swapPerm (N m : ℕ) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (swapFn N m hm L R b) (swapFn_bijective N m hm L R b)


/-- The selected left positions, mapped by the pairing `b` to the selected right
  positions, are exactly the selected right positions: because
  `b : {i // i ∈ L} ≃ {j // j ∈ R}` is a bijection, `rightPosition ∘ b` over the whole
  selected-left subtype has the same image as `rightPosition` over `R`.  This is the
  crux used to show the literal-swap permutation and the finset bookkeeping agree on
  the left pile, **independently of the pairing** `b`. -/
theorem selectedRight_image_eq (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) :
    (Finset.univ : Finset {i : Fin m // i ∈ L}).image (fun (s : {i : Fin m // i ∈ L}) =>
        rightPosition N m hm (b s).val) = R.image (rightPosition N m hm) := by
  apply Finset.ext
  intro x
  simp only [Finset.mem_image, Finset.mem_univ]
  constructor
  · intro ⟨s, hs, h⟩
    refine ⟨(b s).val, ?_, ?_⟩
    · simpa using (b s).2
    · simpa [h] using rfl
  · intro ⟨r, hr, h⟩
    exact ⟨b.symm ⟨r, hr⟩, by simp, by rw [Equiv.apply_symm_apply]; simpa using h⟩

end FiniteDeck
end Shufflemath
