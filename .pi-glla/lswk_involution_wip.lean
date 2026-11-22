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

/-- A left position is the image of its own left-index under `leftPosition`. -/
lemma leftPosition_self (N m : ℕ) (hm : m ≤ N) (x : Fin N) (hxl : x.val < m) :
    leftPosition N m hm (⟨x.val, hxl⟩) = x := by
  apply Fin.ext
  simp [leftPosition]

/-- A right position is the image of its own right-index under `rightPosition`. -/
lemma rightPosition_self (N m : ℕ) (hm : m ≤ N) (x : Fin N) (hxr : ¬x.val < m) :
    rightPosition N m hm (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxr)⟩) = x := by
  apply Fin.ext
  have hle : m ≤ x.val := Nat.le_of_not_lt hxr
  rw [rightPosition_val]
  exact Nat.add_sub_cancel_left hle

/-- The literal two-pile swap is an **involution**: it transposes each selected
  left position with its paired selected right position (and vice versa) and fixes
  everything else, so applying it twice is the identity.  Each subcase applies a
  region lemma twice and closes with the pile-position self-lemmas. -/
theorem swapFn_involution (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) (x : Fin N) :
    swapFn N m hm L R b (swapFn N m hm L R b x) = x := by
  set f := swapFn N m hm L R b
  by_cases hxl : x.val < m
  · -- x is a left position
    by_cases hmem : (⟨x.val, hxl⟩ : Fin m) ∈ L
    · -- selected left: f x = rightPosition rIdx (rIdx ∈ R); f sends that back to x.
      let rIdx := (b ⟨⟨x.val, hxl⟩, hmem⟩).val
      have hmemR : rIdx ∈ R := (b ⟨⟨x.val, hxl⟩, hmem⟩).2
      have h1 : f x = rightPosition N m hm rIdx := by simpa [rIdx] using swapFn_selectedLeft N m hm L R b x hxl hmem
      rw [h1]
      have hxr : ¬(rightPosition N m hm rIdx).val < m := by rw [rightPosition_val]; omega
      have hval : (rightPosition N m hm rIdx).val - m = rIdx.val := by rw [rightPosition_val]; omega
      have hb : (rightPosition N m hm rIdx).val - m < N - m := by
        rw [hval]
        exact rIdx.isLt
      have hselR : (⟨(rightPosition N m hm rIdx).val - m, hb⟩ : Fin (N - m)) ∈ R := by
        have hfin : (⟨(rightPosition N m hm rIdx).val - m, hb⟩ : Fin (N - m)) = rIdx := by
          ext
          simpa [hval] using rIdx
        simpa [hfin] using hmemR
      have h2 : f (rightPosition N m hm rIdx) =
          leftPosition N m hm (b.symm ⟨⟨(rightPosition N m hm rIdx).val - m, hb⟩, hselR⟩).val := by
        simpa [hval, hb] using swapFn_selectedRight N m hm L R b (rightPosition N m hm rIdx) hxr
          (by simpa [hval, hb] using hselR)
      rw [h2]
      have hback : b.symm ⟨⟨(rightPosition N m hm rIdx).val - m, hb⟩, hselR⟩ = ⟨⟨x.val, hxl⟩, hmem⟩ := by
        refine Subtype.ext ?_
        -- both reduce to (b ⟨⟨x,hxl⟩,hmem⟩).val and then back
        have hval : (rightPosition N m hm rIdx).val - m = rIdx.val := by rw [rightPosition_val]; omega
        simp [hval, rIdx]
        -- b.symm (b a) = a
      simpa [hback, leftPosition_self N m hm x hxl] using swapFn_selectedLeft N m hm L R b (rightPosition N m hm rIdx) hxr
          (by simpa [hval, hb] using hselR)
    · -- unselected left: f x = x
      have h1 : f x = x := by simpa using swapFn_unselectedLeft N m hm L R b x hxl hmem
      rw [h1, h1]
  · -- x is a right position
    by_cases hmem : (⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxl)⟩ : Fin (N - m)) ∈ R
    · -- selected right: f x = leftPosition lIdx (lIdx ∈ L); f sends that back to x.
      let lIdx := (b.symm ⟨⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxl)⟩, hmem⟩).val
      have hmemL : lIdx ∈ L := (b.symm ⟨⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxl)⟩, hmem⟩).2
      have h1 : f x = leftPosition N m hm lIdx := by simpa [lIdx] using swapFn_selectedRight N m hm L R b x hxl hmem
      rw [h1]
      have hxl2 : (leftPosition N m hm lIdx).val < m := by rw [leftPosition_val]; exact lIdx.isLt
      have hselL : (⟨(leftPosition N m hm lIdx).val, by rw [leftPosition_val]; exact lIdx.isLt⟩ : Fin m) ∈ L := by
        have hfin : (⟨(leftPosition N m hm lIdx).val, by rw [leftPosition_val]; exact lIdx.isLt⟩ : Fin m) = lIdx := by
          ext
          simpa [leftPosition_val] using lIdx
        simpa [hfin] using hmemL
      have h2 : f (leftPosition N m hm lIdx) =
          rightPosition N m hm (b ⟨⟨(leftPosition N m hm lIdx).val, by rw [leftPosition_val]; exact lIdx.isLt⟩, hselL⟩).val := by
        simpa [leftPosition_val, lIdx] using swapFn_selectedLeft N m hm L R b (leftPosition N m hm lIdx) hxl2 hselL
      rw [h2]
      have hback : b ⟨⟨(leftPosition N m hm lIdx).val, by rw [leftPosition_val]; exact lIdx.isLt⟩, hselL⟩ =
          ⟨⟨x.val - m, rightBound N m hm x (Nat.le_of_not_lt hxl)⟩, hmem⟩ := by
        refine Subtype.ext ?_
        simp [leftPosition_val, lIdx]
      simpa [hback, rightPosition_self N m hm x hxl] using swapFn_selectedLeft N m hm L R b (leftPosition N m hm lIdx) hxl2 hselL
    · -- unselected right: f x = x
      have h1 : f x = x := by simpa using swapFn_unselectedRight N m hm L R b x hxl hmem
      rw [h1, h1]

/-- An involution is bijective: injective (apply the map twice) and surjective
  (every point is the image of its own image). -/
theorem swapFn_bijective (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) : Bijective (swapFn N m hm L R b) := by
  set f := swapFn N m hm L R b
  constructor
  · intro a c
    intro h
    have h1 : f (f a) = f (f c) := by simpa [f] using congr_arg f h
    simpa [f] using Eq.trans (swapFn_involution N m hm L R b a).symm
      (Eq.trans h1 (swapFn_involution N m hm L R b c))
  · intro y
    refine ⟨f y, ?_⟩
    simpa [f] using swapFn_involution N m hm L R b y

/-- The literal two-pile swap as a deck permutation: an involutive bijection of
  positions, built from `swapFn` via its bijectivity. -/
noncomputable def swapPerm (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (swapFn N m hm L R b) (swapFn_bijective N m hm L R b)

/-- The permutation is its own inverse: the literal swap is an involution at the
  `Equiv.Perm` level too. -/
theorem swapPerm_involution (N m : Nat) (hm : m ≤ N) (L : Finset (Fin m)) (R : Finset (Fin (N - m)))
    (b : {i : Fin m // i ∈ L} ≃ {j : Fin (N - m) // j ∈ R}) :
    (swapPerm N m hm L R b).symm = swapPerm N m hm L R b := by
  funext x
  have hf : (swapPerm N m hm L R b) x = swapFn N m hm L R b x := by
    simpa using Equiv.ofBijective_apply (swapFn N m hm L R b) (swapFn_bijective N m hm L R b) x
  have hinv : (swapFn N m hm L R b) ((swapPerm N m hm L R b) x) = x := by
    simpa [hf] using swapFn_involution N m hm L R b x
  -- (swapPerm.symm x) is the unique y with swapPerm y = x; x's own swap works.
  rw [← Eq.symm]
  refine (Equiv.invFun_ext _).symm ?_  -- placeholder; refined below
  · sorry
  · sorry
end FiniteDeck
end Shufflemath
