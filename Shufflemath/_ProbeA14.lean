module

public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.FiniteDeck.UniformExchange
public import Shufflemath.GSR
public import Shufflemath.Markov
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath.FiniteDeck
open Classical

/-- Cumulative number of cards in piles strictly before `i`.  (No `N`: the
    cumulative count of pile capacities does not depend on the deck size.) -/
def prefixCap (p : Nat) (n : Fin p → Nat) (i : Fin p) : Nat :=
  (Finset.univ : Finset (Fin p)).sum (fun k => if k.val < i.val then n k else 0)

/-- Pile `i` of the **block partition** of the deck: the cards `x` whose
    position `x.val` lies in the half-open interval
    `[prefixCap n i, prefixCap n i + n i)`.  Consecutive blocks tile the deck
    exactly when the capacities fill it. -/
def blockCap (N p : Nat) (n : Fin p → Nat) (i : Fin p) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter
    (fun x => prefixCap p n i ≤ x.val ∧ x.val < prefixCap p n i + n i)

/-- The sum of an ite that selects a single term `i` is just that term. -/
theorem iteSingleSum (p : Nat) (n : Fin p → Nat) (i : Fin p) :
    (Finset.univ : Finset (Fin p)).sum (fun k => if k = i then n k else 0) = n i := by
  simp

/-- The block `i` ends within the deck. -/
theorem prefixCap_le_total (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) (i : Fin p) :
    prefixCap p n i + n i ≤ N := by
  have h1 : prefixCap p n i + n i =
      (Finset.univ : Finset (Fin p)).sum
        (fun k => (if k.val < i.val then n k else 0) + (if k = i then n k else 0)) := by
    dsimp only [prefixCap]
    rw [← iteSingleSum p n i, Finset.sum_add_distrib]
  rw [h1, ← hsum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hlt : k.val < i.val
  · have hne : k ≠ i := by
      intro hki; subst hki; exact Nat.lt_irrefl _ hlt
    have hb : (if k = i then n k else 0) = 0 := by simp [hne]
    have ha : (if k.val < i.val then n k else 0) = n k := by simp [hlt]
    rw [ha, hb]; exact Nat.le_refl _
  · have ha : (if k.val < i.val then n k else 0) = 0 := by simp [hlt]
    by_cases heq : k = i
    · have hb : (if k = i then n k else 0) = n k := by simp [heq]
      rw [ha, hb, Nat.zero_add]
    · have hb : (if k = i then n k else 0) = 0 := by simp [heq]
      rw [ha, hb]; exact Nat.zero_le _

/-- Pile `i` of the block partition holds exactly `n i` cards. -/
theorem blockCap_card (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) (i : Fin p) :
    (blockCap N p n i).card = n i := by
  set a := prefixCap p n i
  set b := a + n i
  have hbN : b ≤ N := prefixCap_le_total N p n hsum i
  have hinj : Function.Injective (fun (x : Fin N) => x.val) := by
    intro x y h; exact Fin.ext h
  have hcard_inj : (blockCap N p n i).card = (Finset.image (·.val) (blockCap N p n i)).card := by
    rw [← (Finset.card_image_of_injective (blockCap N p n i) hinj)]
  have himg : Finset.image (·.val) (blockCap N p n i) =
      (Finset.range N).filter (fun v => a ≤ v ∧ v < b) := by
    dsimp only [blockCap, a, b]
    ext v
    constructor
    · intro hv
      obtain ⟨x, hxmem, hxeq⟩ := Finset.mem_image.mp hv
      -- hxmem : x ∈ univ.filter (fun x => P x), hxeq : x.val = v
      have hP : prefixCap p n i ≤ x.val ∧ x.val < prefixCap p n i + n i :=
        (Finset.mem_filter.mp hxmem).2
      have hvN : v < N := by rw [← hxeq]; exact x.isLt
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvN, ⟨?_, ?_⟩⟩
      · rw [← hxeq]; exact hP.1
      · rw [← hxeq]; exact hP.2
    · intro hv
      have hmem : v < N ∧ a ≤ v ∧ v < b := by
        have h1 := Finset.mem_filter.mp hv
        exact ⟨Finset.mem_range.mp h1.1, h1.2.1, h1.2.2⟩
      obtain ⟨hvn, hA, hB⟩ := hmem
      refine Finset.mem_image.mpr ⟨Fin.mk v hvn, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hA, hB⟩⟩
  have h2 : (Finset.range N).filter (fun v => a ≤ v ∧ v < b) = Finset.range b \ Finset.range a := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    constructor
    · rintro ⟨hNv, hav, hvb⟩
      exact ⟨hvb, Nat.not_lt.2 hav⟩
    · rintro ⟨hvb, hnotva⟩
      exact ⟨Nat.lt_of_lt_of_le hvb hbN, Nat.not_lt.1 hnotva, hvb⟩
  rw [hcard_inj, himg, h2, Finset.card_sdiff_of_subset (Finset.range_subset_range.mpr (by omega)),
      Finset.card_range, Finset.card_range]
  simp only [b, Nat.add_sub_cancel_left]

/-- `x` is in block `i` exactly when its card value falls in the block's
    half-open value interval `[prefixCap i, prefixCap i + n i)`. -/
theorem memBlockCap_iff (N p : Nat) (n : Fin p → Nat) (i : Fin p) (x : Fin N) :
    x ∈ blockCap N p n i ↔ prefixCap p n i ≤ x.val ∧ x.val < prefixCap p n i + n i := by
  -- blockCap i = univ.filter (fun x => P x), so x ∈ blockCap i ↔ P x directly.
  dsimp only [blockCap]
  simp only [Finset.mem_filter, Finset.mem_univ, and_self, true_and]

/-- Monotonicity of `prefixCap`: if `i.val ≤ j.val` then `prefixCap i ≤ prefixCap j`.
    (The prefix sum up to `i` is a sub-sum of the prefix sum up to `j`,
    and every `n k` is nonnegative.)
    -/
-- NEXT (A1.1 closeout): prove by sum-subset. The obstacle: after `dsimp [prefixCap]`
-- the two sides are `∑ k ∈ range (i.val+1), n (Fin.mk k hk_i)` and the same over
-- `range (j.val+1)` with a DIFFERENT `Fin.mk` proof `hk_j`, so
-- `Finset.sum_le_sum_of_subset` needs a common-function step first. Fix: prove
-- `n (Fin.mk k hk_i) = n (Fin.mk k hk_j)` via `Fin.ext` (both have val `k`), then
-- `conv` / `congr` to merge the two sums into one `f`. Then `sum_le_sum_of_subset`.
theorem prefixCap_mono (p : Nat) (n : Fin p → Nat) (i j : Fin p) (h : i.val ≤ j.val) :
    prefixCap p n i ≤ prefixCap p n j := by
  -- prefixCap i = ∑_{k, k.val < i.val} n k and prefixCap j = ∑_{k, k.val < j.val} n k.
  -- Since i.val ≤ j.val, {k | k.val < i.val} ⊆ {k | k.val < j.val}, so the summand is
  -- pointwise ≤ (the smaller ite is 0 wherever the larger one might add, and n k ≥ 0).
  dsimp only [prefixCap]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hklt : k.val < i.val
  · have hkj : k.val < j.val := Nat.lt_of_lt_of_le hklt h
    simp [hklt, hkj]
  · simp [hklt]

/-- Unique ownership: a card lies in at most one block.
    Strategy: each block holds values in `[a_k, a_k + n_k)` with `a_{k+1} = a_k + n_k`
    (telescope); two blocks sharing `x.val` force `i = j` via `prefixCap_mono`. -/
theorem blockUnique (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) (i j : Fin p) (x : Fin N) :
    x ∈ blockCap N p n i → x ∈ blockCap N p n j → i = j := by
  intro hi hj
  have hiI : prefixCap p n i ≤ x.val ∧ x.val < prefixCap p n i + n i :=
    (memBlockCap_iff N p n i x).mp hi
  have hjI : prefixCap p n j ≤ x.val ∧ x.val < prefixCap p n j + n j :=
    (memBlockCap_iff N p n j x).mp hj
  -- i ≤ j: else j < i, so a_{j+1} = a_j + n_j ≤ a_i (prefixCap_mono) and
  -- x.val < a_{j+1} ≤ a_i ≤ x.val, contradiction. (Needs prefixCap_mono.)
  -- j ≤ i: symmetric.
  -- Then Fin.le_antisymm.
  sorry

/-- Coverage: every card lies in some block. -/
-- NEXT (A1.1 closeout): the blocks tile [0, N): take i* = max {i | prefixCap i ≤ x.val}
-- (nonempty since prefixCap 0 = 0 ≤ x.val); maximality + the telescope give
-- prefixCap i* ≤ x.val < prefixCap i* + n i*, i.e. x ∈ blockCap i*.
-- Alternatively the smallest i with prefixCap (i+1) > x.val.
theorem blockCover (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) (x : Fin N) :
    ∃ i : Fin p, x ∈ blockCap N p n i := by
  sorry

/-- The block partition is a genuine `IsPartition` of the deck. -/
theorem blockIsPartition (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) :
    IsPartition (blockCap N p n) := by
  constructor
  · intro x; exact blockCover N p n hsum x
  · intro i j x h1 h2; exact blockUnique N p n hsum i j x h1 h2

/-- Feasible capacities (they fill the deck) admit a valid allocation: split the
    deck into consecutive blocks of the given pile sizes. -/
theorem nonemptyOfSumCapacities (N p : Nat) (n : Fin p → Nat) (hsum : (∑ i, n i) = N) :
    Nonempty (Allocation N p n) := by
  let P := blockCap N p n
  let hP : IsPartition P := blockIsPartition N p n hsum
  have heq : (fun i : Fin p => (P i).card) = n := funext fun i => blockCap_card N p n hsum i
  exact heq ▸ Allocation.nonemptyOfPartition P hP

-- NOTE (A1 capstone, deferred to handoff): `swapKernel hN` is a bare transition
-- `Allocation → Dist (Allocation)`, NOT a `FiniteKernel`, so the `DetailedBalance`/
-- `FiniteKernel.apply` machinery does not apply directly. The correct statement is
-- that the **uniform law over feasible allocations is stationary** under the swap
-- transition, proved via (i) row-stochasticity `∑_A mass (swapKernel hN B) A = 1`
-- (from `swapKernel_mass` — a row is `(N*N)⁻¹` over the `N*N` swap positions) and
-- (ii) `swapKernel_symmetric`, which flips `∑_A mass (K A) B` to `∑_A mass (K B) A = 1`.
-- This is documented in the handoff rather than stubbed here.

end FiniteDeck
