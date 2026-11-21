module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic
public import Shufflemath.FiniteDeck.Gate6FiniteGSR

@[expose] public section

namespace Shufflemath
namespace _ProbeGate6Collision

open Finset

/-! Gate 6 — the §4 collision-coupling chain (deep-structural-hints §4), lemma 1
of 4: `collisionProb_le`. The probability that a uniform random label array
`f : Fin n → Fin a` (`a > 0`) has a collision (two distinct positions share a
label) is at most the pairwise union bound `choose(n,2) / a`. This is the
per-pile half of the Gate 6 two-pile budget
`delta1 = (choose 50 2 + choose 49 2) / 2^23` (hint §8).

The §4.3 strategy: couple the finite-riffle world (sort each pile by its
2³-binary GSR labels) with the perfect world (uniform within-pile permutation)
on the SAME label arrays; the decks agree exactly when both arrays are
collision-free, so
`TV(finiteLocal, perfectLocal) ≤ P(collision) ≤ choose(m,2)/a_L + choose(N-m,2)/a_R`,
row-wise, with no big TV-isometry theorem needed. This file develops the
abstract collision bound; the remaining §4 lemmas (`uniform_rank_when_no_ties`,
`TV ≤ mismatchProbability`, `localCoupling_rowTV`) build on it. -/

/-- The label-array space `[n] → (alphabet of size a)` has `a^n` points: one
    i.i.d. uniform choice per position. -/
theorem cardFnFinA (n a : Nat) : Fintype.card (Fin n → Fin a) = a ^ n := by
  simp [Fintype.card_fin, Finset.prod_const]

/-- A label array has a collision when two distinct positions share a label. -/
def collision (n a : Nat) (f : Fin n → Fin a) : Bool :=
  ((univ : Finset (Fin n × Fin n)).filter fun p => decide (p.1 ≠ p.2) && decide (f p.1 = f p.2)).Nonempty

/-- The set of all colliding label arrays. -/
noncomputable def collisionSet (n a : Nat) : Finset (Fin n → Fin a) :=
  (univ : Finset (Fin n → Fin a)).filter fun f => collision n a f

/-- (sub-lemma 1a, helper) The `i < j` pairs are counted by the double sum
    `Σ_i Σ_j [i < j]`. Two standard reindexing steps: (1) `sum_boole`
    (`∑ x ∈ s, [p x] = # {x ∈ s | p x} = (s.filter p).card`) turns the filter
    cardinality into an indicator sum over `univ (Fin n × Fin n)`; (2)
    `Fintype.sum_prod_type'` (`∑ x : α×β, f x.1 x.2 = ∑ x, ∑ y, f x y`) collapses
    the product-type sum into the nested `Σ_i Σ_j`. *Remaining* for `cardIjPairs`:
    the **inner** count `Σ_j : Fin n, [i < j] = n - 1 - i.val` (the `Fin` range
    strictly above `i`; prove `Fintype.card {j : Fin n // i < j} = n - 1 - i.val` via
    an explicit `Equiv {j : Fin n // i < j} ≃ Fin (n - 1 - i.val)`, `j ↦ j.val - (i.val+1)`),
    then `Σ_i (n - 1 - i.val) = Σ_{k < n} k = n*(n-1)/2` by `Finset.sum_range_id`,
    then `Nat.choose_two_right`. -/
noncomputable def ijPairs (n : Nat) : Finset (Fin n × Fin n) :=
  (univ : Finset (Fin n × Fin n)).filter fun p => decide (p.1 < p.2)

theorem cardIj_eq_doubleSum (n : Nat) :
    (ijPairs n).card = (∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0) := by
  -- A: filter-card = indicator sum over `univ (Fin n × Fin n)`  (sum_boole)
  have hA : (ijPairs n).card = (∑ x : Fin n × Fin n, if x.1 < x.2 then 1 else 0) := by
    simp only [ijPairs]
    simpa using (sum_boole (fun x : Fin n × Fin n => x.1 < x.2)
      (Finset.univ : Finset (Fin n × Fin n))).symm
  -- B: product-sum collapses `∑ x : Fin n × Fin n` to the nested `∑ i, ∑ j`.
  set g : (Fin n) → (Fin n) → ℕ := fun i j => if i < j then 1 else 0
  have hB : (∑ x : Fin n × Fin n, if x.1 < x.2 then 1 else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0) := by
    simpa [g] using Fintype.sum_prod_type' (f := g)
  simpa using hA.trans hB

/-- Map a position `j` strictly above `i` down to its offset from `i+1` in
    `Fin (n - 1 - i.val)`. The `Equiv`'s `toFun`/`invFun` are kept as SEPARATE named
    defs (`ijToFin`/`finToIj`) so `simp` can unfold them in the `left_inv`/`right_inv`
    proofs (a `noncomputable def` of `Equiv` cannot be `simp`-unfolded by its own name). -/
noncomputable def ijToFin (n : Nat) (i : Fin n) (x : {j : Fin n // i < j}) : Fin (n - 1 - i.val) := by
  refine ⟨x.1.val - (i.val + 1), ?_⟩
  by_cases hlast : i.val = n - 1
  · exfalso
    have hijv : i.val < x.1.val := by simpa using x.2
    have hjn : x.1.val < n := x.1.isLt
    omega
  · have hijv : i.val < x.1.val := by simpa using x.2
    have hjn : x.1.val < n := x.1.isLt
    have h1 : i.val + 1 ≤ x.1.val := by omega
    have h2 : x.1.val - (i.val + 1) < n - (i.val + 1) := (Nat.sub_lt_sub_iff_right h1).mpr hjn
    have h3 : n - (i.val + 1) = n - 1 - i.val := by omega
    simpa [h3] using h2

/-- The inverse map: an offset `k` in `Fin (n - 1 - i.val)` back to the `Fin n` position
    `k.val + (i.val + 1)`, strictly above `i`. -/
noncomputable def finToIj (n : Nat) (i : Fin n) (k : Fin (n - 1 - i.val)) : {j : Fin n // i < j} := by
  refine ⟨?_, ?_⟩
  · refine ⟨k.val + (i.val + 1), ?_⟩
    by_cases hlast : i.val = n - 1
    · exfalso
      have klt : k.val < n - 1 - i.val := k.isLt
      omega
    · have klt : k.val < n - 1 - i.val := k.isLt
      omega
  · by_cases hlast : i.val = n - 1
    · exfalso
      have klt : k.val < n - 1 - i.val := k.isLt
      omega
    · exact (by omega : i.val < k.val + (i.val + 1))

/-- The `Fin` positions strictly above a fixed `i` are in bijection with
    `Fin (n - 1 - i.val)`: `j ↦ j.val - (i.val + 1)`, inverse `k ↦ k.val + (i.val + 1)`. -/
noncomputable def aboveIEquiv (n : Nat) (i : Fin n) :
    {j : Fin n // i < j} ≃ Fin (n - 1 - i.val) :=
  ⟨fun x => ijToFin n i x, fun k => finToIj n i k,
    fun x => by
      apply Subtype.ext
      apply Fin.ext
      simp only [ijToFin, finToIj, Subtype]
      rw [Nat.sub_add_cancel (by omega : i.val + 1 ≤ x.1.val)]
      <;> simp,
    fun k => by
      apply Fin.ext
      simp only [ijToFin, finToIj, Subtype]
      rw [Nat.add_sub_cancel (k.val) (i.val + 1)]
      <;> simp⟩

/-- For a fixed `i : Fin n`, the number of positions `j` strictly above `i` is
    `n - 1 - i.val` (`Fintype.card_congr` over `aboveIEquiv`). -/
theorem innerAboveCount (n : Nat) (i : Fin n) :
    Fintype.card {j : Fin n // i < j} = n - 1 - i.val := by
  have hcard : Fintype.card {j : Fin n // i < j} = Fintype.card (Fin (n - 1 - i.val)) :=
      Fintype.card_congr (aboveIEquiv n i)
  simpa [Fintype.card_fin] using hcard

/-- For a fixed `i : Fin n`, the indicator sum over positions `j` above `i` is
    `n - 1 - i.val` (`sum_boole` / filter-card form of `innerAboveCount`). -/
theorem innerAboveSum (n : Nat) (i : Fin n) :
    (∑ j : Fin n, if i < j then 1 else 0) = n - 1 - i.val := by
  have h1 : (∑ j : Fin n, if i < j then 1 else 0) =
      (Finset.univ : Finset (Fin n)).sum (fun j => if i < j then 1 else 0) := rfl
  have h2 : (Finset.univ : Finset (Fin n)).sum (fun j => if i < j then 1 else 0) =
      Fintype.card {j : Fin n // i < j} := by
    simpa [Fintype.card_subtype] using
      (sum_boole (fun j : Fin n => i < j) (Finset.univ : Finset (Fin n))).symm
  simpa using (h1.trans h2).trans (innerAboveCount n i)

/-- The outer sum `∑ i : Fin n, (n-1-i.val)` reindexes to `∑ k in range n, k`
    (`Finset.sum_bij` over the reverse permutation `i ↦ n-1-i.val`, a bijection
    `Fin n ≃ range n`; the surjectivity witness uses `Nat.sub_sub_self`). -/
theorem outerSum_eq_rangeSum (n : Nat) :
    (∑ i : Fin n, (n - 1 - i.val)) = (Finset.range n).sum (fun k => k) := by
  have h1 : (∑ i : Fin n, (n - 1 - i.val)) =
      (Finset.univ : Finset (Fin n)).sum (fun i => (n - 1 - i.val)) := rfl
  have h2 : (Finset.univ : Finset (Fin n)).sum (fun i => (n - 1 - i.val)) =
      (Finset.range n).sum (fun k => k) := by
    apply Finset.sum_bij (i := fun a _ => n - 1 - a.val)
    · intro a _
      simp only [Finset.mem_range]
      omega
    · intro a1 _ a2 _ h
      apply Fin.ext
      omega
    · intro k hk
      have hkn : k < n := by simp [Finset.mem_range] at hk; exact hk
      have hkm : k ≤ n - 1 := by omega
      refine ⟨Fin.mk (n - 1 - k) (by omega), by simp [Finset.mem_univ], ?_⟩
      exact Nat.sub_sub_self hkm
    · intro a _
      rfl
  simpa [h1] using h2

/-- (sub-lemma 1a) Exactly `choose n 2` unordered position pairs `i < j`.
    *Assembled:* `cardIj_eq_doubleSum` (filter→double sum) + `innerAboveSum`
    (inner `Σ_j [i<j] = n-1-i.val`) + `outerSum_eq_rangeSum` (outer `Σ_i (n-1-i.val) =
    Σ_{k<n} k`) + `Finset.sum_range_id` (`Σ_{k<n} k = n*(n-1)/2`) + `Nat.choose_two_right`. -/
theorem cardIjPairs (n : Nat) : (ijPairs n).card = n.choose 2 := by
  rw [cardIj_eq_doubleSum]
  -- inner: `Σ_i Σ_j [i<j]` → `Σ_i (n-1-i.val)`, pointwise via `innerAboveSum`.
  have hInner : (∑ i : Fin n, ∑ j : Fin n, if i < j then 1 else 0) =
      (∑ i : Fin n, (n - 1 - i.val)) := by
    apply Fintype.sum_congr
    intro i
    exact innerAboveSum n i
  -- outer: `Σ_i (n-1-i.val)` → `Σ_{k<n} k` → `n*(n-1)/2` → `choose n 2`.
  rw [hInner, outerSum_eq_rangeSum, Finset.sum_range_id]
  rw [Nat.choose_two_right]

/-- For a fixed pair `(i, j)`, the arrays with `f i = f j`; there are
    `a^(n-1)` of them when `i ≠ j` and `n ≥ 2` (sub-lemma 1b: `cardPairEqSet`). -/
noncomputable def pairEqSet (n a : Nat) (i j : Fin n) : Finset (Fin n → Fin a) :=
  (univ : Finset (Fin n → Fin a)).filter fun f => decide (f i = f j)

theorem cardPairEqSet (n a : Nat) (ha : 0 < a) (i j : Fin n) (hne : i ≠ j) (hn : 1 < n) :
    (pairEqSet n a i j).card = a ^ (n - 1) := by
  have hbridge : (pairEqSet n a i j).card =
      Fintype.card {f : Fin n → Fin a // f i = f j} := by
    rw [pairEqSet]
    simpa [Fintype.card_subtype]
  calc (pairEqSet n a i j).card
      _ = Fintype.card {f : Fin n → Fin a // f i = f j} := hbridge
      _ = a ^ (n - 1) := Shufflemath.cardPairEqSet n a i j hne hn

/-- (union bound, core) the cardinality of a `biUnion` is at most the sum of the
    part cardinalities: `# (s.biUnion f) ≤ Σ x ∈ s, # (f x)`.  Induction on `s`;
    the `a ∉ s0` step uses `card_union_le` + `sum_insert`, the degenerate `a ∈ s0`
    step is a no-op. -/
theorem biUnion_card_le_sum {X : Type*} [DecidableEq X] (s : Finset X) (f : X → Finset X) :
    (s.biUnion f).card ≤ ∑ x ∈ s, (f x).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s0 _ ih =>
    by_cases ha : a ∈ s0
    · have hs : insert a s0 = s0 := by rwa [insert_eq_self]
      calc ((insert a s0).biUnion f).card
          _ = (s0.biUnion f).card := by rw [hs]
          _ ≤ ∑ x ∈ s0, (f x).card := ih
          _ = ∑ x ∈ insert a s0, (f x).card := by rw [hs]
    · calc ((insert a s0).biUnion f).card
          _ = (f a ∪ s0.biUnion f).card := by rw [biUnion_insert]
          _ ≤ (f a).card + (s0.biUnion f).card := card_union_le _ _
          _ ≤ (f a).card + ∑ x ∈ s0, (f x).card := Nat.add_le_add_left ih _
          _ = ∑ x ∈ insert a s0, (f x).card := by rw [sum_insert ha]

/-- (sub-lemma 1d, union bound) `|A| ≤ Σ |B_i|` when `A ⊆ ⋃_{i ∈ s} B i`. -/
lemma card_le_biUnion_sum {X : Type*} [DecidableEq X] (s : Finset X) (f : X → Finset X)
    (A : Finset X) (hA : A ⊆ s.biUnion f) : A.card ≤ s.sum (fun x => (f x).card) := by
  exact (Finset.card_mono hA).trans (biUnion_card_le_sum s f)

/-- **Lemma 1 of 4 (Gate 6 §4):** the collision probability of a uniform
    `[n] → Fin a` label array is at most `choose(n,2) / a`. Assembles the four
    sub-lemmas: `collisionSet ≤ ⋃ pairEqSet`, union bound, `|pairEqSet| = a^(n-1)`,
    `|ijPairs| = choose n 2`, then `choose(n,2)·a^(n-1)/a^n = choose(n,2)/a`. -/
theorem collisionProb_le (n a : Nat) (ha : 0 < a) :
    ((collisionSet n a).card : Rat) / (a ^ n : Rat) ≤ (n.choose 2 : Rat) / a := by
  -- roadmap: `hbound : collisionSet.card ≤ (ijPairs).sum (fun p => (pairEqSet _ _).card)`
  -- via `card_le_biUnion_sum` + `collisionSet_le_biUnion`; then bound that sum by
  -- `choose n 2 * a ^ (n-1)` using `cardIjPairs` + `cardPairEqSet` (each pairEqSet has
  -- `a^(n-1)` members and there are `choose n 2` pairs); finally
  -- `choose n 2 * a^(n-1) / a^n = choose n 2 / a` by `a^n = a * a^(n-1)` and Rat
  -- division. (Heavy Fintype-univ WHNF: keep each sub-lemma small; do NOT inline
  -- `collisionSet`'s filter here.)
  sorry

end _ProbeGate6Collision
end Shufflemath
