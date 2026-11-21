module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic
public import Shufflemath.FiniteDeck.Gate6FiniteGSR

@[expose] public section

namespace Shufflemath

open Finset

/-!
## Gate 6 — the bad-label event as a union of pair-equality events

The **canonical** bad event for the Gate 6 §4 collision coupling
(`docs/planning/proof-strategies/2026-11-21-gate6-nonobvious-proof-hints.md`
§1): the set of label arrays `ell : Fin n → Fin a` in which *some* ordered
pair of positions `i < j` shares a label,

```
badLabels n a = ⋃_{p ∈ ijPairs n} pairEqSet n a p.1 p.2
```

is defined **as** that union — not as the `Bool`-valued
`collision : Fin n → Fin a → Bool` / `Finset.Nonempty` predicate of the
historical notebook `Shufflemath._ProbeGate6Collision`.  Because the event
*is* the union, its cardinality bound starts from `card_biUnion_le`
(two-type union bound) directly, with no `decide`-filtered `Nonempty`
predicate to WHNF-normalize (the wall that blocked the Bool route).

Contents:

* `cardFnFinA` — `|Fin n → Fin a| = a^n` (the uniform label space).
* `ijPairs`, `pairEqSet` — the ordered-pair index set and the per-pair
  equal-label sets (plain `Prop` predicates, no `decide` wrappers).
* `cardIjPairs` — `|ijPairs n| = choose n 2` (the moved sub-lemma chain
  `cardIj_eq_doubleSum`, `aboveIEquiv`, `innerAboveCount`, `innerAboveSum`,
  `outerSum_eq_rangeSum`).
* `badLabels_card_le` — the finite union bound
  `|badLabels n a| ≤ choose(n,2) · a^(n-1)` (no `n ≥ 2` branch: the index
  set is empty for `n < 2`).
* `badLabels_uniform_bound` — the headline probability bound
  `|badLabels n a| / a^n ≤ choose(n,2) / a` for all `n` and `a > 0`.
* `not_mem_badLabels_iff_injective` — `ell ∉ badLabels n a ↔ ell` is
  injective (the bridge to the collision-free coupling of §2–§3).
-/

/-- The label-array space `[n] → (alphabet of size a)` has `a^n` points: one
    i.i.d. uniform choice per position. -/
theorem cardFnFinA (n a : Nat) : Fintype.card (Fin n → Fin a) = a ^ n := by
  simp [Fintype.card_fin, Finset.prod_const]

/-- The ordered position pairs `i < j` in `[n]`.  (Plain `Prop` predicate —
    no `decide` wrapper, so nothing Bool-valued sits in the filter. -/
noncomputable def ijPairs (n : Nat) : Finset (Fin n × Fin n) :=
  (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)

/-- (sub-lemma 1a, helper) The `i < j` pairs are counted by the double sum
    `Σ_i Σ_j [i < j]`. Two standard reindexing steps: (1) `sum_boole`
    (`∑ x ∈ s, [p x] = # {x ∈ s | p x} = (s.filter p).card`) turns the filter
    cardinality into an indicator sum over `univ (Fin n × Fin n)`; (2)
    `Fintype.sum_prod_type'` (`∑ x : α×β, f x.1 x.2 = ∑ x, ∑ y, f x y`)
    collapses the product-type sum into the nested `Σ_i Σ_j`. -/
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
    Assembled from `cardIj_eq_doubleSum` + `innerAboveSum` + `outerSum_eq_rangeSum`
    + `Finset.sum_range_id` + `Nat.choose_two_right`. -/
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

/-- For a fixed pair `(i, j)`, the arrays with `f i = f j` (a plain `Prop`
    filter; there are `a^(n-1)` of them when `i ≠ j`, `n ≥ 2` — see
    `Shufflemath.cardPairEqSet` in `Gate6FiniteGSR`). -/
noncomputable def pairEqSet (n a : Nat) (i j : Fin n) : Finset (Fin n → Fin a) :=
  (univ : Finset (Fin n → Fin a)).filter (fun f => f i = f j)

/-- **The canonical Gate 6 bad-label event**: the arrays in which *some*
    ordered pair `i < j` of positions shares a label — defined **as** the union
    of the per-pair equal-label sets.  Exactly the non-injective arrays; but
    for the probability bound only the union form is needed. -/
noncomputable def badLabels (n a : Nat) : Finset (Fin n → Fin a) :=
  (ijPairs n).biUnion (fun p => pairEqSet n a p.1 p.2)

/-- **Gate 6 §1 (cardinal bound).**  `|badLabels n a| ≤ choose(n,2) · a^(n-1)`
    for all `n` and `a > 0`.  The two-type union bound `card_biUnion_le`
    (Mathlib) gives `|⋃ B_p| ≤ Σ_p |B_p|`; each `B_p` has `a^(n-1)` members
    (`cardPairEqSet`, since `p.1 < p.2` implies `p.1 ≠ p.2` and `1 < n`), and
    there are `choose n 2` pairs (`cardIjPairs`).  No `n ≥ 2` branch is
    needed: for `n < 2` the index set is empty, so both sides are `0`. -/
theorem badLabels_card_le (n a : Nat) (ha : 0 < a) :
    (badLabels n a).card ≤ (n.choose 2) * a ^ (n - 1) := by
  -- (1) union bound: |⋃ B_p| ≤ Σ_p |B_p|
  have h1 : (badLabels n a).card ≤ (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) := by
    rw [badLabels]
    exact card_biUnion_le (s := ijPairs n)
  -- (2) each B_p has a^(n-1) members: `p ∈ ijPairs n` gives `p.1 < p.2`,
  --     hence `p.1 ≠ p.2` and `1 < n`.  (No `fun` lambda may appear in a calc
  --     step, so the reindexing is a chain of `have`s.)
  have h2 : (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) =
      (ijPairs n).sum (fun _ => a ^ (n - 1)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hlt : p.1 < p.2 := by
      simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    have h2n : 1 < n := by
      have hv1 : p.1.val < p.2.val := by simpa using hlt
      have hv2 : p.2.val < n := p.2.isLt
      omega
    calc (pairEqSet n a p.1 p.2).card
        _ = Fintype.card {f : Fin n → Fin a // f p.1 = f p.2} := by
          rw [pairEqSet]
          simpa [Fintype.card_subtype]
        _ = a ^ (n - 1) := cardPairEqSet n a p.1 p.2 hne h2n
  -- (3) constant-sum collapses to |ijPairs| · a^(n-1); (4) |ijPairs| = choose n 2.
  have h3 : (ijPairs n).sum (fun _ => a ^ (n - 1)) = (ijPairs n).card * a ^ (n - 1) := by
    simpa [Nat.nsmul_eq_mul] using Finset.sum_const (ijPairs n) (a ^ (n - 1))
  have h4 : (ijPairs n).card * a ^ (n - 1) = (n.choose 2) * a ^ (n - 1) := by
    rw [cardIjPairs n]
  exact le_trans h1 (le_of_eq (Eq.trans (Eq.trans h2 h3) h4))

/-- **Gate 6 §1 (headline probability bound).**  A uniform random label array
    `ell : Fin n → Fin a` (`a > 0`) falls in `badLabels` with probability at
    most `choose(n,2) / a`, for **all** `n` (the `n = 0` case is vacuous: the
    index set is empty).  Proof: `|badLabels| ≤ choose(n,2)·a^(n-1)`
    (`badLabels_card_le`), then `choose(n,2)·a^(n-1)/a^n = choose(n,2)/a` for
    `n ≥ 1` (since `a^n = a·a^(n-1)`); the `n = 0` case is `0 ≤ 0`. -/
theorem badLabels_uniform_bound (n a : Nat) (ha : 0 < a) :
    ((badLabels n a).card : Rat) / (a ^ n : Rat) ≤ (n.choose 2 : Rat) / a := by
  by_cases hn0 : n = 0
  · -- n = 0: `badLabels 0 a = ∅`, so both sides are `0`.
    subst n
    have hI : (ijPairs 0).card = 0 := by
      rw [cardIjPairs 0]
      norm_num
    have hE : ijPairs 0 = (∅ : Finset (Fin 0 × Fin 0)) := Finset.card_eq_zero.1 hI
    have hB : (badLabels 0 a).card = 0 := by
      rw [badLabels, hE]
      simp
    have hL : ((badLabels 0 a).card : Rat) / (a ^ 0 : Rat) = 0 := by
      simp [hB, Nat.cast_zero, pow_zero, zero_div]
    have hR : (Nat.choose 0 2 : Rat) / a = 0 := by
      rw [show (Nat.choose 0 2 : Rat) = 0 from by norm_num, zero_div]
    rw [hL, hR]
    -- (closes: the remaining `0 ≤ 0` goal is trivial for Rat)
  · -- n ≥ 1
    have hcard : (badLabels n a).card ≤ (n.choose 2) * a ^ (n - 1) :=
        badLabels_card_le n a ha
    have hpow : (a ^ n : Rat) = (a ^ (n - 1) : Rat) * (a : Rat) := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv in (a ^ n : Rat) => rw [hn1]
      rw [pow_succ]
    calc ((badLabels n a).card : Rat) / (a ^ n : Rat)
        _ ≤ ((n.choose 2) * a ^ (n - 1) : Rat) / (a ^ n : Rat) := by
          gcongr
          -- side goal: `↑#bad ≤ ↑(choose n 2) * ↑a ^ (n-1)`.  Rebuild the RHS
          -- as a single cast of the Nat product (`Nat.cast_mul`/`Nat.cast_pow`
          -- over an *explicit* `↑`), uncast both sides (`Nat.cast_le`),
          -- recover `hcard`.
          have hR : (↑((n.choose 2) * a ^ (n - 1)) : Rat) =
                  (n.choose 2 : Rat) * (a : Rat) ^ (n - 1) := by
            simp [Nat.cast_mul, Nat.cast_pow]
          rw [← hR]
          rw [Nat.cast_le]
          exact hcard
        _ = (n.choose 2 : Rat) / a := by
          rw [hpow]
          have hapos : 0 < (a : Rat) := Nat.cast_pos.mpr ha
          have hnpos : 0 < (a ^ (n - 1) : Rat) := by
            exact pow_pos (Nat.cast_pos.mpr ha) (n - 1)
          field_simp [hapos, hnpos]

/-- **Gate 6 §1 (bridge to the coupling).**  `ell` is outside the bad-label
    event exactly when it is injective.  Non-injective gives a (possibly
    unordered) equal-label pair; sort it to `i < j` to land in the union.
    Conversely a union member gives `i < j` with equal labels, contradicting
    injectivity.  Only the single pair is touched — no giant `Nonempty`
    predicate, no Bool WHNF. -/
theorem not_mem_badLabels_iff_injective {n a : Nat} (ell : Fin n → Fin a) :
    ell ∉ badLabels n a ↔ Function.Injective ell := by
  constructor
  · -- ∉ badLabels → injective
    intro hnon
    by_contra h
    obtain ⟨i, j, heq, hneij⟩ := (Function.not_injective_iff.mp h)
    by_cases hlt : i < j
    · have hmem : ell ∈ badLabels n a := by
        refine Finset.mem_biUnion.2 ⟨⟨i, j⟩, ?_, ?_⟩
        · simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hlt
        · simp only [pairEqSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact heq
      exact hnon hmem
    · -- i ≠ j and not (i < j), so j < i
      have hjlt : j < i := by
        by_contra hj
        have h1 : i ≤ j := by simpa using hj
        have h2 : j ≤ i := by simpa using hlt
        exact hneij (le_antisymm h1 h2)
      have hmem : ell ∈ badLabels n a := by
        refine Finset.mem_biUnion.2 ⟨⟨j, i⟩, ?_, ?_⟩
        · simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hjlt
        · simp only [pairEqSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact heq.symm
      exact hnon hmem
  · -- injective → ∉ badLabels
    intro h
    by_contra hnon
    obtain ⟨p, hp1, hp2⟩ := Finset.mem_biUnion.1 hnon
    simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp1
    simp only [pairEqSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp2
    have hne : p.1 ≠ p.2 := ne_of_lt hp1
    exact hne (h hp2)

end Shufflemath
end
