/-
General Bernoulli--Laplace exchange chains.

This file builds the general theory: the macrostate space of a
two-pile exchange with pile sizes `m` and `N - m`, symbolic row
stochasticity (double Vandermonde), the hypergeometric stationary
distribution (Vandermonde with a symmetry reindex), detailed balance,
and the exchange kernel `blExchangeKernel N m k : FiniteKernel
(BLState N m) (BLState N m)`.

Import direction (GPT review finding #3): this module does NOT import
the concrete `Shufflemath.BernoulliLaplace` Commander module. The
equality between this general theory and the Commander 99-card instance
lives in the small bridge module `Shufflemath/BernoulliLaplaceCommanderBridge`
(which imports both), so the concrete file stays untouched and no
import cycle can form.

Parameters: the state space depends only on `N m` (finding #2: `k`,
the exchange size, is a kernel parameter, not a state-space parameter —
composing or comparing different `k` kernels must live on ONE state
space). `N m k : Nat` with `0 < m < N`, `0 < k`, `k ≤ m`,
`k ≤ N - m` (the exchange size fits in both piles).

Macrostate `x` = number of original-left cards currently in the left
pile. The left pile has size `m` and the right pile size `N - m`, with
`m` original-left cards in total. Admissibility:

- `x ≤ m` (left pile size; also the total number of original-left cards);
- `m - x ≤ N - m`, i.e. `x ≥ 2*m - N` (right-pile capacity),
- `x ≥ 0`.

So the admissible range is `max (2*m - N) 0 ≤ x ≤ m`. (For the Commander
`N = 99, m = 50` this is `1 ≤ x ≤ 50`, matching `commanderLeftCount`.)
The upper bound is `m`, not `min m (N - m)`: the left pile holds `m`
cards, so all `m` original-left cards can sit in it (the segregated
state), regardless of which pile is smaller.
-/
import Shufflemath.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Shufflemath
namespace BernoulliLaplaceGeneral

variable {N m k : Nat}

/-- Lower admissible bound for the macrostate: the right pile (size
`N - m`) must be able to hold the `m - x` original-left cards that are
not in the left pile. -/
def lo (N m : Nat) : Nat := max (2 * m - N) 0

/-- Upper admissible bound for the macrostate: the left pile (size `m`). -/
def hi (_ : Nat) (m : Nat) : Nat := m

@[simp]
theorem lo_def (N m : Nat) : lo N m = max (2 * m - N) 0 := rfl

@[simp]
theorem hi_def (N m : Nat) : hi N m = m := rfl

/-- Macrostate space: the admissible counts of original-left cards in
the left pile, as a subtype of `ℕ`. Depends only on `N m` (GPT review
finding #2): the exchange size `k` is a kernel parameter, so different
`k`-kernels and compositions of them live on this one state space. -/
def BLState (N m : Nat) : Type := {x : ℕ // lo N m ≤ x ∧ x ≤ hi N m}

variable {N m k : Nat}

/-- The admissible macrostates form a finite set. -/
instance fintypeBLState (N m : Nat) : Fintype (BLState N m) :=
  Fintype.ofFinset (Finset.Icc (lo N m) (hi N m)) fun _ => Finset.mem_Icc

variable {N m k : Nat}

/-- Projection to the count. -/
abbrev stateVal (x : BLState N m) : Nat := x.val

/-- The macrostate Finset: the `Finset ℕ` of admissible counts. This is
the summation domain for row sums and the stationary total. -/
def stateFinset (N m : Nat) : Finset ℕ := Finset.Icc (lo N m) (hi N m)

variable {N m k : Nat}

/-- Hypergeometric stationary mass at macrostate `x`: the probability a
uniformly random arrangement of the `N`-card deck has exactly `x`
original-left cards in the left pile. Depends only on `N m`, like the
state space. -/
def blStationary (N m : Nat) (x : BLState N m) : Rat :=
  ((Nat.choose m x.val * Nat.choose (N - m) (m - x.val) : Nat) : Rat) /
    (Nat.choose N m : Rat)

variable {N m k : Nat}

/-- For the admissible range to be inhabited (and for the exchange to be
defined) we need `0 < m < N` and the exchange size to fit both piles. -/
structure Params where
  /-- Number of cards. -/
  N : Nat
  /-- Left pile size (number of original-left cards). -/
  m : Nat
  /-- Exchange size. -/
  k : Nat
  /-- `0 < m`. -/
  h0m : 0 < m
  /-- `m < N`. -/
  hmn : m < N
  /-- `0 < k`. -/
  hk0 : 0 < k
  /-- The exchange fits in the left pile. -/
  hkm : k ≤ m
  /-- The exchange fits in the right pile. -/
  hknm : k ≤ N - m

/-- The stationary mass is nonnegative. -/
theorem blStationary_nonneg (p : Params) (x : BLState p.N p.m) :
    0 ≤ blStationary p.N p.m x := by
  rw [blStationary]
  exact div_nonneg_iff.mpr (Or.inl ⟨Nat.cast_nonneg' _, Nat.cast_nonneg' _⟩)

/-! ## The exchange kernel

The microscopic transition law, copied from the Commander module
(`Shufflemath.BernoulliLaplace`) into the general theory (GPT review
finding #3: the general file must not import the Commander file — the
coincidence of the two copies is proved in the bridge module).
`transitionNumerator N m k x y` counts the microscopic exchanges taking
macrostate `x` to `y`: for each `a` (original-left cards leaving the left
pile) the target determines the unique `b = y - (x - a)` of original-left
cards returning from the right pile; the four binomial factors count the
ways to choose the leaving and returning cards in each pile.
-/ 

/-- Number of microscopic exchange choices taking macrostate `x` to `y`.

`x` is the number of original-left cards currently in the left pile. We
exchange `k` cards chosen uniformly from each pile. For each possible
number `a` of original-left cards leaving the left pile, the target state
determines the number `b` that must return from the right pile:

`(x - a) + b = y`.

The sum iterates over `a` only: the unique `b` is computed directly, so
each entry is `O(k)` binomial factors rather than an `O(k^2)` candidate
search. Nat subtraction is intentional and matches the state-counting
formula. -/
def transitionNumerator (N m k x y : Nat) : Nat :=
  Finset.sum (Finset.range (k + 1)) fun a =>
    let remaining := x - a
    if remaining ≤ y then
      let b := y - remaining
      if b ≤ k then
        Nat.choose x a *
          Nat.choose (m - x) (k - a) *
          Nat.choose (m - x) b *
          Nat.choose ((N - m) - (m - x)) (k - b)
      else
        0
    else
      0

/-- Number of equally likely pairs of `k`-subsets selected from the two
piles: the transition denominator. -/
def transitionDenominator (N m k : Nat) : Nat :=
  Nat.choose m k * Nat.choose (N - m) k

/-- Exact rational Bernoulli--Laplace transition probability. -/
def transitionWeight (N m k x y : Nat) : Rat :=
  (transitionNumerator N m k x y : Rat) /
    (transitionDenominator N m k : Rat)

/-! Row stochasticity: for an admissible state `x`, the transition weights
sum to `1`. The count of microscopic exchanges is a double Vandermonde:
for each `a` (original-left cards leaving the left pile) the inner sum
over `b` (original-left cards returning from the right) is
`choose (N - m) k`, and the outer sum over `a` is `choose m k`, so the
row sum equals the transition denominator, which cancels. -/

/-- The `y`-dependent summand of `transitionNumerator` for a fixed `a`,
with the guards of the definition made explicit. This is definitionally
equal to the body of `transitionNumerator` (the `a`-term): the
`let remaining := x - a` and `let b := y - remaining` bindings of the
definition are inlined here. -/
private def guardedTerm (N m k x a y : Nat) : Nat :=
  if x - a ≤ y then
    if y - (x - a) ≤ k then
      Nat.choose x a * Nat.choose (m - x) (k - a) *
        Nat.choose (m - x) (y - (x - a)) *
        Nat.choose (N - m - (m - x)) (k - (y - (x - a)))
    else 0
  else 0

/-- One microscopic-exchange term: `a` original-left cards leave the left
pile, `k - a` of the other kind leave with them; `b` original-left cards
return from the right pile, `k - b` of the other kind. The fourth factor
counts the original-right cards in the right pile
(`(N - m) - (m - x)`). -/
private def exchangeTerm (N m k x a b : Nat) : Nat :=
  Nat.choose x a * Nat.choose (m - x) (k - a) *
    Nat.choose (m - x) b * Nat.choose (N - m - (m - x)) (k - b)

/-- The term vanishes for `b > m - x`: the third factor is zero. -/
private theorem exchangeTerm_zero_above (N m k x a b : Nat) (hb : m - x < b) :
    exchangeTerm N m k x a b = 0 := by
  rw [exchangeTerm, Nat.choose_eq_zero_of_lt hb, mul_zero, zero_mul]

/-- `lo N m` is just `2*m - N` (Nat subtraction already floors at zero).
-/ 
private theorem lo_eq_tsub (N m : Nat) : lo N m = 2 * m - N := by
  rw [lo_def, max_zero]

/-- The transition count vanishes for `y` below the admissible window:
every microscopic-exchange term is zero. For `a ≤ x` the target
`b = y - (x - a)` either exceeds the exchange size (the guard fails) or,
when the guards pass, lands in a fourth binomial factor that the right
pile cannot supply: the right pile holds `(N - m) - (m - x)`
original-right cards, but the exchange would draw `k - b` of them, which
exceeds the supply since `y < 2*m - N ≤ x` (the `2*m ≤ N` case is
vacuous: then `lo = 0` and `y < 0` is impossible). For `a > x` the first
factor `choose x a` is zero. -/
private theorem num_zero_below_lo (p : Params) (x y : Nat) (hx : x ≤ p.m)
    (hlo : lo p.N p.m ≤ x) (hy : y < lo p.N p.m) (_hym : y ≤ p.m) :
    transitionNumerator p.N p.m p.k x y = 0 := by
  rw [lo_eq_tsub] at hy hlo
  by_cases h2m : 2 * p.m ≤ p.N
  · -- `2*m ≤ N`: `lo = 0`, so `hy : y < 0` is impossible.
    exfalso
    rw [Nat.sub_eq_zero_of_le h2m] at hy
    exact Nat.not_lt_zero y hy
  · -- `2*m > N`: `lo = 2*m - N`; the subtractions in the choose
    -- arguments below are true (their minuends dominate).
    have hNlt : p.N < 2 * p.m := Nat.not_le.mp h2m
    have hy' : y + 1 ≤ 2 * p.m - p.N := Nat.succ_le_of_lt hy
    have hlo' : 2 * p.m - p.N ≤ x := hlo
    have hmn := p.hmn
    rw [transitionNumerator]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_range] at ha
    have hka : a ≤ p.k := by omega
    by_cases hax : a ≤ x
    · by_cases hguard : x - a ≤ y
      · by_cases hbk : y - (x - a) ≤ p.k
        · -- All guards hold: the fourth factor is zero.
          -- Core bound, in sum form (no subtraction): from
          -- `y + 1 ≤ 2*m - N` (add `N` to both sides) and
          -- `a ≤ k` (add the two inequalities).
          have h9N : p.N + 1 + y + a ≤ 2 * p.m + p.k := by omega
          -- In the genuine-subtraction region this is
          -- `N - m - (m - x) < k - (y - (x - a))`: the fourth
          -- binomial factor would draw more original-right cards
          -- than the right pile holds.
          have h4n : p.N - p.m - (p.m - x) < p.k - (y - (x - a)) := by
            omega
          have h4' : Nat.choose (p.N - p.m - (p.m - x))
            (p.k - (y - (x - a))) = 0 := Nat.choose_eq_zero_of_lt h4n
          change guardedTerm p.N p.m p.k x a y = 0
          simp only [guardedTerm]
          rw [ite_eq_left hguard, ite_eq_left hbk, h4', mul_zero]
        · -- The guard on `b` fails.
          change guardedTerm p.N p.m p.k x a y = 0
          simp only [guardedTerm]
          rw [ite_eq_left hguard, ite_eq_right hbk]
      · -- The first guard fails.
        change guardedTerm p.N p.m p.k x a y = 0
        simp only [guardedTerm]
        rw [ite_eq_right hguard]
    · -- `a > x`: the first factor `choose x a` is zero.
      have hx' : x < a := Nat.lt_of_not_ge hax
      have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt hx'
      change guardedTerm p.N p.m p.k x a y = 0
      simp only [guardedTerm]
      rw [ite_eq_left (by omega)]
      split_ifs with _
      · simp only [h0, zero_mul]
      · rfl


/-- Inner reindexing: for fixed `a` with `a ≤ k`, the `y`-sum of the
guarded exchange term over `y < m + 1` equals the unguarded `b`-sum over
`b < k + 1`, where `b = y - (x - a)` is the number of original-left cards
returning from the right pile. The support of the LHS is
`y ∈ [x - a, x - a + k]` with `y - (x - a) ≤ m - x` (below the window or
beyond the exchange size the guards fail; within the window the third
factor `choose (m - x) b` kills the term for `b > m - x`). That support
is in bijection, via `b = y - (x - a)`, with the support of the RHS,
`b ∈ [0, min (k, m - x)]`. -/
private theorem innerYToB (N m k x a : Nat) (hm : x ≤ m) (_ha : a ≤ k) :
    (∑ y ∈ Finset.range (m + 1), guardedTerm N m k x a y) =
    ∑ b ∈ Finset.range (k + 1), exchangeTerm N m k x a b := by
  by_cases hax : a ≤ x
  · -- `x - a` is a true subtraction.
    set As := (Finset.range (m + 1)).filter
      (fun y => x - a ≤ y ∧ y ≤ x - a + k ∧ y - (x - a) ≤ m - x) with hAs
    set Bs := (Finset.range (k + 1)).filter (fun b => b ≤ m - x) with hBs
    have hGzero : ∀ y, y ∉ As → guardedTerm N m k x a y = 0 := by
      simp only [guardedTerm]
      intro y hy
      by_cases h1 : x - a ≤ y
      · by_cases h2 : y ≤ x - a + k
        · by_cases h3 : y - (x - a) ≤ m - x
          · -- All four conjuncts hold: `y` is in the window `As`.
            have hsum : (x - a) + (y - (x - a)) = y := by
              rw [Nat.add_comm, Nat.sub_add_cancel h1]
            have hsubk : y - (x - a) ≤ k :=
              (Nat.add_le_add_iff_left (n := x - a)).mp (by
                rw [hsum]
                exact h2)
            have hym : y ≤ m := by
              calc
                y = (x - a) + (y - (x - a)) := hsum.symm
                _ ≤ (x - a) + (m - x) := Nat.add_le_add_left h3 (x - a)
                _ ≤ x + (m - x) := Nat.add_le_add_right (Nat.sub_le x a) (m - x)
                _ = m := by rw [Nat.add_comm]; exact Nat.sub_add_cancel hm
            have hmem : y ∈ As := by
              simp only [hAs, Finset.mem_filter, Finset.mem_range]
              exact ⟨Nat.lt_succ_of_le hym, h1, h2, h3⟩
            contradiction
          · -- `b ≤ k` but `b > m - x`: the third factor is zero.
            by_cases h4 : y - (x - a) ≤ k
            · rw [ite_eq_left h1, ite_eq_left h4]
              change exchangeTerm N m k x a (y - (x - a)) = 0
              exact exchangeTerm_zero_above N m k x a (y - (x - a)) (by
                by_contra h5
                exact h3 (Nat.le_of_not_lt h5))
            · rw [ite_eq_left h1, ite_eq_right h4]
        · -- `y > x - a + k`: then `b = y - (x - a) > k`.
          by_cases h4 : y - (x - a) ≤ k
          · exfalso
            have hsum : (x - a) + (y - (x - a)) = y := by
              rw [Nat.add_comm, Nat.sub_add_cancel h1]
            have hsum2 : y ≤ x - a + k := by
              rw [← hsum]
              exact Nat.add_le_add_left h4 (x - a)
            exact h2 hsum2
          · rw [ite_eq_left h1, ite_eq_right h4]
      · -- `y < x - a`: the first guard fails.
        rw [ite_eq_right h1]
    have hAsupp : (∑ y ∈ Finset.range (m + 1), guardedTerm N m k x a y) =
        (∑ y ∈ As, guardedTerm N m k x a y) := by
      rw [← Finset.sum_sdiff (fun (y : ℕ) (hy : y ∈ As) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (y : ℕ) (hy : y ∈ Finset.range (m + 1) \ As) => by
        simp only [Finset.mem_sdiff, hAs, Finset.mem_filter, Finset.mem_range] at hy
        have hnot : y ∉ As := by
          intro hin
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hin
          exact hy.2 hin
        exact hGzero y hnot]
      rw [zero_add]
    have hφ : (∑ y ∈ As, guardedTerm N m k x a y) =
        (∑ b ∈ Bs, exchangeTerm N m k x a b) := by
      apply Finset.sum_bij (fun y _ => y - (x - a))
      · -- image in Bs
        intro y hy
        simp only [hAs, hBs, Finset.mem_filter, Finset.mem_range] at hy ⊢
        rcases hy with ⟨_, h1, h2, h3⟩
        refine ⟨?_, h3⟩
        · omega
      · -- injective
        intro y1 hy1 y2 hy2 h12
        have h1 : x - a ≤ y1 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy1
          exact hy1.2.1
        have h2 : x - a ≤ y2 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy2
          exact hy2.2.1
        omega
      · -- surjective onto Bs
        intro b hb
        simp only [hBs, hAs, Finset.mem_filter, Finset.mem_range] at hb ⊢
        rcases hb with ⟨hbr, hb2⟩
        exact ⟨x - a + b, by
          -- The goal is `(y < m+1 ∧ (p1 ∧ (p2 ∧ p3))) ∧ (y - (x-a) = b)`:
          -- the membership conjunction and the equation are the two top
          -- level conjuncts of the `∃ y ∈ Bs, ...` desugaring.
          refine ⟨⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩, ?_⟩
          · -- x - a + b < m + 1
            omega
          · -- x - a ≤ x - a + b
            omega
          · -- x - a + b ≤ x - a + k
            omega
          · -- (x - a + b) - (x - a) ≤ m - x
            omega
          · -- (x - a + b) - (x - a) = b
            omega
        ⟩
      · -- equality of terms
        intro y hy
        simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy
        have h4 : y - (x - a) ≤ k :=
          (Nat.sub_le_iff_le_add (a := y) (b := x - a) (c := k)).mpr
            (by simpa only [Nat.add_comm] using hy.2.2.1)
        change guardedTerm N m k x a y = exchangeTerm N m k x a (y - (x - a))
        simp only [guardedTerm, exchangeTerm]
        rw [ite_eq_left hy.2.1, ite_eq_left h4]
    have hTsupp : (∑ b ∈ Bs, exchangeTerm N m k x a b) =
        (∑ b ∈ Finset.range (k + 1), exchangeTerm N m k x a b) := by
      rw [← Finset.sum_sdiff (s₁ := Bs) (s₂ := Finset.range (k + 1))
          (h := fun (y : ℕ) (hy : y ∈ Bs) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (b : ℕ) (hb : b ∈ Finset.range (k + 1) \ Bs) => by
        simp only [Finset.mem_sdiff, hBs, Finset.mem_filter, Finset.mem_range] at hb
        by_cases h5 : b ≤ m - x
        · -- then `b ∈ Bs`, contradicting `hb.2`
          exact False.elim (hb.2 ⟨hb.1, h5⟩)
        · -- `b > m - x`: the third factor is zero
          have h5' : m - x < b := by
            by_contra h6
            exact h5 (Nat.le_of_not_lt h6)
          exact exchangeTerm_zero_above N m k x a b h5']
      rw [zero_add]
    calc
      _ = ∑ y ∈ As, guardedTerm N m k x a y := hAsupp
      _ = ∑ b ∈ Bs, exchangeTerm N m k x a b := hφ
      _ = ∑ b ∈ Finset.range (k + 1), exchangeTerm N m k x a b := hTsupp
  · -- `a > x`: every term carries `choose x a = 0`.
    have hx : x < a := Nat.lt_of_not_ge hax
    have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt hx
    have hL : (∑ y ∈ Finset.range (m + 1), guardedTerm N m k x a y) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      change guardedTerm N m k x a y = 0
      simp only [guardedTerm]
      rw [ite_eq_left (by omega)]
      split_ifs with _
      · simp only [h0, zero_mul]
      · rfl
    have hR : (∑ b ∈ Finset.range (k + 1), exchangeTerm N m k x a b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp only [exchangeTerm, h0, zero_mul]
    rw [hL, hR.symm]

/-- Vandermonde's identity in `range` form:
`∑ b < k + 1, choose M b * choose L (k - b) = choose (M + L) k`. -/
private theorem vandermondeRange (M L k : Nat) : (∑ b ∈ Finset.range (k + 1),
    Nat.choose M b * Nat.choose L (k - b)) =
    Nat.choose (M + L) k := by
  rw [Nat.add_choose_eq M L k]
  change ∑ b ∈ Finset.range (k + 1), Nat.choose M b * Nat.choose L (k - b) =
    ∑ ij ∈ Finset.antidiagonal k, (fun i j => Nat.choose M i * Nat.choose L j) ij.1 ij.2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    Nat.choose M i * Nat.choose L j) k]

/-- Symbolic row stochasticity: the exact transition weights in an
admissible row sum to `1`. -/
theorem blRowStochastic (p : Params) (x : BLState p.N p.m) :
    (∑ y ∈ stateFinset p.N p.m,
      (transitionNumerator p.N p.m p.k x.val y : Rat) /
      (transitionDenominator p.N p.m p.k : Rat)) = 1 := by
  have hx : x.val ≤ p.m := x.2.2
  have hlo : lo p.N p.m ≤ x.val := x.2.1
  have hden : 0 < transitionDenominator p.N p.m p.k := by
    rw [transitionDenominator]
    exact Nat.mul_pos (Nat.choose_pos p.hkm) (Nat.choose_pos p.hknm)
  -- Step 1: the sum of ratios is the ratio of sums (Rat is a field).
  have hsumdiv :
      (∑ y ∈ stateFinset p.N p.m,
        (transitionNumerator p.N p.m p.k x.val y : Rat) /
        (transitionDenominator p.N p.m p.k : Rat)) =
      (∑ y ∈ stateFinset p.N p.m,
        (transitionNumerator p.N p.m p.k x.val y : Rat)) /
      (transitionDenominator p.N p.m p.k : Rat) := by
    rw [← Finset.sum_div]
  -- Step 2: extend the summation domain to `y < m + 1`; the count is
  -- zero below the admissible window.
  have hsub : stateFinset p.N p.m ⊆ Finset.range (p.m + 1) := by
    intro y hy
    simp only [stateFinset, lo_def, hi_def, Finset.mem_Icc, Finset.mem_range] at hy ⊢
    omega
  have hzero : (∑ y ∈ Finset.range (p.m + 1) \ stateFinset p.N p.m,
      (transitionNumerator p.N p.m p.k x.val y : Rat)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Finset.mem_sdiff, stateFinset, Finset.mem_Icc, Finset.mem_range] at hy
    have hy1 : y < p.m + 1 := hy.1
    by_cases hyl : y < lo p.N p.m
    · -- below the window: the count is zero there.
      have hym : y ≤ p.m := by omega
      simpa using num_zero_below_lo p x.val y hx hlo hyl hym
    · -- `y ≥ lo` and `y ≤ m` put `y` in the window, contradicting
      -- its membership in the difference.
      have hle : lo p.N p.m ≤ y := Nat.le_of_not_lt hyl
      have hym : y ≤ p.m := by omega
      have hmem : lo p.N p.m ≤ y ∧ y ≤ hi p.N p.m := by
        simpa only [hi_def] using ⟨hle, hym⟩
      exact False.elim (hy.2 hmem)
  have hext : (∑ y ∈ stateFinset p.N p.m,
      (transitionNumerator p.N p.m p.k x.val y : Rat)) =
      (∑ y ∈ Finset.range (p.m + 1),
        (transitionNumerator p.N p.m p.k x.val y : Rat)) := by
    rw [← Finset.sum_sdiff hsub]
    rw [hzero, zero_add]
  rw [hsumdiv, hext]
  -- Step 3: the count row sum over `y < m + 1` is the transition
  -- denominator (double Vandermonde).
  have hinner : ∀ a, a ∈ Finset.range (p.k + 1) →
      (∑ y ∈ Finset.range (p.m + 1), guardedTerm p.N p.m p.k x.val a y) =
      (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.k x.val a b) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    exact innerYToB p.N p.m p.k x.val a hx (by omega)
  have hfac : ∀ a, (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.k x.val a b) =
      (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a)) *
      (∑ b ∈ Finset.range (p.k + 1),
        Nat.choose (p.m - x.val) b *
          Nat.choose (p.N - p.m - (p.m - x.val)) (p.k - b)) := by
    intro a
    have h1 : (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.k x.val a b) =
        (∑ b ∈ Finset.range (p.k + 1),
          (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a)) *
            (Nat.choose (p.m - x.val) b *
              Nat.choose (p.N - p.m - (p.m - x.val)) (p.k - b))) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [exchangeTerm]
      ring
    rw [h1, ← Finset.mul_sum]
  have hsubwin : p.m - x.val ≤ p.N - p.m := by
    -- `m - x ≤ N - m`, in both cases of `2*m` vs `N`.
    have hlo2 : 2 * p.m - p.N ≤ x.val := by
      simpa [lo_eq_tsub] using hlo
    have hmn := p.hmn
    by_cases h2m : 2 * p.m ≤ p.N
    · -- `2*m ≤ N`: `x ≤ m` and `m < N` give `m - x ≤ N - m`.
      omega
    · -- `2*m > N`: `2*m - N ≤ x ≤ m` implies `m - x ≤ N - m`.
      have hNlt : p.N < 2 * p.m := Nat.not_le.mp h2m
      omega

  have hdouble : (∑ y ∈ Finset.range (p.m + 1),
      transitionNumerator p.N p.m p.k x.val y) =
      transitionDenominator p.N p.m p.k := by
    -- The `let`/`ite` body of `transitionNumerator` is definitionally the
    -- let-free `guardedTerm`; `change` bridges what `rw` cannot.
    change (∑ y ∈ Finset.range (p.m + 1),
        (∑ a ∈ Finset.range (p.k + 1), guardedTerm p.N p.m p.k x.val a y)) =
      transitionDenominator p.N p.m p.k
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a ha => hinner a ha)]
    rw [Finset.sum_congr rfl (fun a _ => hfac a)]
    rw [← Finset.sum_mul]
    rw [vandermondeRange x.val (p.m - x.val) p.k]
    rw [show (x.val + (p.m - x.val)) = p.m from by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hx]
    rw [vandermondeRange (p.m - x.val) (p.N - p.m - (p.m - x.val)) p.k]
    rw [show (p.m - x.val) + (p.N - p.m - (p.m - x.val)) = p.N - p.m from by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hsubwin]
    rw [transitionDenominator]
  -- Lift the Nat sum to Rat and cancel.
  rw [← Nat.cast_sum]
  rw [hdouble]
  exact div_self (by positivity)

end BernoulliLaplaceGeneral
end Shufflemath
