/-
General Bernoulli--Laplace exchange chains.

This file builds the general theory: the macrostate space of a two-pile
exchange with `r` marked ("special") cards, symbolic row stochasticity
(double Vandermonde), the hypergeometric stationary law, and the exchange
kernel `blExchangeKernel : FiniteKernel (BLState N m r) (BLState N m r)`.
Detailed balance and stationarity of that kernel are proved in the
companion module `Shufflemath/BernoulliLaplaceFiber` (the microscopic
fiber counting; kept out of this file so the general theory stays
readable).

Import direction (GPT review finding #3): this module does NOT import the
concrete `Shufflemath.BernoulliLaplace` Commander module. The equality
between this general theory and the Commander 99-card instance lives in
the small bridge module `Shufflemath/BernoulliLaplaceCommanderBridge`
(which imports both), so the concrete file stays untouched and no import
cycle can form.

Parameters (GPT review finding #2): the state space depends on `N m r`
— deck size, left-pile size, total number of special cards — and NOT on
`k`, the exchange size: composing or comparing different `k` kernels
must live on ONE state space. The admissibility structure
`ExchangeAdmissible N m r k` carries the bounds: `0 < m < N`, `r ≤ N`,
`0 < k`, and `k` fits in both piles (`k ≤ m`, `k ≤ N - m`).

Macrostate `x` = number of special cards currently in the left pile.
The left pile has size `m`, the right pile size `N - m`, and the deck
holds `r` special cards in total. Admissibility:

- `x ≤ m` and `x ≤ r` (left-pile size; special-card supply),
- `r - x ≤ N - m`, i.e. `x ≥ r - (N - m)` (right-pile capacity for the
  special cards),
- `x ≥ 0`.

So the admissible range is `max (r - (N - m)) 0 ≤ x ≤ min m r`. (For the
Commander `N = 99, m = 50, r = 50` this is `1 ≤ x ≤ 50`, matching
`commanderLeftCount`.) The upper bound is `min m r`, not `m`: the left
pile holds at most `m` cards, and the deck holds at most `r` special
cards.
-/
import Shufflemath.Finite
import Shufflemath.Markov
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Shufflemath
namespace BernoulliLaplaceGeneral

variable {N m r k : Nat}

/-- Lower admissible bound for the macrostate: the right pile (size
`N - m`) must be able to hold the `r - x` special cards that are not in
the left pile. -/
def blLo (N m r : Nat) : Nat := max (r - (N - m)) 0

/-- Upper admissible bound for the macrostate: the left pile holds at
most `m` cards, and the deck holds at most `r` special cards. -/
def blHi (_ m r : Nat) : Nat := min m r

@[simp]
theorem blLo_def (N m r : Nat) : blLo N m r = max (r - (N - m)) 0 := rfl

@[simp]
theorem blHi_def (N m r : Nat) : blHi N m r = min m r := rfl

/-- Macrostate space: the admissible counts of special cards in the
left pile, as a subtype of `ℕ`. Depends on `N m r` (GPT review finding
#2): the exchange size `k` is a kernel parameter, so different `k`
kernels and compositions of them live on this one state space. -/
def BLState (N m r : Nat) : Type := {x : ℕ // blLo N m r ≤ x ∧ x ≤ blHi N m r}

variable {N m r k : Nat}

/-- The admissible macrostates form a finite set. -/
instance fintypeBLState (N m r : Nat) : Fintype (BLState N m r) :=
  Fintype.ofFinset (Finset.Icc (blLo N m r) (blHi N m r)) fun _ => Finset.mem_Icc

/-- Macrostates are decidable-equal: the subtype lives over `Nat`, and
`Subtype.ext` reduces equality to equality of the counts. -/
instance decidableEqBLState {N m r : Nat} : DecidableEq (BLState N m r) :=
  fun x y =>
    if h : x.val = y.val then isTrue (Subtype.ext h)
    else isFalse (fun heq => h (congrArg (fun (t : BLState N m r) => t.val) heq))

variable {N m r k : Nat}

/-- Projection to the count. -/
abbrev stateVal (x : BLState N m r) : Nat := x.val

variable {N m r k : Nat}

/-- The macrostate Finset: the `Finset ℕ` of admissible counts. This is
the summation domain for row sums and the stationary total. -/
def stateFinset (N m r : Nat) : Finset ℕ := Finset.Icc (blLo N m r) (blHi N m r)

variable {N m r k : Nat}

/-- Hypergeometric stationary mass at macrostate `x`: the probability a
uniformly random choice of the left pile (an `m`-subset of the `N`-card
deck) contains exactly `x` of the `r` special cards. Depends only on
`N m r`, like the state space. -/
def blStationary (N m r : Nat) (x : BLState N m r) : Rat :=
  ((Nat.choose r x.val * Nat.choose (N - r) (m - x.val) : Nat) : Rat) /
    (Nat.choose N m : Rat)

variable {N m r k : Nat}

/-- Admissibility of a two-pile exchange: deck of `N` cards, left pile
of size `m`, right pile of size `N - m`, `r` special cards in the deck,
exchanging `k` cards between the piles. The exchange fits in both piles.
(From `0 < k`, `k ≤ m`, `k ≤ N - m` one also gets `0 < m < N`.) -/
structure ExchangeAdmissible where
  /-- Number of cards. -/
  N : Nat
  /-- Left pile size. -/
  m : Nat
  /-- Total number of special cards in the deck. -/
  r : Nat
  /-- Exchange size. -/
  k : Nat
  /-- `0 < m`. -/
  h0m : 0 < m
  /-- `m < N` (the right pile is nonempty). -/
  hmn : m < N
  /-- The deck holds the `r` special cards. -/
  hrN : r ≤ N
  /-- `0 < k`. -/
  hk0 : 0 < k
  /-- The exchange fits in the left pile. -/
  hkm : k ≤ m
  /-- The exchange fits in the right pile. -/
  hknm : k ≤ N - m

variable {N m r k : Nat}

/-- The stationary mass is nonnegative. -/
theorem blStationary_nonneg (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    0 ≤ blStationary p.N p.m p.r x := by
  rw [blStationary]
  exact div_nonneg_iff.mpr (Or.inl ⟨Nat.cast_nonneg' _, Nat.cast_nonneg' _⟩)

/-! ## The exchange kernel

The microscopic transition law (the same one the Commander module uses
for its 50/49 split; the coincidence of the two copies is proved in the
bridge module). `transitionNumerator N m r k x y` counts the
microscopic exchanges taking macrostate `x` to `y`: for each `a`
(special cards leaving the left pile) the target determines the unique
`b = y - (x - a)` of special cards returning from the right pile; the
four binomial factors count the ways to choose the leaving and
returning cards in each pile.
-/

/-- Number of microscopic exchange choices taking macrostate `x` to `y`.

`x` is the number of special cards currently in the left pile. We
exchange `k` cards chosen uniformly from each pile. For each possible
number `a` of special cards leaving the left pile, the target state
determines the number `b` that must return from the right pile:

`(x - a) + b = y`.

The sum iterates over `a` only: the unique `b` is computed directly, so
each entry is `O(k)` binomial factors rather than an `O(k^2)` candidate
search. Nat subtraction is intentional and matches the state-counting
formula. -/
def transitionNumerator (N m r k x y : Nat) : Nat :=
  Finset.sum (Finset.range (k + 1)) fun a =>
    let remaining := x - a
    if remaining ≤ y then
      let b := y - remaining
      if b ≤ k then
        Nat.choose x a *
          Nat.choose (m - x) (k - a) *
          Nat.choose (r - x) b *
          Nat.choose ((N - m) - (r - x)) (k - b)
      else
        0
    else
      0

/-- Number of equally likely pairs of `k`-subsets selected from the two
piles: the transition denominator. -/
def transitionDenominator (N m k : Nat) : Nat :=
  Nat.choose m k * Nat.choose (N - m) k

/-- Exact rational Bernoulli--Laplace transition probability. -/
def transitionWeight (N m r k x y : Nat) : Rat :=
  (transitionNumerator N m r k x y : Rat) /
    (transitionDenominator N m k : Rat)

variable {N m r k : Nat}

/-- The transition denominator is positive: both piles are at least as
big as the exchange. -/
theorem transitionDenominator_pos (p : ExchangeAdmissible) :
    0 < transitionDenominator p.N p.m p.k := by
  rw [transitionDenominator]
  exact Nat.mul_pos (Nat.choose_pos p.hkm) (Nat.choose_pos p.hknm)

variable {N m r k : Nat}

/-! Row stochasticity: for an admissible state `x`, the transition
weights sum to `1`. The count of microscopic exchanges is a double
Vandermonde: for each `a` (special cards leaving the left pile) the
inner sum over `b` (special cards returning from the right) is
`choose (N - m) k`, and the outer sum over `a` is `choose m k`, so the
row sum equals the transition denominator, which cancels. -/

/-- The `y`-dependent summand of `transitionNumerator` for a fixed `a`,
with the guards of the definition made explicit. This is definitionally
equal to the body of `transitionNumerator` (the `a`-term): the
`let remaining := x - a` and `let b := y - remaining` bindings of the
definition are inlined here. -/
private def guardedTerm (N m r k x a y : Nat) : Nat :=
  if x - a ≤ y then
    if y - (x - a) ≤ k then
      Nat.choose x a * Nat.choose (m - x) (k - a) *
        Nat.choose (r - x) (y - (x - a)) *
        Nat.choose (N - m - (r - x)) (k - (y - (x - a)))
    else 0
  else 0

/-- One microscopic-exchange term: `a` special cards leave the left
pile, `k - a` of the other kind leave with them; `b` special cards
return from the right pile, `k - b` of the other kind. The fourth factor
counts the non-special cards in the right pile
(`(N - m) - (r - x)`). -/
private def exchangeTerm (N m r k x a b : Nat) : Nat :=
  Nat.choose x a * Nat.choose (m - x) (k - a) *
    Nat.choose (r - x) b * Nat.choose (N - m - (r - x)) (k - b)

variable {N m r k : Nat}

/-- The term vanishes for `b > r - x`: the third factor is zero. -/
private theorem exchangeTerm_zero_above (N m r k x a b : Nat) (hb : r - x < b) :
    exchangeTerm N m r k x a b = 0 := by
  rw [exchangeTerm, Nat.choose_eq_zero_of_lt hb, mul_zero, zero_mul]

/-- `blLo N m r` is just `r - (N - m)` (Nat subtraction already floors
at zero). -/
private theorem blLo_eq_tsub (N m r : Nat) : blLo N m r = r - (N - m) := by
  rw [blLo_def, max_zero]

variable {N m r k : Nat}

/-- The transition count vanishes for `y` below the admissible window:
every microscopic-exchange term is zero. For `a ≤ x` the target
`b = y - (x - a)` either exceeds the exchange size (the guard fails) or,
when the guards pass, lands in a fourth binomial factor that the right
pile cannot supply: the right pile holds `(N - m) - (r - x)`
non-special cards, but the exchange would draw `k - b` of them, which
exceeds the supply since `y < r - (N - m) ≤ x` (the `r ≤ N - m` case is
vacuous: then `blLo = 0` and `y < 0` is impossible). For `a > x` the
first factor `choose x a` is zero. -/
private theorem num_zero_below_lo (p : ExchangeAdmissible) (x y : Nat) (_hx : x ≤ p.m)
    (hlo : blLo p.N p.m p.r ≤ x) (hy : y < blLo p.N p.m p.r) (_hym : y ≤ p.m) :
    transitionNumerator p.N p.m p.r p.k x y = 0 := by
  rw [blLo_eq_tsub] at hy hlo
  by_cases h2m : p.r ≤ p.N - p.m
  · -- `r ≤ N - m`: `blLo = 0`, so `hy : y < 0` is impossible.
    exfalso
    rw [Nat.sub_eq_zero_of_le h2m] at hy
    exact Nat.not_lt_zero y hy
  · -- `r > N - m`: `blLo = r - (N - m)`; the subtractions in the choose
    -- arguments below are true (their minuends dominate).
    have hNlt : p.N - p.m < p.r := Nat.not_le.mp h2m
    have hy' : y + 1 ≤ p.r - (p.N - p.m) := Nat.succ_le_of_lt hy
    have hlo' : p.r - (p.N - p.m) ≤ x := hlo
    have hmn := p.hmn
    have hrN := p.hrN
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
          -- `y + 1 ≤ r - (N - m)` (add `N - m`, then `a ≤ k`) and
          -- `a ≤ k`.
          have h9N : p.N + 1 + y + a ≤ p.r + p.k + p.m := by omega
          -- In the genuine-subtraction region this is
          -- `N - m - (r - x) < k - (y - (x - a))`: the fourth
          -- binomial factor would draw more non-special cards
          -- than the right pile holds.
          have h4n : p.N - p.m - (p.r - x) < p.k - (y - (x - a)) := by omega
          have h4' : Nat.choose (p.N - p.m - (p.r - x))
            (p.k - (y - (x - a))) = 0 := Nat.choose_eq_zero_of_lt h4n
          change guardedTerm p.N p.m p.r p.k x a y = 0
          simp only [guardedTerm]
          rw [ite_eq_left hguard, ite_eq_left hbk, h4', mul_zero]
        · -- The guard on `b` fails.
          change guardedTerm p.N p.m p.r p.k x a y = 0
          simp only [guardedTerm]
          rw [ite_eq_left hguard, ite_eq_right hbk]
      · -- The first guard fails.
        change guardedTerm p.N p.m p.r p.k x a y = 0
        simp only [guardedTerm]
        rw [ite_eq_right hguard]
    · -- `a > x`: the first factor is zero.
      have _hx' : x < a := Nat.lt_of_not_ge hax
      have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt _hx'
      change guardedTerm p.N p.m p.r p.k x a y = 0
      simp only [guardedTerm]
      rw [ite_eq_left (by omega)]
      split_ifs with _
      · simp only [h0, zero_mul]
      · rfl

variable {N m r k : Nat}

/-- The transition count vanishes for `y` above the special-card supply:
for `a ≤ x` the target `b = y - (x - a)` exceeds `r - x` (the number of
special cards in the right pile), so the third factor is zero; for
`a > x` the first factor is zero. Used to close the row sum over the
admissible window when `blHi = min m r < m`. -/
private theorem num_zero_above_r (p : ExchangeAdmissible) (x y : Nat) (_hx : x ≤ p.m)
    (hxr : x ≤ p.r) (hyr : y > p.r) :
    transitionNumerator p.N p.m p.r p.k x y = 0 := by
  rw [transitionNumerator]
  apply Finset.sum_eq_zero
  intro a ha
  simp only [Finset.mem_range] at ha
  by_cases hax : a ≤ x
  · by_cases hguard : x - a ≤ y
    · by_cases hbk : y - (x - a) ≤ p.k
      · -- All guards hold: the third factor is zero.
        -- `y > r` and `a ≤ x` give `b = y - (x - a) > r - x`: both
        -- subtractions are true (x - a by hax, r - x by hxr,
        -- y - (x - a) by hguard).
        have hbx : p.r - x < y - (x - a) := by omega
        have hb3 : Nat.choose (p.r - x) (y - (x - a)) = 0 :=
          Nat.choose_eq_zero_of_lt hbx
        change guardedTerm p.N p.m p.r p.k x a y = 0
        simp only [guardedTerm]
        rw [ite_eq_left hguard, ite_eq_left hbk, hb3, mul_zero, zero_mul]
      · -- The guard on `b` fails.
        change guardedTerm p.N p.m p.r p.k x a y = 0
        simp only [guardedTerm]
        rw [ite_eq_left hguard, ite_eq_right hbk]
    · -- The first guard fails.
      change guardedTerm p.N p.m p.r p.k x a y = 0
      simp only [guardedTerm]
      rw [ite_eq_right hguard]
  · -- `a > x`: the first factor is zero.
    have _hx' : x < a := Nat.lt_of_not_ge hax
    have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt _hx'
    change guardedTerm p.N p.m p.r p.k x a y = 0
    simp only [guardedTerm]
    rw [ite_eq_left (by omega)]
    split_ifs with _
    · simp only [h0, zero_mul]
    · rfl

variable {N m r k : Nat}

/-- Inner reindexing: for fixed `a` with `a ≤ k`, the `y`-sum of the
guarded exchange term over `y < m + 1` equals the unguarded `b`-sum
over `b < k + 1`, where `b = y - (x - a)` is the number of special
cards returning from the right pile. The support of the LHS is
`y ∈ [x - a, x - a + k]` with `y - (x - a) ≤ r - x` (below the window
or beyond the exchange size the guards fail; within the window the
third factor `choose (r - x) b` kills the term for `b > r - x`). That
support is in bijection, via `b = y - (x - a)`, with the support of the
RHS, `b ∈ [0, min (k, r - x)]`. -/
private theorem innerYToB (N m r k x a : Nat) (hm : x ≤ m) (_ha : a ≤ k) :
    (∑ y ∈ Finset.range (m + 1), guardedTerm N m r k x a y) =
    ∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b := by
  by_cases hax : a ≤ x
  · -- `x - a` is a true subtraction.
    set As := (Finset.range (m + 1)).filter
      (fun y => x - a ≤ y ∧ y ≤ x - a + k ∧ y - (x - a) ≤ r - x) with hAs
    set Bs := (Finset.range (k + 1)).filter (fun b => b ≤ r - x) with hBs
    have hGzero : ∀ y, y ∉ As → guardedTerm N m r k x a y = 0 := by
      simp only [guardedTerm]
      intro y hy
      by_cases h1 : x - a ≤ y
      · by_cases h2 : y ≤ x - a + k
        · by_cases h3 : y - (x - a) ≤ r - x
          · -- All three window conjuncts hold.
            by_cases hym : y ≤ m
            · -- `y ∈ As`: contradiction.
              have hmem : y ∈ As := by
                simp only [hAs, Finset.mem_filter, Finset.mem_range]
                exact ⟨Nat.lt_succ_of_le hym, h1, h2, h3⟩
              contradiction
            · -- `y > m`: the second binomial factor is zero.
              -- `b = y - (x - a) ≤ k` and `y > m` force `k - a > m - x`:
              -- otherwise `y ≤ (x - a) + k ≤ (x - a) + (m - x) + a = m`.
              by_cases h4 : y - (x - a) ≤ k
              · rw [ite_eq_left h1, ite_eq_left h4]
                have h4n : m - x < k - a := by
                  by_contra hc
                  have hle : k - a ≤ m - x := Nat.le_of_not_lt hc
                  have hlm : y ≤ m := by
                    have hka : a ≤ k := _ha
                    calc
                      y = (x - a) + (y - (x - a)) := by
                        rw [Nat.add_comm, Nat.sub_add_cancel h1]
                      _ ≤ (x - a) + k := Nat.add_le_add_left h4 (x - a)
                      _ = (x - a) + ((k - a) + a) := by
                        conv in (x - a + k) =>
                          rw [(Nat.sub_add_cancel hka).symm]
                      _ ≤ (x - a) + ((m - x) + a) :=
                        Nat.add_le_add_left (Nat.add_le_add_right hle a) (x - a)
                      _ = ((x - a) + (m - x)) + a := by rw [← Nat.add_assoc]
                      _ = (x - a) + ((m - x) + a) := by rw [Nat.add_assoc]
                      _ = (x - a) + (a + (m - x)) := by
                        rw [Nat.add_comm (m - x) a]
                      _ = ((x - a) + a) + (m - x) := by rw [← Nat.add_assoc]
                      _ = x + (m - x) := by rw [Nat.sub_add_cancel hax]
                      _ = m := by
                        rw [Nat.add_comm]
                        exact Nat.sub_add_cancel hm
                  exact False.elim (hym hlm)
                have h2z : Nat.choose (m - x) (k - a) = 0 :=
                  Nat.choose_eq_zero_of_lt h4n
                change exchangeTerm N m r k x a (y - (x - a)) = 0
                simp only [exchangeTerm]
                rw [h2z, mul_zero, zero_mul, zero_mul]
              · rw [ite_eq_left h1, ite_eq_right h4]
          · -- `b ≤ k` but `b > r - x`: the third factor is zero.
            by_cases h4 : y - (x - a) ≤ k
            · rw [ite_eq_left h1, ite_eq_left h4]
              change exchangeTerm N m r k x a (y - (x - a)) = 0
              exact exchangeTerm_zero_above N m r k x a (y - (x - a)) (by
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
    have hAsupp : (∑ y ∈ Finset.range (m + 1), guardedTerm N m r k x a y) =
        (∑ y ∈ As, guardedTerm N m r k x a y) := by
      rw [← Finset.sum_sdiff (s₁ := As) (s₂ := Finset.range (m + 1))
          (h := fun (y : ℕ) (hy : y ∈ As) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (y : ℕ) (hy : y ∈ Finset.range (m + 1) \ As) => by
        simp only [Finset.mem_sdiff, hAs, Finset.mem_filter, Finset.mem_range] at hy
        have hnot : y ∉ As := by
          intro hin
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hin
          exact hy.2 hin
        exact hGzero y hnot]
      rw [zero_add]
    -- The reindexing `b = y - (x - a)` maps the window `As` bijectively onto
    -- the part of `Bs` whose preimage still lies below `m + 1`. On the
    -- complement, the second factor `choose (m - x) (k - a)` vanishes (or,
    -- when `a > x`, the first factor `choose x a` vanishes), so the tail is 0.
    set Bs1 := (Finset.range (k + 1)).filter
      (fun b => b ≤ r - x ∧ b < m + 1 - (x - a)) with hBs1
    have hBs1sub : Bs1 ⊆ Bs := by
      intro b hb
      simp only [hBs1, hBs, Finset.mem_filter, Finset.mem_range] at hb ⊢
      exact ⟨hb.1, hb.2.1⟩
    have hsplit : (∑ b ∈ Bs, exchangeTerm N m r k x a b) =
        (∑ b ∈ Bs1, exchangeTerm N m r k x a b) +
        (∑ b ∈ Bs \ Bs1, exchangeTerm N m r k x a b) := by
      rw [← Finset.sum_sdiff (s₁ := Bs1) (s₂ := Bs) (h := hBs1sub)]
      rw [add_comm]
    have hzero2 : (∑ b ∈ Bs \ Bs1, exchangeTerm N m r k x a b) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_sdiff, hBs, hBs1, Finset.mem_filter, Finset.mem_range] at hb
      have hb1 : b < k + 1 := hb.1.1
      have hb2 : b ≤ r - x := hb.1.2
      have hbnot : ¬(b < m + 1 - (x - a)) := by
        by_contra h6
        exact hb.2 ⟨hb1, hb2, h6⟩
      by_cases hax : a ≤ x
      · -- `a ≤ x`: the second factor is zero, since `k ≤ (m - x) + a <
        -- m + 1 - (x - a) ≤ b ≤ k` is impossible.
        have hk2 : m + 1 - (x - a) ≤ b :=
          Nat.le_of_not_lt (fun hlt => hbnot hlt)
        have h4n : m - x < k - a := by
          by_contra hc
          have hle : k - a ≤ m - x := Nat.le_of_not_lt hc
          have hle2 : k ≤ (m - x) + a := by
            rw [show k = (k - a) + a from (Nat.sub_add_cancel _ha).symm]
            exact Nat.add_le_add_right hle a
          have hlt : (m - x) + a < m + 1 - (x - a) := by omega
          have hk4 : k < b := by
            calc
              k ≤ (m - x) + a := hle2
              _ < m + 1 - (x - a) := hlt
              _ ≤ b := hk2
          have hbk : b ≤ k := by omega
          exact False.elim (Nat.lt_irrefl k (by omega))
        have h2z : Nat.choose (m - x) (k - a) = 0 :=
          Nat.choose_eq_zero_of_lt h4n
        simp only [exchangeTerm]
        rw [h2z, mul_zero, zero_mul, zero_mul]
      · -- `a > x`: the first factor is zero.
        have h1z : Nat.choose x a = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hax)
        simp only [exchangeTerm]
        rw [h1z, zero_mul, zero_mul, zero_mul]
    have hbij : (∑ y ∈ As, guardedTerm N m r k x a y) =
        (∑ b ∈ Bs1, exchangeTerm N m r k x a b) := by
      apply Finset.sum_bij (fun y _ => y - (x - a))
      · -- image in Bs1
        intro y hy
        simp only [hAs, hBs1, Finset.mem_filter, Finset.mem_range] at hy ⊢
        rcases hy with ⟨_, h1, h2, h3⟩
        refine ⟨?_, ?_, ?_⟩
        · -- y - (x - a) < k + 1
          have hsubk : y - (x - a) ≤ k := by omega
          exact Nat.lt_succ_of_le hsubk
        · -- y - (x - a) ≤ r - x
          exact h3
        · -- y - (x - a) < m + 1 - (x - a)
          omega
      · -- injective
        intro y1 hy1 y2 hy2 h12
        have h1 : x - a ≤ y1 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy1
          exact hy1.2.1
        have h2 : x - a ≤ y2 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy2
          exact hy2.2.1
        omega
      · -- surjective onto Bs1
        intro b hb
        simp only [hAs, hBs1, Finset.mem_filter, Finset.mem_range] at hb ⊢
        rcases hb with ⟨hbr, hb2, hbm⟩
        exact ⟨x - a + b, by
          refine ⟨⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩, ?_⟩
          · -- x - a + b < m + 1
            have hxa : x - a ≤ m + 1 := by omega
            have hplus : x - a + (m + 1 - (x - a)) = m + 1 := by
              rw [Nat.add_comm]
              exact Nat.sub_add_cancel hxa
            calc
              x - a + b < x - a + (m + 1 - (x - a)) :=
                Nat.add_lt_add_left hbm (x - a)
              _ = m + 1 := hplus
          · -- x - a ≤ x - a + b
            omega
          · -- x - a + b ≤ x - a + k
            omega
          · -- (x - a + b) - (x - a) ≤ r - x
            have hsub : (x - a + b) - (x - a) = b := by omega
            rw [hsub]
            exact hb2
          · -- (x - a + b) - (x - a) = b
            omega
        ⟩
      · -- equality of terms
        intro y hy
        simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy
        have h4 : y - (x - a) ≤ k :=
          (Nat.sub_le_iff_le_add (a := y) (b := x - a) (c := k)).mpr
            (by simpa only [Nat.add_comm] using hy.2.2.1)
        change guardedTerm N m r k x a y = exchangeTerm N m r k x a (y - (x - a))
        simp only [guardedTerm, exchangeTerm]
        rw [ite_eq_left hy.2.1, ite_eq_left h4]
    have hφ : (∑ y ∈ As, guardedTerm N m r k x a y) =
        (∑ b ∈ Bs, exchangeTerm N m r k x a b) := by
      rw [hsplit, hzero2]
      exact hbij
    have hTsupp : (∑ b ∈ Bs, exchangeTerm N m r k x a b) =
        (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b) := by
      rw [← Finset.sum_sdiff (s₁ := Bs) (s₂ := Finset.range (k + 1))
          (h := fun (y : ℕ) (hy : y ∈ Bs) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (b : ℕ) (hb : b ∈ Finset.range (k + 1) \ Bs) => by
        simp only [Finset.mem_sdiff, hBs, Finset.mem_filter, Finset.mem_range] at hb
        by_cases h5 : b ≤ r - x
        · -- then `b ∈ Bs`, contradicting `hb.2`
          exact False.elim (hb.2 ⟨hb.1, h5⟩)
        · -- `b > r - x`: the third factor is zero
          have h5' : r - x < b := by
            by_contra h6
            exact h5 (Nat.le_of_not_lt h6)
          exact exchangeTerm_zero_above N m r k x a b h5']
      rw [zero_add]
    calc
      _ = ∑ y ∈ As, guardedTerm N m r k x a y := hAsupp
      _ = ∑ b ∈ Bs, exchangeTerm N m r k x a b := hφ
      _ = ∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b := hTsupp
  · -- `a > x`: every term carries `choose x a = 0`.
    have hx : x < a := Nat.lt_of_not_ge hax
    have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt hx
    have hL : (∑ y ∈ Finset.range (m + 1), guardedTerm N m r k x a y) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      change guardedTerm N m r k x a y = 0
      simp only [guardedTerm]
      rw [ite_eq_left (by omega)]
      split_ifs with _
      · simp only [h0, zero_mul]
      · rfl
    have hR : (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp only [exchangeTerm, h0, zero_mul]
    rw [hL, hR.symm]

variable {N m r k : Nat}

/-- Weighted version of `innerYToB`: the inner `y`-sum of the `a`-term of
`guardedTerm`, weighted by `y - (x - a)` (the number `b` of special cards
returning from the right pile), reindexes to the `b`-sum of
`exchangeTerm` weighted by `b`. -/
private theorem innerYToB_b (N m r k x a : Nat) (hm : x ≤ m) (ha : a ≤ k) :
    (∑ y ∈ Finset.range (m + 1), (y - (x - a)) * (guardedTerm N m r k x a y)) =
    (∑ b ∈ Finset.range (k + 1), (b : Nat) * (exchangeTerm N m r k x a b)) := by
  by_cases hax : a ≤ x
  · -- `x - a` is a true subtraction.
    set As := (Finset.range (m + 1)).filter
      (fun y => x - a ≤ y ∧ y ≤ x - a + k ∧ y - (x - a) ≤ r - x) with hAs
    set Bs := (Finset.range (k + 1)).filter (fun b => b ≤ r - x) with hBs
    have hGzero : ∀ y, y ∉ As → guardedTerm N m r k x a y = 0 := by
      simp only [guardedTerm]
      intro y hy
      by_cases h1 : x - a ≤ y
      · by_cases h2 : y ≤ x - a + k
        · by_cases h3 : y - (x - a) ≤ r - x
          · -- All three window conjuncts hold.
            by_cases hym : y ≤ m
            · -- `y ∈ As`: contradiction.
              have hmem : y ∈ As := by
                simp only [hAs, Finset.mem_filter, Finset.mem_range]
                exact ⟨Nat.lt_succ_of_le hym, h1, h2, h3⟩
              contradiction
            · -- `y > m`: the second binomial factor is zero.
              by_cases h4 : y - (x - a) ≤ k
              · rw [ite_eq_left h1, ite_eq_left h4]
                have h4n : m - x < k - a := by
                  by_contra hc
                  have hle : k - a ≤ m - x := Nat.le_of_not_lt hc
                  have hlm : y ≤ m := by
                    have hka : a ≤ k := ha
                    calc
                      y = (x - a) + (y - (x - a)) := by
                        rw [Nat.add_comm, Nat.sub_add_cancel h1]
                      _ ≤ (x - a) + k := Nat.add_le_add_left h4 (x - a)
                      _ = (x - a) + ((k - a) + a) := by
                        conv in (x - a + k) =>
                          rw [(Nat.sub_add_cancel hka).symm]
                      _ ≤ (x - a) + ((m - x) + a) :=
                        Nat.add_le_add_left (Nat.add_le_add_right hle a) (x - a)
                      _ = ((x - a) + (m - x)) + a := by rw [← Nat.add_assoc]
                      _ = (x - a) + ((m - x) + a) := by rw [Nat.add_assoc]
                      _ = (x - a) + (a + (m - x)) := by
                        rw [Nat.add_comm (m - x) a]
                      _ = ((x - a) + a) + (m - x) := by rw [← Nat.add_assoc]
                      _ = x + (m - x) := by rw [Nat.sub_add_cancel hax]
                      _ = m := by
                        rw [Nat.add_comm]
                        exact Nat.sub_add_cancel hm
                  exact False.elim (hym hlm)
                have h2z : Nat.choose (m - x) (k - a) = 0 :=
                  Nat.choose_eq_zero_of_lt h4n
                change exchangeTerm N m r k x a (y - (x - a)) = 0
                simp only [exchangeTerm]
                rw [h2z, mul_zero, zero_mul, zero_mul]
              · rw [ite_eq_left h1, ite_eq_right h4]
          · -- `b ≤ k` but `b > r - x`: the third factor is zero.
            by_cases h4 : y - (x - a) ≤ k
            · rw [ite_eq_left h1, ite_eq_left h4]
              change exchangeTerm N m r k x a (y - (x - a)) = 0
              exact exchangeTerm_zero_above N m r k x a (y - (x - a)) (by
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
    have hGzeroW : ∀ y, y ∉ As → (y - (x - a)) * (guardedTerm N m r k x a y) = 0 := by
      intro y hy
      rw [hGzero y hy, mul_zero]
    have hAsupp : (∑ y ∈ Finset.range (m + 1),
        (y - (x - a)) * (guardedTerm N m r k x a y)) =
        (∑ y ∈ As, (y - (x - a)) * (guardedTerm N m r k x a y)) := by
      rw [← Finset.sum_sdiff (s₁ := As) (s₂ := Finset.range (m + 1))
          (h := fun (y : ℕ) (hy : y ∈ As) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (y : ℕ) (hy : y ∈ Finset.range (m + 1) \ As) => by
        simp only [Finset.mem_sdiff, hAs, Finset.mem_filter, Finset.mem_range] at hy
        have hnot : y ∉ As := by
          intro hin
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hin
          exact hy.2 hin
        exact hGzeroW y hnot]
      rw [zero_add]
    set Bs1 := (Finset.range (k + 1)).filter
      (fun b => b ≤ r - x ∧ b < m + 1 - (x - a)) with hBs1
    have hBs1sub : Bs1 ⊆ Bs := by
      intro b hb
      simp only [hBs1, hBs, Finset.mem_filter, Finset.mem_range] at hb ⊢
      exact ⟨hb.1, hb.2.1⟩
    have hsplit : (∑ b ∈ Bs, (b : Nat) * (exchangeTerm N m r k x a b)) =
        (∑ b ∈ Bs1, (b : Nat) * (exchangeTerm N m r k x a b)) +
        (∑ b ∈ Bs \ Bs1, (b : Nat) * (exchangeTerm N m r k x a b)) := by
      rw [← Finset.sum_sdiff (s₁ := Bs1) (s₂ := Bs) (h := hBs1sub)]
      rw [add_comm]
    have hzero2 : (∑ b ∈ Bs \ Bs1, (b : Nat) * (exchangeTerm N m r k x a b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_sdiff, hBs, hBs1, Finset.mem_filter, Finset.mem_range] at hb
      have hb1 : b < k + 1 := hb.1.1
      have hb2 : b ≤ r - x := hb.1.2
      have hbnot : ¬(b < m + 1 - (x - a)) := by
        by_contra h6
        exact hb.2 ⟨hb1, hb2, h6⟩
      by_cases hax : a ≤ x
      · -- `a ≤ x`: the second factor is zero, since `k ≤ (m - x) + a <
        -- m + 1 - (x - a) ≤ b ≤ k` is impossible.
        have hk2 : m + 1 - (x - a) ≤ b :=
          Nat.le_of_not_lt (fun hlt => hbnot hlt)
        have h4n : m - x < k - a := by
          by_contra hc
          have hle : k - a ≤ m - x := Nat.le_of_not_lt hc
          have hle2 : k ≤ (m - x) + a := by
            rw [show k = (k - a) + a from (Nat.sub_add_cancel ha).symm]
            exact Nat.add_le_add_right hle a
          have hlt : (m - x) + a < m + 1 - (x - a) := by omega
          have hk4 : k < b := by
            calc
              k ≤ (m - x) + a := hle2
              _ < m + 1 - (x - a) := hlt
              _ ≤ b := hk2
          have hbk : b ≤ k := by omega
          exact False.elim (Nat.lt_irrefl k (by omega))
        have h2z : Nat.choose (m - x) (k - a) = 0 :=
          Nat.choose_eq_zero_of_lt h4n
        simp only [exchangeTerm]
        rw [h2z, mul_zero, zero_mul, zero_mul, mul_zero]
      · -- `a > x`: the first factor is zero.
        have h1z : Nat.choose x a = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hax)
        simp only [exchangeTerm]
        rw [h1z, zero_mul, zero_mul, zero_mul, mul_zero]
    have hbij : (∑ y ∈ As, (y - (x - a)) * (guardedTerm N m r k x a y)) =
        (∑ b ∈ Bs1, (b : Nat) * (exchangeTerm N m r k x a b)) := by
      apply Finset.sum_bij (fun y _ => y - (x - a))
      · -- image in Bs1
        intro y hy
        simp only [hAs, hBs1, Finset.mem_filter, Finset.mem_range] at hy ⊢
        rcases hy with ⟨_, h1, h2, h3⟩
        refine ⟨?_, ?_, ?_⟩
        · -- y - (x - a) < k + 1
          have hsubk : y - (x - a) ≤ k := by omega
          exact Nat.lt_succ_of_le hsubk
        · -- y - (x - a) ≤ r - x
          exact h3
        · -- y - (x - a) < m + 1 - (x - a)
          omega
      · -- injective
        intro y1 hy1 y2 hy2 h12
        have h1 : x - a ≤ y1 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy1
          exact hy1.2.1
        have h2 : x - a ≤ y2 := by
          simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy2
          exact hy2.2.1
        omega
      · -- surjective onto Bs1
        intro b hb
        simp only [hAs, hBs1, Finset.mem_filter, Finset.mem_range] at hb ⊢
        rcases hb with ⟨hbr, hb2, hbm⟩
        exact ⟨x - a + b, by
          refine ⟨⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩, ?_⟩
          · -- x - a + b < m + 1
            have hxa : x - a ≤ m + 1 := by omega
            have hplus : x - a + (m + 1 - (x - a)) = m + 1 := by
              rw [Nat.add_comm]
              exact Nat.sub_add_cancel hxa
            calc
              x - a + b < x - a + (m + 1 - (x - a)) :=
                Nat.add_lt_add_left hbm (x - a)
              _ = m + 1 := hplus
          · -- x - a ≤ x - a + b
            omega
          · -- x - a + b ≤ x - a + k
            omega
          · -- (x - a + b) - (x - a) ≤ r - x
            have hsub : (x - a + b) - (x - a) = b := by omega
            rw [hsub]
            exact hb2
          · -- (x - a + b) - (x - a) = b
            omega
        ⟩
      · -- equality of terms
        intro y hy
        simp only [hAs, Finset.mem_filter, Finset.mem_range] at hy
        have h4 : y - (x - a) ≤ k :=
          (Nat.sub_le_iff_le_add (a := y) (b := x - a) (c := k)).mpr
            (by simpa only [Nat.add_comm] using hy.2.2.1)
        have hge : guardedTerm N m r k x a y =
            exchangeTerm N m r k x a (y - (x - a)) := by
          simp only [guardedTerm, exchangeTerm]
          rw [ite_eq_left hy.2.1, ite_eq_left h4]
        rw [hge]
    have hφ : (∑ y ∈ As, (y - (x - a)) * (guardedTerm N m r k x a y)) =
        (∑ b ∈ Bs, (b : Nat) * (exchangeTerm N m r k x a b)) := by
      rw [hsplit, hzero2]
      exact hbij
    have hTsupp : (∑ b ∈ Bs, (b : Nat) * (exchangeTerm N m r k x a b)) =
        (∑ b ∈ Finset.range (k + 1), (b : Nat) * (exchangeTerm N m r k x a b)) := by
      rw [← Finset.sum_sdiff (s₁ := Bs) (s₂ := Finset.range (k + 1))
          (h := fun (y : ℕ) (hy : y ∈ Bs) => (Finset.mem_filter.1 hy).1)]
      rw [Finset.sum_eq_zero fun (b : ℕ) (hb : b ∈ Finset.range (k + 1) \ Bs) => by
        simp only [Finset.mem_sdiff, hBs, Finset.mem_filter, Finset.mem_range] at hb
        by_cases h5 : b ≤ r - x
        · -- then `b ∈ Bs`, contradicting `hb.2`
          exact False.elim (hb.2 ⟨hb.1, h5⟩)
        · -- `b > r - x`: the third factor is zero
          have h5' : r - x < b := by
            by_contra h6
            exact h5 (Nat.le_of_not_lt h6)
          rw [exchangeTerm_zero_above N m r k x a b h5', mul_zero]]
      rw [zero_add]
    calc
      _ = ∑ y ∈ As, (y - (x - a)) * (guardedTerm N m r k x a y) := hAsupp
      _ = ∑ b ∈ Bs, (b : Nat) * (exchangeTerm N m r k x a b) := hφ
      _ = ∑ b ∈ Finset.range (k + 1), (b : Nat) * (exchangeTerm N m r k x a b) := hTsupp
  · -- `a > x`: every term carries `choose x a = 0`.
    have hx : x < a := Nat.lt_of_not_ge hax
    have h0 : Nat.choose x a = 0 := Nat.choose_eq_zero_of_lt hx
    have hL : (∑ y ∈ Finset.range (m + 1),
        (y - (x - a)) * (guardedTerm N m r k x a y)) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      change (y - (x - a)) * (guardedTerm N m r k x a y) = 0
      simp only [guardedTerm]
      rw [ite_eq_left (by omega)]
      split_ifs with _
      · simp only [h0, zero_mul, mul_zero]
      · simp
    have hR : (∑ b ∈ Finset.range (k + 1), (b : Nat) * (exchangeTerm N m r k x a b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp only [exchangeTerm, h0, zero_mul, mul_zero]
    rw [hL, hR.symm]

variable {N m r k : Nat}

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

variable {N m r k : Nat}

/-- Symbolic row stochasticity over the admissible window: the exact
transition weights in an admissible row sum to `1`. -/
theorem blRowStochastic (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    (∑ y ∈ stateFinset p.N p.m p.r,
      (transitionNumerator p.N p.m p.r p.k x.val y : Rat) /
      (transitionDenominator p.N p.m p.k : Rat)) = 1 := by
  have hx : x.val ≤ p.m := by
    -- `x ≤ blHi = min (p.m) (p.r) ≤ p.m`.
    exact x.2.2.trans (min_le_left p.m p.r)
  have hlo : blLo p.N p.m p.r ≤ x.val := x.2.1
  have hden : 0 < transitionDenominator p.N p.m p.k := by
    rw [transitionDenominator]
    exact Nat.mul_pos (Nat.choose_pos p.hkm) (Nat.choose_pos p.hknm)
  -- Step 1: the sum of ratios is the ratio of sums (Rat is a field).
  have hsumdiv :
      (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionNumerator p.N p.m p.r p.k x.val y : Rat) /
        (transitionDenominator p.N p.m p.k : Rat)) =
      (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionNumerator p.N p.m p.r p.k x.val y : Rat)) /
      (transitionDenominator p.N p.m p.k : Rat) := by
    rw [← Finset.sum_div]
  -- Step 2: extend the summation domain to `y < m + 1`; the count is
  -- zero below the window (num_zero_below_lo) and above `r` when the
  -- window top `blHi = min m r` is below `m` (num_zero_above_r).
  have hsub : stateFinset p.N p.m p.r ⊆ Finset.range (p.m + 1) := by
    intro y hy
    simp only [stateFinset, blLo_def, blHi_def, Finset.mem_Icc, Finset.mem_range] at hy ⊢
    omega
  have hzero : (∑ y ∈ Finset.range (p.m + 1) \ stateFinset p.N p.m p.r,
      (transitionNumerator p.N p.m p.r p.k x.val y : Rat)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Finset.mem_sdiff, stateFinset, Finset.mem_Icc, Finset.mem_range] at hy
    by_cases hyl : y < blLo p.N p.m p.r
    · -- below the window: the count is zero there.
      have hym : y ≤ p.m := by omega
      simpa using num_zero_below_lo p x.val y hx hlo hyl hym
    · -- `y ≥ blLo` and `y ≤ m` but `y ∉ Icc (blLo) (blHi)`: so
      -- `y > blHi = min (p.m) (p.r)` while `y ≤ p.m`.
      have hle : blLo p.N p.m p.r ≤ y := Nat.le_of_not_lt hyl
      have hym : y ≤ p.m := by omega
      have hnot : ¬(y ≤ blHi p.N p.m p.r) := by
        intro hyy
        exact hy.2 ⟨hle, hyy⟩
      by_cases hmr : p.m ≤ p.r
      · -- `blHi = p.m` here: `¬(y ≤ p.m)` contradicts `y ≤ p.m`.
        have hnot' : ¬(y ≤ p.m) := by
          simpa only [blHi_def, min_eq_left hmr] using hnot
        exact False.elim (hnot' hym)
      · -- `blHi = p.r` here: `y > p.r`; the count is zero there.
        have hrle : p.r ≤ p.m := Nat.le_of_lt (Nat.not_le.mp hmr)
        have hxr : x.val ≤ p.r := by
          exact x.2.2.trans (min_le_right p.m p.r)
        have hnot' : ¬(y ≤ p.r) := by
          simpa only [blHi_def, min_eq_right hrle] using hnot
        have hyr : y > p.r := Nat.not_le.mp hnot'
        simpa [blHi_def] using num_zero_above_r p x.val y hx hxr hyr
  have hext : (∑ y ∈ stateFinset p.N p.m p.r,
      (transitionNumerator p.N p.m p.r p.k x.val y : Rat)) =
      (∑ y ∈ Finset.range (p.m + 1),
        (transitionNumerator p.N p.m p.r p.k x.val y : Rat)) := by
    rw [← Finset.sum_sdiff hsub]
    rw [hzero, zero_add]
  rw [hsumdiv, hext]
  -- Step 3: the count row sum over `y < m + 1` is the transition
  -- denominator (double Vandermonde).
  have hinner : ∀ a, a ∈ Finset.range (p.k + 1) →
      (∑ y ∈ Finset.range (p.m + 1), guardedTerm p.N p.m p.r p.k x.val a y) =
      (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.r p.k x.val a b) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    exact innerYToB p.N p.m p.r p.k x.val a hx (by omega)
  have hfac : ∀ a, (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.r p.k x.val a b) =
      (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a)) *
      (∑ b ∈ Finset.range (p.k + 1),
        Nat.choose (p.r - x.val) b *
          Nat.choose (p.N - p.m - (p.r - x.val)) (p.k - b)) := by
    intro a
    have h1 : (∑ b ∈ Finset.range (p.k + 1), exchangeTerm p.N p.m p.r p.k x.val a b) =
        (∑ b ∈ Finset.range (p.k + 1),
          (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a)) *
            (Nat.choose (p.r - x.val) b *
              Nat.choose (p.N - p.m - (p.r - x.val)) (p.k - b))) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [exchangeTerm]
      ring
    rw [h1, ← Finset.mul_sum]
  have hsubwin : p.r - x.val ≤ p.N - p.m := by
    -- `r - x ≤ N - m`, i.e. `x ≥ r - (N - m) = blLo`.
    have hlo2 : p.r - (p.N - p.m) ≤ x.val :=
      (Nat.le_max_left (p.r - (p.N - p.m)) 0).trans hlo
    by_cases h2m : p.r ≤ p.N - p.m
    · -- `r ≤ N - m`: `r - x ≤ r ≤ N - m`.
      calc
        p.r - x.val ≤ p.r := Nat.sub_le p.r x.val
        _ ≤ p.N - p.m := h2m
    · -- `r > N - m`: `r - (N - m) ≤ x` is a genuine subtraction,
      -- so `r ≤ x + (N - m)`, i.e. `r - x ≤ N - m`.
      have hle : p.r ≤ x.val + (p.N - p.m) :=
        (Nat.sub_le_iff_le_add).mp hlo2
      have hle2 : p.r ≤ (p.N - p.m) + x.val := by
        rw [Nat.add_comm] at hle
        exact hle
      exact (Nat.sub_le_iff_le_add).mpr hle2
  have hdouble : (∑ y ∈ Finset.range (p.m + 1),
      transitionNumerator p.N p.m p.r p.k x.val y) =
      transitionDenominator p.N p.m p.k := by
    -- The `let`/`ite` body of `transitionNumerator` is definitionally the
    -- let-free `guardedTerm`; `change` bridges what `rw` cannot.
    change (∑ y ∈ Finset.range (p.m + 1),
        (∑ a ∈ Finset.range (p.k + 1), guardedTerm p.N p.m p.r p.k x.val a y)) =
      transitionDenominator p.N p.m p.k
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a ha => hinner a ha)]
    rw [Finset.sum_congr rfl (fun a _ => hfac a)]
    rw [← Finset.sum_mul]
    rw [vandermondeRange x.val (p.m - x.val) p.k]
    rw [show x.val + (p.m - x.val) = p.m from by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hx]
    rw [vandermondeRange (p.r - x.val) (p.N - p.m - (p.r - x.val)) p.k]
    rw [show (p.r - x.val) + (p.N - p.m - (p.r - x.val)) = p.N - p.m from by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hsubwin]
    rw [transitionDenominator]
  -- Lift the Nat sum to Rat and cancel.
  rw [← Nat.cast_sum]
  rw [hdouble]
  exact div_self (by positivity)

variable {N m r k : Nat}

/-- The transition weight is nonnegative. -/
theorem transitionWeight_nonneg (p : ExchangeAdmissible) (x y : BLState p.N p.m p.r) :
    0 ≤ transitionWeight p.N p.m p.r p.k x.val y.val := by
  rw [transitionWeight]
  have hnum : 0 ≤ (transitionNumerator p.N p.m p.r p.k x.val y.val : Rat) := by
    rw [transitionNumerator]
    rw [Nat.cast_sum]
    apply Finset.sum_nonneg
    intro a _
    -- The `let`-form a-term is definitionally the let-free guardedTerm.
    change 0 ≤ (guardedTerm p.N p.m p.r p.k x.val a y.val : Rat)
    simp only [guardedTerm]
    split_ifs
    · exact Nat.cast_nonneg _
    · norm_num
    · norm_num
  exact div_nonneg_iff.mpr (Or.inl ⟨hnum, Nat.cast_nonneg (transitionDenominator p.N p.m p.k)⟩)

variable {N m r k : Nat}

/-- The exact exchange kernel on the admissible macrostate space: each
row is the law `y ↦ transitionWeight N m r k x y`, a genuine
distribution (row stochasticity) by construction. -/
noncomputable def blExchangeKernel (p : ExchangeAdmissible) :
    FiniteKernel (BLState p.N p.m p.r) (BLState p.N p.m p.r) :=
  fun x => Dist.ofFun
    (fun y => transitionWeight p.N p.m p.r p.k x.val y.val)
    (fun y => transitionWeight_nonneg p x y)
    (by
      -- The `Fintype`'s `Finset.univ` is `stateFinset` modulo the subtype
      -- coercion; transport the row-stochasticity sum across the bijection
      -- `y ↦ y.val`.
      have hbridge : Finset.sum Finset.univ
          (fun (y : BLState p.N p.m p.r) =>
            transitionWeight p.N p.m p.r p.k x.val y.val) =
          (∑ z ∈ stateFinset p.N p.m p.r,
            transitionWeight p.N p.m p.r p.k x.val z) := by
        apply Finset.sum_bij
          (fun (y : BLState p.N p.m p.r) (_ : y ∈ Finset.univ) => y.val)
        · -- image in `stateFinset`
          intro y _
          simp only [stateFinset, Finset.mem_Icc]
          exact ⟨y.2.1, y.2.2⟩
        · -- injective
          intro y1 _ y2 _ h12
          exact Subtype.coe_injective h12
        · -- surjective onto `stateFinset`
          intro z hz
          simp only [stateFinset, Finset.mem_Icc] at hz
          exact ⟨⟨z, hz⟩, Fintype.complete _, rfl⟩
        · -- equality of terms
          intro y _
          rfl
      rw [hbridge]
      simpa only [transitionWeight] using blRowStochastic p x)


/-! ## Stationary distribution: sum-one and as a `Dist`

The stationary law of the exchange is the hypergeometric distribution
`x ↦ choose r x * choose (N-r) (m-x) / choose N m` on the window
`[blLo, blHi]` — it is `blStationary` transported off the `BLState`
coercion. -/

/-- A stationary window term vanishes outside the window: for
`b ∈ range (m+1) \ stateFinset`, either `b < blLo` (then
`N - r < m - b`, so `choose (N-r) (m-b) = 0`) or `b > blHi` (then
`choose r b = 0`, or the case is impossible). This is what lets the
Vandermonde sum over the whole range `(0..m]` be restricted to the
admissible window. -/
private theorem blStationaryTerm_zero (p : ExchangeAdmissible) (b : ℕ)
    (hb : b ∈ Finset.range (p.m + 1) \ stateFinset p.N p.m p.r) :
    Nat.choose p.r b * Nat.choose (p.N - p.r) (p.m - b) = 0 := by
  simp only [stateFinset, Finset.mem_Icc, Finset.mem_sdiff] at hb
  have hbN : b ≤ p.m := by simpa using hb.1
  by_cases hlo : b < blLo p.N p.m p.r
  · -- `b < blLo`
    by_cases h2m : p.r ≤ p.N - p.m
    · -- `r ≤ N - m`: `blLo = 0`, so `b < 0`, impossible.
      have hb0 : blLo p.N p.m p.r = 0 := by
        simp only [blLo_def, Nat.sub_eq_zero_of_le h2m, max_zero]
      have hlo0 : b < 0 := by
        rw [← hb0]
        exact hlo
      exact False.elim (Nat.not_lt_zero b hlo0)
    · -- `b < r - (N - m)` with `r > N - m`
      have hbl : blLo p.N p.m p.r = p.r - (p.N - p.m) := by
        simp only [blLo_def]
        rw [max_zero]
      have hlo' : b < p.r - (p.N - p.m) := by simpa [hbl] using hlo
      have hN2m : p.N - p.m < p.r := Nat.not_le.mp h2m
      have hA : (p.N - p.m) + b < p.r := by
        calc
          _ < (p.N - p.m) + (p.r - (p.N - p.m)) :=
            Nat.add_lt_add_left hlo' (p.N - p.m)
          _ = p.r := Nat.add_sub_of_le (Nat.le_of_lt hN2m)
      -- Lift to `Z`: from `(N-m) + b < r` get `N + b < m + r`,
      -- which in `Z` rearranges to `N - r < m - b`.
      -- Work entirely in `Nat`: from `(N-m) + b < r` get `N + b < m + r`,
      -- then peel off `r` to reach `N - r < m - b`.
      have hB : p.N + b < p.m + p.r := by
        have hNm : p.m + (p.N - p.m) = p.N :=
          Nat.add_sub_of_le (Nat.le_of_lt p.hmn)
        calc
          p.N + b = p.m + (p.N - p.m) + b := by
            conv in (p.N + b) => rw [← hNm]
          _ = p.m + ((p.N - p.m) + b) := by rw [Nat.add_assoc]
          _ < p.m + p.r := Nat.add_lt_add_left hA p.m
      -- `N - r < m - b` kills the second factor.
      have hNat : p.N - p.r < p.m - b := by
        have h1 : p.N + b - p.r < p.m := by
          have h2 : p.N + b - p.r < (p.m + p.r) - p.r :=
            (Nat.sub_lt_sub_iff_right
                (Nat.le_trans p.hrN (Nat.le_add_right p.N b))).mpr hB
          simpa [Nat.add_sub_cancel_right] using h2
        have h3 : p.N + b - p.r = p.N - p.r + b := by
          rw [← Nat.sub_add_comm p.hrN]
        exact (Nat.lt_sub_iff_add_lt.mpr (by simpa [h3] using h1))
      rw [Nat.choose_eq_zero_of_lt hNat, mul_zero]
  · -- `b > blHi`
    have hbHi : blLo p.N p.m p.r ≤ b := Nat.not_lt.mp hlo
    have hnot : ¬(b ≤ blHi p.N p.m p.r) := fun h => hb.2 ⟨hbHi, h⟩
    have hbhi' : b > blHi p.N p.m p.r := Nat.not_le.mp hnot
    by_cases hmr : p.m ≤ p.r
    · -- `blHi = m`: `b > m` contradicts `b ≤ m`.
      have hbhi'' : b > p.m := by
        simpa only [blHi_def, min_eq_left hmr] using hbhi'
      exact False.elim (Nat.lt_irrefl p.m (Nat.lt_of_lt_of_le hbhi'' hbN))
    · -- `blHi = r`: `b > r` kills the first factor.
      have hbhi'' : b > p.r := by
        simpa only [blHi_def, min_eq_right (Nat.le_of_lt (Nat.not_le.mp hmr))]
          using hbhi'
      rw [Nat.choose_eq_zero_of_lt hbhi'', zero_mul]

/-- The stationary masses sum to one: Vandermonde over the window
`∑_{x ∈ [blLo, blHi]} choose r x * choose (N-r) (m-x) = choose N m`,
with the range-form extension justified by
`blStationaryTerm_zero`. -/
theorem blStationary_total (p : ExchangeAdmissible) :
    (∑ x ∈ stateFinset p.N p.m p.r,
      (Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) : Rat) /
        (Nat.choose p.N p.m : Rat)) = 1 := by
  -- 1. The window sum equals the full `range (m+1)` sum.
  have hext : (∑ x ∈ stateFinset p.N p.m p.r,
      (Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) : Rat)) =
      (∑ b ∈ Finset.range (p.m + 1),
        (Nat.choose p.r b * Nat.choose (p.N - p.r) (p.m - b) : Rat)) := by
    have hsub : stateFinset p.N p.m p.r ⊆ Finset.range (p.m + 1) := by
      intro x hx
      simp only [stateFinset, Finset.mem_Icc, Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (Nat.le_trans hx.2 (min_le_left p.m p.r))
    have hzero : (∑ b ∈ Finset.range (p.m + 1) \ stateFinset p.N p.m p.r,
        (Nat.choose p.r b * Nat.choose (p.N - p.r) (p.m - b) : Rat)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simpa using blStationaryTerm_zero p b hb
    have hsum' := by
      have hsum := Finset.sum_sdiff
        (f := fun (b : ℕ) =>
          (Nat.choose p.r b * Nat.choose (p.N - p.r) (p.m - b) : Rat)) hsub
      simpa [hzero, add_zero] using hsum
    exact hsum'
  -- 2. The range sum is Vandermonde: `choose (r + (N-r)) m = choose N m`.
  have hvan : (∑ b ∈ Finset.range (p.m + 1),
      (Nat.choose p.r b * Nat.choose (p.N - p.r) (p.m - b) : Rat)) =
      (Nat.choose p.N p.m : Rat) := by
    simp only [← Nat.cast_mul, ← Nat.cast_sum]
    rw [vandermondeRange p.r (p.N - p.r) p.m]
    rw [Nat.add_sub_of_le p.hrN]
  -- 3. Pull the constant denominator out and divide.
  calc
    (∑ x ∈ stateFinset p.N p.m p.r,
        (Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) : Rat) /
          (Nat.choose p.N p.m : Rat)) =
      (∑ x ∈ stateFinset p.N p.m p.r,
        (Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) : Rat)) /
        (Nat.choose p.N p.m : Rat) := by
      rw [Finset.sum_congr rfl (fun _ _ => by rw [div_eq_mul_inv]),
          ← Finset.sum_mul, ← div_eq_mul_inv]
    _ = (Nat.choose p.N p.m : Rat) / (Nat.choose p.N p.m : Rat) := by
      rw [hext, hvan]
    _ = 1 := by
      rw [div_self]
      exact ne_of_irrefl' (Rat.natCast_pos.mpr (Nat.choose_pos (Nat.le_of_lt p.hmn)))

/-- The stationary distribution of the general exchange, as a genuine
`Dist` on the state space: the hypergeometric masses, total `1` by
`blStationary_total`, nonnegative termwise. -/
noncomputable def blStationaryDist (p : ExchangeAdmissible) :
    Dist (BLState p.N p.m p.r) :=
  Dist.ofFun
    (fun x => blStationary p.N p.m p.r x)
    (fun x => blStationary_nonneg p x)
    (by
      -- Bridge `Finset.univ` (the pmap finset of the `Fintype.ofFinset`
      -- instance) to the `stateFinset` sum via the `val` bijection,
      -- then use the window total.
      have hbridge : Finset.sum Finset.univ
          (fun (x : BLState p.N p.m p.r) => blStationary p.N p.m p.r x) =
          (∑ z ∈ stateFinset p.N p.m p.r,
            (Nat.choose p.r z * Nat.choose (p.N - p.r) (p.m - z) : Rat) /
              (Nat.choose p.N p.m : Rat)) := by
        apply Finset.sum_bij
          (fun (x : BLState p.N p.m p.r) (_ : x ∈ Finset.univ) => x.val)
        · -- image in `stateFinset`
          intro x _
          simp only [stateFinset, Finset.mem_Icc]
          exact ⟨x.2.1, x.2.2⟩
        · -- injective
          intro x1 _ x2 _ h12
          exact Subtype.coe_injective h12
        · -- surjective onto `stateFinset`
          intro z hz
          simp only [stateFinset, Finset.mem_Icc] at hz
          exact ⟨⟨z, hz⟩, Fintype.complete _, rfl⟩
        · -- `blStationary x` is the raw formula at `x.val`
          intro x _
          rw [blStationary, Nat.cast_mul]
      rw [hbridge]
      exact blStationary_total p)

/-- The mass of the stationary distribution at `x` is the hypergeometric
stationary mass. This simp lemma is the authoritative pointwise access to
`blStationaryDist`; it exposes the defining scalar and keeps the
construction's nonnegativity/normalization proofs out of `simp`. -/
@[simp]
theorem mass_blStationaryDist (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    Dist.mass (blStationaryDist p) x = blStationary p.N p.m p.r x := by
  dsimp only [blStationaryDist]
  rw [Dist.mass_ofFun]

/-- The mass of the exchange-kernel row at `y` is the exact transition
probability. This simp lemma is the authoritative pointwise access to
`blExchangeKernel`. -/
@[simp]
theorem mass_blExchangeKernel (p : ExchangeAdmissible)
    (x y : BLState p.N p.m p.r) :
    Dist.mass (blExchangeKernel p x) y =
      transitionWeight p.N p.m p.r p.k x.val y.val := by
  dsimp only [blExchangeKernel]
  rw [Dist.mass_ofFun]


/-! ### First mode: hypergeometric means and the first eigenfunction

The exchange kernel is affine on the macrostate: `E[y | x] = x - a
mean + b mean` with the means given by the 1-D hypergeometric
computations below. From that, the centered macrostate
`f(x) = x - m*r/N` is an eigenfunction with eigenvalue
`blFirstModeFactor = 1 - N*k/(m*(N-m))`. -/
section firstMode
variable {N m r k : Nat}

/-- The first-mode factor of the general exchange kernel: the eigenvalue
of the first centered linear mode. The coefficient is independent of
`r` (the centering, not the contraction, depends on `r`). For the
Commander split (`N = 99`, `m = 50`) this specializes to the concrete
`firstModeFactor` of `Shufflemath.BernoulliLaplace` (agreement is proved
in the bridge module). -/
def blFirstModeFactor (N m k : Nat) : Rat :=
  1 - ((N : Rat) * k) / ((m : Rat) * (N - m))

/-- Pointwise `y`-product and its `(x-a)` / `(y-(x-a))` split parts, as
`Nat` terms. Wrapper `def`s keep the `Nat.cast` of a product opaque
(a `: Rat` ascription on a product would normalize to a product of
casts, which the `Nat.cast_*` lemmas cannot match). -/
private def gProd (N m r k x a y : Nat) : Nat := y * (guardedTerm N m r k x a y)
private def gProdA (N m r k x a y : Nat) : Nat := (x - a) * (guardedTerm N m r k x a y)
private def gProdB (N m r k x a y : Nat) : Nat := (y - (x - a)) * (guardedTerm N m r k x a y)
private def gSplit (N m r k x a y : Nat) : Nat :=
  (x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y)

/-- Weighted inner reindexing: for fixed `a <= k`, the `y`-sum of
`(y : Rat) * (guarded term)` over `y < m + 1` equals
`(x - a) * (b-sum) + (b-weighted b-sum)`, all as `Rat` sums.
The `y = (x-a) + (y-(x-a))` split is done in `Nat` (inside `Nat.cast`);
each half is then bridged to its `b`-sum by `innerYToB` / `innerYToB_b`. -/
private theorem innerYToB_w (N m r k x a : Nat) (hm : x <= m) (ha : a <= k) :
    (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
      ((x : Rat) - (a : Rat)) * (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat))
      + (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) := by
  by_cases hax : a <= x
  · -- `a <= x`: genuine `x - a`.
    -- The unweighted `y`-sum (as a `Rat` sum of casts) is the unweighted `b`-sum.
    have hB : (∑ y ∈ Finset.range (m + 1), (guardedTerm N m r k x a y : Rat)) =
        (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      rw [show (∑ y ∈ Finset.range (m + 1), guardedTerm N m r k x a y) =
            (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b)
        from innerYToB N m r k x a hm ha]
    -- The `b`-weighted `b`-sum is the `(y - (x-a))`-weighted `y`-sum
    -- (cast of `innerYToB_b`).
    have hBw : (∑ y ∈ Finset.range (m + 1), (gProdB N m r k x a y : Rat)) =
        (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) := by
      have hN := innerYToB_b N m r k x a hm ha
      have hR : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (Nat.cast ((b : Nat) * (exchangeTerm N m r k x a b)) : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← Nat.cast_mul]
      rw [hR]
      change (∑ y ∈ Finset.range (m + 1), Nat.cast ((y - (x - a)) * (guardedTerm N m r k x a y))) = _
      rw [← Nat.cast_sum, hN, Nat.cast_sum]
    -- Per term, inside the cast: `y * g = (x-a) * g + (y-x+a) * g`
    -- (a genuine subtraction distributes; otherwise `g = 0`).
    have hS1 : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
        (∑ y ∈ Finset.range (m + 1), (gSplit N m r k x a y : Rat)) := by
      apply Finset.sum_congr rfl
      intro y _
      -- Work in `Nat` (inside the cast): `y * g = (x-a) * g + (y-x+a) * g`.
      refine congrArg (Nat.cast ·) ?_
      change y * (guardedTerm N m r k x a y) =
          (x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y)
      by_cases hgy : x - a <= y
      · -- Genuine: `y = (y-x+a) + (x-a)`, so the `Nat` product distributes.
        have hsum : y = (y - (x - a)) + (x - a) := by
          rw [Nat.sub_add_cancel hgy]
        rw [hsum]
        rw [Nat.add_mul]
        rw [show ((y - (x - a)) + (x - a)) - (x - a) = y - (x - a) from by
          rw [Nat.add_sub_cancel_right]]
        ring
      · -- `y < x - a`: the guarded term vanishes.
        have hgz : (guardedTerm N m r k x a y) = 0 := by
          simp only [guardedTerm]
          rw [ite_eq_right hgy]
        rw [hgz]
        simp
    -- The sum of the two cast halves is the cast of the split `Nat` sum.
    have hS2 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) +
          (∑ y ∈ Finset.range (m + 1), (gProdB N m r k x a y : Rat)) =
        (∑ y ∈ Finset.range (m + 1), (gSplit N m r k x a y : Rat)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      change Nat.cast ((x - a) * (guardedTerm N m r k x a y)) +
            Nat.cast ((y - (x - a)) * (guardedTerm N m r k x a y)) =
          Nat.cast ((x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y))
      rw [← Nat.cast_add]
    -- The constant half factors out of the sum.
    have hS3 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) =
        (Nat.cast (x - a)) * (∑ y ∈ Finset.range (m + 1), (guardedTerm N m r k x a y : Rat)) := by
      have h0 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) =
          (∑ y ∈ Finset.range (m + 1), (Nat.cast (x - a)) * (Nat.cast (guardedTerm N m r k x a y))) := by
        apply Finset.sum_congr rfl
        intro y _
        change Nat.cast ((x - a) * (guardedTerm N m r k x a y)) =
            (Nat.cast (x - a)) * (Nat.cast (guardedTerm N m r k x a y))
        rw [Nat.cast_mul]
      rw [h0, ← Finset.mul_sum]
    -- Assemble: fold each half to its `b`-sum and match the `Rat` difference.
    rw [hS1, ← hS2]
    rw [hS3, ← hBw]
    rw [hB, Nat.cast_sub hax]
  · -- `a > x`: `C(x, a) = 0` kills both `g` and `E`, so both sides are `0`.
    have hxlt : x < a := by omega
    have hgz (y : Nat) : (guardedTerm N m r k x a y) = 0 := by
      simp only [guardedTerm]
      by_cases h1 : x - a <= y
      · by_cases h2 : y - (x - a) <= k
        · -- Both guards pass: the product; `C(x, a) = 0` kills it.
          rw [ite_eq_left h1, ite_eq_left h2, Nat.choose_eq_zero_of_lt hxlt]
          simp
        · -- Inner guard fails: the inner `else 0`.
          rw [ite_eq_left h1, ite_eq_right h2]
      · -- Outer guard fails: the outer `else 0`.
        rw [ite_eq_right h1]
    have hez (b : Nat) : (exchangeTerm N m r k x a b) = 0 := by
      simp only [exchangeTerm]
      rw [Nat.choose_eq_zero_of_lt hxlt]
      simp
    have hL : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) = 0 := by
      have h1 : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
          (∑ y ∈ Finset.range (m + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [gProd]
        rw [hgz y]
        simp
      rw [h1]
      simp
    have hB : (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) = 0 := by
      have h1 : (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hez b]
        simp
      rw [h1]
      simp
    have hBw : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) = 0 := by
      have h1 : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hez b]
        simp
      rw [h1]
      simp
    rw [hL, hB, hBw]
    simp
/-- Per-term Pascal shift: `(x + 1) * C(n, x+1) = n * C(n-1, x)`.
Holds for all `n x`: when `x >= n` both sides are `0`. -/
theorem chooseSucc_weighted (n x : Nat) :
    (x + 1) * (Nat.choose n (x + 1)) = n * (Nat.choose (n - 1) x) := by
  by_cases h : x < n
  · -- `x <= n - 1`: Pascal + the `(x+1)`-weighted Pascal recurrence.
    have h1 : Nat.choose n (x + 1) = Nat.choose (n - 1) x + Nat.choose (n - 1) (x + 1) := by
      have : n - 1 + 1 = n := by omega
      rw [← this]
      rw [Nat.choose_succ_succ (n - 1) x]
      simp
    have h2 : (x + 1) * (Nat.choose (n - 1) (x + 1)) =
        (Nat.choose (n - 1) x) * (n - 1 - x) := by
      rw [Nat.mul_comm]
      rw [Nat.choose_succ_right_eq (n - 1) x]
    calc
      (x + 1) * (Nat.choose n (x + 1)) =
          (x + 1) * (Nat.choose (n - 1) x + Nat.choose (n - 1) (x + 1)) := by rw [h1]
      _ = (x + 1) * (Nat.choose (n - 1) x) + (x + 1) * (Nat.choose (n - 1) (x + 1)) := by ring
      _ = (x + 1) * (Nat.choose (n - 1) x) + (Nat.choose (n - 1) x) * (n - 1 - x) := by rw [h2]
      _ = (Nat.choose (n - 1) x) * ((x + 1) + (n - 1 - x)) := by
        rw [Nat.mul_comm]
        ring
      _ = n * (Nat.choose (n - 1) x) := by
        have hle : x <= n - 1 := by omega
        have : (x + 1) + (n - 1 - x) = n := by
          have h1 : (n - 1 - x) + x = n - 1 := Nat.sub_add_cancel hle
          omega
        rw [this]
        exact Nat.mul_comm (Nat.choose (n - 1) x) n
  · -- `x >= n`: both binomials vanish (`n = 0` handled separately).
    by_cases hn0 : n = 0
    · simp [hn0]
    ·
      have hxn : x >= n := Nat.not_lt.mp h
      have h1 : n < x + 1 := by omega
      have h2 : n - 1 < x := by
        have hnn : n = (n - 1) + 1 := by
          have : 0 < n := Nat.pos_of_ne_zero hn0
          omega
        rw [hnn] at hxn
        omega
      have hz1 : Nat.choose n (x + 1) = 0 := by
        rw [Nat.choose_eq_zero_iff]
        exact h1
      have hz2 : Nat.choose (n - 1) x = 0 := by
        rw [Nat.choose_eq_zero_iff]
        exact h2
      rw [hz1, hz2]
      simp

/-- 1-D hypergeometric mean, exact rational form: a pile of `n` cards
holding `x` marked ones, drawing `k`: the expected number of marked
cards drawn is `k*x/n`. Equivalently the weighted sum identity -/
theorem chooseSum_weighted (n x k : Nat) (hx : x <= n) :
    (∑ a ∈ Finset.range (k + 1),
      (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
      (k : Rat) * (x : Rat) / (n : Rat) * (Nat.choose n k : Rat) := by
  by_cases hk : k = 0
  · -- The only summand has `a = 0` (hence is 0); the right side has `k = 0`.
    simp [hk]
  ·
    by_cases hx0 : x = 0
    · -- `C(0, a)` is 0 for `a >= 1` and the `a = 0` summand has a `0` factor;
      -- the right side has an `x = 0` factor.
    
      have hL : (∑ a ∈ Finset.range (k + 1),
          (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a = 0
        · simp [ha]
        · have ha1 : 0 < a := Nat.pos_of_ne_zero ha
          have hz : Nat.choose x a = 0 := by
            rw [Nat.choose_eq_zero_iff]
            simpa [hx0] using ha1
          simp [hz]
      rw [hL]
      simp [hx0]
    ·
      -- `0 < x <= n`, so `0 < n`: the division by `n` is an honest one.
      have hx1 : 0 < x := Nat.pos_of_ne_zero hx0
      have hn1 : 0 < n := Nat.lt_of_lt_of_le hx1 hx
      have hnpos : (n : Rat) ≠ 0 := by
        intro h
        have h1 : (0 : Rat) < (n : Rat) := Nat.cast_pos.mpr hn1
        rw [h] at h1
        linarith
      -- Step 1: drop the zero `a = 0` summand and reindex `a = i + 1` (`i < k`),
      -- using `k - (i+1) = k - 1 - i`.
      have h1 :
          (∑ a ∈ Finset.range (k + 1),
            (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
          (∑ i ∈ Finset.range k,
            ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) *
              (Nat.choose (n - x) (k - 1 - i) : Rat)) := by
        -- `range (k+1) \ {0}` is in bijection with `range k` via `i + 1`.
        have hdrop : (∑ a ∈ Finset.range (k + 1),
              (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
              (∑ a ∈ Finset.range (k + 1) \ {0},
                (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) := by
          have hsub : ({0} : Finset Nat) ⊆ Finset.range (k + 1) := by
            intro x hx
            simp only [Finset.mem_singleton] at hx
            rw [hx]
            simp
          rw [← Finset.sum_sdiff hsub]
          simp
        rw [hdrop]
        apply Finset.sum_bij (fun a _ => a - 1)
        · intro a ha
          simp at ha
          rcases ha with ⟨hle, hne⟩
          have hpos : 0 < a := Nat.pos_of_ne_zero hne
          simp
          omega
        · intro a₁ h₁ a₂ h₂ h
          have h1 : 0 < a₁ := by
            simp at h₁
            rcases h₁ with ⟨_, hn⟩
            exact Nat.pos_of_ne_zero hn
          have h2 : 0 < a₂ := by
            simp at h₂
            rcases h₂ with ⟨_, hn⟩
            exact Nat.pos_of_ne_zero hn
          have h' : a₁ - 1 = a₂ - 1 := h
          omega
        · intro b hb
          use b + 1
          simp at hb
          simp
          omega
        · intro a ha
          have h0a : 0 < a := by
            simp at ha
            rcases ha with ⟨_, hne⟩
            exact Nat.pos_of_ne_zero hne
          have h1a : 1 ≤ a := Nat.succ_le_of_lt h0a
          have h2 : a - 1 + 1 = a := by omega
          have h3 : k - 1 - (a - 1) = k - a := by omega
          have hcast : (a : Rat) = (Nat.cast (a - 1) : Rat) + 1 := by
            have hsub : (Nat.cast (a - 1) : Rat) = (a : Rat) - 1 := by
              rw [Nat.cast_sub h1a]
              ring
            rw [hsub]
            ring
          rw [h2, h3, hcast]
      -- Step 2: per-term shift `(i+1) * C(x, i+1) = x * C(x-1, i)`; the sum
      -- factors as `x * (sum over i < k of C(x-1, i) * C(n-x, k-1-i))`.
      rw [h1]
      have h2 :
          (∑ i ∈ Finset.range k,
            ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) *
              (Nat.choose (n - x) (k - 1 - i) : Rat)) =
          (x : Rat) * (∑ i ∈ Finset.range k,
            (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat)) := by
        -- The per-term identity is `chooseSucc_weighted x i`, cast to `Rat`.
        calc
          _ = ∑ i ∈ Finset.range k,
              ((x : Rat) * (Nat.choose (x - 1) i : Rat)) *
                (Nat.choose (n - x) (k - 1 - i) : Rat) := by
            apply Finset.sum_congr rfl
            intro i _
            have hN : (i + 1) * (Nat.choose x (i + 1)) = x * (Nat.choose (x - 1) i) :=
              chooseSucc_weighted x i
            have hR : ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) =
                (x : Rat) * (Nat.choose (x - 1) i : Rat) := by
              have hA : (i : Rat) + 1 = (Nat.cast (i + 1) : Rat) := by
                rw [Nat.cast_add, Nat.cast_one]
              rw [hA, ← Nat.cast_mul, ← Nat.cast_mul]
              exact congrArg Nat.cast hN
            rw [hR]
          _ = (x : Rat) * ∑ i ∈ Finset.range k,
            (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      rw [h2]
      -- Step 3: Vandermonde: the range sum is the antidiagonal sum, which
      -- is `C((x-1) + (n-x), k-1) = C(n-1, k-1)` (with `x >= 1` the Nat
      -- subtraction is honest and `(x-1) + (n-x) = n-1`).
      have h3 : (∑ i ∈ Finset.range k,
          (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat)) =
          (Nat.choose (n - 1) (k - 1) : Rat) := by
        have hk1 : k - 1 + 1 = k := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          omega
        rw [show (Finset.range k : Finset Nat) = Finset.range (k - 1 + 1) from
            congrArg Finset.range hk1.symm]
        have hN : (∑ ij ∈ Finset.antidiagonal (k - 1),
            (Nat.choose (x - 1) ij.1) * (Nat.choose (n - x) ij.2)) =
            (Nat.choose ((x - 1) + (n - x)) (k - 1)) := by
          rw [← Nat.add_choose_eq (x - 1) (n - x) (k - 1)]
        have hmid : (∑ ij ∈ Finset.antidiagonal (k - 1),
            (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat)) =
            (Nat.choose ((x - 1) + (n - x)) (k - 1) : Rat) := by
          have hA : (∑ ij ∈ Finset.antidiagonal (k - 1),
              (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat)) =
              (∑ ij ∈ Finset.antidiagonal (k - 1),
                (Nat.cast (Nat.choose (x - 1) ij.1 * (Nat.choose (n - x) ij.2)) : Rat)) := by
            apply Finset.sum_congr rfl
            intro ij _
            rw [← Nat.cast_mul]
          rw [hA]
          rw [← Nat.cast_sum]
          exact congrArg Nat.cast hN
        calc
          _ = ∑ ij ∈ Finset.antidiagonal (k - 1),
              (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat) := by
            rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) j : Rat))
                (k - 1)]
          _ = (Nat.choose ((x - 1) + (n - x)) (k - 1) : Rat) := by
            exact hmid
          _ = (Nat.choose (n - 1) (k - 1) : Rat) := by
            have hsum : (x - 1) + (n - x) = n - 1 := by omega
            rw [hsum]
      rw [h3]
      -- Step 4: close. The goal is
      -- `(n : Rat) * ((x : Rat) * C(n-1, k-1)) = (k : Rat) * (x : Rat) / (n : Rat) * C(n, k)`.
      -- Both sides are `x * ( ... )`; inside, the coefficient relation
      -- `n * C(n-1, k-1) = k * C(n, k)` is exactly `chooseSucc_weighted n (k-1)`,
      -- and the right side's `/ (n : Rat) * (n : Rat)` cancels (`n ≠ 0`).
      have h4 : (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) =
          (k : Rat) * (Nat.choose n k : Rat) := by
        have h0 : (k - 1 + 1) * (Nat.choose n (k - 1 + 1)) = n * (Nat.choose (n - 1) (k - 1)) :=
          chooseSucc_weighted n (k - 1)
        have hk1 : k - 1 + 1 = k := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          omega
        have hN : n * (Nat.choose (n - 1) (k - 1)) = k * (Nat.choose n k) := by
          simpa [hk1] using h0.symm
        rw [show (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) =
               (Nat.cast (n * (Nat.choose (n - 1) (k - 1))) : Rat) by
              rw [← Nat.cast_mul],
            show (k : Rat) * (Nat.choose n k : Rat) =
               (Nat.cast (k * (Nat.choose n k)) : Rat) by
              rw [← Nat.cast_mul]]
        exact congrArg Nat.cast hN
      -- Rewrite the right side into the `x * (...)` shape.
      have hR : (k : Rat) * (x : Rat) / (n : Rat) * (Nat.choose n k : Rat) =
          (x : Rat) * ((k : Rat) * (Nat.choose n k : Rat) / (n : Rat)) := by
        field_simp [hnpos]
      rw [hR]
      -- Clear the fraction using `n * C(n-1,k-1) = k * C(n,k)` (chooseSucc_weighted n (k-1)).
      have hdiv : (k : Rat) * (Nat.choose n k : Rat) / (n : Rat) =
          (Nat.choose (n - 1) (k - 1) : Rat) := by
        rw [show (k : Rat) * (Nat.choose n k : Rat) =
               (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) from h4.symm]
        field_simp [hnpos]
      rw [hdiv]

end firstMode
end BernoulliLaplaceGeneral
end Shufflemath
