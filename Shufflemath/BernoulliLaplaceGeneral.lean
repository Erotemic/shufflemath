/-
General Bernoulli--Laplace exchange chains.

This file builds the general theory: the macrostate space of a two-pile
exchange with `r` marked ("special") cards, symbolic row stochasticity
(double Vandermonde), the hypergeometric stationary law, and the exchange
kernel `blExchangeKernel : FiniteKernel (BLState N m r) (BLState N m r)`.

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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
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

/-- The exchange parameters force `m < N` and `0 < m` to be coherent:
`0 < m` is a field, and `m < N` follows already from `0 < k ≤ N - m`.
This lemma just collects the derived facts used in proofs. -/
theorem exchangeAdmissible_derived (p : ExchangeAdmissible) :
    p.m < p.N ∧ 0 < p.m ∧ p.m ≤ p.N ∧ p.r ≤ p.N :=
  ⟨p.hmn, p.h0m, p.hmn.le, p.hrN⟩

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

/-! ## Detailed balance, part 1: the exchange fiber and its count

The exchange step "move `k` cards from the top pile `S` to the bottom and
`k` cards back" is counted by 7-tuples `(S1, S2, a, A1, A2, B1, B2)`:
`S1 ⊆ stars`, `|S1| = x`, `S2 ⊆ plain`, `|S2| = m - x` (the pile `S`),
`a` specials moved out (`A1`, `|A1| = a`), `A2` ordinary cards moved out
(`|A2| = k - a`), `B1` specials moved in (`|B1| = y - (x - a)`), and
`B2` ordinary cards moved in (`|B2| = k - (y - (x - a))`).  The new pile
has `x - a + (y - (x - a)) = y` specials, so the fiber count with the
numerator guard is exactly
`choose r x * choose (N - r) (m - x) * transitionNumerator x y`.

The involution `(S, A, B) ↦ (S \ A ∪ B, B, A)` then swaps the fiber of
`(x, y)` with that of `(y, x)`, giving detailed balance.
-/

section detailedBalance

variable (p : ExchangeAdmissible)

/-- The universe of special cards (there are `r` of them) and the universe
of ordinary cards (there are `N - r` of them), as concrete `Fin` types.
Choosing a pile `S` of size `m` with `x` specials is the same as choosing
`S1 ⊆ starsUniv` with `|S1| = x` and `S2 ⊆ plainUniv` with
`|S2| = m - x`. -/
private def starsUniv (p : ExchangeAdmissible) : Finset (Fin p.r) :=
  Finset.univ

private def plainUniv (p : ExchangeAdmissible) : Finset (Fin (p.N - p.r)) :=
  Finset.univ

/-- The exchange fiber count for the macrostate pair `(x, y)`: see the
section comment. -/
private def fiberSum (p : ExchangeAdmissible) (x y : Nat) : Nat :=
  ∑ S1 ∈ (starsUniv p).powersetCard x,
  ∑ S2 ∈ (plainUniv p).powersetCard (p.m - x),
  ∑ a ∈ (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k),
      (∑ _A1 ∈ S1.powersetCard a,
      ∑ _A2 ∈ S2.powersetCard (p.k - a),
      ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
      ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)

/-- A sum of constant `1`s over a finset is its cardinality. -/
private theorem sumOnes {α : Type*} (s : Finset α) : (∑ _x ∈ s, 1 : Nat) = s.card := by
  rw [Finset.sum_const_nat (fun _ _ => rfl)]
  simp

/-- The `(A, B)` part of the fiber, given the pile `(S1, S2)` and the
special-exchange index `a`: the four nested sums of `1`s collapse to the
product of the four `powersetCard` cardinalities. -/
private theorem fiberABcount (p : ExchangeAdmissible) (x y a : Nat)
    (S1 : Finset (Fin p.r)) (_hS1 : S1 ∈ (starsUniv p).powersetCard x)
    (S2 : Finset (Fin (p.N - p.r))) (_hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x))
    (_ha : a ∈ Finset.range (p.k + 1)) :
    (∑ _A1 ∈ S1.powersetCard a,
    ∑ _A2 ∈ S2.powersetCard (p.k - a),
    ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
    ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
    (S1.powersetCard a).card * (S2.powersetCard (p.k - a)).card *
      ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
      ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
  have h4 :
      (∑ B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
        ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [sumOnes]
  have h3 :
      (∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
        (∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)) =
        ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
          ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [h4, Finset.sum_const_nat (fun _ _ => rfl)]
  have h2 :
      (∑ _A2 ∈ S2.powersetCard (p.k - a),
        (∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
          (∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1))) =
        (S2.powersetCard (p.k - a)).card *
          ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
          ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [h3, Finset.sum_const_nat (fun _ _ => rfl)]
    ring_nf
  rw [h2, Finset.sum_const_nat (fun _ _ => rfl)]
  ring_nf


/-- Given the pile and the index `a`, the `(A, B)` part of the fiber is
the product of the four `powersetCard` cardinalities, i.e. the
`a`-summand factors with the plain-card count written as
`(N - r) - (m - x)`. -/
private theorem fiberABchoose (p : ExchangeAdmissible) (x y a : Nat)
    (S1 : Finset (Fin p.r)) (hS1 : S1 ∈ (starsUniv p).powersetCard x)
    (S2 : Finset (Fin (p.N - p.r))) (hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x))
    (ha : a ∈ Finset.range (p.k + 1))
    (_hg : x - a ≤ y ∧ y - (x - a) ≤ p.k) :
    (∑ _A1 ∈ S1.powersetCard a,
    ∑ _A2 ∈ S2.powersetCard (p.k - a),
    ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
    ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
    Nat.choose x a * Nat.choose (p.m - x) (p.k - a) *
      Nat.choose (p.r - x) (y - (x - a)) *
      Nat.choose ((p.N - p.r) - (p.m - x)) (p.k - (y - (x - a))) := by
  have hS1c : S1.card = x := (Finset.mem_powersetCard.1 hS1).2
  have hS2c : S2.card = p.m - x := (Finset.mem_powersetCard.1 hS2).2
  have hS1s : S1 ⊆ starsUniv p := (Finset.mem_powersetCard.1 hS1).1
  have hS2s : S2 ⊆ plainUniv p := (Finset.mem_powersetCard.1 hS2).1
  rw [fiberABcount p x y a S1 hS1 S2 hS2 ha]
  rw [Finset.card_powersetCard, Finset.card_powersetCard, hS1c, hS2c]
  have h3c : ((starsUniv p \ S1).powersetCard (y - (x - a))).card =
      (p.r - x).choose (y - (x - a)) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff]
    have hi : S1 ∩ starsUniv p = S1 := Finset.inter_eq_left.mpr hS1s
    rw [hi]
    have hcard : (starsUniv p).card - S1.card = p.r - x := by
      show (Finset.univ : Finset (Fin p.r)).card - S1.card = p.r - x
      rw [Finset.card_fin p.r, hS1c]
    rw [hcard]
  rw [h3c]
  have h4c : ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card =
      ((p.N - p.r) - (p.m - x)).choose (p.k - (y - (x - a))) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff]
    have hi : S2 ∩ plainUniv p = S2 := Finset.inter_eq_left.mpr hS2s
    rw [hi]
    have hcard : (plainUniv p).card - S2.card = (p.N - p.r) - (p.m - x) := by
      show (Finset.univ : Finset (Fin (p.N - p.r))).card - S2.card =
        (p.N - p.r) - (p.m - x)
      rw [Finset.card_fin (p.N - p.r), hS2c]
    rw [hcard]
  rw [h4c]

/-! The main counting lemma: the exchange fiber of `(x, y)` factors into
the stationary-weight factors and the transition numerator. -/
private theorem fiberSum_eq (p : ExchangeAdmissible) (x y : Nat)
    (hx : x ∈ stateFinset p.N p.m p.r) :
    fiberSum p x y =
      Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) *
        transitionNumerator p.N p.m p.r p.k x y := by
  have hlo : blLo p.N p.m p.r ≤ x := by
    simp only [stateFinset, Finset.mem_Icc] at hx
    exact hx.1
  have hhi : x ≤ blHi p.N p.m p.r := by
    simp only [stateFinset, Finset.mem_Icc] at hx
    exact hx.2
  have hxm : x ≤ p.m := hhi.trans (Nat.min_le_left p.m p.r)
  have hxr : x ≤ p.r := hhi.trans (Nat.min_le_right p.m p.r)
  -- The two plain-card counts `(N - r) - (m - x)` and `(N - m) - (r - x)`
  -- agree for `x` in the window: both sides are exact exactly when
  -- `m + r - x ≤ N`, and in that case both equal `N - r - m + x`;
  -- otherwise both saturate to `0`.
  have hfour : (p.N - p.r) - (p.m - x) = (p.N - p.m) - (p.r - x) := by
    by_cases hsum : p.m + p.r ≤ p.N + x
    · -- Both differences are exact.
      have h1 : p.m - x ≤ p.N - p.r := by
        have hA : p.m + p.r - x ≤ p.N := (Nat.sub_le_iff_le_add).mpr (by omega)
        have hB : p.r + (p.m - x) = (p.m + p.r) - x := by
          simpa [Nat.add_comm] using (Nat.add_sub_assoc hxm p.r).symm
        have hC : (p.m - x) + p.r ≤ p.N := by
          simpa [Nat.add_comm, hB] using hA
        exact (Nat.le_sub_iff_add_le p.hrN).mpr hC
      have h2 : p.r - x ≤ p.N - p.m := by
        have hA : p.m + p.r - x ≤ p.N := (Nat.sub_le_iff_le_add).mpr (by omega)
        have hB : p.m + (p.r - x) = (p.m + p.r) - x := by
          simpa [Nat.add_comm] using (Nat.add_sub_assoc hxr p.m).symm
        have hC : p.m + (p.r - x) ≤ p.N := by
          simpa [hB] using hA
        have hC' : p.r - x + p.m ≤ p.N := by
          simpa [Nat.add_comm] using hC
        exact (Nat.le_sub_iff_add_le p.hmn.le).mpr hC'
        
      have hL : (↑((p.N - p.r) - (p.m - x)) : ℤ) =
          (p.N : ℤ) - (p.r : ℤ) - (p.m : ℤ) + (x : ℤ) := by
        rw [Int.ofNat_sub h1, Int.ofNat_sub p.hrN, Int.ofNat_sub hxm]
        ring
      have hR : (↑((p.N - p.m) - (p.r - x)) : ℤ) =
          (p.N : ℤ) - (p.m : ℤ) - (p.r : ℤ) + (x : ℤ) := by
        rw [Int.ofNat_sub h2, Int.ofNat_sub p.hmn.le, Int.ofNat_sub hxr]
        ring
      have heq : (↑((p.N - p.r) - (p.m - x)) : ℤ) =
          (↑((p.N - p.m) - (p.r - x)) : ℤ) := by
        rw [hL, hR]
        ring
      exact Int.natCast_inj.mp heq
    · -- `m + r > N + x`: both differences saturate to `0`.
      have hL0 : (p.N - p.r) - (p.m - x) = 0 := by
        have hK : p.N - p.r ≤ p.m - x := by
          have h1 : (↑(p.N - p.r) : ℤ) ≤ (↑(p.m - x) : ℤ) := by
            rw [Int.ofNat_sub p.hrN, Int.ofNat_sub hxm]
            have hsum' : (p.N : ℤ) + (x : ℤ) < (p.m : ℤ) + (p.r : ℤ) := by
              norm_cast
              omega
            linarith
          exact Int.ofNat_le.mp h1
        rw [Nat.sub_eq_zero_iff_le]
        exact hK
      have hR0 : (p.N - p.m) - (p.r - x) = 0 := by
        have hK : p.N - p.m ≤ p.r - x := by
          have h1 : (↑(p.N - p.m) : ℤ) ≤ (↑(p.r - x) : ℤ) := by
            rw [Int.ofNat_sub p.hmn.le, Int.ofNat_sub hxr]
            have hsum' : (p.N : ℤ) + (x : ℤ) < (p.m : ℤ) + (p.r : ℤ) := by
              norm_cast
              omega
            linarith
          exact Int.ofNat_le.mp h1
        rw [Nat.sub_eq_zero_iff_le]
        exact hK
      rw [hL0, hR0]
  dsimp only [fiberSum]
  -- The `(A, B)` fiber of a fixed pile `(S1, S2)` and index `a` is the
  -- `a`-summand of the transition numerator.
  have hnum (S1 : Finset (Fin p.r))
      (hS1 : S1 ∈ (starsUniv p).powersetCard x)
      (S2 : Finset (Fin (p.N - p.r)))
      (hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x)) :
      (∑ a ∈ (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k),
          (∑ _A1 ∈ S1.powersetCard a,
          ∑ _A2 ∈ S2.powersetCard (p.k - a),
          ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
          ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)) =
      transitionNumerator p.N p.m p.r p.k x y := by
    rw [transitionNumerator]
    -- The filter-domain a-sum equals the ite-sum over the full range.
    rw [Finset.sum_filter (fun a : Nat => x - a ≤ y ∧ y - (x - a) ≤ p.k) _]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only
    by_cases c1 : x - a ≤ y
    · by_cases c2 : y - (x - a) ≤ p.k
      · -- Both ite branches select the positive side: `simp` has already
        -- unfolded the four level sums into a product of `choose` factors
        -- indexed by the pile cards.
        simp [c1, c2]
        have hS1if : S1 ∈ (starsUniv p).powersetCard x ↔
            S1 ⊆ starsUniv p ∧ S1.card = x := Finset.mem_powersetCard
        have hS1c : S1.card = x := (hS1if.mp hS1).2
        have hS1s : S1 ⊆ starsUniv p := (hS1if.mp hS1).1
        have hS2if : S2 ∈ (plainUniv p).powersetCard (p.m - x) ↔
            S2 ⊆ plainUniv p ∧ S2.card = p.m - x := Finset.mem_powersetCard
        have hS2c : S2.card = p.m - x := (hS2if.mp hS2).2
        have hS2s : S2 ⊆ plainUniv p := (hS2if.mp hS2).1
        have hU1 : (starsUniv p \ S1).card = p.r - x := by
          rw [Finset.card_sdiff]
          have hi : S1 ∩ starsUniv p = S1 := Finset.inter_eq_left.mpr hS1s
          rw [hi]
          have hcard : (starsUniv p).card - S1.card = p.r - x := by
            show (Finset.univ : Finset (Fin p.r)).card - S1.card = p.r - x
            rw [Finset.card_fin p.r, hS1c]
          rw [hcard]
        have hU2 : (plainUniv p \ S2).card = (p.N - p.r) - (p.m - x) := by
          rw [Finset.card_sdiff]
          have hi : S2 ∩ plainUniv p = S2 := Finset.inter_eq_left.mpr hS2s
          rw [hi]
          have hcard : (plainUniv p).card - S2.card =
              (p.N - p.r) - (p.m - x) := by
            show (Finset.univ : Finset (Fin (p.N - p.r))).card - S2.card =
              (p.N - p.r) - (p.m - x)
            rw [Finset.card_fin (p.N - p.r), hS2c]
          rw [hcard]
        rw [hS1c, hS2c, hU1, hU2, hfour]
        ring
      · simp [c1, c2]
    · by_cases c2 : y - (x - a) ≤ p.k
      · simp [c1, c2]
      · simp [c1, c2]
  -- Peel off the pile sums: the `a`-sum is the same for every pile.
  rw [Finset.sum_congr rfl (fun S1 hS1 => Finset.sum_congr rfl (fun S2 hS2 => hnum S1 hS1 S2 hS2))]
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.sum_const_nat (fun _ _ => rfl)]
  rw [Finset.card_powersetCard, Finset.card_powersetCard]
  have hcard1 : (starsUniv p).card = p.r := by
    show (Finset.univ : Finset (Fin p.r)).card = p.r
    rw [Finset.card_fin p.r]
  have hcard2 : (plainUniv p).card = p.N - p.r := by
    show (Finset.univ : Finset (Fin (p.N - p.r))).card = p.N - p.r
    rw [Finset.card_fin (p.N - p.r)]
  rw [hcard1, hcard2]
  ring_nf


/-! ### Flat 7-tuple formulation for the involution argument

The exchange fiber is counted by a finset of 7-tuples `(S1, S2, a, A1, A2,
B1, B2)` drawn from the powersets of the two card universes and the index
range, restricted by a single predicate. The involution
`(S1, S2, a, A1, A2, B1, B2) ↦ (S1 \ A1 ∪ B1, S2 \ A2 ∪ B2, B1.card,
B1, B2, A1, A2)` is a bijection between the `(x, y)` and `(y, x)`
instances of this finset. -/

private abbrev fiber7Tuple (p : ExchangeAdmissible) :=
  (((((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) × Nat) ×
    Finset (Fin p.r)) × Finset (Fin (p.N - p.r))) × Finset (Fin p.r)) ×
  Finset (Fin (p.N - p.r))

private def tS1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.1.1
private def tS2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.1.2
private def tA {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.2
private def tA1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.2
private def tA2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.2
private def tB1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.2
private def tB2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.2

private def fiber7U1 (p : ExchangeAdmissible) :=
  (starsUniv p).powerset ×ˢ (plainUniv p).powerset
private def fiber7U2 (p : ExchangeAdmissible) := fiber7U1 p ×ˢ Finset.range (p.k + 1)
private def fiber7U3 (p : ExchangeAdmissible) := fiber7U2 p ×ˢ (starsUniv p).powerset
private def fiber7U4 (p : ExchangeAdmissible) := fiber7U3 p ×ˢ (plainUniv p).powerset
private def fiber7U5 (p : ExchangeAdmissible) := fiber7U4 p ×ˢ (starsUniv p).powerset
private def fiber7Univ (p : ExchangeAdmissible) : Finset (fiber7Tuple p) :=
  fiber7U5 p ×ˢ (plainUniv p).powerset

abbrev fiber7Pred (p : ExchangeAdmissible) (x y : Nat) : fiber7Tuple p → Prop := fun t =>
  (tS1 t).card = x ∧ (tS2 t).card = p.m - x ∧ tA1 t ⊆ tS1 t ∧ tA2 t ⊆ tS2 t ∧
  tB1 t ⊆ starsUniv p \ tS1 t ∧ tB2 t ⊆ plainUniv p \ tS2 t ∧
  (tA1 t).card = tA t ∧ (tA2 t).card = p.k - tA t ∧
  (tB1 t).card = y - (x - tA t) ∧ (tB2 t).card = p.k - (y - (x - tA t)) ∧
  x - tA t ≤ y ∧ y - (x - tA t) ≤ p.k

private def fiber7Set (p : ExchangeAdmissible) (x y : Nat) : Finset (fiber7Tuple p) := by
  exact (fiber7Univ p).filter (fiber7Pred p x y)

/-- The 7-tuple repackaged as the 3-tuple `(S1, (S2, a))`. -/
private def t3Of {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ) :=
  (t.1.1.1.1.1.1, (t.1.1.1.1.1.2, t.1.1.1.1.2))

/-- The 7-tuple repackaged as the 4-tuple `((A1, A2), (B1, B2))`. -/
private def t4Of {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) :=
  ((t.1.1.1.2, t.1.1.2), (t.1.2, t.2))

/-- A 7-tuple rebuilt from a 3-tuple `((S1, S2), a)` and a 4-tuple
`((A1, A2), (B1, B2))`. -/
private def mk7 {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) : fiber7Tuple p :=
  by
    have S1 := t3.1
    have S2 := t3.2.1
    have a := t3.2.2
    have A1 := t4.1.1
    have A2 := t4.1.2
    have B1 := t4.2.1
    have B2 := t4.2.2
    exact ((((((S1, S2), a), A1), A2), B1), B2)

/-- The re-packaging is lossless in both directions. -/
private theorem re7 {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    mk7 (t3Of t) (t4Of t) = t := by
  rfl

private theorem re7' {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :
    t3Of (mk7 t3 t4) = t3 := by
  rfl

private theorem re7'' {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :
    t4Of (mk7 t3 t4) = t4 := by
  rfl

/-- The 3-tuple part of the fiber: the two piles and the index, with the
cardinality and guard restrictions. -/
private def fiber3Set (p : ExchangeAdmissible) (x y : Nat) :
    Finset (Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ)) :=
  (starsUniv p).powersetCard x ×ˢ (plainUniv p).powersetCard (p.m - x) ×ˢ
    (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k)

/-- The ambient 4-tuple space. -/
private def fiber4Max (p : ExchangeAdmissible) :
    Finset ((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :=
  ((starsUniv p).powerset ×ˢ (plainUniv p).powerset) ×ˢ
    ((starsUniv p).powerset ×ˢ (plainUniv p).powerset)

/-- The 4-tuple `(A1, A2, B1, B2)` is a valid fiber element over the
3-tuple `t3 = ((S1, S2), a)`. -/
private abbrev isFiber4 (p : ExchangeAdmissible) (x y : Nat)
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) : Prop :=
  t4.1.1 ∈ (t3.1).powersetCard (t3.2.2) ∧
    t4.1.2 ∈ (t3.2.1).powersetCard (p.k - t3.2.2) ∧
    t4.2.1 ∈ (starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)) ∧
    t4.2.2 ∈ (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2)))

/-- The 4-tuple fiber over a fixed 3-tuple. -/
private def fiber4Set (p : ExchangeAdmissible) (x y : Nat)
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ)) :
    Finset ((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :=
  ((t3.1.powersetCard t3.2.2 ×ˢ t3.2.1.powersetCard (p.k - t3.2.2)) ×ˢ
    ((starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)) ×ˢ
      (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2)))))

end detailedBalance
end BernoulliLaplaceGeneral
end Shufflemath
