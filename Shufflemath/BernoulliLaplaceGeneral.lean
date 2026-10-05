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

end BernoulliLaplaceGeneral
end Shufflemath
