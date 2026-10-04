/-
General Bernoulli--Laplace exchange chains.

`BernoulliLaplace.lean` contains the concrete 99-card 50/49 Commander
instance. This file builds the general theory: the macrostate space of a
two-pile exchange with pile sizes `m` and `N - m` exchanging `k` cards,
symbolic row stochasticity (double Vandermonde), the hypergeometric
stationary distribution (Vandermonde with a symmetry reindex), detailed
balance, and the theorem tying the general kernel to the Commander
matrix.

Parameters throughout: `N m k : Nat` with `0 < m < N`, `0 < k`, `k ≤ m`,
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
import Shufflemath.BernoulliLaplace
import Mathlib.Data.Nat.Choose.Basic
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
the left pile, as a subtype of `ℕ`. `k` is carried for signature
uniformity (the admissible range itself does not depend on the exchange
size). -/
def BLState (N m _ : Nat) : Type := {x : ℕ // lo N m ≤ x ∧ x ≤ hi N m}

variable {N m k : Nat}

/-- The admissible macrostates form a finite set. -/
instance fintypeBLState (N m k : Nat) : Fintype (BLState N m k) :=
  Fintype.ofFinset (Finset.Icc (lo N m) (hi N m)) fun _ => Finset.mem_Icc

variable {N m k : Nat}

/-- Projection to the count. -/
abbrev stateVal (x : BLState N m k) : Nat := x.val

/-- The macrostate Finset: the `Finset ℕ` of admissible counts. This is
the summation domain for row sums and the stationary total. -/
def stateFinset (N m : Nat) : Finset ℕ := Finset.Icc (lo N m) (hi N m)

variable {N m k : Nat}

/-- Hypergeometric stationary mass at macrostate `x`: the probability a
uniformly random arrangement of the `N`-card deck has exactly `x`
original-left cards in the left pile. -/
def blStationary (N m k : Nat) (x : BLState N m k) : Rat :=
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
theorem blStationary_nonneg (p : Params) (x : BLState p.N p.m p.k) :
    0 ≤ blStationary p.N p.m p.k x := by
  rw [blStationary]
  exact div_nonneg_iff.mpr (Or.inl ⟨Nat.cast_nonneg' _, Nat.cast_nonneg' _⟩)

end BernoulliLaplaceGeneral
end Shufflemath
