import Shufflemath.TotalVariation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Defs

namespace Shufflemath
namespace BernoulliLaplace

/-- Number of microscopic exchange choices taking macrostate `x` to `y`.

`x` is the number of original-left cards currently in the left pile. We exchange
`k` cards chosen uniformly from each pile. For each possible number `a` of
original-left cards leaving the left pile, the target state determines the
number `b` that must return from the right pile:

`(x - a) + b = y`.

The previous implementation summed over both `a` and `b` and discarded all but
one `b` with an `if`. This equivalent formulation computes that unique `b`
directly, reducing each matrix entry from `O(k^2)` candidate pairs to `O(k)`.
Nat subtraction is intentional here and matches the state-counting formula. -/
def transitionNumerator (N m k x y : Nat) : Nat :=
  Finset.sum (Finset.range (k + 1)) fun a =>
    let remaining := x - a
    if _h : remaining <= y then
      let b := y - remaining
      if b <= k then
        Nat.choose x a *
          Nat.choose (m - x) (k - a) *
          Nat.choose (m - x) b *
          Nat.choose ((N - m) - (m - x)) (k - b)
      else
        0
    else
      0

/-- Number of equally likely pairs of `k`-subsets selected from the two piles. -/
def transitionDenominator (N m k : Nat) : Nat :=
  Nat.choose m k * Nat.choose (N - m) k

/-- Exact rational Bernoulli--Laplace transition probability. -/
def transitionWeight (N m k x y : Nat) : Rat :=
  (transitionNumerator N m k x y : Rat) /
    (transitionDenominator N m k : Rat)

/-- The first-mode factor appearing in the unequal two-urn Bernoulli--Laplace
exchange chain. -/
def firstModeFactor (N m k : Nat) : Rat :=
  1 - ((N : Rat) * k) / ((m : Rat) * (N - m))

/-- Exchange sizes 1 through 49, encoded by zero-based `Fin 49`. -/
def commanderExchangeSize (k : Fin 49) : Nat := k.val + 1

/-- First-mode factor for the 99-card, 50/49 split. -/
def commanderFirstMode (k : Fin 49) : Rat :=
  firstModeFactor 99 50 (commanderExchangeSize k)

/-- `Fin 49` value corresponding to exchanging 25 cards. -/
def exchange25 : Fin 49 := Fin.mk 24 (by decide)

/-- `Fin 49` value corresponding to exchanging 24 cards. -/
def exchange24 : Fin 49 := Fin.mk 23 (by decide)

/-- `Fin 49` value corresponding to exchanging 26 cards. -/
def exchange26 : Fin 49 := Fin.mk 25 (by decide)

@[simp]
theorem commander_factor_25 : commanderFirstMode exchange25 = -(1 / 98 : Rat) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange25, firstModeFactor]

@[simp]
theorem commander_factor_24 : commanderFirstMode exchange24 = (37 / 1225 : Rat) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange24, firstModeFactor]

@[simp]
theorem commander_factor_26 : commanderFirstMode exchange26 = -(62 / 1225 : Rat) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange26, firstModeFactor]

/-- Among integer exchanges 1..49, 25 minimizes the absolute value of the
Commander 50/49 first-mode factor. -/
theorem commander_exchange25_minimizes_first_mode :
    forall k : Fin 49,
      |commanderFirstMode exchange25| <= |commanderFirstMode k| := by
  native_decide

/-- Macrostate for the 99-card 50/49 split.

The actual left-original-card count is `val + 1`, so the 50 feasible states are
1 through 50. -/
abbrev CommanderState := Fin 50

/-- Decode the macrostate into the number of original-left cards in the left pile. -/
def commanderLeftCount (x : CommanderState) : Nat := x.val + 1

/-- Exact transition matrix for exchanging `k` cards between the 50/49 piles. -/
def commanderExchangeMatrix (k : Nat) : Matrix CommanderState CommanderState Rat :=
  fun x y => transitionWeight 99 50 k (commanderLeftCount x) (commanderLeftCount y)

/-- The practically interesting quarter-deck exchange matrix. -/
def commanderExchange25Matrix : Matrix CommanderState CommanderState Rat :=
  commanderExchangeMatrix 25

/-- Closed decidability instance for the inner row-nonnegativity predicate.

Mathlib's finite-forall decider does not recursively synthesize itself beneath
another `∀` binder. Keeping this instance at namespace scope is important for
`native_decide`: a theorem-local `letI` becomes a free variable in the compiled
decision procedure and therefore cannot be natively evaluated. -/
private instance commanderExchange25RowNonnegDecidable :
    DecidablePred (fun i : CommanderState =>
      ∀ j : CommanderState, 0 <= commanderExchange25Matrix i j) :=
  fun _ => Fintype.decidableForallFintype

/-- Machine-checked finite certificate that the exact 25-card exchange matrix is
row stochastic. With the single-sum transition formula this checks only about
`50 * 50 * 26` combinatorial terms rather than a quadratic inner search. -/
theorem commanderExchange25Matrix_rowStochastic :
    commanderExchange25Matrix ∈ Matrix.rowStochastic Rat CommanderState := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  native_decide

/-- Semantic Markov-kernel view of the exact computational matrix. -/
noncomputable def commanderExchange25 : FiniteKernel CommanderState CommanderState :=
  FiniteKernel.ofRowStochastic
    commanderExchange25Matrix commanderExchange25Matrix_rowStochastic

/-- Hypergeometric stationary mass induced by a uniformly random 99-card deck. -/
def commanderStationaryVector (x : CommanderState) : Rat :=
  ((Nat.choose 50 (commanderLeftCount x) *
      Nat.choose 49 (50 - commanderLeftCount x) : Nat) : Rat) /
    (Nat.choose 99 50 : Rat)

theorem commanderStationaryVector_nonneg :
    forall x : CommanderState, 0 <= commanderStationaryVector x := by
  native_decide

theorem commanderStationaryVector_total :
    Finset.sum Finset.univ commanderStationaryVector = 1 := by
  native_decide

/-- Semantic exact stationary distribution. -/
noncomputable def commanderStationary : Dist CommanderState :=
  Dist.ofFun commanderStationaryVector
    commanderStationaryVector_nonneg commanderStationaryVector_total

/-- Fully segregated initial macrostate: all 50 original-left cards remain left. -/
def commanderSegregatedState : CommanderState := Fin.mk 49 (by decide)

/-- Computable point-mass vector used by exact matrix certificates. -/
def commanderInitialVector (x : CommanderState) : Rat :=
  if x = commanderSegregatedState then 1 else 0

/-! ## Materialized exact certificate engine

The mathematical transition matrix is a function, which is the right representation
for proofs. It is a poor representation for repeated native evaluation: composing
function-valued vectors causes earlier steps to be recomputed once for every later
coordinate. The following arrays are only an executable view of the same exact
objects. `Array.ofFn` eagerly materializes every coordinate, so each Markov step is
ordinary `O(50^2)` dynamic programming rather than a `50^t` expansion of paths.
-/

/-- Materialized 50-entry exact rational vector. -/
abbrev CommanderArray := Array Rat

/-- Materialized 50x50 exact rational transition table. -/
abbrev CommanderTable := Array (Array Rat)

/-- Materialize the exact mathematical 25-card transition matrix exactly once. -/
def commanderExchange25Table : CommanderTable :=
  Array.ofFn fun x : CommanderState =>
    Array.ofFn fun y : CommanderState =>
      commanderExchange25Matrix x y

/-- Materialized segregated initial distribution. -/
def commanderInitialArray : CommanderArray :=
  Array.ofFn commanderInitialVector

/-- Materialized hypergeometric stationary distribution. -/
def commanderStationaryArray : CommanderArray :=
  Array.ofFn commanderStationaryVector

/-- Read a materialized vector using the canonical Commander state index. -/
@[inline]
def commanderArrayGet (p : CommanderArray) (x : CommanderState) : Rat :=
  p[x.val]!

/-- Read a materialized transition table using canonical Commander state indices. -/
@[inline]
def commanderTableGet (P : CommanderTable) (x y : CommanderState) : Rat :=
  (P[x.val]!)[y.val]!

/-- One exact Markov step on materialized arrays.

The result is eagerly materialized before the next step. -/
def stepCommanderArray (p : CommanderArray) (P : CommanderTable) : CommanderArray :=
  Array.ofFn fun y : CommanderState =>
    Finset.sum Finset.univ fun x : CommanderState =>
      commanderArrayGet p x * commanderTableGet P x y

/-- Repeated exact evolution using materialized intermediate vectors. -/
def runCommanderArray (P : CommanderTable) : Nat -> CommanderArray -> CommanderArray
  | 0, p => p
  | n + 1, p => runCommanderArray P n (stepCommanderArray p P)

/-- Run the 25-card exchange from complete segregation. The local `let` bindings
force the matrix and initial vector to be materialized values shared by all steps. -/
def commanderRun25 (n : Nat) : CommanderArray :=
  let P := commanderExchange25Table
  let p0 := commanderInitialArray
  runCommanderArray P n p0

/-- View a materialized Commander vector through the mathematical function API used
by `vectorTV`. This is only array indexing; it does not recompute prior steps. -/
def commanderArrayAsVector (p : CommanderArray) : CommanderState -> Rat :=
  fun x => commanderArrayGet p x

/-- Exact finite verification that the hypergeometric law is stationary for the
25-card exchange, using the materialized certificate engine. -/
theorem commanderStationary_fixed_point :
    let q := stepCommanderArray commanderStationaryArray commanderExchange25Table
    forall y : CommanderState,
      commanderArrayGet q y = commanderStationaryVector y := by
  native_decide

/-- The exact TV distance after two 25-card exchanges from complete segregation. -/
theorem commander_tv_after_two_exchange25 :
    vectorTV
      (commanderArrayAsVector (commanderRun25 2))
      commanderStationaryVector =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  native_decide

/-- The exact TV distance after three 25-card exchanges from complete segregation. -/
theorem commander_tv_after_three_exchange25 :
    vectorTV
      (commanderArrayAsVector (commanderRun25 3))
      commanderStationaryVector =
      (172379525755689183991816396516567920780192827919620440221147749 /
        6691837923759692633601708022649918108038775216019298375918637677488 : Rat) := by
  native_decide

end BernoulliLaplace
end Shufflemath
