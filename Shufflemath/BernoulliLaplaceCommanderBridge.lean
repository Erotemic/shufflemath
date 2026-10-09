/-
Bridge between the general Bernoulli--Laplace exchange theory
(`Shufflemath.BernoulliLaplaceGeneral`) and the concrete 99-card
Commander instance (`Shufflemath.BernoulliLaplace`).

The Commander deck has 99 cards with a 50-card left pile and 50 marked
("original-left") cards; the quarter-deck exchange moves 25 cards from
each pile. In the general parameters that is `N = 99`, `m = 50`,
`r = 50 = m` (every marked card sits in the deck's left half),
`k = 25`. The admissible macrostates of `BLState 99 50 50` are
`1 <= x <= 50`, exactly the values of `commanderLeftCount` on `Fin 50`.

This module proves the two theories coincide under that identification:
the transition weights of the two kernels and the masses of the two
stationary distributions are equal pointwise. The concrete file stays
untouched; the import direction is one-way (both concrete -> general).
-/
import Shufflemath.BernoulliLaplace
import Shufflemath.BernoulliLaplaceGeneral
import Mathlib.Tactic

namespace Shufflemath

open BernoulliLaplace

/-- The Commander 99-card instance as general parameters: 99 cards,
50-card left pile, all 50 original-left cards marked, 25-card exchange. -/
abbrev commanderBLParams : BernoulliLaplaceGeneral.ExchangeAdmissible :=
  ⟨99, 50, 50, 25, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Commander states are `Fin 50`; the general macrostate of state `i`
holds `i.val + 1` original-left cards (the `1 <= x <= 50` range of
`BLState 99 50 50`: `blLo 99 50 50 = max (50 - 49) 0 = 1` and
`blHi 99 50 50 = min 50 50 = 50`). -/
def commanderToBL (i : CommanderState) :
    BernoulliLaplaceGeneral.BLState 99 50 50 :=
  ⟨i.val + 1, Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt i.2⟩

/-- The inverse identification: a general macrostate `x` (with
`1 <= x <= 50`) is Commander state `x - 1`. -/
def blToCommander (x : BernoulliLaplaceGeneral.BLState 99 50 50) :
    CommanderState :=
  ⟨x.val - 1, by
    -- The state property is `blLo 99 50 50 <= x.val <= blHi 99 50 50`,
    -- which evaluates to `1 <= x.val <= 50`.
    have hlo : 1 <= x.val := by
      simpa [BernoulliLaplaceGeneral.blLo, BernoulliLaplaceGeneral.blLo_def]
        using x.2.1
    have hhi : x.val <= 50 := by
      simpa [BernoulliLaplaceGeneral.blHi, BernoulliLaplaceGeneral.blHi_def]
        using x.2.2
    omega⟩

theorem blToCommander_commanderToBL (i : CommanderState) :
    blToCommander (commanderToBL i) = i := by
  apply Fin.ext
  simp only [blToCommander, commanderToBL, Nat.add_one_sub_one]

theorem commanderToBL_blToCommander (x : BernoulliLaplaceGeneral.BLState 99 50 50) :
    commanderToBL (blToCommander x) = x := by
  have hlo : 1 <= x.val := by
    simpa [BernoulliLaplaceGeneral.blLo, BernoulliLaplaceGeneral.blLo_def]
      using x.2.1
  apply Subtype.ext
  simp only [commanderToBL, blToCommander]
  exact Nat.sub_add_cancel hlo

/-- The general transition formula with `r = m` (all marked cards in
the deck) is exactly the Commander's: the two definitions differ only
by the phantom `r` parameter, which the numerator uses as `r - x` and
the denominator does not use at all. -/
theorem transitionWeight_general_eq_commander (N m k x y : Nat) :
    BernoulliLaplaceGeneral.transitionWeight N m m k x y =
      BernoulliLaplace.transitionWeight N m k x y := by
  simp only [BernoulliLaplaceGeneral.transitionWeight,
    BernoulliLaplace.transitionWeight,
    BernoulliLaplaceGeneral.transitionNumerator,
    BernoulliLaplace.transitionNumerator,
    BernoulliLaplaceGeneral.transitionDenominator,
    BernoulliLaplace.transitionDenominator]
  rfl

/-- The Commander quarter-deck kernel and the general exchange kernel at
the Commander parameters agree on every matrix entry, under the state
identification. -/
theorem commanderExchange25_matches_blExchange (i j : CommanderState) :
    Dist.mass (commanderExchange25 i) j =
      Dist.mass (BernoulliLaplaceGeneral.blExchangeKernel commanderBLParams
        (commanderToBL i)) (commanderToBL j) := by
  simp only [commanderExchange25, FiniteKernel.ofRowStochastic, Dist.mass_ofFun,
    BernoulliLaplaceGeneral.blExchangeKernel, commanderToBL]
  rfl

/-- The Commander hypergeometric stationary distribution and the general
one agree pointwise under the same identification: both are
`C(50, x) * C(49, 50 - x) / C(99, 50)`. -/
theorem commanderStationary_matches_blStationary (i : CommanderState) :
    Dist.mass commanderStationary i =
      Dist.mass (BernoulliLaplaceGeneral.blStationaryDist commanderBLParams)
        (commanderToBL i) := by
  -- `dsimp` (not `simp`) for the concrete `commanderStationary`: its
  -- normalization proof is a heavy `native_decide` over the 50-entry
  -- table, and any `simp` pass that whnfs the `ofFun` structure stalls
  -- past even a 400k-heartbeat budget. `dsimp` only delta-unfolds, so
  -- the `rw` below (whose lemma is `rfl`) matches. The general side
  -- goes through the packaged `mass_blStationaryDist` simp lemma.
  dsimp only [commanderStationary]
  rw [Dist.mass_ofFun (f := commanderStationaryVector)
      commanderStationaryVector_nonneg commanderStationaryVector_total i,
    BernoulliLaplaceGeneral.mass_blStationaryDist commanderBLParams (commanderToBL i)]
  simp only [commanderStationaryVector, BernoulliLaplaceGeneral.blStationary,
    commanderLeftCount, commanderToBL]

/-- The Commander-state ↔ general-macrostate identification as an explicit
`Equiv` (`i ↦ i.val + 1`, with inverse `x ↦ x.val - 1`). -/
def commanderBLEquiv :
    Equiv CommanderState (BernoulliLaplaceGeneral.BLState 99 50 50) :=
  ⟨commanderToBL, blToCommander,
    blToCommander_commanderToBL, commanderToBL_blToCommander⟩

/-- The general first-mode factor and the concrete Commander first-mode
factor are the *same* definition (`1 - N·k/(m·(N-m))`); the two coincide for
all parameters. -/
theorem blFirstModeFactor_eq_firstModeFactor (N m k : Nat) :
    BernoulliLaplaceGeneral.blFirstModeFactor N m k = firstModeFactor N m k :=
  by rfl

/-- The three Commander specializations derived directly from the single
general formula `blFirstModeFactor 99 50 k = 1 - (99·k)/(50·49)`: the
half-deck exchange `k = 25` gives `-1/98`, and the neighboring `k = 24, 26`
give `37/1225` and `-62/1225`. These match the concrete `commanderFirstMode`
values, now as an instance of the general eigenfunction theorem. -/

theorem commanderFirstMode_general_25 :
    BernoulliLaplaceGeneral.blFirstModeFactor 99 50 25 = -(1 / 98 : Rat) := by
  norm_num [BernoulliLaplaceGeneral.blFirstModeFactor]

theorem commanderFirstMode_general_24 :
    BernoulliLaplaceGeneral.blFirstModeFactor 99 50 24 = 37 / 1225 := by
  norm_num [BernoulliLaplaceGeneral.blFirstModeFactor]

theorem commanderFirstMode_general_26 :
    BernoulliLaplaceGeneral.blFirstModeFactor 99 50 26 = -(62 / 1225 : Rat) := by
  norm_num [BernoulliLaplaceGeneral.blFirstModeFactor]

/-- The general first centered eigenfunction theorem, specialized to the
Commander parameters, reads with the concrete first-mode factor: the
`blFirstModeFunc` contraction is exactly `firstModeFactor 99 50 25`. -/
theorem commanderFirstModeFunc (x : BernoulliLaplaceGeneral.BLState 99 50 50) :
    applyFn (BernoulliLaplaceGeneral.blExchangeKernel commanderBLParams)
      (fun y => (y.val : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) x =
      firstModeFactor 99 50 25 *
        ((x.val : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) := by
  -- `blFirstModeFunc` at the Commander parameters gives the same statement
  -- with the factor `blFirstModeFactor 99 50 25`; rename it to the concrete
  -- `firstModeFactor 99 50 25` (they are definitionally the same term).
  have h := BernoulliLaplaceGeneral.blFirstModeFunc commanderBLParams x
  convert h using 1
  -- The hole is `firstModeFactor 99 50 25 * c = blFirstModeFactor 99 50 25 * c`
  -- (the two centered terms `c` are definitionally the same). The factors are
  -- the same rational, so renaming one side to the other closes it.
  rw [(blFirstModeFactor_eq_firstModeFactor 99 50 25).symm]
  rfl
