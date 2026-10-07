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
  ⟨99, 50, 50, 25, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Commander states are `Fin 50`; the general macrostate of state `i`
holds `i.val + 1` original-left cards (the `1 <= x <= 50` range of
`BLState 99 50 50`). -/
def commanderToBL (i : CommanderState) :
    BernoulliLaplaceGeneral.BLState 99 50 50 :=
  ⟨i.val + 1, Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt (Fin.val_lt i)⟩

/-- The inverse identification: a general macrostate `x` (with
`1 <= x <= 50`) is Commander state `x - 1`. -/
def blToCommander (x : BernoulliLaplaceGeneral.BLState 99 50 50) :
    CommanderState :=
  ⟨x.val - 1, by
    have hlo : 1 <= x.val := by
      dsimp only [BernoulliLaplaceGeneral.BLState] at x
      simp only [BernoulliLaplaceGeneral.blLo] at x
      norm_num at x
      exact x.1
    have hhi : x.val <= 50 := by
      dsimp only [BernoulliLaplaceGeneral.BLState] at x
      simp only [BernoulliLaplaceGeneral.blHi] at x
      norm_num at x
      exact x.2
    omega⟩

theorem blToCommander_commanderToBL (i : CommanderState) :
    blToCommander (commanderToBL i) = i := by
  simp only [blToCommander, commanderToBL]
  apply Fin.ext
  omega

theorem commanderToBL_blToCommander (x : BernoulliLaplaceGeneral.BLState 99 50 50) :
    commanderToBL (blToCommander x) = x := by
  apply Subtype.ext
  have hlo : 1 <= x.val := by
    dsimp only [BernoulliLaplaceGeneral.BLState] at x
    simp only [BernoulliLaplaceGeneral.blLo] at x
    norm_num at x
    exact x.1
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
    BernoulliLaplaceGeneral.blExchangeKernel, commanderExchangeMatrix,
    commanderLeftCount, commanderToBL]
  rw [transitionWeight_general_eq_commander 99 50 25 (i.val + 1) (j.val + 1)]
  rfl

/-- The Commander hypergeometric stationary distribution and the general
one agree pointwise under the same identification: both are
`C(50, x) * C(49, 50 - x) / C(99, 50)`. -/
theorem commanderStationary_matches_blStationary (i : CommanderState) :
    Dist.mass commanderStationary i =
      Dist.mass (BernoulliLaplaceGeneral.blStationaryDist commanderBLParams)
        (commanderToBL i) := by
  simp only [commanderStationary, BernoulliLaplaceGeneral.blStationaryDist,
    Dist.mass_ofFun, commanderStationaryVector,
    BernoulliLaplaceGeneral.blStationary, commanderLeftCount, commanderToBL]
  norm_num
