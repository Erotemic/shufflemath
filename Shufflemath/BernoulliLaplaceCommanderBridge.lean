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
module

public import Shufflemath.BernoulliLaplace
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceFirstMode
public import Shufflemath.BernoulliLaplaceFiber
public import Shufflemath.Markov
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderFiberCount
public import Shufflemath.Finite
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace CommanderMembershipKernels

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

/-- The first centered eigenfunction equation, read directly on the concrete
Commander kernel `commanderExchange25` over `Fin 50` (no reference to the
general kernel): the `leftCount`-centered observable with mean `2500/99` is
contracted by the factor `-1/98`. This is a pure *transport* of the general
`blFirstModeFunc` along the state identification — the two kernels agree
pointwise (`commanderExchange25_matches_blExchange`) and the pulled-back
centered observable is the general one (`leftCount (blToCommander z) = z.val`) —
not a second combinatorial derivation. -/
theorem commanderFirstModeFunc_concrete (i : CommanderState) :
    applyFn commanderExchange25 (fun j =>
      (commanderLeftCount j : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) i =
      (-(1 / 98 : Rat)) *
        ((commanderLeftCount i : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) := by
  -- Transport the `applyFn` sum from the Commander `Fin 50` states to the
  -- general `BLState 99 50 50` along the `val` bijection.
  have htransport :
      applyFn commanderExchange25 (fun (j : CommanderState) =>
        (commanderLeftCount j : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) i =
      applyFn (BernoulliLaplaceGeneral.blExchangeKernel commanderBLParams)
        (fun (z : BernoulliLaplaceGeneral.BLState 99 50 50) =>
          (z.val : Rat) - (50 : Rat) * (50 : Rat) / (99 : Rat)) (commanderToBL i) := by
    dsimp only [applyFn]
    apply Finset.sum_bij
      (fun (j : CommanderState) (_ : j ∈ Finset.univ) => commanderToBL j)
    · -- the image lies in the general `Finset.univ`
      intro _ _
      simp only [Finset.mem_univ]
    · -- `toBL` is injective (it is the forward map of the equiv)
      intro j1 _ j2 _ h12
      exact commanderBLEquiv.injective h12
    · -- surjective onto the general `Finset.univ`
      intro z _
      simp only [Finset.mem_univ]
      exact ⟨blToCommander z, by simp,
        by simp [commanderToBL_blToCommander]⟩
    · -- the summand: the masses agree and `leftCount (toBL j) = (toBL j).val`
      intro j _
      rw [commanderExchange25_matches_blExchange i j]
      simp only [commanderLeftCount, commanderToBL]
  rw [htransport]
  -- The general eigenfunction at the Commander parameters (G5).
  rw [commanderFirstModeFunc (commanderToBL i)]
  -- `firstModeFactor 99 50 25 = blFirstModeFactor 99 50 25 = -1/98`.
  rw [← blFirstModeFactor_eq_firstModeFactor, commanderFirstMode_general_25]
  -- `leftCount (toBL i) = (toBL i).val`, so the two centered terms agree.
  simp [commanderLeftCount, commanderToBL]

/-- Detailed balance (reversibility) of the Commander quarter-deck kernel:
    the stationary distribution `commanderStationary` and the `commanderExchange25`
    kernel satisfy `π(i) W(i, j) = π(j) W(j, i)` for every pair of macro states.
    This is the general Bernoulli-Laplace `detailedBalance` (the fiber involution
    `(S, A, B) ↦ (S \ A ∪ B, B, A)`) transported across the two bridge theorems.
    Reversibility of the macro kernel is one of the two ingredients of the A3
    membership-exchange discharge. -/
theorem commanderDetailedBalance (i j : CommanderState) :
    Dist.mass commanderStationary i * Dist.mass (commanderExchange25 i) j =
      Dist.mass commanderStationary j * Dist.mass (commanderExchange25 j) i := by
  rw [commanderStationary_matches_blStationary, commanderExchange25_matches_blExchange]
  -- both sides are now the general BL stationary/kernel masses at the
  -- Commander parameters; that is exactly `blDetailedBalance` applied to the
  -- two transported states.
  exact (BernoulliLaplaceGeneral.blDetailedBalance commanderBLParams
      (commanderToBL i) (commanderToBL j))

/-- The Commander stationary (hypergeometric) distribution is a fixed point of the
    `commanderExchange25` kernel: one exchange step leaves it unchanged. This is the
    generic `stationary_of_detailedBalance` applied to `commanderDetailedBalance` —
    the invariance ingredient of the A3 membership-exchange discharge. -/
theorem commanderStationary_is_stationary :
    Stationary commanderStationary commanderExchange25 := by
  exact stationary_of_detailedBalance commanderStationary commanderExchange25
    (fun i j => commanderDetailedBalance i j)

/-- The Commander stationary distribution is fixed by any number of exchange steps
    (iterating the one-step fixed point). -/
theorem commanderStationaryRun (n : Nat) :
    FiniteKernel.run commanderExchange25 n commanderStationary = commanderStationary := by
  exact stationary_run n commanderStationary commanderExchange25 commanderStationary_is_stationary

-- --------------------------------------------------------------------------
-- Membership-level concrete↔general bridge (65th session).
--
-- The 99-card concrete membership machinery of `CommanderMembershipKernels`
-- (`Membership`, `membershipLift`, `membershipCount`, `membershipFiberCount`,
-- `leftOrigSet`) is the instantiation of the arbitrary-finite general
-- `BLRefinement` machinery (`Membership N m`, `uniformCountFiberMembership`,
-- `countInPile`, `countFiberMemb`, `markedSet`) at the Commander parameters
-- `(99, 50, 50)` under the state identification `commanderToBL`. These four
-- identification lemmas, plus the capstone `membershipLift_matches_uniformCountFiber`,
-- are the "uniform-fiber half" of the membership-level bridge: the resample
-- kernel, the count, the fiber size, and the state's marked-count all agree
-- pointwise between the concrete and general definitions.
-- --------------------------------------------------------------------------

/-- The 50 initially-left card identities (`leftOrigSet`) are the marked set at
  the Commander parameters `(99, 50)`: both are the image of `Fin 50` into
  `Fin 99` (cards `0..49`). -/
theorem leftOrigSet_eq_markedSet99_50 (hr : 50 ≤ 99) :
    leftOrigSet = FiniteDeck.markedSet 99 50 hr := by
  rw [FiniteDeck.markedSet, leftOrigSet_eq_image]
  rfl

/-- The marked-card count a membership carries agrees with the general
  `countInPile` at the Commander parameters: both count the intersection of
  the 50-card pile with the initially-left identities. -/
theorem membershipCount_eq_countInPile (m : Membership) :
    membershipCount m =
      (FiniteDeck.countInPile 99 50 50 (Nat.le_of_lt commanderBLParams.hmn)
        commanderBLParams.hrN m).val := by
  unfold membershipCount
  simp only [FiniteDeck.countInPile, FiniteDeck.countInPileVal]
  rw [leftOrigSet_eq_markedSet99_50 commanderBLParams.hrN]

/-- The concrete membership-fiber size agrees with the general
  `countFiberMemb` at the Commander parameters (both are the same
  choose-product). -/
theorem membershipFiberCount_eq_countFiberMemb (x : CommanderState) :
    membershipFiberCount (commanderLeftCount x) =
      (FiniteDeck.countFiberMemb 99 50 50 commanderBLParams.hrN
        (commanderToBL x)).card := by
  unfold membershipFiberCount
  rw [FiniteDeck.countFiberMemb_card (N := 99) (m := 50) (r := 50)
      (hm := Nat.le_of_lt commanderBLParams.hmn)
      (hr := commanderBLParams.hrN) (x := commanderToBL x),
    commanderToBL, commanderLeftCount]

/-- The state's general-marked-count agrees with the concrete
  `commanderLeftCount`: both are `x.val + 1`. -/
theorem commanderToBL_val_eq_commanderLeftCount (x : CommanderState) :
    (commanderToBL x).val = commanderLeftCount x := by
  simp only [commanderToBL, commanderLeftCount]

/-- The concrete `membershipLift` (resample uniformly within the
  `commanderLeftCount` fiber) is, under the state identification
  `commanderToBL`, exactly the general `uniformCountFiberMembership` at the
  Commander parameters: the "uniform-fiber half" of the membership-level
  concrete↔general bridge. The proof reuses the general
  `uniformCountFiberMembership_mass` and the three identification lemmas
  above. -/
theorem membershipLift_matches_uniformCountFiber (x : CommanderState) (m : Membership) :
    Dist.mass (membershipLift x) m =
      Dist.mass (FiniteDeck.uniformCountFiberMembership commanderBLParams
        (commanderToBL x)) m := by
  simp only [membershipLift, Dist.mass_ofFun]
  rw [FiniteDeck.uniformCountFiberMembership_mass,
    membershipCount_eq_countInPile m,
    commanderToBL_val_eq_commanderLeftCount x,
    membershipFiberCount_eq_countFiberMemb x]

