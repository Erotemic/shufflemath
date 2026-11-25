module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberWitness
public import Shufflemath.FiberDisintegration
public import Shufflemath.BernoulliLaplace
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.Perturbation
public import Shufflemath.FiniteDeck.Gate6FiniteGSR
public import Shufflemath.CommanderFullDeckDisintegration
public import Shufflemath._ProbeCompListRun

@[expose]
public section

namespace Shufflemath

open CommanderPermutation
open BernoulliLaplace

/-!
## Gate 6 (3-round headline) — sub-lemma B: `TV(finite round³, uniform) ≤ q3`.

The 99-card three-round **finite** kernel
`L = exchangeThenLocalReset membership localLift rawExchange` applied three
times to the fiber-uniform start `μ = apply (pointMass commanderSegregatedState)
(fiberLaw project project_surjective)` is at distance `q3` (hence `≤ q3`)
from the uniform 99! deck.

Two rewrites close it, no equinumerosity / `native_decide` / 99! enumeration:
1. the `compList↔run` bridge `g6_threeRound_compList3_eq_run` turns
   `apply μ (compList [L, L, L])` into `run L 3 μ`;
2. the already-proved `three_physical_perfect_exchanges_uniform_unconditional`
   states `TV (run L 3 μ) (uniform) = q3` (the exact 3-round ideal residual),
   whence `≤ q3` by `q3 ≤ q3`.

This is sub-lemma B of the 3-round Gate-6 headline assembly
(`docs/planning/proof-strategies/2026-12-30-gate6-3round-headline-assembly.md`):
the finite three-round run is TV-`q3` from uniform, so the remaining headline
gap is only the per-round collision budget `3·δ1`.
-/

-- The 99-card 3-round finite kernel: exchange, then perfect-local reset.
noncomputable def g6ThreeRoundFiniteKernel : FiniteKernel Deck Deck :=
  PhysicalExchangeReduction.exchangeThenLocalReset
    CommanderMembershipKernels.membership
    CommanderMembershipKernels.localLift
    CommanderPhysicalExchange.rawExchange

-- The fiber-uniform start: the 49-segregated commander state lifted to its deck fiber.
noncomputable def g6ThreeRoundStart : Dist Deck :=
  FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
    (FiberDisintegration.fiberLaw project project_surjective)

/-- Sub-lemma B: the three-round finite run from the fiber-uniform start is at
    total variation `≤ q3` from the uniform 99! deck. -/
theorem g6_threeRound_finiteRun3_tv_le_q3 :
    Dist.tv (FiniteKernel.apply g6ThreeRoundStart
                 (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                           g6ThreeRoundFiniteKernel]))
            (GSR.uniformDist Deck) ≤ q3 := by
  rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel)
       (μ := g6ThreeRoundStart)]
  dsimp only [g6ThreeRoundFiniteKernel, g6ThreeRoundStart]
  rw [CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional]
  simp [q3]

end Shufflemath
