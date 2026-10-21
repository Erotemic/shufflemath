import Shufflemath.CommanderFiberWitness
import Shufflemath.FiberDisintegration
import Shufflemath.PhysicalExchangeReduction

namespace Shufflemath
namespace CommanderFullDeckDisintegration

open CommanderPermutation
open BernoulliLaplace

/-!
# Reduction of the remaining 99-card uniform-law theorem to exact counting

`CommanderFiberWitness.project_surjective` already proves that all 50
macrostate fibers exist as full 99-card permutations.

`FiberDisintegration` now proves the general 99!-state mixture theorem
symbolically; the one remaining Commander-specific premise is the
cardinality-weight identity of the existing hypergeometric stationary law.
There is no enumeration of `Equiv.Perm (Fin 99)` in these proofs.

Importantly, the exact two- and three-exchange full-deck consequences here
refer to the canonical *ideal oracle*. A physical perfect-local exchange
still needs the projected-exchange law, and finite GSR errors still need
a quantitative discrepancy bound.
-/

/-- The exact single outstanding stationary-law counting identity. The
right side is the proportion of complete 99-card permutations containing
`x+1` marked cards in the left pile. -/
def HasCommanderFiberCounts : Prop :=
  ∀ x : CommanderState,
    Dist.mass commanderStationary x =
      ((FiberDisintegration.fiberSet project x).card : Rat) /
        (Fintype.card Deck : Rat)

/-- The universal disintegration theorem specialized to 99-card decks.
This does not assume equal-size fibers, nor a pointwise oracle/physical
kernel equality. -/
theorem commander_uniform_disintegration
    (hcounts : HasCommanderFiberCounts) :
    FiniteKernel.apply commanderStationary
      (FiberDisintegration.fiberLaw project project_surjective) =
    GSR.uniformDist Deck := by
  exact FiberDisintegration.stationary_disintegrates_of_mass
    project project_surjective commanderStationary hcounts

/-- The normalized-per-fiber lift is proved to recover each of the
50 macro counts, with no premise from the caller. -/
theorem normalized_fiber_recovers :
    FiniteKernel.comp
      (FiberDisintegration.fiberLaw project project_surjective)
      (FiniteKernel.deterministic project) = FiniteKernel.identity :=
  FiberDisintegration.fiberLaw_recovers project project_surjective

/-- The hypergeometric fiber-count identity is enough to turn the already
proved exact two-exchange rational result into an exact TV result against
uniform over all 99! permutations. -/
theorem two_oracle_exchanges_uniform_of_counts
    (hcounts : HasCommanderFiberCounts) :
    Dist.tv
      (FiniteKernel.run
        (OracleRefinement.oracleStep project
          (FiberDisintegration.fiberLaw project project_surjective)
          commanderExchange25) 2
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (FiberDisintegration.fiberLaw project project_surjective)))
      (GSR.uniformDist Deck) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  rw [← commander_uniform_disintegration hcounts]
  exact OracleRefinement.commander_oracle_two_exact project
    (FiberDisintegration.fiberLaw project project_surjective)
    normalized_fiber_recovers

/-- The exact full-deck three-exchange identity, conditional only on
the same explicit fiber cardinality formula. -/
theorem three_oracle_exchanges_uniform_of_counts
    (hcounts : HasCommanderFiberCounts) :
    Dist.tv
      (FiniteKernel.run
        (OracleRefinement.oracleStep project
          (FiberDisintegration.fiberLaw project project_surjective)
          commanderExchange25) 3
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (FiberDisintegration.fiberLaw project project_surjective)))
      (GSR.uniformDist Deck) =
      (172379525755689183991816396516567920780192827919620440221147749 /
        6691837923759692633601708022649918108038775216019298375918637677488 : Rat) := by
  rw [← commander_uniform_disintegration hcounts]
  exact OracleRefinement.commander_oracle_three_exact project
    (FiberDisintegration.fiberLaw project project_surjective)
    normalized_fiber_recovers

/-- To specialize the physical-perfect theorem, supply a decomposition
of the uniform-count-to-deck lift through a named-card pile-membership
state, together with the law of exchanging card positions *as observed at
membership level*. This rules out replacing a local shuffle with a global
resampling oracle. -/
theorem two_physical_perfect_exchanges_uniform_of_counts
    (hcounts : HasCommanderFiberCounts)
    {γ : Type*}
    (membership : Deck → γ)
    (membershipLift : FiniteKernel CommanderState γ)
    (localLift : FiniteKernel γ Deck)
    (hLocalRecovers : FiniteKernel.comp localLift
      (FiniteKernel.deterministic membership) = FiniteKernel.identity)
    (hfactor : FiniteKernel.comp membershipLift localLift =
      FiberDisintegration.fiberLaw project project_surjective)
    (rawExchange : FiniteKernel Deck Deck)
    (hMembershipExchange :
      FiniteKernel.comp
        (FiniteKernel.comp
          (FiniteKernel.comp membershipLift localLift) rawExchange)
        (FiniteKernel.deterministic membership) =
      FiniteKernel.comp commanderExchange25 membershipLift) :
    Dist.tv
      (FiniteKernel.run
        (PhysicalExchangeReduction.exchangeThenLocalReset membership
          localLift rawExchange) 2
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (FiberDisintegration.fiberLaw project project_surjective)))
      (GSR.uniformDist Deck) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  have _hMembershipPreserved :=
    PhysicalExchangeReduction.localReset_preserves_membership
      membership localLift hLocalRecovers
  rw [← commander_uniform_disintegration hcounts]
  have hsteps :
      FiniteKernel.comp (FiberDisintegration.fiberLaw project project_surjective)
        (PhysicalExchangeReduction.exchangeThenLocalReset membership
          localLift rawExchange) =
      FiniteKernel.comp commanderExchange25
        (FiberDisintegration.fiberLaw project project_surjective) := by
    rw [← hfactor]
    exact PhysicalExchangeReduction.intertwining_of_membership_exchange
      membershipLift localLift membership rawExchange commanderExchange25
      hMembershipExchange
  rw [FiberLifting.run_tv_eq_macro
    (FiberDisintegration.fiberLaw project project_surjective)
    (FiniteKernel.deterministic project) commanderExchange25
    (PhysicalExchangeReduction.exchangeThenLocalReset membership localLift
      rawExchange) normalized_fiber_recovers hsteps
    (Dist.pointMass commanderSegregatedState) commanderStationary 2]
  exact commander_tv_after_two_semantic

end CommanderFullDeckDisintegration
end Shufflemath
