module

public import Shufflemath.FiniteDeck.BLDisintegration
public import Shufflemath.FiniteDeck.A3KernelLaw
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceFiber
public import Shufflemath.Dobrushin
public import Shufflemath.Markov
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.PhysicalExchangeReduction
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

variable (p : BernoulliLaplaceGeneral.ExchangeAdmissible)

/-- **TV < 0.001 pipeline, decay bound.**  The total variation between `n` physical
    perfect-exchange steps (perfect-local resample around the physical exchange) run
    from a macrostate `x0` on the full deck and the uniform distribution on the whole
    deck is at most the `n`-th power of the Dobrushin contraction coefficient of the
    Bernoulli-Laplace macro chain.

    Composition of already-proved facts:
      (1) `two_physical_perfect_exchanges_uniform_deck` — the physical deck-TV equals
          the BL macro-chain `n`-step TV toward its stationary law;
      (2) `blStationaryRun` — the stationary law is a fixed point of the `n`-step run,
          so the target is also an `n`-step run (enabling the contraction);
      (3) `dobrushin.run_contraction` — `TV(run K n μ, run K n ν) ≤ d(K)^n · TV(μ,ν)`;
      (4) `Dist.tv_le_one` — `TV(pointMass x0, blStationary) ≤ 1`, so `d^n · TV ≤ d^n`.

    Hence the whole physical-exchange-to-uniform discrepancy is bounded by `d^n`,
    where `d = dobrushinCoeff (blExchangeKernel p)`.  The 99-card TV < 0.001 headline
    is then the concrete instance of this bound plus a verified `d < 1` and a concrete
    `n` with `d^n < 1/1000`. -/
theorem physicalExchange_dobrushinDecay
    [hNonempty : Nonempty (BernoulliLaplaceGeneral.BLState p.N p.m p.r)]
    (x0 : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (n : Nat) :
    Dist.tv
      (FiniteKernel.run
          (PhysicalExchangeReduction.exchangeThenLocalReset
            (membership p.N p.m (Nat.le_of_lt p.hmn))
            (localLift p.N p.m (Nat.le_of_lt p.hmn)) (rawExchange p)) n
          (FiniteKernel.apply (Dist.pointMass x0)
            (FiniteKernel.comp (uniformCountFiberMembership p)
              (localLift p.N p.m (Nat.le_of_lt p.hmn)))))
      (GSR.uniformDist (Deck p.N))
    ≤ Dobrushin.dobrushinCoeff (BernoulliLaplaceGeneral.blExchangeKernel p) ^ n := by
  -- (1) physical deck-TV = BL macro-chain n-step TV -> stationary
  rw [two_physical_perfect_exchanges_uniform_deck p x0 n]
  -- (2) the stationary target is a fixed point of the n-step run
  rw [← BernoulliLaplaceGeneral.blStationaryRun p n]
  -- (3) Dobrushin n-step contraction
  have hcontra : Dist.tv
      (FiniteKernel.run (BernoulliLaplaceGeneral.blExchangeKernel p) n (Dist.pointMass x0))
      (FiniteKernel.run (BernoulliLaplaceGeneral.blExchangeKernel p) n (BernoulliLaplaceGeneral.blStationaryDist p))
      ≤ Dobrushin.dobrushinCoeff (BernoulliLaplaceGeneral.blExchangeKernel p) ^ n *
        Dist.tv (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p) :=
    Dobrushin.run_contraction (BernoulliLaplaceGeneral.blExchangeKernel p) n
      (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p)
  -- (4) TV(pointMass, stationary) ≤ 1, and dobrushinCoeff ^ n ≥ 0
  have hTV : Dist.tv (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p) ≤ 1 :=
    Dist.tv_le_one _ _
  have hPowNN : 0 ≤ Dobrushin.dobrushinCoeff (BernoulliLaplaceGeneral.blExchangeKernel p) ^ n :=
    pow_nonneg (Dobrushin.dobrushinCoeff_nonneg (BernoulliLaplaceGeneral.blExchangeKernel p)) n
  have hFinal : Dobrushin.dobrushinCoeff (BernoulliLaplaceGeneral.blExchangeKernel p) ^ n *
      Dist.tv (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p)
      ≤ Dobrushin.dobrushinCoeff (BernoulliLaplaceGeneral.blExchangeKernel p) ^ n := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left hTV hPowNN
  exact hcontra.trans hFinal

end FiniteDeck
end Shufflemath
