module

public import Shufflemath.Finite
public import Shufflemath.Cost
public import Shufflemath.ProtocolCertificate
public import Shufflemath.Perturbation
public import Shufflemath.TotalVariation
public import Shufflemath.CommanderPermutation
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFullDeckDisintegration
public import Shufflemath.GSR
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open ProtocolCertificate
open CostedKernel

/-!
## Costed-exchange certificate (F5 skeleton)

F5's acceptance is a theorem with the **model, action class, initial state,
target, terminal TV bound, and cost all explicit**, with any optimization
quantifiers stated separately.  The model-agnostic halves are already in the
library:

* `CostedKernel` + `protocolCost` + `protocolCost_nonneg` (the cost half);
* `ProtocolCertificate.costed_terminalTV_le` / `costedProtocol_certificate`
  (the sufficient TV upper-bound half);
* `ActionKind` (the action alphabet: local riffle / exchange / split-recombine).

This module assembles those halves over one explicit protocol on the
*macro-state* space `CommanderState` (the marked-card count, a small `Fintype`):

* **model** — `CommanderState` (the marked-card count of the left pile);
* **action class** — a card exchange between the two piles (`.exchange`);
* **actual** — two macro count-exchange steps (`commanderExchange25`), each
  assigned one abstract cost unit (total cost `2`);
* **ideal reference** — the Bernoulli--Laplace count transition
  (`commanderExchange25`); at the macro level the physical perfect exchange
  projects to exactly this (F3), so the physical-vs-ideal discrepancy — and
  hence the perturbation budget — vanishes;
* **initial state** — the segregated count (`pointMass commanderSegregatedState`);
* **target** — the uniform law over the macro states (`GSR.uniformDist`).

No minimum-cost / optimality claim is made; `macroCountExchange_costedCertificate`
states the sufficient TV bound with every component named.

**Scope note.**  This is the *macro-level* F5 skeleton.  The **full-deck
finite-GSR** F5 (a non-vanishing budget, over `Deck = Equiv.Perm (Fin 99)`)
is the F4.2-blocked follow-up: the `errorBudget`/Dobrushin machinery computes
over `Finset.univ : Finset Deck` (99! elements) and recurses at elaboration,
the same sub-wall as the F4.2 deck-level GSR lift.  On the macro space the
physical and Bernoulli--Laplace projections coincide (F3), so the budget is
exactly zero and the certificate reduces to the assembled sufficient bound.
-/

/-- The action class of this certificate: a card exchange between the two piles. -/
def f5ActionClass : ActionKind := .exchange

/-- One costed macro count-exchange step (cost 1 unit). -/
noncomputable def f5ExchangeOp : CostedKernel CommanderState :=
  ⟨commanderExchange25, 1, by norm_num⟩

/-- **F5 skeleton certificate.**  Model = the macro-count space; action class =
    exchange; two count-exchange steps (total cost `2`); initial state the
    segregated count; target the uniform macro law.  The terminal TV is bounded
    by the ideal-reference TV plus the weighted perturbation budget (zero here,
    since the physical and Bernoulli--Laplace projections coincide at the macro
    level, by F3).  No minimum-cost / optimality claim is made. -/
theorem macroCountExchange_costedCertificate :
    f5ActionClass = .exchange ∧
    0 ≤ protocolCost [f5ExchangeOp, f5ExchangeOp] ∧
    Dist.tv
      (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
        (kernelOfCosted [f5ExchangeOp, f5ExchangeOp]))
      (GSR.uniformDist CommanderState) ≤
      errorBudget
        [commanderExchange25, commanderExchange25]
        [commanderExchange25, commanderExchange25] +
      Dist.tv
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (compList [commanderExchange25, commanderExchange25]))
        (GSR.uniformDist CommanderState) := by
  refine ⟨rfl, ?_⟩
  exact costedProtocol_certificate
    [f5ExchangeOp, f5ExchangeOp]
    [commanderExchange25, commanderExchange25]
    rfl
    (Dist.pointMass commanderSegregatedState)
    (GSR.uniformDist CommanderState)

/-! The full-deck finite-GSR certificate, recursion-free. -/

/-- One costed physical perfect-exchange "round" (an exchange followed by the
    within-pile local reset) on the full 99-card permutation space. -/
noncomputable def f5PhysOp : CostedKernel Deck :=
  ⟨PhysicalExchangeReduction.exchangeThenLocalReset
      CommanderMembershipKernels.membership
      CommanderMembershipKernels.localLift
      CommanderPhysicalExchange.rawExchange, 1, by norm_num⟩

/-- **F5 full-deck certificate (recursion-free).**  Model = the 99-card
    permutation space `Deck`; action class = exchange; the concrete two-round
    physical perfect-exchange protocol (segregated start → uniform 99! target);
    total cost `2`.  The terminal TV is bounded above by its **exact** value
    (the F3 discharge, `two_physical_perfect_exchanges_uniform_unconditional`),
    stated here without touching the `errorBudget`/Dobrushin machinery, which
    recurses at elaboration over the 99! `Finset.univ`.  No minimum-cost /
    optimality claim is made. -/
theorem f5FullDeck_certificate :
    ActionKind.exchange = .exchange ∧
    0 ≤ protocolCost [f5PhysOp, f5PhysOp] ∧
    Dist.tv
      (FiniteKernel.run
        (PhysicalExchangeReduction.exchangeThenLocalReset
          CommanderMembershipKernels.membership
          CommanderMembershipKernels.localLift
          CommanderPhysicalExchange.rawExchange) 2
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (FiberDisintegration.fiberLaw project project_surjective)))
      (GSR.uniformDist Deck)
      ≤ (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  have hEq :=
    Shufflemath.CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional
  have hCost :=
    protocolCost_nonneg ([f5PhysOp, f5PhysOp] : List (CostedKernel Deck))
  refine ⟨rfl, ⟨hCost, ?_⟩⟩
  exact le_of_eq hEq

/-! Non-degenerate certificate (macro space): a genuine perturbation budget. -/

/-- The ideal reference: send every macro state to the uniform macro law. This
    is a genuinely different kernel from `commanderExchange25`, so the one-step
    discrepancy budget of the physical-vs-ideal pair is nonzero. -/
noncomputable def uniformMacroKernel : FiniteKernel CommanderState CommanderState :=
  fun _ => GSR.uniformDist CommanderState

/-- **Non-degenerate F5 certificate (macro space).**  The physical two-exchange
    terminal TV (segregated start → uniform macro target) is bounded by the
    ideal (uniform-resample) terminal TV plus the exact one-step discrepancy
    budget of the physical-vs-ideal pair.  Because the ideal is a genuinely
    different kernel, the budget is nonzero — a real instance of F5's
    "sufficient TV upper bound."  Over `Fin 50` the budget elaborates without
    the 99! univ recursion.  No optimality claim. -/
theorem f5Nondegenerate_certificate :
    0 ≤ protocolCost [f5ExchangeOp, f5ExchangeOp] ∧
    Dist.tv
      (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
        (kernelOfCosted [f5ExchangeOp, f5ExchangeOp]))
      (GSR.uniformDist CommanderState) ≤
      errorBudget
        [commanderExchange25, commanderExchange25]
        [uniformMacroKernel, uniformMacroKernel] +
      Dist.tv
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
          (compList [uniformMacroKernel, uniformMacroKernel]))
        (GSR.uniformDist CommanderState) :=
  costedProtocol_certificate
    [f5ExchangeOp, f5ExchangeOp]
    [uniformMacroKernel, uniformMacroKernel]
    rfl
    (Dist.pointMass commanderSegregatedState)
    (GSR.uniformDist CommanderState)

end Shufflemath
end
