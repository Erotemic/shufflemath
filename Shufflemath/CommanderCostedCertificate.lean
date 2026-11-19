module

public import Shufflemath.Finite
public import Shufflemath.Cost
public import Shufflemath.ProtocolCertificate
public import Shufflemath.Perturbation
public import Shufflemath.TotalVariation
public import Shufflemath.CommanderPermutation
public import Shufflemath.BernoulliLaplace
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

end Shufflemath
end
