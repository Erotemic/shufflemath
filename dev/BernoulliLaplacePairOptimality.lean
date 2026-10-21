import Shufflemath.BernoulliLaplace

namespace Shufflemath
namespace BernoulliLaplace

/-!
# Optional exact two-exchange finite optimality certificate

**Expensive target.** Import/build this file explicitly rather than adding
its 2,401-candidate native decision procedure to the default library build.
The numerical state `x = 50 - k₁` after the *first* exchange from complete
segregation is deterministic: all selected cards from the left are marked,
all selected cards from the right are unmarked.

The `commanderPairTV` objective is therefore the TV distance of the single
`k₂` transition row out of that `x`, evaluated against the exact stationary
hypergeometric vector. This statement is a mathematical objective, and the
finite certificate checks its minimum exactly. The general-to-semantic
Commander kernel bridge for arbitrary exchange sizes is a later target.
-/

/-- Rational TV of the second exchange row from the deterministic post-first-
exchange macrostate, for a candidate ordered pair of legal exchange sizes. -/
def commanderPairTV (k₁ k₂ : Fin 49) : Rat :=
  vectorTV
    (fun y : CommanderState =>
      transitionWeight 99 50 (commanderExchangeSize k₂)
        (50 - commanderExchangeSize k₁) (commanderLeftCount y))
    commanderStationaryVector

/-- The reference `(25,25)` row expression has the existing exact TV value.
Use the single-row computation, independent of the two-step array evaluator. -/
theorem commanderPair25TV_value :
    commanderPairTV exchange25 exchange25 =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  native_decide

/-- Nested finite forall needs an instance at namespace scope for native
execution (a theorem-local instance would be a free variable). -/
private instance pairOptimalityInnerDecidable :
    DecidablePred (fun k₁ : Fin 49 =>
      ∀ k₂ : Fin 49,
        commanderPairTV exchange25 exchange25 ≤ commanderPairTV k₁ k₂) :=
  fun _ => Fintype.decidableForallFintype

/-- Global exact two-exchange optimum in the 49-by-49 candidate class,
for the deterministic-first-row objective. Not the first-mode surrogate.
This may take significantly longer than an ordinary incremental module
build, which is why it is kept as an opt-in target. -/
theorem commanderPair25_minimizes_exact_TV :
    ∀ k₁ k₂ : Fin 49,
      commanderPairTV exchange25 exchange25 ≤ commanderPairTV k₁ k₂ := by
  native_decide

end BernoulliLaplace
end Shufflemath
