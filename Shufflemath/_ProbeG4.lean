module
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.Finite
@[expose] public section

namespace Shufflemath
namespace FiniteDeck
open BernoulliLaplaceGeneral

/-- G4 capstone (WIP skeleton, session 59). The pointwise-mass equality
`mass (comp (UCFM) (SE) x) S = mass (comp (blExchangeKernel) (UCFM) x) S`,
reduced via `funext; unfold comp; ext S`. The three sub-lemmas to fill:
  hLHS : LHS mass at S = transitionNumerator c x.val / (#fiber x * D)
         (via apply_mass_finsupp + the UCFM/SE mass bodies + reachSetFiberCard_eq_yMoves)
  hRHS : RHS mass at S = transitionNumerator x.val c / (#fiber c * D)
         (via apply_mass_finsupp + mass_blExchangeKernel + UCFM mass at S)
  hDB  : #fiber x * transitionNumerator(x.val,c) = #fiber c * transitionNumerator(c,x.val)
         (via detailedBalance + countFiber_blStationary + transitionWeight_def)
  close: rw [hLHS, hRHS, <-hDB]; ring_nf
-/
theorem g4MacroIntertwining (p : ExchangeAdmissible) :
    FiniteKernel.comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p)
    = FiniteKernel.comp (blExchangeKernel p) (uniformCountFiberMembership p) := by
  funext x
  unfold FiniteKernel.comp
  ext S
  change
    Dist.mass ((uniformCountFiberMembership p x).map (subsetExchangeMembershipKernel p)).join S =
      Dist.mass ((blExchangeKernel p x).map (uniformCountFiberMembership p)).join S
  sorry

end FiniteDeck
end Shufflemath
