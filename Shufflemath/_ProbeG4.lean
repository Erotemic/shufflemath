module
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.Finite
@[expose] public section

namespace Shufflemath
namespace FiniteDeck
open BernoulliLaplaceGeneral

/- G4 capstone (WIP, session 59). Kernel-composition equality, reduced to the mass
level. KEY recipe (the step that was blocking the hLHS/hRHS decomposition):
  funext x; unfold FiniteKernel.comp; ext S;
  change <explicit `apply`-form mass equality>;   -- `.map.join` (from unfold) is defeq to `apply`
  rw [Shufflemath.FiniteKernel.apply_mass]         -- LHS mass -> ∑_j mass (UCFM x) j * mass (SE j) S
After the `rw`, the LHS is the two-level sum and the RHS is `mass (apply (blExchangeKernel p x)
(UCFM p)) S`. Remaining work (one `sorry` here):
  (a) expand the LHS summands (UCFM/SE mass bodies) + collapse via
      reachSetFiberCard_eq_yMoves / markedCountChange / countFiber_blStationary to
      transitionNumerator c x.val / (#(fiber x) * D);
  (b) RHS: rw [apply_mass] again + mass_blExchangeKernel + UCFM-mass-at-S ->
      transitionNumerator x.val c / (#(fiber c) * D);
  (c) close with the detailedBalance fiber-swap.
-/
theorem g4MacroIntertwining (p : ExchangeAdmissible) :
    FiniteKernel.comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p)
    = FiniteKernel.comp (blExchangeKernel p) (uniformCountFiberMembership p) := by
  funext x
  unfold FiniteKernel.comp
  ext S
  change
    Dist.mass (FiniteKernel.apply (uniformCountFiberMembership p x) (subsetExchangeMembershipKernel p)) S =
      Dist.mass (FiniteKernel.apply (blExchangeKernel p x) (uniformCountFiberMembership p)) S
  rw [Shufflemath.FiniteKernel.apply_mass]
  sorry

end FiniteDeck
end Shufflemath
