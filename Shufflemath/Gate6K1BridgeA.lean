module

public import Shufflemath.RhoRoundIdealLift
public import Shufflemath.Gate6Crux
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Mathlib.Tactic

set_option linter.style.haveILetI false

@[expose] public section

namespace Shufflemath
open FiniteDeck
open GSR

/-!
## Gate 6 K1, Bridge A (99/50): the ideal within-pile action as the membership lift kernel

The 99/50 instance of the generic batch-5b bridge (`RhoRoundIdealLift`).  The
permutation-action kernel of the finite-GSR *ideal* within-pile round law
`rho99Ideal` is exactly the Commander kernel "read the membership, then lift
uniformly into its fiber":

  `permutationActionKernel rho99Ideal`
    `= comp (deterministic CommanderMembershipKernels.membership) CommanderMembershipKernels.localLift`

`rho99Ideal` is an `abbrev` for `rhoRoundIdeal 99 50 … (2 ^ 23) …`, so the LHS is the
generic bridge's LHS at `N = 99, m = 50` (by `dsimp`); the RHS is the same fiberLaw
kernel as `comp (deterministic (membership 99 50)) (fiberLaw-kernel)`, which is
`CommanderMembershipKernels.localLift` (`localLift := fiberLaw membership membership_surjective`)
once the frame bridges `membership 99 50 = CommanderMembershipKernels.membership`
and the corresponding surjectivity are applied (both `rfl`).  This is the kernel-law
"batch-5b bridge" side of `K1_oneRound` in the 2026-12-25 K1 plan.  No factorial /
Fintype unrolling.
-/

/-- **K1 Bridge A (99/50).**  The ideal within-pile action of `rho99Ideal` is the Commander
  kernel "read the membership, then lift uniformly into its fiber": the 99/50 instance of
  the generic `rhoRoundIdeal_eq_membershipLift` plus the rfl frame bridges -/
theorem k1_bridgeA :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal =
      FiniteKernel.comp (FiniteKernel.deterministic CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  dsimp only [Gate6Crux.rho99Ideal]
  rw [rhoRoundIdeal_eq_membershipLift 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)]
  simp only [CommanderMembershipKernels.localLift]
  rfl

end Shufflemath
