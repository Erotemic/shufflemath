module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.Gate6Crux
public import Shufflemath.Gate6K1Direct
public import Shufflemath._ProbeK1half

@[expose]
public section

namespace Shufflemath

/-- §3.2 **ideal half, kernel form**: the ideal within-pile riffle
    permutation-action kernel equals "read the membership, then lift uniformly
    inside its fiber":
    `PAK rho99Ideal = comp (deterministic membership) localLift`.
    This is the point-mass ideal half `k1a_riffle_half` (already proven)
    promoted to a *kernel* equality by the generic `kernelOfFiberRows`
    (a fiber-row identity for all `d` determines the kernel) — no new mass
    computation. -/
theorem k1_idealKernel_eq_membershipLift :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal =
      FiniteKernel.comp
        (FiniteKernel.deterministic CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  exact Gate6K1Direct.kernelOfFiberRows
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)
      CommanderMembershipKernels.membership
      CommanderMembershipKernels.localLift
      (fun d => k1a_riffle_half d)

end Shufflemath
