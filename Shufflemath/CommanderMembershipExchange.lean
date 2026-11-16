module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderMembershipExchange

/-!
# The `hMembershipExchange` kernel equality (F3 item 3 / Spec C, A3)

The two-layer physical-perfect capstone
`two_physical_perfect_exchanges_uniform_of_counts`
(`Shufflemath.CommanderFullDeckDisintegration`) takes the membership-exchange law
`hMembershipExchange` as a hypothesis.  This module **proves** that law for the
concrete Commander objects.

The 3a reduction (`hMembershipExchange_lhs_reduces`) already shows the LHS is the
uniform `project`-fiber deck law pushed through the membership-level exchange:

    comp (fiberLaw project) rawExchangeMembership

so the target is

    comp (fiberLaw project project_surjective) rawExchangeMembership
      = comp commanderExchange25 membershipLift                                    (A3)

Both sides are kernels `CommanderState → Membership`.  A source macro state `x`
has count `c_x = commanderLeftCount x`; every deck in the `x`-fiber has
membership count `c_x` (`membershipCount_of_project`), and `rawExchangeMembership`
pushes each such deck through a uniform 25-25 position exchange.

The proof has two parts, matching F3 item 3's two halves:
* **counting (part (i))** — the *count* of the post-exchange membership,
  averaged over the uniform `x`-fiber and the uniform 25-25 choice, is exactly
  the `commanderExchange25` transition from `c_x`.
* **within-count uniformity (part (ii))** — conditioned on landing on count `c`,
  the membership is *uniform* over the `c`-fiber, because the exchange law is
  equivariant under the deck-relabeling group (`newLeftCards_conjugate`) and that
  group acts transitively on each count-fiber (`membershipFiber_transitive`).

`comp commanderExchange25 membershipLift` is precisely "transition the count by
`commanderExchange25`, then lift uniformly to the membership fiber," which is the
sum of those two parts.
-/

open BernoulliLaplace
open CommanderMembershipKernels
open CommanderPhysicalExchange
open FiberDisintegration

/-
## Next (A3 part (i), counting): the count-level projection

Prove

    comp (comp (fiberLaw project project_surjective) rawExchangeMembership)
      (deterministic membershipCount) =
    comp commanderExchange25 (deterministic commanderLeftCount)

by reducing the fiber-average of `newLeftOriginalCount_eq` to the hypergeometric
`transitionWeight` (the counting core, cf. `fiberSum_eq_overlap`).
-/

end CommanderMembershipExchange
end Shufflemath
