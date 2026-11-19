module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.Finite
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open CommanderPhysicalExchange
open FiberDisintegration
open CommanderMembershipExchange
open Finset
open Fintype

/-!
## A3 capstone assembly (71st session) — the concrete `hMembershipExchange`

The final A3 discharge is the kernel equality

```
comp (fiberLaw project project_surjective) rawExchangeMembership = comp commanderExchange25 membershipLift
```

(i.e. the `hMembershipExchange` premise of `PhysicalExchangeReduction.intertwining_of_membership_exchange`).
It is a **clean, non-walled assembly** of already-proven lemmas — the f4 count-bridge wall does not
apply here (part (i) already bypassed it via `fintypeCard_subtypeCongr` + `Fintype.card_of_subtype`):

  LHS mass at `m` (count `c`) = (constant on the `c`-fiber, `mu_x_constant_on_countFiber`)
                                = (fiber total, `mu_x_fiberSum` + part (i) `rawExchange_membershipCount_mass`
                                   + `newLeftCount_deckIndependent`) / `membershipFiberCount c`
                              = `transitionWeight 99 50 25 (commanderLeftCount x) c / membershipFiberCount c`
                              = RHS mass (`hMembershipExchange_rhs_mass`).

This probe develops the pieces incrementally (safe: a new file, not in the aggregator, so the
tree stays green).  `mu_x_fiberSum` is the first, self-contained piece.
-/

/-- The post-exchange membership law `mu_x`: push the fiber-uniform law of the source macro
    state `x` forward through the physical (raw) membership-exchange kernel.  This is the
    left-hand side of the A3 `hMembershipExchange` equality. -/
noncomputable def mu_x (x : CommanderState) : Dist Membership :=
    (FiniteKernel.comp (fiberLaw project project_surjective) rawExchangeMembership) x

/-- The `c`-fiber of the marked left-card count. -/
noncomputable def cFiber (c : Nat) : Finset Membership :=
    (Finset.univ : Finset Membership).filter (fun m => membershipCount m = c)

/-- **Fiber-sum lemma.**  Because `mu_x` is constant on each count fiber
    (`mu_x_constant_on_countFiber`), the total mass it puts on the `c`-fiber of a membership
    `m` (count `c = membershipCount m`) is the fiber size `membershipFiberCount c` times the
    point mass at `m`.  Combined with part (i) this recovers the fiber *average* = the BL
    transition weight, the distributional core of the `hMembershipExchange` discharge. -/
theorem mu_x_fiberSum (x : CommanderState) (m : Membership) :
    (∑ m' ∈ cFiber (membershipCount m), Dist.mass (mu_x x) m') =
      (membershipFiberCount (membershipCount m) : Rat) * Dist.mass (mu_x x) m := by
  set c := membershipCount m
  -- every element of the `c`-fiber has mass `mu_x m` (same count => equal mass)
  have hConst (m' : Membership) (hm' : m' ∈ cFiber c) : Dist.mass (mu_x x) m' = Dist.mass (mu_x x) m := by
    simp only [cFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hm'
    exact mu_x_constant_on_countFiber x m' m hm'
  rw [Finset.sum_congr rfl fun m' hm' => hConst m' hm']
  -- the sum of a constant over the fiber is the fiber card times that constant
  simp only [cFiber]
  rw [Finset.sum_const]
  -- nsmul of a Rat by a Nat is the Nat-cast times the value
  rw [nsmul_eq_mul]
  -- the fiber card is `membershipFiberCount c`
  rw [membershipFiber_card c]

end Shufflemath
end
