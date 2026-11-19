module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath._ProbeA3Capstone
public import Shufflemath.Finite
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Perm

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
## The A3 membership-exchange kernel law — `hMembershipExchange`

The concrete kernel equality that discharges the abstract `hMembershipExchange`
hypothesis (F3 item 3).  For every source macrostate `x` and membership `m`, the
raw-exchange pushforward `mu_x x` puts the same mass at `m` as the
`commanderExchange25 ∘ membershipLift` kernel (the Bernoulli--Laplace uniform
resample within the marked-count fiber).

A `Membership` is a 50-subset of the 99-card deck (50 originally-left + 49
originally-right), so its marked count `membershipCount m = (m.1 ∩ leftOrigSet).card`
always satisfies `1 ≤ count ≤ 50` (pigeonhole: a 50-subset of 50 + 49 must contain at
least one left-orig card).  The `ite` feasibility test in `hMembershipExchange_rhs_mass`
is therefore always true, and the law assembles directly from two count-level facts
(both in `Shufflemath._ProbeA3Capstone`, where the A3 count-bridge machinery lives):

* **LHS pointwise** — `mu_x x m` (the raw-exchange pushforward mass at `m`) is the
  total mass of the `membershipCount m`-fiber divided by the fiber size
  (`mu_x_fiberSum`, constant on the fiber), and that fiber total is
  `transitionWeight (commanderLeftCount x) (membershipCount m)`
  (`mu_x_countFiberTotal`, the A3 capstone count bridge).
* **RHS** — `hMembershipExchange_rhs_mass`: the mass of the
  `commanderExchange25 ∘ membershipLift` kernel at `m` is exactly
  `transitionWeight (count x) (count m) / membershipFiberCount (count m)`.

Both sides reduce to the same `transitionWeight / membershipFiberCount`.

(See also the A3 count-bridge count half in `Shufflemath.CommanderA3Count`, and the
cardinality bridge `exchangeChoice_card_eq_transitionDenominator` in
`Shufflemath.CommanderA3ExchangeCard`.)
-/

theorem hMembershipExchange (x : CommanderState) (m : Membership) :
    Dist.mass (mu_x x) m =
      Dist.mass (FiniteKernel.comp commanderExchange25 membershipLift x) m := by
  classical
  have hfeas1 : 1 ≤ membershipCount m := membershipCount_pos m
  have hfeas2 : membershipCount m ≤ 50 := membershipCount_le_50 m
  -- the fiber size is nonzero for a feasible count
  have hpos : 0 < membershipFiberCount (membershipCount m) := by
    unfold membershipFiberCount
    have h50mk : 50 - membershipCount m ≤ 49 := by omega
    exact Nat.mul_pos (Nat.choose_pos hfeas2) (Nat.choose_pos h50mk)
  have hnz : (membershipFiberCount (membershipCount m) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  -- the fiber total, two ways: fiber-size * pointwise  and  transitionWeight
  have hprod : (membershipFiberCount (membershipCount m) : Rat) * Dist.mass (mu_x x) m =
      transitionWeight 99 50 25 (commanderLeftCount x) (membershipCount m) := by
    rw [← (mu_x_countFiberTotal x (membershipCount m))]
    exact (mu_x_fiberSum x m).symm
  -- LHS pointwise mass = transitionWeight / fiber-size
  have hLHS : Dist.mass (mu_x x) m =
      transitionWeight 99 50 25 (commanderLeftCount x) (membershipCount m) /
        (membershipFiberCount (membershipCount m) : Rat) := by
    -- hprod : a * b = c  =>  b = c / a  (a = fiber-size, b = pointwise mass, c = transitionWeight)
    rw [← hprod]
    field_simp [hnz, mul_comm]
  rw [hLHS, hMembershipExchange_rhs_mass]
  -- the RHS ite is feasible (1 ≤ count ≤ 50), so it collapses to its then-branch
  simp [hfeas1, hfeas2]

end Shufflemath
end
