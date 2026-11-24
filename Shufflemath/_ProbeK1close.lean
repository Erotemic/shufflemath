module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath.Gate6K1Direct
public import Shufflemath.Gate6K1Swap
public import Shufflemath._ProbeGate6K1
public import Shufflemath.TotalVariation

@[expose]
public section

namespace Shufflemath

open FiniteKernel

/-!
# Gate 6, K1 — the swap-first (correct-order) one-round-law assembly

One physical round is a uniform 25/25 **exchange** (the `swapLaw` choice)
followed by an **independent 23-riffle within each resulting pile**.  Expressed
as permutation-action kernels, that is the **swap-first** composition

    comp (PAK swapLaw) (PAK rho99Ideal)          -- the correct (swap-then-riffle) order

and this file assembles it, by pure kernel algebra, into the A3
**exchange-then-local-reset** form used by the F3/G3 machinery:

    comp (PAK swapLaw) (PAK rho99Ideal)  =  comp (rawExchangeMembership) localLift.

Two proven halves do the work:
  * **riffle half** `k1_idealKernel_eq_membershipLift` (this file, §3.2):
    `PAK rho99Ideal = comp (deterministic membership) localLift` — a within-pile
    riffle is exactly "read the pile membership, resample the fiber uniformly".
  * **swap half** `Gate6K1Swap.k1_swapMembership_eq_exchangeMembership`:
    `comp (PAK swapLaw) (deterministic membership) = rawExchangeMembership` —
    the literal-swap kernel projected to membership is the exchange-membership
    kernel (Fintype-free: only the 25/25 choice space is ever a carrier).

Then associativity fuses the two halves into the identity above.  This is the
ideal-kernel bridge the 3-round Gate 6 headline reuses: the `q3` residual is the
TV of the three-round chain of exactly this kernel, and the 3-round telescope
compares it (≤ δ1 per round, `gate6_crux_correct`) against the finite full-round
kernel `comp (PAK swapLaw) (PAK rho99Finite)`.

The **riffle-first** (wrong) order `comp (PAK rho99Ideal) (PAK swapLaw)` is
*not* the exchange-then-local-reset law (a within-pile riffle does not commute
with the cross-pile exchange) — that ordering was the source of the historical
"opposite-order" K1 dead-ends and is not pursued here.
-/

-- §3.2  ideal (within-pile riffle) round kernel = membership then lift.
--  From the already-proved point-mass (fiber-row) fact `k1a_riffle_half`
--  (`_ProbeGate6K1`) via the generic `kernelOfFiberRows`.
theorem k1_idealKernel_eq_membershipLift :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal =
      comp (deterministic CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  exact Gate6K1Direct.kernelOfFiberRows
    (H := FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)
    (f := CommanderMembershipKernels.membership)
    (L := CommanderMembershipKernels.localLift)
    k1a_riffle_half

-- §3.4a  K1 assembly, swap-first (correct) order:
--         comp (PAK swapLaw) (PAK rho99Ideal) = comp (rawExchangeMembership) localLift
--  Pure kernel algebra from the two proven halves + associativity.
theorem K1_swapFirst_eq_exchangeLift :
    comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      comp CommanderPhysicalExchange.rawExchangeMembership
        CommanderMembershipKernels.localLift := by
  have hH := k1_idealKernel_eq_membershipLift
  have hK := k1_swapMembership_eq_exchangeMembership
  rw [hH, ← comp_assoc, hK]

end Shufflemath
