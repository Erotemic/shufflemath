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
public import Shufflemath._ProbeK1close
public import Shufflemath.TotalVariation
public import Shufflemath.FiniteDeck.Gate6FiniteGSR

@[expose]
public section

namespace Shufflemath

open FiniteKernel

/-!
## Gate 6 (G6.3, 3-round headline) — the ideal-kernel bridge.

The `q3` constant — the ideal three-round residual
(`CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`,
already proven) — is the TV of the three-round chain of the A3 kernel
`exchangeThenLocalReset membership localLift rawExchange` from the fiber-uniform
segregated start, against the uniform `99!` law.

This bridge shows that A3 kernel **is** the correct-order full-round ideal kernel
`comp (PAK swapLaw) (PAK rho99Ideal)` (i.e. `conv swapLaw rho99Ideal` viewed as a
state-dependent `FiniteKernel`, the same object as `Gate6K1Capstone.fullRoundIdealCorrect`
lifted to a kernel).  Hence the 3-round physical headline can be assembled from
the one-round `gate6_crux_correct` (≤ δ1) + `q3` + the standard `n`-step telescope,
on the **correct** (swap-then-riffle) order — no `99!×99!` joint, no
`maxHeartbeats 0`.

The bridge is pure kernel algebra:
  * `exchangeThenLocalReset m ll ex = comp ex (comp (deterministic m) ll)` (defs);
  * `comp ex (comp (det m) ll) = comp (comp ex (det m)) ll` (associativity);
  * `comp rawExchange (deterministic m) = rawExchangeMembership`
    (`rawExchange_membership_pushforward` — the fiber resample preserves
    membership);
  * `comp rawExchangeMembership ll = comp (PAK swapLaw) (PAK rho99Ideal)`
    (`_ProbeK1close.K1_swapFirst_eq_exchangeLift`, the proven K1 assembly).
-/

-- [1]  The `q3` ideal kernel (`exchangeThenLocalReset membership localLift rawExchange`,
--  the A3 exchange-then-local-reset kernel) = the correct-order full-round ideal
--  kernel `comp (PAK swapLaw) (PAK rho99Ideal)`.  Pure kernel algebra: unfold the
--  two defs, regroup by associativity, push the exchange through membership
--  (`rawExchange_membership_pushforward`), and fuse with the K1 swap-first assembly.
theorem g6_3round_idealKernel_eq_fullRound :
    PhysicalExchangeReduction.exchangeThenLocalReset
        CommanderMembershipKernels.membership
        CommanderMembershipKernels.localLift
        CommanderPhysicalExchange.rawExchange =
      comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
  unfold PhysicalExchangeReduction.exchangeThenLocalReset
  unfold PhysicalExchangeReduction.localReset
  rw [← comp_assoc, CommanderPhysicalExchange.rawExchange_membership_pushforward,
      ← K1_swapFirst_eq_exchangeLift]

end Shufflemath

end
