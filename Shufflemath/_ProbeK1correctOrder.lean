module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.Gate6K1Swap
public import Shufflemath._ProbeGate6K1

@[expose]
public section

namespace Shufflemath

variable (d : Equiv.Perm (Fin 99))

abbrev Deck := Equiv.Perm (Fin 99)

/-! ## Gate-6 K1 — the **correct-order** capstone

    `Gate6Crux.fullRoundIdeal = conv rho99Ideal swapLaw` is the **local-then-swap**
    round: `conv μ W` applies `μ` first, then `W` (`convAsApply` + `act_composition`),
    so `conv rho99Ideal swapLaw` = within-pile riffle first, then the literal swap.

    The direct-K1 milestone and the 2026-12-25 "settled" note specify the physical
    round as **swap-then-local** = `conv swapLaw rho99Ideal`.  In that order the
    ideal side carries the *specific-deck* exchange law all the way through, so the
    residual is the deck-specific exchange-then-local-reset and is provable from the
    already-committed `k1a_riffle_half` + `k1_swapMembership_eq_exchangeMembership`
    — no 99! wall, no K1b extensive counting, no right-pile fiber-bijection crux.

    The opposite-order reduction (`_ProbeK1cap2` / `k1_swapLift_eq_exchangeLift`)
    hits a false-looking asymmetric residual because `k1a_riffle_half` fiber-averages
    the ideal half at a stage that must keep the deck-specific information.
-/

-- The permutation-action kernel of the ideal riffle, at a deck `p`, is exactly the
-- uniform fiber at `membership p` — `k1a_riffle_half` restated at the kernel level
-- (each side is a kernel row, so `apply_pointMass` cancels the point mass).
theorem paK_rho99Ideal_eq_localLift (p : Deck) :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal p =
      CommanderMembershipKernels.localLift (CommanderMembershipKernels.membership p) := by
  rw [← (FiniteKernel.apply_pointMass p (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)),
      k1a_riffle_half p,
      FiniteKernel.apply_pointMass]

-- **Linearity of the ideal riffle.**  Applying the ideal within-pile riffle to any
-- deck-law `μ` gives the uniform fiber of `μ`'s *membership* distribution: the
-- riffle preserves the membership (it only reorders within piles) and uniformizes
-- within each fiber, so `apply μ (PAK rho99Ideal) = apply (μ.map membership) localLift`.
theorem riffleApply (μ : Dist Deck) :
    FiniteKernel.apply μ (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      FiniteKernel.apply (μ.map CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  unfold FiniteKernel.apply
  congr 1
  -- goal: μ.map (PAK rho99Ideal) = (μ.map membership).map localLift
  rw [Convexity.StdSimplex.map_map]
  congr 1
  funext p
  exact paK_rho99Ideal_eq_localLift p

-- The correct-order perfect full round: swap first, then within-pile ideal riffle.
noncomputable def fullRoundIdealCorrect : Dist Deck :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal

/-! **Gate-6 K1 capstone (correct order).**  The pushforward of the state-independent
    perfect full-round law (`conv swapLaw rho99Ideal`, swap-then-riffle) by the
    deterministic deck action `·.act d` equals the exchange-then-local-reset:
    `apply (rawExchangeMembership d) localLift`.  No 99! wall, no K1b counting. -/
theorem k1_capstone_correct :
    fullRoundIdealCorrect.map (fun (x : Deck) => FiniteDeck.act x d) =
      FiniteKernel.apply (CommanderPhysicalExchange.rawExchangeMembership d)
        CommanderMembershipKernels.localLift := by
  dsimp only [fullRoundIdealCorrect]
  rw [convPush_eq_pointMassComp Gate6Crux.swapLaw Gate6Crux.rho99Ideal d]
  rw [← FiniteKernel.apply_comp]
  rw [riffleApply]
  -- goal: apply ((apply (pointMass d) (PAK swapLaw)).map membership) localLift
  --       = apply (rawExchangeMembership d) localLift
  have hswapmap :
      (FiniteKernel.apply (Dist.pointMass d)
          (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)).map
          CommanderMembershipKernels.membership =
        FiniteKernel.apply (Dist.pointMass d) (CommanderPhysicalExchange.rawExchangeMembership) := by
    rw [← FiniteKernel.apply_deterministic_eq_map,
        FiniteKernel.apply_comp,
        k1_swapMembership_eq_exchangeMembership]
  rw [hswapmap]
  -- goal: apply (apply (pointMass d) (rawExchangeMembership)) localLift
  --       = apply (rawExchangeMembership d) localLift
  rw [FiniteKernel.apply_pointMass]

end Shufflemath
