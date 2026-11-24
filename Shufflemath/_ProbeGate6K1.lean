module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux

@[expose]
public section

namespace Shufflemath

/-!
# Gate 6, batch 4 — K1: the state-dependent one-round law identity (probe stage)

The batch-4 headline `TV(3-round physical chain from μ0, uniform) ≤
q3 + 3·δ1 < 1/1000` is assembled from the three-lemma chain
K1 → K2 → K3.  This probe file develops **K1**:

```
fullRoundIdeal.map (·.trans d) =
  apply (pointMass d) (exchangeThenLocalReset membership localLift rawExchange)
```

for every deck `d` — the pushforward of the state-independent perfect
full-round law (within-pile uniform riffle, then the common literal-swap law,
`conv rho99Ideal swapLaw`) by the deterministic deck action equals applying
the A3 exchange-then-local-reset kernel to the point mass at `d`.

**Bookkeeping (this file):** both sides reduce to `apply (pointMass d) K` for
explicit kernels `K` — LHS to `comp (PAK rho99Ideal) (PAK swapLaw)` (riffle
kernel then swap kernel), RHS to `apply (rawExchangeMembership d) localLift`
(the membership after exchange, then the uniform fiber lift).  The remaining
gap between the two kernels is the per-deck "within-pile orbit = uniform
fiber" uniformity (the general batch-5b bridge), discharged next via the
structural bijection between the within-pile group and the membership fiber.
-/

variable (d : Equiv.Perm (Fin 99))

/-- **The conv-push bookkeeping, generic in `N` (the wall-free core).**
   Pushing the one-step convolution `conv μ W` by the deterministic deck
   action `(·).trans d` equals the point mass at `d` run through the
   composed permutation-action kernels of `μ` and `W`.  Pure Finsupp/kernel
   bookkeeping — `convMapEqApplyMap` (the join–map commutation, already
   proved), `permutationActionKernel_eq_map` (definitional),
   `apply_pointMass`, `apply_comp` — and generic in `N` so no concrete
   99-card law reference ever enters the rewrite search.  Instantiating at
   `N = 99`, `μ = rho99Ideal`, `W = swapLaw` gives the K1 LHS normal form. -/
theorem convPush_eq_pointMassComp {N : Nat} (μ W : Dist (FiniteDeck.Deck N))
    (d : FiniteDeck.Deck N) :
    (FiniteDeck.conv μ W).map (fun p : FiniteDeck.Deck N => FiniteDeck.act p d) =
      FiniteKernel.apply (Dist.pointMass d)
        (FiniteKernel.comp (FiniteDeck.permutationActionKernel μ)
          (FiniteDeck.permutationActionKernel W)) := by
  -- Term-level composition (no rewrite search — the heavy 99! law refs never
  -- enter; μ W d are generic variables):
  --   step 1  convMapEqApplyMap.symm :  conv-push  =  apply (μ.map (·.act·d)) (PAK W)
  --   step 2  ← apply_comp            :  RHS  =  apply (apply (pointMass d) (PAK μ)) (PAK W)
  --   step 3  point-mass bridge       :  apply (μ.map (·.act·d)) (PAK W)
  --                                      =  apply (apply (pointMass d) (PAK μ)) (PAK W)
  --     [apply_pointMass, permutationActionKernel_eq_map — both rfl-level]
  --   step 4  act ≡ trans inside the push (rfl).
  refine (FiniteDeck.convMapEqApplyMap μ W d).symm.trans ?_
  rw [← FiniteKernel.apply_comp]
  congr
  rw [FiniteKernel.apply_pointMass, FiniteDeck.permutationActionKernel_eq_map]
  apply congrArg (fun f => μ.map f)
  funext p
  rfl

/- **LHS normal form (99-card instance).**  The pushforward of the perfect
   full-round law by `(·).trans d` is the point mass at `d` run through the
   two-step kernel "within-pile riffle, then literal swap" — the
   permutation-action kernels of `rho99Ideal` and `swapLaw` composed.
   One instantiation of the generic `convPush_eq_pointMassComp` — the heavy
   99! law references stay opaque (no rewrite search at all). -/
theorem k1_lhs_bookkeeping :
    Gate6Crux.fullRoundIdeal.map (fun x : Equiv.Perm (Fin 99) => FiniteDeck.act x d) =
      FiniteKernel.apply (Dist.pointMass d)
        (FiniteKernel.comp
           (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)
           (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)) := by
  dsimp only [Gate6Crux.fullRoundIdeal]
  exact convPush_eq_pointMassComp Gate6Crux.rho99Ideal Gate6Crux.swapLaw d
/- **RHS normal form.**  Applying the A3 exchange-then-local-reset kernel to
   the point mass at `d` equals: draw the *membership after exchange* from
   `rawExchangeMembership d` (uniform over the 25/25 choices), then lift
   uniformly inside its fiber (`localLift`).  The double local-reset tail
   collapses by associativity + the committed `localLift_preserves_membership`
   (read-the-membership-after-a-fiber-resample is the identity).  Pure
   kernel algebra — no deck-space computation. -/
theorem k1_rhs_bookkeeping :
    FiniteKernel.apply (Dist.pointMass d)
      (PhysicalExchangeReduction.exchangeThenLocalReset
        CommanderMembershipKernels.membership
        CommanderMembershipKernels.localLift
        CommanderPhysicalExchange.rawExchange) =
      FiniteKernel.apply
        (CommanderPhysicalExchange.rawExchangeMembership d)
        CommanderMembershipKernels.localLift := by
  dsimp only [PhysicalExchangeReduction.exchangeThenLocalReset,
      PhysicalExchangeReduction.localReset]
  -- apply (pointMass d) (comp rawExchange L2) = apply (apply (pointMass d) rawExchange) L2
  rw [← FiniteKernel.apply_comp]
  -- apply (pointMass d) rawExchange = rawExchange d
  rw [FiniteKernel.apply_pointMass]
  -- rawExchange d = apply (rawExchangeMembership d) localLift (definitionally,
  -- by the definitions of comp and apply — unfolded in isolation so the
  -- 99!-laden `localLift` body never enters a rewrite pattern)
  have hraw : CommanderPhysicalExchange.rawExchange d =
      FiniteKernel.apply (CommanderPhysicalExchange.rawExchangeMembership d)
        CommanderMembershipKernels.localLift := by
    dsimp only [CommanderPhysicalExchange.rawExchange,
        FiniteKernel.comp, FiniteKernel.apply]
  rw [hraw]
  -- Goal: apply (apply (rawExchangeMembership d) localLift)
  --          (comp (deterministic membership) localLift) =
  --        apply (rawExchangeMembership d) localLift
  rw [FiniteKernel.apply_comp]
  have hassoc :
      FiniteKernel.comp CommanderMembershipKernels.localLift
        (FiniteKernel.comp
          (FiniteKernel.deterministic CommanderMembershipKernels.membership)
          CommanderMembershipKernels.localLift) =
        FiniteKernel.comp
          (FiniteKernel.comp CommanderMembershipKernels.localLift
            (FiniteKernel.deterministic CommanderMembershipKernels.membership))
          CommanderMembershipKernels.localLift := by
    rw [← FiniteKernel.comp_assoc]
  have hident :
      FiniteKernel.comp CommanderMembershipKernels.localLift
        (FiniteKernel.deterministic CommanderMembershipKernels.membership) =
      FiniteKernel.identity :=
    CommanderMembershipKernels.localLift_preserves_membership
  rw [hassoc, hident, FiniteKernel.comp_id_left]

/- **K1 statement** (assembly pending the per-deck orbit-fiber uniformity). -/
theorem K1_oneRoundLaw_eq_exchangeThenLocalReset :
    Gate6Crux.fullRoundIdeal.map (fun x : Equiv.Perm (Fin 99) => FiniteDeck.act x d) =
      FiniteKernel.apply (Dist.pointMass d)
        (PhysicalExchangeReduction.exchangeThenLocalReset
          CommanderMembershipKernels.membership
          CommanderMembershipKernels.localLift
          CommanderPhysicalExchange.rawExchange) := by
  rw [k1_lhs_bookkeeping d, k1_rhs_bookkeeping d]
  -- Both sides are now  apply (pointMass d) K  with explicit kernels;
  -- the remaining gap is the per-deck within-pile orbit = uniform fiber
  -- uniformity (the general batch-5b bridge) plus K1a — next step.
  sorry

end Shufflemath
