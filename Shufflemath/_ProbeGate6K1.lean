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
public import Shufflemath._ProbeK1wall

@[expose]
public section

namespace Shufflemath

/-!
# Gate 6, batch 4 — K1: the state-dependent one-round law identity (probe stage)

> **STATUS (2026-12-30): the two bookkeeping lemmas here are promoted, and this
> file's own capstone is DEAD.** `convPush_eq_pointMassComp` and `k1a_riffle_half`
> are now in the real module `Shufflemath.Gate6K1Capstone` (with the correct-order
> capstone `k1_capstone_correct`). The capstone in *this* file,
> `K1_oneRoundLaw_eq_exchangeThenLocalReset` (the 99! `sorry`), is the **opposite
> (local-then-swap) order** and its residual `k1_swapLift_eq_exchangeLift` is **false
> as stated** — it cannot be closed. See
> `docs/planning/proof-strategies/2026-12-30-k1-correct-order-crack.md`. This probe is
> retained only for its dependents (`_ProbeK1half`, `_ProbeK1close`, `_ProbeK1cap2`).

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

/-- **K1a — the riffle half (the batch-5b bridge generalized to an arbitrary
   deck).**  Pushing the ideal within-pile riffle law from deck `d` (the
   permutation-action kernel of `rho99Ideal` applied at `d`) gives exactly the
   uniform fiber lift at `d`'s membership:  both sides carry mass
   `1 / (50!·49!)` at the decks carrying the same membership as `d` and `0`
   elsewhere.  LHS mass: `k1wall_riffle_push_mass_factorial` (the K1-wall
   per-deck orbit-fiber uniformity, `GSR.map_injective_uniform_mass` — the
   99! deck universe never enters a sum).  RHS mass: `localLift_mass` +
   `fiberSet_membership_card` (every membership fiber has `50!·49!` decks).
   Definitional bridges: `rho99Ideal` unfolds to the same `roundEmbedMap`-pushed
   pair law as the K1-wall's `rho99Ideal_pairs`;  `act` is definitionally
   `·.trans ·`. -/
theorem k1a_riffle_half (d : Equiv.Perm (Fin 99)) :
    FiniteKernel.apply (Dist.pointMass d)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      FiniteKernel.apply
        (Dist.pointMass (CommanderMembershipKernels.membership d))
        CommanderMembershipKernels.localLift := by
  ext1
  ext1 X
  rw [FiniteKernel.apply_pointMass, FiniteDeck.permutationActionKernel_eq_map,
      FiniteKernel.apply_pointMass]
  change (Dist.mass (Gate6Crux.rho99Ideal.map (fun p => Equiv.trans p d)) X) =
      (Dist.mass (CommanderMembershipKernels.localLift (CommanderMembershipKernels.membership d)) X)
  rw [CommanderMembershipKernels.localLift_mass,
      CommanderMembershipKernels.fiberSet_membership_card]
  have hBr : Gate6Crux.rho99Ideal = rho99Ideal_pairs := by rfl
  rw [hBr]
  -- The K1-wall mass fact as a *term* (no `rw`, whose normalisation would
  -- pull the pair-law's Fintype-instance wall into whnf);  `simpa` bridges
  -- the definitional gaps (lambda beta, ite condition) without reducing the
  -- `map` term.
  have hmass := k1wall_riffle_push_mass_factorial d X
  simpa using hmass

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
