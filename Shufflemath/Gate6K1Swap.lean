module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath._ProbeK1b

@[expose]
public section

namespace Shufflemath

/-!
# Gate 6, K1 — the literal-swap / exchange-membership kernel identity

This is the **swap/membership half** of the Gate-6 K1 one-round-law identity
(`K1_oneRoundLaw_eq_exchangeThenLocalReset`, the batch-4 headline kernel).  It
states that the literal-swap permutation-action kernel, projected to
membership, is exactly the exchange-membership kernel:

```
comp (PAK swapLaw) (deterministic membership) = rawExchangeMembership
```

i.e. "draw a uniform `(L, R)` exchange choice, apply the induced literal swap,
then read the membership" gives the same membership law as "draw a uniform
`(L, R)` choice and compute the post-exchange membership directly."

**Why it is Fintype-free.**  No `Fintype (Equiv.Perm (Fin 99))` (the 99! deck
universe) ever enters a sum or a cardinality:
  * the permutation-action kernel unfolds by `permutationActionKernel_eq_map`
    (definitional: `PAK W d = W.map (fun p => p.trans d)`),
  * the join of the pushed point-mass law collapses by the Fintype-free
    Giry-mondad unit `FiniteKernel.map_det_join_eq_map`
    (`(ν.map (x ↦ deterministic f (g x))).join = (ν.map g).map f`),
  * both sides reduce to `(uniformDist exchangeChoice).map (fun c => …)` — the
    pushforward of the *choice* law (a 25/25 set space, not the 99! space) —
  * function extensionality then lands on `K1a_stmt_only`: membership after the
    swap equals the post-exchange membership, pointwise in the choice.

This identity is the `E` half of the `fuseSwapLocal` composition that assembles
K1:  with the riffle half `PAK rho99Ideal = comp (deterministic membership)
localLift` (`k1a_riffle_half`), the perfect full-round one-step kernel
`comp (PAK rho99Ideal) (PAK swapLaw)` equals the A3 exchange-then-local-reset
kernel `comp rawExchangeMembership localLift = rawExchange`.
-/

theorem k1_swapMembership_eq_exchangeMembership :
    FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
      (FiniteKernel.deterministic CommanderMembershipKernels.membership) =
      CommanderPhysicalExchange.rawExchangeMembership := by
  funext d
  -- comp K L d = ((K d).map L).join, K = PAK swapLaw, L = deterministic membership
  unfold FiniteKernel.comp
  -- PAK swapLaw d = swapLaw.map (fun p => p.trans d)  (definitional, no `act` term)
  rw [FiniteDeck.permutationActionKernel_eq_map]
  -- push the deterministic projection into the pushforward
  rw [Convexity.StdSimplex.map_map]
  -- collapse the join: (swapLaw.map (fun p => pointMass (membership (p.trans d)))).join
  --                = (swapLaw.map (fun p => p.trans d)).map membership
  rw [FiniteKernel.map_det_join_eq_map (Gate6Crux.swapLaw)
      (fun p : Equiv.Perm (Fin 99) => p.trans d)
      (CommanderMembershipKernels.membership)]
  -- LHS = (swapLaw.map (fun p => p.trans d)).map membership
  rw [Convexity.StdSimplex.map_map]
  -- LHS = swapLaw.map (fun p => membership (p.trans d))
  unfold Gate6Crux.swapLaw
  unfold CommanderPhysicalExchange.rawExchangeMembership
  rw [Convexity.StdSimplex.map_map]
  -- Both sides are now (uniformDist exchangeChoice).map (fun c => …)
  refine congrArg (fun f => (GSR.uniformDist CommanderPhysicalExchange.exchangeChoice).map f) ?_
  funext c
  -- membership after the swap = post-exchange membership, pointwise in the choice
  let L := c.1.1
  let hL := CommanderPhysicalExchange.leftCard25 c.1.2
  let R := c.2.1
  let hR := CommanderPhysicalExchange.rightCard25 c.2.2
  let hl := Gate6Crux.exchangeLCard c
  let hr := Gate6Crux.exchangeRCard c
  let b := Gate6Crux.canonicalPairing L hl R hr
  simpa using K1a_stmt_only d L hL R hR b

end Shufflemath
