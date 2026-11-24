module

public import Shufflemath.UniformOrbitLaw
public import Shufflemath.GSRDeckRound
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Shufflemath.GSRSegHeadline
public import Mathlib.Tactic

set_option linter.style.haveILetI false

@[expose] public section

namespace Shufflemath
open FiniteDeck
open GSR

/-!
## Batch-5b bridge: the ideal within-pile round law as the membership lift kernel

Generalization of the 99/50 batch-5b bridge.  The finite-GSR *ideal* within-pile
round law `rhoRoundIdeal N m` (push the product of the two within-pile uniform
permutation laws through the pile-embedding `roundEmbedMap`, then act on the deck)
satisfies, for every deck `d`,

  `permutationActionKernel (rhoRoundIdeal N m …) d`
    `= FiberDisintegration.fiberLaw (membership N m …) (membership_surjective N m …) (membership N m … d)`

— i.e. the within-pile orbit of `d` is exactly its membership fiber, uniformly.  This
is the direct kernel-level instantiation of `UniformOrbitLaw.uniformOrbitLaw`
(within-pile orbit = membership fiber law) and is the batch-5b bridge that
`K1_oneRound` assembles from: at `N = 99, m = 50` it is the
`comp (deterministic membership) localLift` side of the K1 kernel law, the
membership side of which is definitionally the Commander `Membership` (see the
2026-12-25 K1 plan, "Batch-5b bridge (the key step)").

No factorial or `Fintype` unrolling: the only uniform-distribution step is the
generic `GSRSegHeadline.distProduct_uniform_is_uniformProd`, and the orbit step is
`UniformOrbitLaw` (itself proved without unrolling the deck).

The 99-card Commander framing (the K1 capstone) needs, on top of this generic
statement, the definitional frame bridges
`membership 99 50 = CommanderMembershipKernels.membership` and
`rho99Ideal = rhoRoundIdeal 99 50 …`, both of which are `rfl` (verified).
-/

/-- **Batch-5b bridge (generic).**  The ideal within-pile round law `rhoRoundIdeal N m`
  acting on a deck equals the kernel "read the membership, then lift uniformly into its
  fiber" (the fiberLaw kernel): both sides push the within-pile orbit, which
  `uniformOrbitLaw` identifies with the membership fiber law.  No factorial / Fintype
  unrolling — the product-uniform step is the generic `distProduct_uniform_is_uniformProd`. -/
theorem rhoRoundIdeal_eq_membershipLift (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m) (hRpos : 0 < N - m)
    (a : Nat) (ha : 0 < a) :
    permutationActionKernel (rhoRoundIdeal N m hm hLpos hRpos a ha) =
      FiniteKernel.comp (FiniteKernel.deterministic (membership N m hm))
        (fun x : Membership N m =>
          FiberDisintegration.fiberLaw (membership N m hm) (membership_surjective N m hm) x) := by
  classical
  funext (d : Deck N)
  let f := membership N m hm
  -- LHS: the ideal within-pile action on d is the uniform membership fiber at d's membership.
  have hLHS : (permutationActionKernel (rhoRoundIdeal N m hm hLpos hRpos a ha)) d =
      FiberDisintegration.fiberLaw f (membership_surjective N m hm) (f d) := by
    rw [permutationActionKernel_eq_map, rhoRoundIdeal]
    haveI : Nonempty (Equiv.Perm (Fin m)) := ⟨Equiv.refl (Fin m)⟩
    haveI : Nonempty (Equiv.Perm (Fin (N - m))) := ⟨Equiv.refl (Fin (N - m))⟩
    rw [distProduct_uniform_is_uniformProd]
    rw [Convexity.StdSimplex.map_map (uniformDist (MOrbit N m))
        (roundEmbedMap N m hm) (fun p => Equiv.trans p d)]
    simpa only [roundEmbedMap, act, Dist] using uniformOrbitLaw N m hm d
  rw [hLHS]
  -- RHS: (comp (deterministic f) (fiberLaw-kernel)) d = apply (pointMass (f d)) L = L (f d).
  dsimp only [FiniteKernel.comp, FiniteKernel.deterministic]
  change FiberDisintegration.fiberLaw f (membership_surjective N m hm) (f d) =
      FiniteKernel.apply (Dist.pointMass (f d))
        (fun x : Membership N m => FiberDisintegration.fiberLaw (membership N m hm) (membership_surjective N m hm) x)
  rw [FiniteKernel.apply_pointMass]
  -- both sides are now `fiberLaw (membership N m hm) (membership_surj) (f d)` (`f` unfolds) -> rfl

end Shufflemath
