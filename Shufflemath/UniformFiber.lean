module

public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open GSR

/-!
Uniform law on a fiber / orbit (Nov 23 Gate 6 plan, "Proof separation", step 2).

The uniform law on a fiber `{ b // observe b = x }`, pushed through `Subtype.val`,
equals the disintegration `fiberLaw observe hsurj x`. This is the reusable
mechanism that `uniformOrbitLaw N m` (step 3) instantiates to the membership
observation: a bijection (here the fiber's `Subtype.val`) pushes a uniform law
on its domain to the uniform conditional on the image fiber — the same argument
as `GSR.map_bijective_uniformDist`, re-expressed over
`FiberDisintegration.fiberLaw` so it transfers to `membership`.

The proof is `by_cases` on whether `b` lies in the fiber:
- in the fiber, both laws assign `1 / |fiber|`, computed on the LHS by
  `Finsupp.mapDomain_apply_of_injective` (mirroring `GSR.map_bijective_uniformDist`);
- outside the fiber, both assign `0`, computed on the LHS by
  `Finsupp.mapDomain_of_notMem_range`.
The fiber's `Fintype` cardinality equals the `Finset.filter` cardinality
(`Fintype.card_subtype`), so the two mass expressions are identical pointwise.
No 99! / Fintype unrolling: everything is structural in `observe`.
-/

variable {α β : Type*}
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]

/-- The uniform law on the fiber `{ b // observe b = x }` pushed through
  `Subtype.val` is the uniform conditional `fiberLaw observe hsurj x`.
  Both assign `1/|fiber|` to every element of the fiber and `0` elsewhere; the
  fiber's `Fintype` cardinality equals the `Finset.filter` cardinality, so the
  two laws are pointwise identical. The in-fiber case mirrors
  `GSR.map_bijective_uniformDist`; the not-in-fiber case uses
  `Finsupp.mapDomain_of_notMem_range`. -/
theorem uniformFiberMapEqFiberLaw (observe : β → α)
    (hsurj : Function.Surjective observe) (x : α)
    [Nonempty (Subtype (fun b => observe b = x))] :
    (uniformDist (Subtype (fun b => observe b = x))).map Subtype.val =
      FiberDisintegration.fiberLaw observe hsurj x := by
  classical
  have hval : (Subtype.val : (Subtype (fun b => observe b = x)) → β).Injective :=
    Subtype.val_injective
  -- the fiber's Fintype cardinality equals the Finset.filter cardinality
  have hcard : (Fintype.card (Subtype (fun b => observe b = x)) : Rat) =
      ((FiberDisintegration.fiberSet observe x).card : Rat) := by
    simp only [FiberDisintegration.fiberSet, Fintype.card_subtype]
  ext b
  by_cases h : observe b = x
  · -- b is in the fiber: both laws put mass `1/|fiber|` at b
    have hLHS : Dist.mass ((uniformDist (Subtype (fun b => observe b = x))).map Subtype.val) b =
        ((Fintype.card (Subtype (fun b => observe b = x)) : Rat)⁻¹) := by
      simp only [Dist.mass, Convexity.StdSimplex.map]
      have hb : b = (Subtype.val : (Subtype (fun b => observe b = x)) → β) (⟨b, h⟩) := rfl
      rw [hb, Finsupp.mapDomain_apply_of_injective hval]
      simp only [uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
    have hRHS : Dist.mass (FiberDisintegration.fiberLaw observe hsurj x) b =
        ((FiberDisintegration.fiberSet observe x).card : Rat)⁻¹ := by
      simp only [FiberDisintegration.fiberLaw_mass]
      split_ifs
      · rfl
    change Dist.mass ((uniformDist (Subtype (fun b => observe b = x))).map Subtype.val) b =
             Dist.mass (FiberDisintegration.fiberLaw observe hsurj x) b
    rw [hLHS, hRHS, hcard]
  · -- b is not in the fiber: both laws put mass `0` at b
    have hLHS : Dist.mass ((uniformDist (Subtype (fun b => observe b = x))).map Subtype.val) b = 0 := by
      simp only [Dist.mass, Convexity.StdSimplex.map]
      have hnotmem : b ∉ Set.range (Subtype.val : (Subtype (fun b => observe b = x)) → β) := by
        rintro ⟨⟨a, hpa⟩, rfl⟩
        exact h hpa
      rw [Finsupp.mapDomain_of_notMem_range _ b hnotmem]
    have hRHS : Dist.mass (FiberDisintegration.fiberLaw observe hsurj x) b = 0 := by
      simp only [FiberDisintegration.fiberLaw_mass]
      split_ifs
      · rfl
    change Dist.mass ((uniformDist (Subtype (fun b => observe b = x))).map Subtype.val) b =
             Dist.mass (FiberDisintegration.fiberLaw observe hsurj x) b
    rw [hLHS, hRHS]

end Shufflemath
