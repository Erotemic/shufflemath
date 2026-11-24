module

public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open GSR

/-!
Uniform laws on fibers and orbits (Nov 23 Gate 6 plan, "Proof separation").

This module holds the two reusable building blocks that `uniformOrbitLaw N m`
(the Gate 6 headline) instantiates to the membership observation:

- `uniform_map_equiv`: pushing the uniform law on `A` through an equivalence
  `e : A ≃ B` gives the uniform law on `B` (step 1);
- `uniformFiberMapEqFiberLaw`: the uniform law on the fiber
  `{ b // observe b = x }` pushed through `Subtype.val` equals the disintegration
  `fiberLaw observe hsurj x` (step 2).

Both are stated generically (no 99! / Fintype unrolling). The only cardinality
step in each is a `Fintype.card_*` congruence; the pointwise mass is computed via
`Finsupp.mapDomain` — the in-image case via `Finsupp.mapDomain_apply_of_injective`
(mirroring `GSR.map_bijective_uniformDist`) and the not-in-image case via
`Finsupp.mapDomain_of_notMem_range`.
-/

/-- Pushing the uniform law on `A` through an equivalence `e : A ≃ B` gives the
  uniform law on `B`. Every `b : B` has a unique preimage `e.symm b`, so it
  receives mass `1/|A| = 1/|B|` (via `Fintype.card_congr e`); because `e` is onto,
  every point of `B` lies in the image. -/
theorem uniform_map_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (uniformDist A).map e = uniformDist B := by
  classical
  ext b
  -- LHS: push uniform through the bijection e; b's unique preimage is e.symm b
  have hLHS : Dist.mass ((uniformDist A).map e) b = (Fintype.card A : Rat)⁻¹ := by
    simp only [Dist.mass, Convexity.StdSimplex.map]
    have hb : b = e (e.symm b) := Eq.symm (e.apply_symm_apply b)
    rw [hb, Finsupp.mapDomain_apply_of_injective e.injective]
    simp only [uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  -- RHS: uniform on B
  have hRHS : Dist.mass (uniformDist B) b = (Fintype.card B : Rat)⁻¹ := by
    simp only [Dist.mass, uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  change Dist.mass ((uniformDist A).map e) b = Dist.mass (uniformDist B) b
  rw [hLHS, hRHS, Fintype.card_congr e]

/-- The uniform law on the fiber `{ b // observe b = x }` pushed through
  `Subtype.val` is the uniform conditional `fiberLaw observe hsurj x`.
  Both assign `1/|fiber|` to every element of the fiber and `0` elsewhere; the
  fiber's `Fintype` cardinality equals the `Finset.filter` cardinality, so the
  two laws are pointwise identical. The in-fiber case mirrors
  `GSR.map_bijective_uniformDist`; the not-in-fiber case uses
  `Finsupp.mapDomain_of_notMem_range`. -/
theorem uniformFiberMapEqFiberLaw {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (observe : β → α)
    (hsurj : Function.Surjective observe) (x : α)
    [Nonempty β] [Nonempty (Subtype (fun b => observe b = x))] :
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
