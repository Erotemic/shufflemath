module

public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
open GSR

/-!
Uniform law on a fiber (Nov 23 Gate 6 plan, "Proof separation", step 2).

This module holds the genuinely new reusable building block that the Gate 6
headline `uniformOrbitLaw N m` composes with the *existing* `GSR.map_bijective_uniformDist`
(step 1, the fact that pushing a uniform law through an equivalence gives the
uniform law on the target):

- `uniformFiberMapEqFiberLaw`: the uniform law on the fiber
  `{ b // observe b = x }` pushed through `Subtype.val` equals the disintegration
  `fiberLaw observe hsurj x` (step 2).

`uniformOrbitLaw` needs step 1 (uniform is invariant under the equiv
`fiberOrbit_equiv`) and step 2 (the resulting fiber uniform, pushed through the
fiber's `Subtype.val`, is the `fiberLaw`). Step 1 is `GSR.map_bijective_uniformDist`
already; this file supplies only step 2. Everything is generic (no 99! /
Fintype unrolling): the only cardinality step is `Fintype.card_subtype`, and the
pointwise mass is computed via `Finsupp.mapDomain` (the in-fiber case via
`mapDomain_apply_of_injective`, mirroring `GSR.map_bijective_uniformDist`, the
not-in-fiber case via `mapDomain_of_notMem_range`).
-/

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
