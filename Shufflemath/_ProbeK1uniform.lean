module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR

@[expose]
public section

namespace Shufflemath
open BigOperators

/-!
# K1 headline (WIP) — a surjective map with equal-size fibers pushes uniform to uniform.

This is the general lemma the K1 `permImage_uniform` headline reduces to: pushing
`GSR.uniformDist X` through a surjective `f : X → Y` whose fibers all have the same
cardinality `m > 0` gives `GSR.uniformDist Y`.  (Apply with `X = Equiv.Perm (Fin n)`,
`Y = {k-subsets}`, `f (e) = s0.image e` — surjective by `permImage_transitive`, equal
fibers by the conjugation `e ↦ e.trans g`.)

**Status (session 2026-11-25, resynced):**
- `fiberSum_eq` — **PROVEN** (pushforward fiber-sum = fiber-card × unit-mass).
- `fiberCardPartition` — **PROVEN** (`fiberCardPartition_nat` via
  `Finset.card_biUnion` over the disjoint fiber partition + `Fintype.card_subtype`
  + the Rat cast bridge):  `|X| = Σ_y |fiber y|`.
- `map_equalFiber_uniform` — **PROVEN**: a surjective map with all fibers of size
  `m > 0` pushes `GSR.uniformDist X` to `GSR.uniformDist Y`.
  Route: `|X| = |Y|·m` (partition + equal fibers), pointwise mass via
  `Dist.map_mass_eq_univ_fiber` + `fiberSum_eq`, closed by `field_simp`.

Next: apply this in `_ProbeK1comb.lean` — the equal-fibers lemma (conjugation
`e ↦ e.trans g` makes every fiber equinumerous with the reference fiber)
then gives the K1 headline `permImage_uniform`.
-/

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Pushforward-fiber sum = fiber-card × unit-mass (PROVEN). -/
theorem fiberSum_eq (f : X → Y) (y : Y) :
    (Finset.univ : Finset X).sum (fun x => if f x = y then (Fintype.card X : Rat)⁻¹ else 0) =
      (Fintype.card {x : X // f x = y} : Rat) * (Fintype.card X : Rat)⁻¹ := by
  simp [← Finset.sum_filter, Finset.sum_const, Fintype.card_subtype, Finset.card_univ,
    Nat.cast_id, Nat.cast_mul]

/-- `X ≃ Σ y, {x // f x = y}`:  every `x` sits in the fiber of `f x`.  The `right_inv`
    bridges the fiber predicate:  both endpoints of the reconstructed fiber point have
    proof of `f (·) = f p.2.val` / `f (·) = p.1`, and `p.2.2` identifies those.
    (This works for ANY `f` — fibers of unhit `y` are empty and contribute nothing.) -/
protected def fiberSigmaEquiv (f : X → Y) : X ≃ Σ y : Y, {x : X // f x = y} where
  toFun x := ⟨f x, ⟨x, rfl⟩⟩
  invFun p := p.2.val
  left_inv x := by simp
  right_inv p := by
    ext
    · simpa using p.2.2
    · simp

/-! The `f`-fiber of `y`, as a `Finset` (the preimage of `y` in `univ X`). -/
def fiber (f : X → Y) : Y → Finset X :=
  fun y => (Finset.univ : Finset X).filter (fun x => f x = y)

/-! `|X| = Σ_y |fiber y|`, Nat version — the fibers partition `univ X`:
    pairwise disjoint (`card_biUnion`) and their `biUnion` is `univ X`.
    Each fiber's Finset-card bridges to the subtype-card via `Fintype.card_subtype`.
    **PROVEN.** -/
theorem fiberCardPartition_nat (f : X → Y) :
    Fintype.card X = ∑ y : Y, Fintype.card {x : X // f x = y} := by
  haveI hdecX : DecidableEq X := Classical.decEq X
  -- The fibers partition univ X: pairwise disjoint
  have hdisj : ((Finset.univ : Finset Y) : Set Y).PairwiseDisjoint (fiber f) := by
    rintro y _ z _ (hne : y ≠ z)
    by_contra H
    have hne2 := (Finset.not_disjoint_iff : ¬Disjoint (fiber f y) (fiber f z) ↔ ∃ a, a ∈ fiber f y ∧ a ∈ fiber f z).1 H
    obtain ⟨x, hxy, hxz⟩ := hne2
    have hfxy : f x = y := by simpa [fiber] using hxy
    have hfzx : f x = z := by simpa [fiber] using hxz
    exact Ne.symm hne (hfzx.symm.trans hfxy)
  -- univ X = biUnion of the fibers
  have hbi : (Finset.univ : Finset X) = (Finset.univ : Finset Y).biUnion (fiber f) := by
    ext x
    simp only [fiber, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro hx
      exact ⟨f x, by simp, hx, rfl⟩
    · rintro ⟨y, _, hx, _⟩
      exact hx
  calc Fintype.card X
    _ = ((Finset.univ : Finset X) : Finset X).card := by rfl
    _ = ((Finset.univ : Finset Y).biUnion (fiber f)).card := by rw [← hbi]
    _ = ∑ y ∈ (Finset.univ : Finset Y), (fiber f y).card := by rw [Finset.card_biUnion hdisj]
    _ = ∑ y : Y, Fintype.card {x : X // f x = y} := by
      apply Finset.sum_congr rfl
      intro y _
      simpa [fiber] using (Fintype.card_subtype (p := fun x : X => f x = y)).symm

/-! Casting a Fintype nat-sum to `Rat` equals the sum of the casts. -/
theorem fintypeSumNatCast_eq_sumNatCast (g : Y → ℕ) :
    (∑ y : Y, g y : Rat) = ∑ y : Y, (g y : Rat) := by
  simp

/-- `|X| = Σ_y |fiber y|` (every `x` lies in exactly one fiber) — the partition
    count, as a `Rat` identity.  Via `fiberCardPartition_nat` + the cast bridge.
    **PROVEN.** -/
theorem fiberCardPartition (f : X → Y) :
    (Fintype.card X : Rat) = ∑ y : Y, (Fintype.card {x : X // f x = y} : Rat) := by
  have hN := fiberCardPartition_nat f
  rw [← fintypeSumNatCast_eq_sumNatCast (g := fun y => Fintype.card {x : X // f x = y})]
  exact_mod_cast hN

/-- A surjective map whose fibers all have size `m > 0` sends the uniform law on `X`
    to the uniform law on `Y`.  (Surjectivity of `f` is implied by `hFibers` + `0 < m`:
    every `y` has an `m`-element fiber, hence is hit.)  **PROVEN.** -/
theorem map_equalFiber_uniform [Nonempty X] [Nonempty Y] (f : X → Y)
    (m : Nat) (hm : 0 < m)
    (hFibers : ∀ y, Fintype.card {x : X // f x = y} = m) :
    (GSR.uniformDist X).map f = GSR.uniformDist Y := by
  -- |X| = Σ_y |fiber y| = Σ_y m = |Y| * m
  have hXcard : (Fintype.card X : Rat) = (Fintype.card Y : Rat) * (m : Rat) := by
    rw [fiberCardPartition f, Finset.sum_congr rfl (fun y _ => by rw [hFibers y]),
      Finset.sum_const, Finset.card_univ]
    ring
  -- pointwise on `y`
  ext y
  change Dist.mass ((GSR.uniformDist X).map f) y = Dist.mass (GSR.uniformDist Y) y
  -- LHS: the fiber-sum of the uniform masses over `x` with `f x = y`
  have hLHS : Dist.mass ((GSR.uniformDist X).map f) y = (m : Rat) / (Fintype.card X : Rat) := by
    rw [Dist.map_mass_eq_univ_fiber]
    have hsub : ∀ x,
        (if f x = y then Dist.mass (GSR.uniformDist X) x else 0 : Rat) =
        (if f x = y then (Fintype.card X : Rat)⁻¹ else 0) := by
      intro x
      by_cases hf : f x = y
      · rw [if_pos hf, if_pos hf, GSR.mass_uniformDist]
      · rw [if_neg hf, if_neg hf]
    rw [Finset.sum_congr rfl (fun x _ => hsub x), fiberSum_eq f y, hFibers y]
    ring
  rw [hLHS, hXcard]
  -- goal: (m : Rat) / ((card Y) * (m : Rat)) = Dist.mass (GSR.uniformDist Y) y
  rw [GSR.mass_uniformDist]
  have hposY : 0 < (Fintype.card Y : Rat) := by
    rw [Nat.cast_pos]
    exact Fintype.card_pos (α := Y)
  field_simp [hm, hposY]

end Shufflemath
