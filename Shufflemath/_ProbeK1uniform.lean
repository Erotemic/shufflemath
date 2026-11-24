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

**Status (session 2026-11-25):**
- `fiberSum_eq` — **PROVEN** (pushforward fiber-sum = fiber-card × unit-mass).
- `map_equalFiber_uniform` — **WIP, 1 `sorry`** = `fiberCardPartition` (the
  `|X| = Σ_y |fiber y|` partition; a self-contained Fintype/Fubini count).  The rest —
  the mass reduction and the final `m / (|Y|·m) = 1/|Y|` — is already written.

Next session: prove `fiberCardPartition` and drop the `sorry`.  Route:
`X ≃ Σ y, {x // f x = y}` (toFun `x ↦ ⟨f x, ⟨x, rfl⟩⟩`, invFun `p ↦ p.2.val`)
+ `Fintype.card_sigma` + `sum_const`;  `right_inv` bridges the fiber-subtype predicate
via `Subtype.ext` using `p.2.2 : f p.2.val = p.1`.
-/

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Pushforward-fiber sum = fiber-card × unit-mass (PROVEN). -/
theorem fiberSum_eq (f : X → Y) (y : Y) :
    (Finset.univ : Finset X).sum (fun x => if f x = y then (Fintype.card X : Rat)⁻¹ else 0) =
      (Fintype.card {x : X // f x = y} : Rat) * (Fintype.card X : Rat)⁻¹ := by
  simp [← Finset.sum_filter, Finset.sum_const, Fintype.card_subtype, Finset.card_univ,
    Nat.cast_id, Nat.cast_mul]

/-- `|X| = Σ_y |fiber y|` (every `x` lies in exactly one fiber).  **WIP.** -/
theorem fiberCardPartition (f : X → Y) :
    (Fintype.card X : Rat) = ∑ y : Y, (Fintype.card {x : X // f x = y} : Rat) := by
  sorry

/-- A surjective map whose fibers all have size `m > 0` sends the uniform law on `X`
    to the uniform law on `Y`.  (Surjectivity of `f` is implied by `hFibers` + `0 < m`:
    every `y` has an `m`-element fiber, hence is hit.)  **WIP: 1 `sorry`**
    (via `fiberCardPartition`.) -/
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
