module

public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.ReversibleQuotient

/-! ## Reversible-quotient theory, abstractly.

For a symmetric stationary fiber-preserving kernel `K` and a strongly lumpable
observation `f`, this module proves:

* the block-mass identity `blockMass_eq` (the stationary joint edge law
  pushed through the observation factors as the quotient joint edge law),
* the resulting detailed-balance law `reversible_quotient`,
* the uniform pushforward mass formula `uniformPushforward_mass`,
* the fiber-weight balance `fiber_weight_balance`,
* the uniform-fiber lift `fiberLaw_comp_eq_quotient_fiberLaw`: the lifted
  kernel `comp U K` and the quotient-pushed kernel `comp Q U` coincide.

Nothing here mentions allocations, decks, or counts — only abstract `α`/`β`,
`Dist` and kernel algebra. -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- The mass of a pushforward at `y` is the sum of the source masses over the
fiber of `y`. -/
theorem map_mass_on_fiber (mu : Dist β) (f : β → α) (y : α) :
    Dist.mass (mu.map f) y =
      ∑ x ∈ (Finset.univ.filter (fun x : β => f x = y)), Dist.mass mu x := by
  classical
  rw [Dist.map_mass_eq_univ_fiber, Finset.sum_filter]

/-- The block mass: the total microscopic edge mass between the fibers of
`y` and `z`. -/
noncomputable def blockMass (mu : Dist β) (K : FiniteKernel β β) (f : β → α) (y z : α) : Rat :=
  ∑ x ∈ (Finset.univ.filter (fun x : β => f x = y)),
    ∑ t ∈ (Finset.univ.filter (fun t : β => f t = z)),
      Dist.mass mu x * Dist.mass (K x) t

/-- The quotient joint edge mass equals the total microscopic edge mass
between the two fibers.  This is the only sum rearrangement needed. -/
theorem blockMass_eq (mu : Dist β) (K : FiniteKernel β β) (f : β → α) (Q : FiniteKernel α α)
    (hQ : ∀ x, (K x).map f = Q (f x)) (y z : α) :
    Dist.mass (mu.map f) y * Dist.mass (Q y) z = blockMass mu K f y z := by
  classical
  rw [map_mass_on_fiber, Finset.sum_mul]
  unfold blockMass
  apply Finset.sum_congr rfl
  intro x hx
  have hfx : f x = y := (Finset.mem_filter.mp hx).2
  have hr : Dist.mass (Q y) z =
      ∑ t ∈ (Finset.univ.filter (fun t : β => f t = z)), Dist.mass (K x) t := by
    rw [← hfx, ← hQ x, map_mass_on_fiber]
  rw [hr, Finset.mul_sum]

/-- Reversibility of a microscopic chain descends through strong lumpability.
No equal-fiber assumption: the quotient is usually NOT symmetric. -/
theorem reversible_quotient (mu : Dist β) (K : FiniteKernel β β) (f : β → α) (Q : FiniteKernel α α)
    (hQ : ∀ x, (K x).map f = Q (f x))
    (hrev : ∀ x t, Dist.mass mu x * Dist.mass (K x) t =
      Dist.mass mu t * Dist.mass (K t) x) (y z : α) :
    Dist.mass (mu.map f) y * Dist.mass (Q y) z =
      Dist.mass (mu.map f) z * Dist.mass (Q z) y := by
  classical
  rw [blockMass_eq mu K f Q hQ y z, blockMass_eq mu K f Q hQ z y]
  unfold blockMass
  calc
    _ = ∑ x ∈ (Finset.univ.filter (fun x : β => f x = y)),
        ∑ t ∈ (Finset.univ.filter (fun t : β => f t = z)),
          Dist.mass mu t * Dist.mass (K t) x := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro t _
      exact hrev x t
    _ = _ := Finset.sum_comm

/-- The uniform pushforward mass at a fiber: the mass equals the fiber
cardinality over the total microscopic card. -/
theorem uniformPushforward_mass [Nonempty β] (f : β → α) (y : α) :
    Dist.mass ((GSR.uniformDist β).map f) y =
      ((FiberDisintegration.fiberSet f y).card : Rat) / (Fintype.card β : Rat) := by
  classical
  rw [map_mass_on_fiber]
  simp only [GSR.mass_uniformDist, FiberDisintegration.fiberSet]
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Fiber-weight balance: the quotient's detailed-balance ratio is
fiber-weighted.  This is the identity `c_y * Q(y,z) = c_z * Q(z,y)` used to
bridge the two sides of the uniform-fiber lift. -/
theorem fiber_weight_balance [Nonempty β] (f : β → α) (_hf : Function.Surjective f)
    (K : FiniteKernel β β) (Q : FiniteKernel α α)
    (hQ : ∀ x, (K x).map f = Q (f x))
    (hsym : ∀ x t, Dist.mass (K x) t = Dist.mass (K t) x)
    (y z : α) :
    ((FiberDisintegration.fiberSet f y).card : Rat) * Dist.mass (Q y) z =
      ((FiberDisintegration.fiberSet f z).card : Rat) * Dist.mass (Q z) y := by
  classical
  have hrev : ∀ x t, Dist.mass (GSR.uniformDist β) x * Dist.mass (K x) t =
      Dist.mass (GSR.uniformDist β) t * Dist.mass (K t) x := by
    intro x t
    rw [GSR.mass_uniformDist, GSR.mass_uniformDist, hsym x t]
  have h := reversible_quotient (GSR.uniformDist β) K f Q hQ hrev y z
  rw [uniformPushforward_mass f y, uniformPushforward_mass f z] at h
  field_simp at h
  exact h

/-- The uniform-fiber lift: starting from any macrostate `y`, lifting to the
fiber-uniform micro law and applying `K` is exactly the quotient law `Q`
followed by the fiber-uniform lift.  The only hypothesis beyond strong
lumpability is pointwise symmetry of `K`. -/
theorem fiberLaw_comp_eq_quotient_fiberLaw [Nonempty β] [DecidableEq β]
    (f : β → α) (hf : Function.Surjective f)
    (K : FiniteKernel β β) (Q : FiniteKernel α α)
    (hQ : ∀ x, (K x).map f = Q (f x))
    (hsym : ∀ x t, Dist.mass (K x) t = Dist.mass (K t) x) :
    FiniteKernel.comp (FiberDisintegration.fiberLaw f hf) K =
      FiniteKernel.comp Q (FiberDisintegration.fiberLaw f hf) := by
  have hcardpos : ∀ y : α, ((FiberDisintegration.fiberSet f y).card : Rat) ≠ 0 :=
    fun y => by exact_mod_cast Nat.ne_of_gt (FiberDisintegration.fiber_card_pos f hf y)
  funext y
  ext b
  show Dist.mass (FiniteKernel.apply (FiberDisintegration.fiberLaw f hf y) K) b =
    Dist.mass (FiniteKernel.apply (Q y) (FiberDisintegration.fiberLaw f hf)) b
  rw [FiniteKernel.apply_mass_dom, FiniteKernel.apply_mass_dom]
  simp only [FiberDisintegration.fiberLaw_mass]
  have hLsum : (∑ x : β, (if f x = y then ((FiberDisintegration.fiberSet f y).card : Rat)⁻¹ else 0) *
      Dist.mass (K x) b) =
      ((FiberDisintegration.fiberSet f y).card : Rat)⁻¹ *
        ∑ x ∈ (FiberDisintegration.fiberSet f y), Dist.mass (K x) b := by
    have hk : (∑ x : β, (if f x = y then ((FiberDisintegration.fiberSet f y).card : Rat)⁻¹ else 0) * Dist.mass (K x) b) =
        ∑ x ∈ (Finset.univ.filter (fun x : β => f x = y)), ((FiberDisintegration.fiberSet f y).card : Rat)⁻¹ * Dist.mass (K x) b := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = y
      · simp [hx]
      · simp [hx]
    rw [hk, Finset.mul_sum]
    rfl
  have hRsum : (∑ z : α, Dist.mass (Q y) z * (if f b = z then ((FiberDisintegration.fiberSet f z).card : Rat)⁻¹ else 0)) =
      Dist.mass (Q y) (f b) * ((FiberDisintegration.fiberSet f (f b)).card : Rat)⁻¹ := by
    rw [Finset.sum_eq_single_of_mem (f b) (Finset.mem_univ _)]
    · simp
    · intro z _ hz
      rw [ite_eq_right (Ne.symm hz)]
      simp
  rw [hLsum, hRsum]
  have hleft1 : (∑ x ∈ (FiberDisintegration.fiberSet f y), Dist.mass (K x) b) =
      Dist.mass (Q (f b)) y := by
    calc
      _ = ∑ x ∈ (FiberDisintegration.fiberSet f y), Dist.mass (K b) x := by
        exact Finset.sum_congr rfl (fun x _ => hsym x b)
      _ = Dist.mass ((K b).map f) y := (map_mass_on_fiber (K b) f y).symm
      _ = Dist.mass (Q (f b)) y := by rw [hQ b]
  rw [hleft1]
  have h2 := fiber_weight_balance f hf K Q hQ hsym y (f b)
  have h_final : ((FiberDisintegration.fiberSet f y).card : Rat)⁻¹ * Dist.mass (Q (f b)) y =
      Dist.mass (Q y) (f b) * ((FiberDisintegration.fiberSet f (f b)).card : Rat)⁻¹ := by
    field_simp [hcardpos y, hcardpos (f b)]
    exact ((mul_comm _ _).trans h2.symm)
  exact h_final

end Shufflemath.ReversibleQuotient
