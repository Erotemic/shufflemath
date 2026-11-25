module

public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.QwenMorningHints

/-!
Candidate proof implementations, NOT compiled by the reviewer. Keep this file out
of the aggregator until each declaration has been checked on the project's actual
Lean/Mathlib toolchain. The first four lemmas have no Fintype assumptions. Do not
unfold concrete allocations, deck distributions, or factorial counts in them.
-/

/-- Construct a quotient row by selecting one representative of the observation.
The row is a Dist by construction; no Vandermonde normalization is needed. -/
noncomputable def quotientRows {X Y : Type*} (f : X → Y)
    (hf : Function.Surjective f) (K : FiniteKernel X X) : FiniteKernel Y Y :=
  fun y => (K (Classical.choose (hf y))).map f

/-- Strong lumpability makes the representative choice irrelevant. -/
theorem quotientRows_at {X Y : Type*} (f : X → Y)
    (hf : Function.Surjective f) (K : FiniteKernel X X)
    (hrows : ∀ x x', f x = f x' → (K x).map f = (K x').map f)
    (x : X) : quotientRows f hf K (f x) = (K x).map f := by
  change (K (Classical.choose (hf (f x)))).map f = (K x).map f
  exact hrows _ x (Classical.choose_spec (hf (f x)))

/-- This is the actual microscopic-to-macroscopic kernel equality, not a
scalar row-sum identity. -/
theorem quotientRows_intertwines {X Y : Type*} (f : X → Y)
    (hf : Function.Surjective f) (K : FiniteKernel X X)
    (hrows : ∀ x x', f x = f x' → (K x).map f = (K x').map f) :
    FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) (quotientRows f hf K) := by
  funext x
  change FiniteKernel.apply (K x) (FiniteKernel.deterministic f) =
    FiniteKernel.apply (Dist.pointMass (f x)) (quotientRows f hf K)
  rw [GSR.apply_deterministic, FiniteKernel.apply_pointMass]
  exact (quotientRows_at f hf K hrows x).symm

/-- Stationarity descends through a strongly lumpable observation. In fact this
works for any stationary microscopic Dist, even on a non-Fintype carrier. -/
theorem stationary_pushforward {X Y : Type*} (f : X → Y)
    (K : FiniteKernel X X) (Q : FiniteKernel Y Y) (mu : Dist X)
    (hmu : FiniteKernel.apply mu K = mu)
    (hQ : FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) :
    FiniteKernel.apply (mu.map f) Q = mu.map f := by
  calc
    _ = FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic f)) Q := by
      rw [GSR.apply_deterministic]
    _ = FiniteKernel.apply mu (FiniteKernel.comp (FiniteKernel.deterministic f) Q) :=
      FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply mu (FiniteKernel.comp K (FiniteKernel.deterministic f)) := by
      rw [hQ]
    _ = FiniteKernel.apply (FiniteKernel.apply mu K) (FiniteKernel.deterministic f) :=
      (FiniteKernel.apply_comp _ _ _).symm
    _ = _ := by rw [hmu, GSR.apply_deterministic]

/-- A symmetric stochastic kernel preserves the uniform law. The stochasticity
is already carried by `Dist`; do not prove an additional column normalization. -/
theorem symmetric_stationary {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (K : FiniteKernel X X)
    (hSym : ∀ x y, Dist.mass (K x) y = Dist.mass (K y) x) :
    FiniteKernel.apply (GSR.uniformDist X) K = GSR.uniformDist X := by
  ext y
  change Dist.mass (FiniteKernel.apply (GSR.uniformDist X) K) y =
    Dist.mass (GSR.uniformDist X) y
  rw [FiniteKernel.apply_mass, GSR.mass_uniformDist y]
  calc
    (∑ x : X, Dist.mass (GSR.uniformDist X) x * Dist.mass (K x) y) =
        ∑ x : X, (Fintype.card X : Rat)⁻¹ * Dist.mass (K y) x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [GSR.mass_uniformDist, hSym x y]
    _ = (Fintype.card X : Rat)⁻¹ * ∑ x : X, Dist.mass (K y) x := by
          rw [Finset.mul_sum]
    _ = _ := by rw [Dist.sum_mass, mul_one]

/-- A small, reusable finite sum interface. Keep all types abstract here. -/
theorem map_mass_on_fiber {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (mu : Dist X) (f : X → Y) (y : Y) :
    Dist.mass (mu.map f) y =
      ∑ x ∈ (Finset.univ.filter (fun x : X => f x = y)), Dist.mass mu x := by
  classical
  rw [Dist.map_mass_eq_univ_fiber, Finset.sum_filter]

/-- The block mass is an edge measure, not a transition probability. -/
noncomputable def blockMass {X Y : Type*} [Fintype X] [DecidableEq Y]
    (mu : Dist X) (K : FiniteKernel X X) (f : X → Y) (y z : Y) : Rat :=
  ∑ x ∈ (Finset.univ.filter (fun x : X => f x = y)),
    ∑ t ∈ (Finset.univ.filter (fun t : X => f t = z)),
      Dist.mass mu x * Dist.mass (K x) t

/-- The quotient joint edge mass equals the total microscopic edge mass
between the two fibers. This is the only sum rearrangement needed. -/
theorem blockMass_eq {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (mu : Dist X) (K : FiniteKernel X X) (f : X → Y) (Q : FiniteKernel Y Y)
    (hQ : ∀ x, (K x).map f = Q (f x)) (y z : Y) :
    Dist.mass (mu.map f) y * Dist.mass (Q y) z = blockMass mu K f y z := by
  classical
  rw [map_mass_on_fiber, Finset.sum_mul]
  unfold blockMass
  apply Finset.sum_congr rfl
  intro x hx
  have hfx : f x = y := (Finset.mem_filter.mp hx).2
  have hr : Dist.mass (Q y) z =
      ∑ t ∈ (Finset.univ.filter (fun t : X => f t = z)), Dist.mass (K x) t := by
    rw [← hfx, ← hQ x, map_mass_on_fiber]
  rw [hr, Finset.mul_sum]

/-- Reversibility of a microscopic chain descends through strong lumpability.
No equal-fiber assumption. In particular, the quotient is usually NOT symmetric. -/
theorem reversible_quotient {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (mu : Dist X) (K : FiniteKernel X X) (f : X → Y) (Q : FiniteKernel Y Y)
    (hQ : ∀ x, (K x).map f = Q (f x))
    (hrev : ∀ x t, Dist.mass mu x * Dist.mass (K x) t =
      Dist.mass mu t * Dist.mass (K t) x) (y z : Y) :
    Dist.mass (mu.map f) y * Dist.mass (Q y) z =
      Dist.mass (mu.map f) z * Dist.mass (Q z) y := by
  classical
  rw [blockMass_eq mu K f Q hQ y z, blockMass_eq mu K f Q hQ z y]
  unfold blockMass
  calc
    _ = ∑ x ∈ (Finset.univ.filter (fun x : X => f x = y)),
        ∑ t ∈ (Finset.univ.filter (fun t : X => f t = z)),
          Dist.mass mu t * Dist.mass (K t) x := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro t _
      exact hrev x t
    _ = _ := Finset.sum_comm

end Shufflemath.QwenMorningHints
