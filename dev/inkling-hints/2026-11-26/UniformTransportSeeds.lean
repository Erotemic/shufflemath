module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.InklingNov26

/-! Proposed, uncompiled. A reusable uniform-transport criterion for kernels
between different finite types. This is the G7 arithmetic core. Apply it to
allocation transfers only after proving the outgoing and incoming degrees. -/

/-- A rectangular stochastic kernel with constant column sums transports
uniform to uniform. No symmetry or equal-sized state spaces is assumed. -/
theorem uniform_transport_of_colsum {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq X] [DecidableEq Y]
    (K : FiniteKernel X Y)
    (h : ∀ y, (∑ x : X, Dist.mass (K x) y) =
      (Fintype.card X : Rat) / (Fintype.card Y : Rat)) :
    FiniteKernel.apply (GSR.uniformDist X) K = GSR.uniformDist Y := by
  classical
  ext y
  change Dist.mass (FiniteKernel.apply (GSR.uniformDist X) K) y =
    Dist.mass (GSR.uniformDist Y) y
  rw [FiniteKernel.apply_mass, GSR.mass_uniformDist y]
  have he : (∑ x : X, Dist.mass (GSR.uniformDist X) x * Dist.mass (K x) y) =
    (Fintype.card X : Rat)⁻¹ * ∑ x : X, Dist.mass (K x) y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [GSR.mass_uniformDist]
  rw [he, h]
  have hx : (Fintype.card X : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hy : (Fintype.card Y : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hx, hy]

/-- Counting a biregular relation two ways. Use this instead of factorial
arithmetic to relate the old and new allocation space sizes. -/
theorem biregular_count {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [∀ x y, Decidable (R x y)] (outdeg indeg : Nat)
    (hout : ∀ x, (Finset.univ.filter (R x)).card = outdeg)
    (hin : ∀ y, (Finset.univ.filter (fun x => R x y)).card = indeg) :
    Fintype.card X * outdeg = Fintype.card Y * indeg := by
  classical
  have ha (x : X) : (∑ y : Y, if R x y then (1 : Nat) else 0) = outdeg := by
    rw [← Finset.sum_filter]
    simpa using hout x
  have hb (y : Y) : (∑ x : X, if R x y then (1 : Nat) else 0) = indeg := by
    rw [← Finset.sum_filter]
    simpa using hin y
  calc
    _ = ∑ x : X, ∑ y : Y, if R x y then (1 : Nat) else 0 := by simp [ha]
    _ = ∑ y : Y, ∑ x : X, if R x y then (1 : Nat) else 0 := Finset.sum_comm
    _ = _ := by simp [hb]

end Shufflemath.InklingNov26
