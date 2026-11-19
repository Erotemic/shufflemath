module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open FiniteKernel
open Finset
open FinsetCombinatorics

/-- The pull-out-constant, boole-ify a finite sum of a constant times an
    indicator:
    `∑ x ∈ univ, c · 1_{p x} = c · #{x ∈ univ | p x}`.
    A pure `Finset`/`Fintype` helper (no probability) used to close the
    bookkeeping in the uniform-pushforward mass computation. -/
theorem sumConstIte [Fintype X] (c : Rat) (p : X → Prop) [DecidablePred p] :
    (∑ j ∈ univ, c * (if p j then (1 : Rat) else 0)) = c * (#{j ∈ univ | p j} : Rat) := by
  rw [← Finset.mul_sum univ (fun j => (if p j then (1 : Rat) else 0)) c]
  rw [Finset.sum_boole]

/-- **A3 normalization (general).** Pushing the GSR uniform law on a finite
    nonempty type `X` forward by any function `f : X → Y` puts mass
    `(1 / card X) · #{j | f j = y}` at the point `y`: the preimage of `y` under
    `f`, one uniform weight per element.

    This is the normalization half of the A3 membership-exchange assembly:
    `rawExchangeMembership d` is itself the pushforward of the uniform choice law
    by the post-exchange membership function, so the membership-count law and the
    BL transition probability both reduce to this count of a preimage. -/
theorem uniformPushforward_pointMass
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (y : Y) :
    Dist.mass ((GSR.uniformDist X).map f) y =
      (Fintype.card X : Rat)⁻¹ * (#{j ∈ univ | f j = y} : Rat) := by
  classical
  let c : Rat := (Fintype.card X : Rat)⁻¹
  -- pushforward = apply U (deterministic f); apply_mass opens the sum
  rw [← apply_deterministic_eq_map (GSR.uniformDist X) f, apply_mass (GSR.uniformDist X) (deterministic f) y]
  -- each summand: uniform mass c times the deterministic point mass = c · 1_{f j = y}
  have hSum (j : X) : (GSR.uniformDist X).mass j * (deterministic f j).mass y =
      c * (if f j = y then (1 : Rat) else 0) := by
    have hm : (GSR.uniformDist X).mass j = c := GSR.mass_uniformDist j
    rw [hm, deterministic, Dist.mass_pointMass]
    -- c * (if y = f j then 1 else 0) = c * (if f j = y then 1 else 0): ites differ only in direction
    rw [show (if y = f j then (1 : Rat) else 0) = (if f j = y then (1 : Rat) else 0) from
      if_congr (Iff.intro Eq.symm Eq.symm) rfl rfl]
  rw [Finset.sum_congr rfl fun j _ => hSum j]
  -- ∑ j, c · 1_{f j = y} = c · #{j : f j = y}
  have hCount : (∑ j ∈ univ, c * (if f j = y then (1 : Rat) else 0)) =
      c * (#{j ∈ univ | f j = y} : Rat) := by
    rw [← Finset.mul_sum univ (fun j => (if f j = y then (1 : Rat) else 0)) c]
    rw [Finset.sum_boole]
  rw [hCount]

/- **A3 normalization, count-fiber event form (general).** The total mass a
    uniform-pushforward `law = (uniformDist X).map f` puts on a finite event
    `S : Finset Y` is `(1 / card X) · #{x | f x ∈ S}`: each of the `card X`
    equally-weighted source points lands in the preimage of `S` or not.

    The event `S` must live in a *finite* codomain `Y` (here `Membership` in the
    Commander application); the count predicate (`f x ∈ S`) is the event, not the
    (infinite) `Nat` count, which keeps the `Fintype` hypotheses intact.  This is
    the sum-over-the-fiber form of `uniformPushforward_pointMass` and the generic
    engine behind the 99-card exchange's membership-count law. -/
theorem uniformPushforward_eventMass
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (S : Finset Y) :
    (∑ y ∈ S, Dist.mass ((GSR.uniformDist X).map f) y) =
      (Fintype.card X : Rat)⁻¹ * (Fintype.card {x : X // f x ∈ S} : Rat) := by
  classical
  -- the double-count, as a Rat equality, from the committed (Nat) fiberSum
  have hFiber : (∑ y ∈ S, (#{x ∈ univ | f x = y} : Rat)) =
      (Fintype.card {x : X // f x ∈ S} : Rat) := by
    classical
    have hPer (y : Y) : (#{x ∈ univ | f x = y} : ℕ) = Fintype.card {x : X // f x = y} := by
      simpa [Fintype.card_subtype] using rfl
    have hNat : (∑ y ∈ S, #{x ∈ univ | f x = y}) = Fintype.card {x : X // f x ∈ S} := by
      rw [Finset.sum_congr rfl fun y _ => hPer y, ← fiberSum_eq_preimageCard Y f S]
    rw [← Nat.cast_sum, hNat]
  -- the mass sum = (1/#X) · (count of the preimage of the event), by point-mass + double-count
  let c : Rat := (Fintype.card X : Rat)⁻¹
  have hPoint (y : Y) : Dist.mass ((GSR.uniformDist X).map f) y =
      c * (#{x ∈ univ | f x = y} : Rat) := uniformPushforward_pointMass f y
  have h1 : (∑ y ∈ S, Dist.mass ((GSR.uniformDist X).map f) y) =
      ∑ y ∈ S, (c * (#{x ∈ univ | f x = y} : Rat)) :=
    Finset.sum_congr rfl (fun y _ => hPoint y)
  have h2 : (∑ y ∈ S, (c * (#{x ∈ univ | f x = y} : Rat))) =
      c * (∑ y ∈ S, (#{x ∈ univ | f x = y} : Rat)) := by
    simp [Finset.mul_sum, Finset.sum_mul, mul_comm]
  have h3 : c * (∑ y ∈ S, (#{x ∈ univ | f x = y} : Rat)) =
      c * (Fintype.card {x : X // f x ∈ S} : Rat) := by
    rw [hFiber]
  exact h1.trans (h2.trans h3)

end Shufflemath
