import Shufflemath.GSR
import Shufflemath.FiberLifting
import Mathlib.Tactic

namespace Shufflemath
namespace FiberDisintegration

/-!
# Exact finite disintegration of the uniform law

For any surjection `observe : β → α` of nonempty finite types, define:

* `fiberLaw x`: the uniform law among microscopic states observed as `x`;
* `marginalLaw`: the probability of `x` under the uniform law on `β`.

Both are defined by exact rational weights and fiber cardinalities, not by
sampling or enumerating permutations. The main theorem reconstructs the
uniform microscopic law from this marginal and these conditionals. It does
*not* require equal-size fibers.

The Commander specialization only needs to identify `marginalLaw` with the
existing hypergeometric `commanderStationary`. That is a single explicit
fiber-counting theorem, rather than an unstructured equality of enormous
probability distributions.
-/

variable {α β : Type*}
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable [Nonempty β]

/-- All microscopic states with observation `x`. -/
def fiberSet (observe : β → α) (x : α) : Finset β :=
  Finset.univ.filter (fun b => observe b = x)

/-- Every fiber of a surjection has positive cardinality. -/
theorem fiber_card_pos (observe : β → α)
    (hsurj : Function.Surjective observe) (x : α) :
    0 < (fiberSet observe x).card := by
  apply Finset.card_pos.mpr
  obtain ⟨b, hb⟩ := hsurj x
  exact ⟨b, by simp [fiberSet, hb]⟩

omit [Fintype β] [DecidableEq β] [Nonempty β] in
private theorem sum_if_constant (s : Finset β) (p : β → Prop)
    [DecidablePred p] (c : Rat) :
    (∑ b ∈ s, if p b then c else 0) = ((s.filter p).card : Rat) * c := by
  classical
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

/-- Finite fibers partition the complete microscopic state space. The
proof is a Fubini rearrangement, not a computation of `Fintype.card β`. -/
theorem sum_fiber_card (observe : β → α) :
    (∑ x : α, ((fiberSet observe x).card : Rat)) =
      (Fintype.card β : Rat) := by
  classical
  calc
    (∑ x : α, ((fiberSet observe x).card : Rat)) =
        ∑ x : α, ∑ b : β, if observe b = x then (1 : Rat) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          simpa only [fiberSet, mul_one] using
            (sum_if_constant (Finset.univ : Finset β)
              (fun b => observe b = x) (1 : Rat)).symm
    _ = ∑ b : β, ∑ x : α, if observe b = x then (1 : Rat) else 0 :=
          Finset.sum_comm
    _ = (Fintype.card β : Rat) := by simp

/-- Exact observed marginal of the uniform microscopic law, expressed in
terms of the cardinality of each fiber. -/
noncomputable def marginalLaw (observe : β → α) : Dist α :=
  Dist.ofFun
    (fun x => ((fiberSet observe x).card : Rat) / (Fintype.card β : Rat))
    (by intro x; positivity)
    (by
      have hden : (Fintype.card β : Rat) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
      calc
        (∑ x : α, ((fiberSet observe x).card : Rat) / (Fintype.card β : Rat)) =
          (∑ x : α, ((fiberSet observe x).card : Rat)) /
            (Fintype.card β : Rat) := by rw [Finset.sum_div]
        _ = 1 := by rw [sum_fiber_card]; exact div_self hden)

@[simp]
theorem marginalLaw_mass (observe : β → α) (x : α) :
    Dist.mass (marginalLaw observe) x =
      ((fiberSet observe x).card : Rat) / (Fintype.card β : Rat) := by
  simp [marginalLaw]

/-- Uniform conditional law on the fiber of the observed state `x`.
The positive denominator follows from surjectivity. -/
noncomputable def fiberLaw (observe : β → α)
    (hsurj : Function.Surjective observe) : FiniteKernel α β :=
  fun x => Dist.ofFun
    (fun b => if observe b = x then ((fiberSet observe x).card : Rat)⁻¹ else 0)
    (by intro b; split_ifs <;> positivity)
    (by
      have hnonzero : ((fiberSet observe x).card : Rat) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (fiber_card_pos observe hsurj x))
      calc
        (∑ b : β, if observe b = x then
            ((fiberSet observe x).card : Rat)⁻¹ else 0) =
          ((fiberSet observe x).card : Rat) *
            ((fiberSet observe x).card : Rat)⁻¹ := by
              simpa only [fiberSet] using
                (sum_if_constant (Finset.univ : Finset β)
                  (fun b => observe b = x)
                  (((fiberSet observe x).card : Rat)⁻¹))
        _ = 1 := mul_inv_cancel₀ hnonzero)

@[simp]
theorem fiberLaw_mass (observe : β → α)
    (hsurj : Function.Surjective observe) (x : α) (b : β) :
    Dist.mass (fiberLaw observe hsurj x) b =
      (if observe b = x then ((fiberSet observe x).card : Rat)⁻¹ else 0) := by
  simp [fiberLaw]

/-- Unlike an arbitrary stochastic refinement, this explicitly uniform
conditional law is a left inverse to deterministic observation. -/
theorem fiberLaw_recovers (observe : β → α)
    (hsurj : Function.Surjective observe) :
    FiniteKernel.comp (fiberLaw observe hsurj)
      (FiniteKernel.deterministic observe) = FiniteKernel.identity := by
  classical
  funext x
  ext y
  change Dist.mass
      (FiniteKernel.apply (fiberLaw observe hsurj x)
        (FiniteKernel.deterministic observe)) y =
    Dist.mass (Dist.pointMass x) y
  rw [FiniteKernel.apply_mass, Dist.mass_pointMass]
  by_cases hxy : y = x
  · subst y
    have hterm (b : β) :
        Dist.mass (fiberLaw observe hsurj x) b *
          Dist.mass (FiniteKernel.deterministic observe b) x =
        Dist.mass (fiberLaw observe hsurj x) b := by
      simp only [fiberLaw_mass, FiniteKernel.deterministic, Dist.mass_pointMass]
      by_cases hb : observe b = x <;> simp [hb]
    have hsum :
        (∑ b : β, Dist.mass (fiberLaw observe hsurj x) b *
          Dist.mass (FiniteKernel.deterministic observe b) x) =
        (∑ b : β, Dist.mass (fiberLaw observe hsurj x) b) := by
      apply Finset.sum_congr rfl
      intro b _
      exact hterm b
    rw [hsum]
    simpa using (Dist.sum_mass (fiberLaw observe hsurj x))
  · have hzero (b : β) :
        Dist.mass (fiberLaw observe hsurj x) b *
          Dist.mass (FiniteKernel.deterministic observe b) y = 0 := by
        by_cases hb : observe b = x
        · -- The deterministic observation cannot assign mass to a
          -- different macrostate; avoid unfolding the fiber weights.
          have hyb : y ≠ observe b := by simpa only [hb] using hxy
          have hdet : Dist.mass (FiniteKernel.deterministic observe b) y = 0 := by
            change Dist.mass (Dist.pointMass (observe b)) y = 0
            rw [Dist.mass_pointMass]
            simp [hyb]
          rw [hdet, mul_zero]
        · rw [fiberLaw_mass]
          simp [hb]
    have hsumzero :
        (∑ b : β, Dist.mass (fiberLaw observe hsurj x) b *
          Dist.mass (FiniteKernel.deterministic observe b) y) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      exact hzero b
    rw [hsumzero]
    simp [hxy]

omit [DecidableEq β] in
private theorem uniform_mass (b : β) :
    Dist.mass (GSR.uniformDist β) b = (Fintype.card β : Rat)⁻¹ := by
  simp [GSR.uniformDist]

/-- Main disintegration theorem: mixing the conditional uniform fiber laws
with their (possibly very unequal) relative fiber sizes is *exactly* the
uniform distribution on the complete microscopic state space. -/
theorem marginal_comp_fiber_eq_uniform (observe : β → α)
    (hsurj : Function.Surjective observe) :
    FiniteKernel.apply (marginalLaw observe) (fiberLaw observe hsurj) =
      GSR.uniformDist β := by
  classical
  ext b
  change Dist.mass
      (FiniteKernel.apply (marginalLaw observe) (fiberLaw observe hsurj)) b =
    Dist.mass (GSR.uniformDist β) b
  rw [FiniteKernel.apply_mass, uniform_mass]
  simp only [marginalLaw_mass, fiberLaw_mass]
  have hc : ((fiberSet observe (observe b)).card : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (fiber_card_pos observe hsurj (observe b)))
  calc
    (∑ x : α, ((fiberSet observe x).card : Rat) / (Fintype.card β : Rat) *
        (if observe b = x then ((fiberSet observe x).card : Rat)⁻¹ else 0)) =
      ((fiberSet observe (observe b)).card : Rat) / (Fintype.card β : Rat) *
        ((fiberSet observe (observe b)).card : Rat)⁻¹ := by
          rw [Finset.sum_eq_single (observe b)]
          · simp
          · intro x _ hx
            simp [Ne.symm hx]
          · simp
    _ = (Fintype.card β : Rat)⁻¹ := by
      rw [div_eq_mul_inv]
      calc
        ((fiberSet observe (observe b)).card : Rat) *
            (Fintype.card β : Rat)⁻¹ *
            ((fiberSet observe (observe b)).card : Rat)⁻¹ =
          (Fintype.card β : Rat)⁻¹ *
            (((fiberSet observe (observe b)).card : Rat) *
              ((fiberSet observe (observe b)).card : Rat)⁻¹) := by ring
        _ = (Fintype.card β : Rat)⁻¹ := by rw [mul_inv_cancel₀ hc, mul_one]

/-- A stationary macro law has uniform microscopic disintegration whenever
its point masses agree with the explicit relative fiber cardinalities.
The only remaining obligation for a concrete shuffle is thus a counting
identity, not a 99!-state kernel calculation. -/
theorem stationary_disintegrates_of_mass
    (observe : β → α) (hsurj : Function.Surjective observe)
    (stationary : Dist α)
    (hweights : ∀ x, Dist.mass stationary x =
      ((fiberSet observe x).card : Rat) / (Fintype.card β : Rat)) :
    FiniteKernel.apply stationary (fiberLaw observe hsurj) =
      GSR.uniformDist β := by
  have hstationary : stationary = marginalLaw observe := by
    ext x
    change Dist.mass stationary x = Dist.mass (marginalLaw observe) x
    rw [marginalLaw_mass]
    exact hweights x
  rw [hstationary]
  exact marginal_comp_fiber_eq_uniform observe hsurj

end FiberDisintegration
end Shufflemath
