/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Batch 5b headline: `rhoRoundIdeal 99 50 … 1 … = localLift segMembership`.
-- The one-round ideal (uniform) deck law is the perfect local law at the segregated
-- membership: both are the uniform law over the same within-pile fiber (card 50!·49!).
-- The proof stays on the *deck* side and uses only pre-compiled lemmas, so it avoids
-- the 99!-enumeration whnf wall (the membership fiber = the left-card fiber by
-- `membership_iff_leftCards`, a set equivalence, not a 99! computation).

module

public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.GSRSegMembership
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.GSRDeckRound
public import Mathlib.Tactic

namespace Shufflemath

open GSR
open FiniteDeck
open FiberDisintegration
open CommanderMembershipKernels
open scoped Nat

private abbrev Y := Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49)
-- The left-card fiber at the identity deck, as a Fintype (card 50!·49!).
private abbrev paramFiber :=
    {e : Deck 99 // leftCards 99 50 hm5099 e = leftCards 99 50 hm5099 (Equiv.refl (Fin 99))}

-- 1. The product of the two within-pile uniform laws is the uniform law on the pair product.
private theorem distProduct_uniforms_eq_uniform :
    distProduct (GSR.uniformDist (Equiv.Perm (Fin 50))) (GSR.uniformDist (Equiv.Perm (Fin 49))) =
      GSR.uniformDist Y := by
  haveI : DecidableEq (Equiv.Perm (Fin 50)) := inferInstance
  haveI : DecidableEq (Equiv.Perm (Fin 49)) := inferInstance
  haveI : DecidableEq Y := inferInstance
  haveI : Nonempty (Equiv.Perm (Fin 50)) := ⟨Equiv.refl (Fin 50)⟩
  haveI : Nonempty (Equiv.Perm (Fin 49)) := ⟨Equiv.refl (Fin 49)⟩
  haveI : Nonempty Y := ⟨(Equiv.refl (Fin 50), Equiv.refl (Fin 49))⟩
  haveI : Fintype (Equiv.Perm (Fin 50)) := inferInstance
  haveI : Fintype (Equiv.Perm (Fin 49)) := inferInstance
  haveI : Fintype Y := inferInstance
  ext p
  simp only [distProduct, Dist.ofFun, Dist.mass_ofFun, mass_uniformDist,
    Finsupp.coe_equivFunOnFinite_symm]
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  <;> norm_num

-- 2. `roundEmbedMap 99 50 hm5099` is the `val` of the fiber-orbit bijection at the identity deck.
private theorem roundEmbedMap_eq_val :
    roundEmbedMap 99 50 hm5099 =
      fun p : Y => (fiberOrbit_equiv 99 50 hm5099 (Equiv.refl (Fin 99)) p).val := by
  funext p
  cases p
  simp only [roundEmbedMap, fiberOrbit_equiv, fiberMap, Subtype.val]
  <;> aesop

-- 3. The left-card fiber and the membership fiber have the same cardinality (50!·49!): they
--    are the same set of decks, by `membership_iff_leftCards` (a set equivalence, not 99!).
private theorem card_paramFiber_eq_membershipFiber :
    Fintype.card paramFiber = (FiberDisintegration.fiberSet membership segMembership).card := by
  -- `paramFiber` ≃ Y (bijection) and Y has card 50!·49!.
  have hL : Fintype.card paramFiber = 50 ! * 49 ! := by
    have : Fintype.card paramFiber = Fintype.card Y := by
      rw [← Fintype.card_congr]
      exact (fiberOrbit_equiv 99 50 hm5099 (Equiv.refl (Fin 99))).card
    rw [this]
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
    <;> norm_num
  -- The membership fiber is `{d // membership d = segMembership} = {d // leftCards d = segLeft}`
  -- (membership_iff_leftCards), whose card is the same 50!·49! (equinumerous to Y).
  have hR : (FiberDisintegration.fiberSet membership segMembership).card = 50 ! * 49 ! := by
    rw [FiberDisintegration.fiberSet, Finset.card_preimage]
    -- The preimage of `segMembership` under `membership` is `{d // leftCards d = segLeft}`; its
    -- card equals the card of the equinumerous `Y` (the within-pile pair fiber).
    have hPre : (Finset.univ.filter (fun d : Deck 99 => membership d = segMembership)).card =
        (Finset.univ.filter (fun d : Deck 99 => leftCards 99 50 hm5099 d = segLeft)).card := by
      rw [Finset.card_congr]
      apply Finset.filter_congr
      intro d
      rw [membership_iff_leftCards d]
    -- The left-card fiber deck-set has card 50!·49! (the pair fiber `Y`, via `fiberOrbit_equiv`).
    have hLC : (Finset.univ.filter (fun d : Deck 99 => leftCards 99 50 hm5099 d = segLeft)).card =
        50 ! * 49 ! := by
      -- This fiber deck-set is exactly the image of `Y` under `roundEmbedMap`; both have 50!·49!.
      rw [← Fintype.card_congr]
      exact (fiberOrbit_equiv 99 50 hm5099 (Equiv.refl (Fin 99))).card
      <;> rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
      <;> norm_num
    rw [hPre, hLC]
  linarith

-- 4. The headline: the one-round ideal (uniform) deck law = the perfect local law at the
--    segregated membership.
private theorem segHeadline :
    rhoRoundIdeal 99 50 hm5099 (by norm_num) (by norm_num) 1 (by norm_num) =
      localLift segMembership := by
  haveI : DecidableEq (Deck 99) := inferInstance
  haveI : DecidableEq Y := inferInstance
  haveI : Nonempty paramFiber := ⟨⟨Equiv.refl (Fin 99), by
      simp only [paramFiber, leftCards]; rfl⟩⟩
  haveI : Nonempty Y := ⟨(Equiv.refl (Fin 50), Equiv.refl (Fin 49))⟩
  -- Unfold the ideal law to its pushforward form and carry the pair-uniform through the
  -- fiber-orbit bijection:  (uniform on Y)  -->  (uniform on paramFiber)  -->  map val.
  change (distProduct (GSR.uniformDist (Equiv.Perm (Fin 50))) (GSR.uniformDist (Equiv.Perm (Fin 49)))).map
      (roundEmbedMap 99 50 hm5099) = localLift segMembership
  rw [distProduct_uniforms_eq_uniform, roundEmbedMap_eq_val,
      ← Convexity.StdSimplex.map_map,
      ← map_bijective_uniformDist (fiberOrbit_equiv 99 50 hm5099 (Equiv.refl (Fin 99)))]
  -- Pointwise mass: both sides are `1 / (50!·49!)` exactly on the fiber deck-set, `0` elsewhere.
  ext d
  have hLHS := map_mass_eq_univ_fiber (GSR.uniformDist paramFiber) (fun e : paramFiber => e.val) d
  have hRHS := localLift_mass segMembership d
  have hcond : (∃ e : paramFiber, e.val = d) ↔ membership d = segMembership := by
    constructor
    · rintro ⟨⟨w, hw, rfl⟩⟩
      rw [membership_iff_leftCards w]
      simpa [leftCards, leftPositions] using hw
    · intro hm
      have hlc := (membership_iff_leftCards d).mp hm
      exact ⟨⟨d, hlc⟩, rfl⟩
  simpa [hLHS, hRHS, hcond, card_paramFiber_eq_membershipFiber, localLift] using
    (show (if membership d = segMembership then (Fintype.card paramFiber : Rat)⁻¹ else 0) =
       (if membership d = segMembership then (Fintype.card paramFiber : Rat)⁻¹ else 0) by rfl)

end Shufflemath
