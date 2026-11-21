module

public import Shufflemath.GSR
public import Shufflemath.GSRF42
public import Shufflemath.GSRPermutationLaw
public import Shufflemath.Gate6BadLabels
public import Shufflemath.FiniteDeck.Gate6TieRank
public import Shufflemath.TotalVariation
public import Shufflemath.Finite
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators

@[expose]
public section

open Shufflemath
open Shufflemath.PermutationLaw

/-! Gate 6 batch 2 (f): TV(ν_{n,a}, U_{S_n}) ≤ Pr(ℓ ∈ badLabels) ≤ choose(n,2)/a. -/

section Probe
variable (n a : Nat) (ha : 0 < a) (hn : 0 < n)

include ha hn

theorem _probeF_main :
    Dist.tv (gsrPermutationLaw n a ha hn) (GSR.uniformDist (Equiv.Perm (Fin n))) ≤
      ((badLabels n a).card : Rat) / (a ^ n : Rat) := by
  let hFinPi : Fintype (Fin n → Fin a) := (by infer_instance : Fintype (Fin n → Fin a))
  let hFinPerm : Fintype (Equiv.Perm (Fin n)) := (by infer_instance : Fintype (Equiv.Perm (Fin n)))
  letI hΩ : Fintype (ΩTieRank n a) := Fintype.mk (Finset.product hFinPi.elems hFinPerm.elems)
    (fun p => Finset.mem_product.2 ⟨hFinPi.complete p.1, hFinPerm.complete p.2⟩)
  letI hNonempty : Nonempty (ΩTieRank n a) := hNonemptyΩ n a ha
  let μ := GSR.uniformDist (ΩTieRank n a)
  let U := GSR.uniformDist (Equiv.Perm (Fin n))
  let ν := gsrPermutationLaw n a ha hn
  let rankFn : ΩTieRank n a → Equiv.Perm (Fin n) := fun p => rankEquiv n a hn p.1
  let tieFn : ΩTieRank n a → Equiv.Perm (Fin n) := fun p => tieRank n a hn p.1 p.2
  have hUnivProd : (Finset.univ : Finset (ΩTieRank n a)) =
      (Finset.univ : Finset (Fin n → Fin a)) ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
    show hΩ.elems = hFinPi.elems ×ˢ hFinPerm.elems
    rfl
  -- (1) μ.map tieFn = U (Key fact A; tieRankLaw = that pushforward)
  have hT : μ.map tieFn = U := by
    dsimp only [μ, tieFn, U, tieRankLaw]
    exact tieRankLaw_uniform n a ha hn
  -- (2) μ.map rankFn = ν
  have hMarg : μ.map Prod.fst = GSR.uniformLabels n a ha := by
    ext ℓ
    -- goal: (μ.map fst).weights ℓ = (GSR.uniformLabels n a ha).weights ℓ
    have hL : (μ.map Prod.fst).weights ℓ =
        (Finset.univ : Finset (ΩTieRank n a)).sum
          (fun p : ΩTieRank n a =>
            (if Prod.fst p = ℓ then Dist.mass μ p else 0)) :=
      Dist.map_mass_eq_univ_fiber μ Prod.fst ℓ
    rw [hL]
    -- mass μ p = 1 / (a^n · n!); Fubini over the product univ.
    have hCard (p : ΩTieRank n a) : Dist.mass μ p =
        1 / (Fintype.card (ΩTieRank n a) : Rat) := by
      dsimp only [μ, GSR.uniformDist]
      simpa only [Dist.mass, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div]
    have hCardProd : (Fintype.card (ΩTieRank n a) : Rat) =
        (Fintype.card (Fin n → Fin a) : Rat) * (Fintype.card (Equiv.Perm (Fin n)) : Rat) := by
      change (Fintype.card ((Fin n → Fin a) × Equiv.Perm (Fin n)) : Rat) =
                (Fintype.card (Fin n → Fin a) : Rat) * (Fintype.card (Equiv.Perm (Fin n)) : Rat)
      rw [Fintype.card_prod]
      simp only [Nat.cast_mul]
    have hPermCard : (Fintype.card (Equiv.Perm (Fin n)) : Rat) = (Nat.factorial n : Rat) := by
      simp only [Fintype.card_perm, Fintype.card_fin, Nat.cast_id]
    simp only [hCard, hCardProd, hPermCard]
    -- ∑_{ℓ',σ} 1/(cardΠ·n!) · [ℓ' = ℓ]
    rw [hUnivProd]
    refine (Finset.sum_product _ _ _).trans ?_
    simp only [Prod.fst, Prod.snd]
    have hInn (ℓ' : Fin n → Fin a) :
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
          (fun σ => (if ℓ' = ℓ then
            1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat))
          else 0)) =
          (if ℓ' = ℓ then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat) := by
      split_ifs with hle hle'
      · simp [Fintype.card_fin, Fintype.card_perm]
        field_simp [Nat.factorial_ne_zero n, Fintype.card_pos_iff]
        <;> ring
      · simp
    refine (Finset.sum_congr rfl (fun x _ => by simpa using (hInn x))).trans ?_
    -- goal now: ∑_x (if x = ℓ then 1 else 0) / a^n = (uniformLabels).weights ℓ
    have hSum1 : (∑ x : (Fin n → Fin a), (if x = ℓ then 1 else 0 : Rat)) = 1 := by
      simpa using (Finset.sum_ite_eq' ℓ (fun _ => (1 : Rat)))
    have hR : (GSR.uniformLabels n a ha).weights ℓ = 1 / (a ^ n : Rat) := by
      dsimp only [GSR.uniformLabels, GSR.uniformDist]
      simpa [Dist.mass, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm,
        Fintype.card_pi, Fintype.card_fin, Nat.cast_pow, Nat.cast_one, one_div]
    rw [hR]
    -- LHS: (∑_x (if x = ℓ then 1 else 0)) / a^n = 1 / a^n
    rw [← Finset.sum_div, hSum1]
  have hV : μ.map rankFn = ν := by
    dsimp only [ν]
    rw [← Convexity.StdSimplex.map_map]
    change (μ.map Prod.fst).map (rankEquiv n a hn) = ν
    rw [hMarg]
    rfl
  -- (3) rewrite the goal to the common-source form
  change Dist.tv ν U ≤ (badLabels n a).card / (a ^ n : Rat)
  rw [← hV, ← hT]
  -- (4) the generic same-source coupling inequality (batch 2 (e))
  apply le_trans (Dist.tv_maps_le_mismatch μ rankFn tieFn)
  -- (5) the bad-mass sum collapses to #bad / a^n (Fubini over the product)
  have hBadSum : (Finset.univ : Finset (ΩTieRank n a)).sum
      (fun p => (if p.1 ∈ badLabels n a then Dist.mass μ p else 0)) =
      ((badLabels n a).card : Rat) / (a ^ n : Rat) := by
    rw [hUnivProd]
    refine (Finset.sum_product _ _ _).trans ?_
    -- goal: ∑ x, ∑ y, if (x,y).1 ∈ bad then mass (x,y) else 0 = bad/a^n
    have hInn (ℓ' : Fin n → Fin a) :
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
          (fun σ => (if ℓ' ∈ badLabels n a then Dist.mass μ (ℓ', σ) else 0)) =
          (if ℓ' ∈ badLabels n a then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat) := by
      split_ifs with hle hle'
      · -- ∑_σ mass μ (ℓ',σ) = n! / (cardΠ·n!) = 1/cardΠ
        have hCard (σ : Equiv.Perm (Fin n)) :
            Dist.mass μ (ℓ', σ) =
              1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat)) := by
          dsimp only [μ, GSR.uniformDist]
          simpa only [Dist.mass, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div,
            Fintype.card_prod]
        simp only [hCard]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        field_simp
        · exact mod_cast (Nat.factorial_ne_zero n)
        · exact mod_cast (show Fintype.card (Fin n → Fin a) ≠ 0 from by
            rw [Fintype.card_fun, Fintype.card_fin]; exact Nat.pow_ne_zero (Nat.ne_of_gt ha) n)
      · simp only [ite_false, zero_mul, Finset.sum_const, Finset.card_univ]
    have hInner : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun x => (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
          (fun y => (if (x, y).1 ∈ badLabels n a then Dist.mass μ (x, y) else 0))) =
        (Finset.univ : Finset (Fin n → Fin a)).sum
          (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) /
            (Fintype.card (Fin n → Fin a) : Rat)) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simpa using hInn x
    rw [hInner]
    have hOut : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) /
          (Fintype.card (Fin n → Fin a) : Rat)) =
        ((badLabels n a).card : Rat) / (Fintype.card (Fin n → Fin a) : Rat) := by
      rw [← Finset.sum_div]
      have hSum : (Finset.univ : Finset (Fin n → Fin a)).sum
          (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) : Rat) = (badLabels n a).card := by
        rw [Finset.sum_ite (fun _ => 1)]
        rw [Finset.card_filter, Finset.filter_mem]
        rw [Finset.inter_eq_self_of_subset (Finset.subset_univ _)]
        simp only [Nat.cast_id]
      rw [hSum]
    rw [hOut]
    have hCard : (Fintype.card (Fin n → Fin a) : Rat) = (a ^ n : Rat) := by
      rw [Fintype.card_fun]
      simp only [Fintype.card_fin]
    rw [hCard]
    rfl
  -- (6) mismatch ≤ bad-mass pointwise (Key fact B contrapositive)
  rw [← hBadSum]
  apply Finset.sum_le_sum
  intro p
  by_cases hbad : p.1 ∈ badLabels n a
  · -- ℓ ∈ bad: RHS = mass μ p
    split_ifs with hfg
    · simp only [ite_true, hfg]
      exact (Dist.mass_nonneg μ p).ge
    · simp only [ite_false]
      exact le_rfl
  · -- ℓ ∉ bad: RHS = 0; the LHS must already be 0
    by_cases hfg : rankFn p = tieFn p
    · simp only [ite_true, hfg, ite_false, hbad]
      exact le_rfl
    · -- rankFn p ≠ tieFn p and ℓ ∉ bad → contradiction
      have hinj : Function.Injective p.1 :=
        (not_mem_badLabels_iff_injective p.1).1 hbad
      have hEq : tieFn p = rankFn p := by
        simpa only [rankFn, tieFn] using tieRank_eq_rankEquiv_inj n a hn p.1 hinj p.2
      exact absurd hEq hfg
  -- (7) collapse: the goal is now #bad/a^n ≤ #bad/a^n
  exact le_rfl

end Probe

end
