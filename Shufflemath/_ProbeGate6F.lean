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
    ext p
    simp only [Finset.mem_product, Finset.mem_univ, true_and, and_true]
  -- (1) μ.map tieFn = U (Key fact A; tieRankLaw = that pushforward)
  have hT : μ.map tieFn = U := by
    dsimp only [μ, tieFn, U]
    rw [← tieRankLaw]
    exact tieRankLaw_uniform n a ha hn
  -- (2) μ.map rankFn = ν
  have hMarg : μ.map Prod.fst = GSR.uniformLabels n a ha := by
    dsimp only [μ]
    ext ℓ
    simp only [Dist.mass, GSR.uniformLabels]
    have hL : Dist.mass (GSR.uniformDist (ΩTieRank n a)).map Prod.fst ℓ =
        (Finset.univ : Finset (ΩTieRank n a)).sum
          (fun p : ΩTieRank n a => (if Prod.fst p = ℓ then 1 else 0) *
            Dist.mass (GSR.uniformDist (ΩTieRank n a)) p) :=
      Dist.map_mass_eq_univ_fiber (GSR.uniformDist (ΩTieRank n a)) Prod.fst ℓ
    rw [hL]
    -- mass μ p = 1 / (a^n · n!); Fubini over the product univ.
    have hCard (p : ΩTieRank n a) : Dist.mass (GSR.uniformDist (ΩTieRank n a)) p =
        1 / (Fintype.card (ΩTieRank n a) : Rat) := by
      dsimp only [GSR.uniformDist]
      simpa only [Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div]
    have hCardProd : (Fintype.card (ΩTieRank n a) : Rat) =
        (Fintype.card (Fin n → Fin a) : Rat) * (Fintype.card (Equiv.Perm (Fin n)) : Rat) := by
      rw [Fintype.card_product]
      simp only [Nat.cast_mul]
    have hPermCard : (Fintype.card (Equiv.Perm (Fin n)) : Rat) = (Nat.factorial n : Rat) := by
      simp only [Fintype.card_perm, Nat.cast_id]
    rw [hL]
    conv at hL => lhs
    simp only [hCard, hCardProd, hPermCard]
    -- ∑_{ℓ',σ} 1/(cardΠ·n!) · [ℓ' = ℓ]
    rw [hUnivProd, Finset.sum_product]
    have hInn (ℓ' : Fin n → Fin a) :
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
          (fun σ => 1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat)) ·
            (if ℓ' = ℓ then 1 else 0)) =
          (if ℓ' = ℓ then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat) := by
      split_ifs with hle hle'
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Nat.cast_id]
        field_simp
      · simp only [ite_false, zero_mul, Finset.sum_const, Finset.card_univ]
    rw [hInn]
    -- outer: ∑_{ℓ'} (if ℓ' = ℓ then 1/cardΠ else 0) = 1/cardΠ
    have hOut : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun ℓ' => (if ℓ' = ℓ then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat)) =
        1 / (Fintype.card (Fin n → Fin a) : Rat) := by
      have hSum : (Finset.univ : Finset (Fin n → Fin a)).sum
          (fun ℓ' => (if ℓ' = ℓ then 1 else 0) : Rat) = 1 := by
        rw [Finset.sum_ite_eq (Finset.mem_univ ℓ)]
      rw [Finset.sum_div, hSum]
      field_simp [show (Fintype.card (Fin n → Fin a) : Rat) ≠ 0 from by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin n → Fin a) ≠ 0)]
    rw [hOut]
    -- RHS: mass uniformLabels ℓ = 1/cardΠ
    have hR : Dist.mass (GSR.uniformLabels n a ha) ℓ =
        1 / (Fintype.card (Fin n → Fin a) : Rat) := by
      dsimp only [GSR.uniformLabels, GSR.uniformDist]
      simpa only [Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div]
    rw [hR]
  have hV : μ.map rankFn = ν := by
    dsimp only [μ, ν, rankFn]
    rw [gsrPermutationLaw, ← Convexity.StdSimplex.map_map]
    rw [hMarg]
    simp only [GSR.uniformLabels]
    funext ℓ
    rfl
  -- (3) rewrite the goal to the common-source form
  rw [← hV, ← hT]
  -- (4) the generic same-source coupling inequality (batch 2 (e))
  apply Dist.tv_maps_le_mismatch μ rankFn tieFn
  -- (5) mismatch → bad: pointwise, (if F=G then 0 else m) ≤ (if bad then m else 0)
  apply Finset.sum_le_sum
  intro p
  by_cases hbad : p.1 ∈ badLabels n a
  · -- ℓ ∈ bad: RHS = mass μ p
    split_ifs with hfg
    · simp only [ite_true, zero_mul, hfg]
      exact (Dist.mass_nonneg μ p).ge
    · simp only [ite_false]
  · -- ℓ ∉ bad: RHS = 0; the LHS must already be 0 (Key fact B contrapositive)
    by_cases hfg : rankFn p = tieFn p
    · simp only [ite_true, zero_mul, hfg, ite_false]
    · -- rankFn p ≠ tieFn p and ℓ ∉ bad → contradiction
      have hinj : Function.Injective p.1 :=
        (not_mem_badLabels_iff_injective p.1).1 (fun h => absurd h hbad)
      have hEq : tieFn p = rankFn p := by
        simpa only [rankFn, tieFn] using tieRank_eq_rankEquiv_inj n a hn p.1 hinj p.2
      exact absurd hEq hfg
  -- (6) collapse to #bad / a^n
  rw [hUnivProd, Finset.sum_product]
  have hInn (ℓ' : Fin n → Fin a) :
      (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
        (fun σ => (if ℓ' ∈ badLabels n a then Dist.mass μ (ℓ', σ) else 0)) =
        (if ℓ' ∈ badLabels n a then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat) := by
    split_ifs with hle hle'
    · -- ∑_σ mass μ (ℓ,σ) = n! / (a^n·n!) = 1/cardΠ
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Nat.cast_id]
      have hCard : Dist.mass (GSR.uniformDist (ΩTieRank n a)) (ℓ', σ) =
          1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat)) := by
        dsimp only [μ]
        dsimp only [GSR.uniformDist]
        simpa only [Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div, Fintype.card_product]
      rw [hCard]
      field_simp
      · field_simp
      · exact mod_cast (Nat.factorial_ne_zero σ)
    · simp only [ite_false, zero_mul, Finset.sum_const, Finset.card_univ]
  rw [hInn]
  have hOut : (Finset.univ : Finset (Fin n → Fin a)).sum
      (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) / (Fintype.card (Fin n → Fin a) : Rat)) =
      ((badLabels n a).card : Rat) / (Fintype.card (Fin n → Fin a) : Rat) := by
    rw [Finset.sum_div]
    have hSum : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) : Rat) = (badLabels n a).card := by
      rw [Finset.sum_ite (fun _ => 1)]
      rw [Finset.card_filter, Finset.filter_mem]
      rw [Finset.inter_eq_self_of_subset (Finset.subset_univ _)]
      simp only [Nat.cast_id]
    rw [hSum]
  rw [hOut]
  -- (7) the headline probability bound
  have hCard : (Fintype.card (Fin n → Fin a) : Rat) = (a ^ n : Rat) := by
    rw [Fintype.card_fun]
    simp only [Fintype.card_fin]
  rw [hCard]
  exact badLabels_uniform_bound n a ha

end Probe

end
