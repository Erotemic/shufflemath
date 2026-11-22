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

section Gate6F
variable (n a : Nat) (ha : 0 < a) (hn : 0 < n)

include ha hn

theorem gsrPermutationLaw_tv_le_badLabels :
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
      by_cases hbx : ℓ' ∈ badLabels n a
      · -- ℓ' ∈ bad: ∑_σ mass μ (ℓ',σ) = n! / (cardΠ·n!) = 1/cardΠ
        have hcCard : (Fintype.card (Fin n → Fin a) : Rat) ≠ 0 := by
          exact_mod_cast (show Fintype.card (Fin n → Fin a) ≠ 0 from by
            rw [Fintype.card_fun, Fintype.card_fin]; exact (Nat.pow_pos ha).ne')
        have hcF : (Nat.factorial n : Rat) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero n)
        have hCard (σ : Equiv.Perm (Fin n)) :
            Dist.mass μ (ℓ', σ) =
              1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat)) := by
          have hMass : Dist.mass μ (ℓ', σ) = 1 / (Fintype.card (ΩTieRank n a) : Rat) := by
            dsimp only [μ, GSR.uniformDist]
            simpa only [Dist.mass, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div]
          rw [hMass]
          change (1 : Rat) / (Fintype.card ((Fin n → Fin a) × Equiv.Perm (Fin n)) : Rat) =
                 1 / ((Fintype.card (Fin n → Fin a) : Rat) * (Nat.factorial n : Rat))
          simp only [Fintype.card_prod, Nat.cast_mul, Fintype.card_perm, Fintype.card_fin,
            Nat.cast_id, one_div]
        simp only [hbx, ite_true, hCard, Finset.sum_const, Finset.card_univ,
          Fintype.card_perm, Fintype.card_fin]
        -- the constant fiber-sum is a lifted mul; reduce n! / (cardΠ·n!) = 1 / cardΠ
        simp only [one_div, mul_inv_rev, smul_eq_mul, nsmul_eq_mul]
        field_simp [hcCard, hcF]
      · -- ℓ' ∉ bad: ∑_σ 0 = 0 = 0/cardΠ
        simp only [hbx, ite_false, zero_mul, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_zero, zero_div]
    have hInner : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun x => (Finset.univ : Finset (Equiv.Perm (Fin n))).sum
          (fun y => (if (x, y).1 ∈ badLabels n a then Dist.mass μ (x, y) else 0))) =
        (Finset.univ : Finset (Fin n → Fin a)).sum
          (fun ℓ' => (if ℓ' ∈ badLabels n a then 1 else 0) /
            (Fintype.card (Fin n → Fin a) : Rat)) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hbx : x ∈ badLabels n a
      · simpa [hbx] using hInn x
      · simpa [hbx] using hInn x
    rw [hInner]
    have hOut : (Finset.univ : Finset (Fin n → Fin a)).sum
        (fun ℓ' => (if ℓ' ∈ badLabels n a then (1 : Rat) else (0 : Rat)) /
          (Fintype.card (Fin n → Fin a) : Rat)) =
        ((badLabels n a).card : Rat) / (Fintype.card (Fin n → Fin a) : Rat) := by
      rw [← Finset.sum_div]
      have hSum : (Finset.univ : Finset (Fin n → Fin a)).sum
          (fun ℓ' => (if ℓ' ∈ badLabels n a then (1 : Rat) else (0 : Rat))) =
          ((badLabels n a).card : Rat) := by
        simp [Finset.sum_ite, Finset.card_filter, Nat.cast_id, nsmul_eq_mul, mul_one]
      rw [hSum]
    rw [hOut]
    have hCard : (Fintype.card (Fin n → Fin a) : Rat) = (a ^ n : Rat) := by
      rw [Fintype.card_fun]
      simp only [Fintype.card_fin, Nat.cast_pow]
    rw [hCard]
  -- (6) mismatch ≤ bad-mass pointwise (Key fact B contrapositive)
  rw [← hBadSum]
  apply Finset.sum_le_sum
  intro p _
  by_cases hbad : p.1 ∈ badLabels n a
  · -- ℓ ∈ bad: RHS = mass μ p, which dominates LHS (either mass μ p or 0)
    split_ifs with hfg
    · exact Dist.mass_nonneg μ p
    · exact le_rfl
  · -- ℓ ∉ bad: RHS = 0, so LHS must be 0 (no mismatch by Key fact B)
    by_cases hfg : rankFn p = tieFn p
    · simp [hfg, hbad]
    · -- rankFn p ≠ tieFn p but ℓ ∉ bad → contradiction (Key fact B)
      have hinj : Function.Injective p.1 :=
        (not_mem_badLabels_iff_injective p.1).1 hbad
      have hEq : tieFn p = rankFn p := by
        simpa only [rankFn, tieFn] using tieRank_eq_rankEquiv_inj n a hn p.1 hinj p.2
      exact absurd hEq (fun h => hfg h.symm)

/-- **Gate 6 batch 2 (f) headline.**  A finite GSR riffle law `ν_{n,a}` is within
  `choose(n,2) / a` (total variation) of the uniform law on `S_n`, for all
  `n > 0` and `a > 0`.  Composition of `gsrPermutationLaw_tv_le_badLabels` (`TV ≤ #bad / a^n`, this
  file) with `Gate6BadLabels.badLabels_uniform_bound` (`#bad / a^n ≤
  choose(n,2) / a`, batch 2 (c)).  This is the §8-style finite-size TV headline
  for the finite GSR law (the 99-card protocol's per-round bound composes with
  the F5 telescope for the `< 1/1000` certification). -/
theorem gsrPermutationLaw_tv_bound :
    Dist.tv (gsrPermutationLaw n a ha hn) (GSR.uniformDist (Equiv.Perm (Fin n))) ≤
      (n.choose 2 : Rat) / a := by
  exact le_trans (gsrPermutationLaw_tv_le_badLabels n a ha hn) (badLabels_uniform_bound n a ha)

end Gate6F

/-- The one-round two-pile local-error bound, at the level of the two
within-pile permutation laws (Gate 6, batch 3, \S5-\S6).  Running one round of
the local GSR on a deck splits into two *independent* within-pile GSR draws — a
left-pile permutation of size `m` with GSR parameter `a_L` and a right-pile
permutation of size `N - m` with parameter `a_R`.  The total variation between
the independent product of those two permutation laws and the fully-uniform
product is at most the sum of the two single-pile bounds
`choose(m,2)/a_L + choose(N-m,2)/a_R`.

This is the reusable "independence subadditivity + per-pile bound" assembly:
`distProduct_tv_subadditive` (the tensor product of two pairs of laws has TV at
most the sum of the marginal TVs) feeds the two `gsrPermutationLaw_tv_bound`
estimates.  The deck-level bound is then this plus a deterministic pushforward
contraction (`tv_map_contraction`) through the pile-embedding `act_d`. -/
theorem twoPilePermutationTV_bound
    (N m a_L a_R : Nat) (hN : 0 < N) (hm : m ≤ N) (hLpos : 0 < m) (hRpos : 0 < N - m)
    (hLa : 0 < a_L) (hRa : 0 < a_R) :
    Dist.tv (distProduct (PermutationLaw.gsrPermutationLaw m a_L hLa hLpos)
                        (PermutationLaw.gsrPermutationLaw (N - m) a_R hRa hRpos))
            (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                        (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) ≤
      (m.choose 2 : Rat) / a_L + ((N - m).choose 2 : Rat) / a_R := by
  classical
  haveI : DecidableEq (Equiv.Perm (Fin m)) := inferInstance
  haveI : DecidableEq (Equiv.Perm (Fin (N - m))) := inferInstance
  calc
    _ ≤ Dist.tv (PermutationLaw.gsrPermutationLaw m a_L hLa hLpos) (GSR.uniformDist (Equiv.Perm (Fin m))) +
        Dist.tv (PermutationLaw.gsrPermutationLaw (N - m) a_R hRa hRpos) (GSR.uniformDist (Equiv.Perm (Fin (N - m)))) :=
      distProduct_tv_subadditive _ _ _ _
    _ ≤ (m.choose 2 : Rat) / a_L + ((N - m).choose 2 : Rat) / a_R := by
      gcongr
      · exact @gsrPermutationLaw_tv_bound m a_L hLa hLpos
      · exact @gsrPermutationLaw_tv_bound (N - m) a_R hRa hRpos

/-- The explicit one-round local-error bound for the concrete 99-card protocol
(Gate 6, batch 3, \S5): the two within-pile GSR riffles (left pile size 50, right
pile size 49, each with GSR parameter `2 ^ 23`) together stay within the collision
budget `\delta1 = 2401 / 8388608` of the independent uniform shuffle, at the level
of the two within-pile permutation laws.

This is `twoPilePermutationTV_bound` instantiated at `N = 99`, `m = 50`,
`a_L = a_R = 2 ^ 23`, with the symbolic right-hand side
`choose(50,2)/2^23 + choose(49,2)/2^23` evaluated to the concrete rational
`2401 / 8388608` (the per-round collision budget already named in
`Shufflemath/FiniteDeck/Gate6FiniteGSR.lean`).  The binomial coefficients reduce
via `Nat.choose_two_right` (`n.choose 2 = n·(n-1)/2`); the pure rational arithmetic
then closes by `norm_num`. -/
theorem oneRoundTwoPileTV_le_delta1 :
    Dist.tv (distProduct (PermutationLaw.gsrPermutationLaw 50 (2 ^ 23) (by norm_num) (by norm_num))
                        (PermutationLaw.gsrPermutationLaw 49 (2 ^ 23) (by norm_num) (by norm_num)))
            (distProduct (GSR.uniformDist (Equiv.Perm (Fin 50)))
                        (GSR.uniformDist (Equiv.Perm (Fin 49)))) ≤ 2401 / 8388608 := by
  haveI : DecidableEq (Equiv.Perm (Fin 50)) := inferInstance
  haveI : DecidableEq (Equiv.Perm (Fin 49)) := inferInstance
  have hL := twoPilePermutationTV_bound 99 50 (2 ^ 23) (2 ^ 23)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hRHS : (Nat.choose 50 2 : Rat) / 8388608 + (Nat.choose 49 2 : Rat) / 8388608 = 2401 / 8388608 := by
    rw [Nat.choose_two_right, Nat.choose_two_right]
    norm_num
  simpa [hRHS] using hL

end
