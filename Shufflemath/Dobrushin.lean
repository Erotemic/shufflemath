import Shufflemath.Finite
import Shufflemath.Matrix
import Shufflemath.TotalVariation
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/- Dobrushin contraction constants for kernels, the general-alphabet
counterpart of `MatrixTV`. For a kernel `K : α → Dist β`, the Dobrushin
coefficient is the supremum of the TV distances between pairs of rows:
`dobrushinCoeff K = max_{i, j} tv (K i) (K j)` (the max exists because the
index set is finite).

Main results:

- `dobrushin_contraction` (sharp, no factor of 2): one application of `K`
  contracts the TV distance by at most the coefficient itself:
      tv (apply μ K) (apply ν K) ≤ dobrushinCoeff K * tv μ ν
  The proof works on the *positive set* of the output difference: the
  output TV is the input difference dotted with the row-mass vector of that
  set; subtracting the vector's minimum (legal because the input difference
  has total mass zero) makes the summand nonnegative and of size at most
  `dobrushinCoeff K`, so only the positive side of the input difference,
  which has total mass `tv μ ν`, can contribute.
- `dobrushinCoeff_submult`: composition is submultiplicative,
  `dobrushinCoeff (comp K L) ≤ dobrushinCoeff K * dobrushinCoeff L`, and
  `run_contraction`: `n` applications contract by `dobrushinCoeff K ^ n`.
- `dobrushinCoeff_matrix_link`: the kernel coefficient of a row-stochastic
  matrix's row kernel equals the matrix Dobrushin coefficient, so the
  fixed-size matrix results and the general-alphabet results are the same
  numbers.
- `dobrushinCoeff_zero_iff`: the coefficient is zero exactly when all rows
  are equal.

Unlike the fixed-size `MatrixTV.dobrushinCoeff`, the rows here are
distributions, so the definition works at the kernel level directly and the
matrix case is recovered as a special case. -/

namespace Shufflemath

namespace Dobrushin

-- ---------------------------------------------------------------------------
-- Dobrushin coefficient for kernels
-- ---------------------------------------------------------------------------

/-- The TV distance between two rows of a kernel. -/
def rowTV [Fintype beta] (K : FiniteKernel alpha beta) (i j : alpha) : Rat :=
  Dist.tv (K i) (K j)

/-- The finite set of all pairwise row distances. -/
def pairDistances [Fintype alpha] [DecidableEq alpha] [Fintype beta]
    (K : FiniteKernel alpha beta) : Finset Rat :=
  (Finset.univ ×ˢ Finset.univ).image (fun ij => rowTV K ij.1 ij.2)

/-- The row-distance set is nonempty when the index set is nonempty. -/
theorem pairDistances_nonempty
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : (pairDistances K).Nonempty := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty alpha)
  refine ⟨rowTV K a a, ?_⟩
  simp only [pairDistances, Finset.mem_image]
  exact ⟨⟨a, a⟩, by simp, rfl⟩

/-- The Dobrushin coefficient: the largest TV distance between two rows. -/
noncomputable def dobrushinCoeff
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : Rat :=
  (pairDistances K).max' (pairDistances_nonempty K)

/-- Every pairwise row distance is at most the Dobrushin coefficient. -/
theorem rowTV_le_dobrushin
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) (i j : alpha) :
    rowTV K i j ≤ dobrushinCoeff K := by
  unfold dobrushinCoeff
  apply Finset.le_max'
  simp [pairDistances]

/-- The coefficient is nonnegative (TV is). -/
@[simp]
theorem dobrushinCoeff_nonneg
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : 0 ≤ dobrushinCoeff K := by
  classical
  let a := Classical.choice (inferInstance : Nonempty alpha)
  calc
    0 ≤ rowTV K a a := Dist.tv_nonneg _ _
    _ ≤ dobrushinCoeff K := rowTV_le_dobrushin K a a

/-- The coefficient is at most 1 (TV of two probability vectors is ≤ 1). -/
theorem dobrushinCoeff_le_one
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : dobrushinCoeff K ≤ 1 := by
  unfold dobrushinCoeff
  apply Finset.max'_le
  intro d hd
  rw [pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  exact Dist.tv_le_one (K ij.1) (K ij.2)

/-- The coefficient is zero exactly when all rows agree as mass functions
(the chain is already stationary after one step; stated at mass level, as
`Dist.tv_eq_zero` is, since distinct `Dist` representations can share a
mass function). -/
theorem dobrushinCoeff_zero_iff
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) :
    dobrushinCoeff K = 0 ↔ ∀ i j x, Dist.mass (K i) x = Dist.mass (K j) x := by
  constructor
  · intro h i j x
    have h1 : rowTV K i j ≤ 0 :=
      (rowTV_le_dobrushin K i j).trans (le_of_eq h)
    have h2 : rowTV K i j = 0 :=
      le_antisymm h1 (Dist.tv_nonneg (K i) (K j))
    exact ((Dist.tv_eq_zero (K i) (K j)).mp h2) x
  · intro h
    classical
    obtain ⟨a⟩ := (inferInstance : Nonempty alpha)
    have h0 : ∀ d ∈ pairDistances K, d ≤ 0 := by
      intro d hd
      rw [pairDistances] at hd
      rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
      have htv : Dist.tv (K ij.1) (K ij.2) = 0 :=
        (Dist.tv_eq_zero (K ij.1) (K ij.2)).mpr (fun x => h ij.1 ij.2 x)
      simpa [rowTV] using le_of_eq htv
    have hmem : (0 : Rat) ∈ pairDistances K := by
      simp only [pairDistances, Finset.mem_image]
      refine ⟨⟨a, a⟩, by simp, ?_⟩
      change rowTV K a a = 0
      rw [rowTV]
      exact Dist.tv_self _
    unfold dobrushinCoeff
    exact (Finset.max'_eq_iff (pairDistances K) (pairDistances_nonempty K) (0 : Rat)).mpr
      ⟨hmem, h0⟩

/-- The coefficient is zero implies all rows agree as mass functions. -/
theorem dobrushinCoeff_zero
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) :
    dobrushinCoeff K = 0 → ∀ i j x, Dist.mass (K i) x = Dist.mass (K j) x := by
  exact (dobrushinCoeff_zero_iff K).mp

-- ---------------------------------------------------------------------------
-- The sharp Dobrushin contraction
-- ---------------------------------------------------------------------------

/-- A univ-sum of a function gated by membership in `t` is the `t`-sum. -/
private theorem sumUnivIte [Fintype alpha] [DecidableEq alpha]
    (f : alpha -> Rat) (t : Finset alpha) :
    Finset.sum (Finset.univ : Finset alpha) (fun x => if x ∈ t then f x else 0) =
    Finset.sum t f := by
  simp

/-- For probability vectors, the *absolute* signed mass difference on any
set is at most the TV. This is the B3 workhorse applied to both `p − q`
and `q − p`, packaged as an absolute value. -/
theorem absSumLeTV [Fintype alpha] [DecidableEq alpha]
    (p q : alpha -> Rat) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : Finset.sum (Finset.univ : Finset alpha) p = 1)
    (hq1 : Finset.sum (Finset.univ : Finset alpha) q = 1)
    (S : Finset alpha) :
    |Finset.sum S (fun x => p x - q x)| ≤ vectorTV p q := by
  have h1 : Finset.sum S (fun x => p x - q x) ≤ vectorTV p q := by
    calc
      _ ≤ positiveSum p q :=
          vectorTV_sum_le_positive_set p q hp hq hp1 hq1 S
      _ = vectorTV p q :=
          (vectorTV_eq_positive_set p q hp hq hp1 hq1).symm
  have h2 : -Finset.sum S (fun x => p x - q x) ≤ vectorTV p q := by
    have h2a : Finset.sum S (fun x => q x - p x) =
        -Finset.sum S (fun x => p x - q x) := by
      have h2b : Finset.sum S (fun x => q x - p x) =
          Finset.sum S (fun x => -(p x - q x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [h2b, Finset.sum_neg_distrib]
    rw [← h2a]
    calc
      _ ≤ positiveSum q p :=
          vectorTV_sum_le_positive_set q p hq hp hq1 hp1 S
      _ = vectorTV q p :=
          (vectorTV_eq_positive_set q p hq hp hq1 hp1).symm
      _ = vectorTV p q := (vectorTV_comm p q).symm
  have hneg : -(vectorTV p q) ≤ Finset.sum S (fun x => p x - q x) := by
    simpa using neg_le_neg h2
  exact abs_le.mpr ⟨hneg, h1⟩

/-- The signed row-mass difference over a set is bounded by the row TV. -/
theorem rowWeightBound
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (K : FiniteKernel alpha beta) (S : Finset beta) (i j : alpha) :
    |Finset.sum S (fun y => Dist.mass (K i) y) -
        Finset.sum S (fun y => Dist.mass (K j) y)| ≤ rowTV K i j := by
  set hsub : Finset.sum S (fun y => (Dist.mass (K i) y - Dist.mass (K j) y)) =
        Finset.sum S (fun y => Dist.mass (K i) y) -
          Finset.sum S (fun y => Dist.mass (K j) y) :=
    Finset.sum_sub_distrib (fun y => Dist.mass (K i) y) (fun y => Dist.mass (K j) y)
  have h1 : |Finset.sum S (fun y => (Dist.mass (K i) y - Dist.mass (K j) y))| ≤
      rowTV K i j := by
    have h2 := absSumLeTV (fun y => Dist.mass (K i) y) (fun y => Dist.mass (K j) y)
      (fun _ => Dist.mass_nonneg (K i) _) (fun _ => Dist.mass_nonneg (K j) _)
      (Dist.sum_mass (K i)) (Dist.sum_mass (K j)) S
    simpa [rowTV, Dist.tv] using h2
  simpa [hsub] using h1

/-- The signed output-mass difference on a set equals the input-mass
difference dotted with the row-mass vector of that set (Fubini). -/
theorem sumOnSEqWeighted [Fintype alpha] [DecidableEq alpha] [Fintype beta]
    [DecidableEq beta]
    (K : FiniteKernel alpha beta) (mu nu : Dist alpha) (S : Finset beta) :
    Finset.sum S (fun y => Dist.mass (FiniteKernel.apply mu K) y -
        Dist.mass (FiniteKernel.apply nu K) y) =
    Finset.sum (Finset.univ : Finset alpha)
      (fun x => (Dist.mass mu x - Dist.mass nu x) *
        Finset.sum S (fun y => Dist.mass (K x) y)) := by
  let p' : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply mu K) y
  let q' : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply nu K) y
  have hpoint (y : beta) :
      (Dist.mass (FiniteKernel.apply mu K) y -
        Dist.mass (FiniteKernel.apply nu K) y) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun x => (Dist.mass mu x - Dist.mass nu x) * Dist.mass (K x) y) := by
    rw [FiniteKernel.apply_mass, FiniteKernel.apply_mass]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  calc
    _ = Finset.sum S (fun y => p' y - q' y) := rfl
    _ = Finset.sum S (fun y => Finset.sum (Finset.univ : Finset alpha)
        (fun x => (Dist.mass mu x - Dist.mass nu x) * Dist.mass (K x) y)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact hpoint y
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => Finset.sum S (fun y => (Dist.mass mu x - Dist.mass nu x) *
          Dist.mass (K x) y)) := by
      apply Finset.sum_comm
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => (Dist.mass mu x - Dist.mass nu x) *
          Finset.sum S (fun y => Dist.mass (K x) y)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Finset.mul_sum]

/-- The main (sharp) Dobrushin contraction theorem for kernels: one
application of `K` contracts the TV distance by at most the Dobrushin
coefficient itself (no extra factor of 2):
    tv (apply μ K) (apply ν K) ≤ dobrushinCoeff K * tv μ ν.
The output TV is the input difference dotted with the row-mass vector of the
output's positive set; subtracting that vector's minimum (legal because the
input difference has total mass zero) makes the summand nonnegative and of
size at most `dobrushinCoeff K`, so only the positive side of the input
difference, which has total mass `tv μ ν`, can contribute. -/
theorem dobrushin_contraction
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    [Nonempty alpha]
    (K : FiniteKernel alpha beta) (mu nu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu K) (FiniteKernel.apply nu K) ≤
    dobrushinCoeff K * Dist.tv mu nu := by
  classical
  let p : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply mu K) y
  let q : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply nu K) y
  let S₀ := positiveSet p q
  let r : alpha -> Rat := fun x => Finset.sum S₀ (fun y => Dist.mass (K x) y)
  have hpn : ∀ y, 0 ≤ p y := fun y => Dist.mass_nonneg (FiniteKernel.apply mu K) y
  have hqn : ∀ y, 0 ≤ q y := fun y => Dist.mass_nonneg (FiniteKernel.apply nu K) y
  have hp1 : Finset.sum (Finset.univ : Finset beta) p = 1 :=
    Dist.sum_mass (FiniteKernel.apply mu K)
  have hq1 : Finset.sum (Finset.univ : Finset beta) q = 1 :=
    Dist.sum_mass (FiniteKernel.apply nu K)
  have hsum0 : Finset.sum (Finset.univ : Finset alpha)
      (fun x => Dist.mass mu x - Dist.mass nu x) = 0 := by
    rw [Finset.sum_sub_distrib, Dist.sum_mass, Dist.sum_mass]
    norm_num
  -- r achieves its minimum at some x₀; write s x := r x - m. After the
  -- shift, 0 ≤ s x ≤ dobrushinCoeff K for every x.
  have hnonempty_img : ((Finset.univ : Finset alpha).image r).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty (α := alpha))
  let m := ((Finset.univ : Finset alpha).image r).min' hnonempty_img
  obtain ⟨x₀, hx₀⟩ := Finset.mem_image.mp (Finset.min'_mem _ hnonempty_img)
  have hsn : ∀ x, 0 ≤ r x - m := by
    intro x
    have hmem : r x ∈ (Finset.univ : Finset alpha).image r :=
      Finset.mem_image_of_mem (fun _ => r _) (Finset.mem_univ x)
    exact sub_nonneg_of_le (Finset.min'_le _ (r x) hmem)
  have hsup : ∀ x, r x - m ≤ dobrushinCoeff K := by
    intro x
    have hosc : |r x - r x₀| ≤ dobrushinCoeff K :=
      (rowWeightBound K S₀ x x₀).trans (rowTV_le_dobrushin K x x₀)
    have hm : m = r x₀ := Eq.symm hx₀.2
    rw [hm]
    exact (abs_le.mp hosc).2
  -- Zero-sum input: subtracting the constant m from r does not change the
  -- dot product with (μ − ν).
  have hshift :
      Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) =
      Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) := by
    calc
      _ = Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x -
            m * (Dist.mass mu x - Dist.mass nu x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) -
          Finset.sum (Finset.univ : Finset alpha)
          (fun x => m * (Dist.mass mu x - Dist.mass nu x)) :=
        Finset.sum_sub_distrib
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x)
          (fun x => m * (Dist.mass mu x - Dist.mass nu x))
      _ = Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) -
          m * Finset.sum (Finset.univ : Finset alpha)
          (fun x => Dist.mass mu x - Dist.mass nu x) := by
        rw [← Finset.mul_sum]
      _ = Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) := by
        simp [hsum0]
  -- The input side where μ > ν: only this side can contribute.
  let A := positiveSet (fun x => Dist.mass mu x) (fun x => Dist.mass nu x)
  have hsumA : Finset.sum A (fun x => Dist.mass mu x - Dist.mass nu x) =
      Dist.tv mu nu := by
    calc
      _ = positiveSum (fun x => Dist.mass mu x) (fun x => Dist.mass nu x) := rfl
      _ = vectorTV (fun x => Dist.mass mu x) (fun x => Dist.mass nu x) :=
        (vectorTV_eq_positive_set (fun x => Dist.mass mu x) (fun x => Dist.mass nu x)
            (fun x => Dist.mass_nonneg mu x) (fun x => Dist.mass_nonneg nu x)
            (Dist.sum_mass mu) (Dist.sum_mass nu)).symm
      _ = Dist.tv mu nu := rfl
  have hdrop :
      Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) ≤
      Finset.sum A (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) := by
    have hdecomp :
        Finset.sum (Finset.univ : Finset alpha)
            (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) =
        Finset.sum (Finset.univ : Finset alpha) (fun x =>
            if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0) +
        Finset.sum (Finset.univ : Finset alpha) (fun x =>
            if x ∈ A then 0 else (Dist.mass mu x - Dist.mass nu x) * (r x - m)) := by
      calc
        _ = Finset.sum (Finset.univ : Finset alpha)
            (fun x => (if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0) +
              (if x ∈ A then 0 else (Dist.mass mu x - Dist.mass nu x) * (r x - m))) := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> ring
        _ = _ := by
          rw [Finset.sum_add_distrib]
    have hnonpos :
        Finset.sum (Finset.univ : Finset alpha) (fun x =>
            if x ∈ A then 0 else (Dist.mass mu x - Dist.mass nu x) * (r x - m)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro x _
      split_ifs with hx
      · norm_num
      · have hnot : ¬ x ∈ positiveSet (fun z => Dist.mass mu z)
              (fun z => Dist.mass nu z) := by
          change ¬ x ∈ positiveSet (fun z => Dist.mass mu z)
              (fun z => Dist.mass nu z) at hx
          exact hx
        simp only [positiveSet, Finset.mem_filter] at hnot
        simp at hnot
        rw [mul_comm]
        exact mul_nonpos_of_nonneg_of_nonpos (hsn x) (sub_nonpos_of_le hnot)
    calc
      _ = (Finset.sum (Finset.univ : Finset alpha) (fun x =>
            if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0)) +
          (Finset.sum (Finset.univ : Finset alpha) (fun x =>
            if x ∈ A then 0 else (Dist.mass mu x - Dist.mass nu x) * (r x - m))) :=
        hdecomp
      _ ≤ Finset.sum (Finset.univ : Finset alpha) (fun x =>
          if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0) := by
        have h2 : (Finset.sum (Finset.univ : Finset alpha) (fun x =>
              if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0)) +
            (Finset.sum (Finset.univ : Finset alpha) (fun x =>
              if x ∈ A then 0 else (Dist.mass mu x - Dist.mass nu x) * (r x - m))) ≤
            (Finset.sum (Finset.univ : Finset alpha) (fun x =>
              if x ∈ A then (Dist.mass mu x - Dist.mass nu x) * (r x - m) else 0)) + 0 := by
          apply add_le_add_right
          exact hnonpos
        simpa [add_zero] using h2
      _ = Finset.sum A (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) :=
        sumUnivIte (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) A
  have hAsum :
      Finset.sum A (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) ≤
      dobrushinCoeff K * Finset.sum A (fun x => Dist.mass mu x - Dist.mass nu x) := by
    calc
      _ = Finset.sum A (fun x => (r x - m) * (Dist.mass mu x - Dist.mass nu x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_comm]
      _ ≤ Finset.sum A (fun x => dobrushinCoeff K * (Dist.mass mu x - Dist.mass nu x)) := by
        apply Finset.sum_le_sum
        intro x hx
        have hpos : x ∈ positiveSet (fun z => Dist.mass mu z) (fun z => Dist.mass nu z) := by
          change x ∈ positiveSet (fun z => Dist.mass mu z) (fun z => Dist.mass nu z) at hx
          exact hx
        have hgt : Dist.mass mu x > Dist.mass nu x := by
          simp only [positiveSet, Finset.mem_filter] at hpos
          exact hpos.2
        have hηpos : 0 ≤ Dist.mass mu x - Dist.mass nu x :=
          le_of_lt (sub_pos_of_lt hgt)
        exact mul_le_mul_of_nonneg_right (hsup x) hηpos
      _ = _ := by
        rw [← Finset.mul_sum]
  calc
    _ = vectorTV p q := by
      change vectorTV p q = _
      exact rfl
    _ = positiveSum p q :=
        vectorTV_eq_positive_set p q hpn hqn hp1 hq1
    _ = Finset.sum S₀ (fun y => p y - q y) := rfl
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) :=
      sumOnSEqWeighted K mu nu S₀
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) := hshift.symm
    _ ≤ Finset.sum A (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - m)) := hdrop
    _ ≤ dobrushinCoeff K * Finset.sum A (fun x => Dist.mass mu x - Dist.mass nu x) :=
      hAsum
    _ = dobrushinCoeff K * Dist.tv mu nu := by rw [hsumA]

-- ---------------------------------------------------------------------------
-- Composition and iteration
-- ---------------------------------------------------------------------------

/-- Dobrushin coefficients are submultiplicative under composition: the
coefficient of `comp K L` is at most the product of the coefficients. -/
theorem dobrushinCoeff_submult
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma] [Nonempty alpha] [Nonempty beta]
    (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma) :
    dobrushinCoeff (FiniteKernel.comp K L) ≤
    dobrushinCoeff K * dobrushinCoeff L := by
  refine Finset.max'_le _ (pairDistances_nonempty (FiniteKernel.comp K L))
      (dobrushinCoeff K * dobrushinCoeff L) ?_
  intro d hd
  rw [pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  have hcontra := dobrushin_contraction L (K ij.1) (K ij.2)
  calc
    _ = Dist.tv (FiniteKernel.apply (K ij.1) L) (FiniteKernel.apply (K ij.2) L) := rfl
    _ ≤ dobrushinCoeff L * rowTV K ij.1 ij.2 := hcontra
    _ ≤ dobrushinCoeff L * dobrushinCoeff K := by
      apply mul_le_mul_of_nonneg_left
      · exact rowTV_le_dobrushin K ij.1 ij.2
      · exact dobrushinCoeff_nonneg L
    _ = dobrushinCoeff K * dobrushinCoeff L := by ring

/-- Iterated application: n steps of `K` contract the TV by
`dobrushinCoeff K ^ n` (no extra factor of 2 per step). -/
theorem run_contraction
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (K : FiniteKernel alpha alpha) (n : Nat) (mu nu : Dist alpha) :
    Dist.tv (FiniteKernel.run K n mu) (FiniteKernel.run K n nu) ≤
    dobrushinCoeff K ^ n * Dist.tv mu nu := by
  induction n with
  | zero =>
    have h0 : FiniteKernel.run K 0 mu = mu := by
      simp [FiniteKernel.run]
    have h0' : FiniteKernel.run K 0 nu = nu := by
      simp [FiniteKernel.run]
    rw [h0, h0', pow_zero, one_mul]
  | succ n ih =>
    rw [FiniteKernel.run_succ_add, FiniteKernel.run_succ_add]
    have h1 := dobrushin_contraction K (FiniteKernel.run K n mu)
        (FiniteKernel.run K n nu)
    calc
      _ ≤ dobrushinCoeff K * Dist.tv (FiniteKernel.run K n mu)
          (FiniteKernel.run K n nu) := h1
      _ ≤ dobrushinCoeff K * (dobrushinCoeff K ^ n * Dist.tv mu nu) := by
        apply mul_le_mul_of_nonneg_left
        · exact ih
        · exact dobrushinCoeff_nonneg K
      _ = dobrushinCoeff K ^ (n + 1) * Dist.tv mu nu := by
        rw [pow_succ]
        ring

-- ---------------------------------------------------------------------------
-- Link with the fixed-size matrix theory
-- ---------------------------------------------------------------------------

/-- A row-stochastic matrix viewed as a kernel. -/
private noncomputable def matrixKernel
    [Fintype alpha] [DecidableEq alpha]
    (P : Matrix alpha alpha Rat) (hP : P ∈ Matrix.rowStochastic Rat alpha)
    (i : alpha) : Dist alpha := by
  let hs := (Matrix.mem_rowStochastic_iff_sum (R := Rat) (n := alpha) (M := P)).mp hP
  exact Dist.ofFun (fun j => P i j)
    (fun j => hs.1 i j)
    (hs.2 i)

/-- The kernel-level coefficient of a matrix-as-kernel equals the
matrix-level Dobrushin coefficient. -/
theorem dobrushinCoeff_matrix_link
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) (hP : P ∈ Matrix.rowStochastic Rat alpha) :
    dobrushinCoeff (fun i => matrixKernel P hP i) =
    MatrixTV.dobrushinCoeff P := by
  classical
  have hrow (i j : alpha) :
      Dist.tv (matrixKernel P hP i) (matrixKernel P hP j) =
      MatrixTV.rowTV P i j := by
    change vectorTV (Dist.mass (matrixKernel P hP i))
        (Dist.mass (matrixKernel P hP j)) =
      vectorTV (P i) (P j)
    simp only [matrixKernel, Dist.mass_ofFun, vectorTV]
  have hfin : pairDistances (fun i => matrixKernel P hP i) =
      MatrixTV.pairDistances P := by
    simp only [pairDistances, MatrixTV.pairDistances]
    apply Finset.image_congr
    intro ij _
    change Dist.tv (matrixKernel P hP ij.1) (matrixKernel P hP ij.2) =
      MatrixTV.rowTV P ij.1 ij.2
    exact hrow ij.1 ij.2
  have h2 : dobrushinCoeff (fun i => matrixKernel P hP i) =
      MatrixTV.dobrushinCoeff P := by
    unfold dobrushinCoeff
    unfold MatrixTV.dobrushinCoeff
    unfold Finset.max'
    unfold Finset.sup'
    apply (WithBot.unbot_inj _ _).mpr
    rw [hfin]
  exact h2

end Dobrushin

end Shufflemath
