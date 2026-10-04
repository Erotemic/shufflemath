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
index set is finite), and `dobrushin2 K = 2 * dobrushinCoeff K` is the
contraction constant for the *standard* TV norm (no 1/2 factor):

    tv (apply μ K) (apply ν K) ≤ dobrushin2 K * tv μ ν

Unlike the fixed-size `MatrixTV.dobrushinCoeff`, the rows here are
distributions, so the definition works at the kernel level directly and the
matrix case is recovered as a special case (`dobrushinCoeff_matrix_link`).
-/
namespace Shufflemath

namespace Dobrushin

variable {alpha : Type*} {beta : Type*} {gamma : Type*}

/-- TV distance between two rows of a kernel. -/
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

/-- The contraction constant for the standard TV norm: `2 * dobrushinCoeff`. -/
noncomputable def dobrushin2
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : Rat :=
  2 * dobrushinCoeff K

@[simp]
theorem dobrushin2_def
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : dobrushin2 K = 2 * dobrushinCoeff K :=
  rfl

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

/-- `dobrushin2` is nonnegative. -/
@[simp]
theorem dobrushin2_nonneg
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) : 0 ≤ dobrushin2 K := by
  rw [dobrushin2]
  exact mul_nonneg (by norm_num) (dobrushinCoeff_nonneg K)

private theorem apply_mass_nonneg
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (mu : Dist alpha)
    (K : FiniteKernel alpha beta) (y : beta) :
    0 ≤ Dist.mass (FiniteKernel.apply mu K) y := by
  rw [FiniteKernel.apply_mass]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (Dist.mass_nonneg mu x) (Dist.mass_nonneg (K x) y)

private theorem apply_sum_mass
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (mu : Dist alpha)
    (K : FiniteKernel alpha beta) :
    Finset.sum (Finset.univ : Finset beta) (fun y => Dist.mass (FiniteKernel.apply mu K) y) = 1 := by
  have h1 : Finset.sum (Finset.univ : Finset beta)
      (fun y => Dist.mass (FiniteKernel.apply mu K) y) =
      Finset.sum (Finset.univ : Finset beta)
        (fun y => Finset.sum (Finset.univ : Finset alpha)
          (fun x => Dist.mass mu x * Dist.mass (K x) y)) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [FiniteKernel.apply_mass]
  have h2 : Finset.sum (Finset.univ : Finset beta)
      (fun y => Finset.sum (Finset.univ : Finset alpha)
        (fun x => Dist.mass mu x * Dist.mass (K x) y)) =
      Finset.sum (Finset.univ : Finset alpha)
        (fun x => Dist.mass mu x *
          Finset.sum (Finset.univ : Finset beta) (fun y => Dist.mass (K x) y)) :=
    Dist.double_sum_pullout (fun x => Dist.mass mu x)
      (fun y x => Dist.mass (K x) y)
  have h3 : Finset.sum (Finset.univ : Finset alpha)
      (fun x => Dist.mass mu x *
        Finset.sum (Finset.univ : Finset beta) (fun y => Dist.mass (K x) y)) =
      Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x * 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Dist.sum_mass]
  have h4 : Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x * 1) =
      Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp
  calc
    _ = Finset.sum (Finset.univ : Finset beta)
        (fun y => Finset.sum (Finset.univ : Finset alpha)
          (fun x => Dist.mass mu x * Dist.mass (K x) y)) := h1
    _ = Finset.sum (Finset.univ : Finset alpha)
        (fun x => Dist.mass mu x *
          Finset.sum (Finset.univ : Finset beta) (fun y => Dist.mass (K x) y)) := h2
    _ = Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x * 1) := h3
    _ = Finset.sum (Finset.univ : Finset alpha) (fun x => Dist.mass mu x) := h4
    _ = 1 := Dist.sum_mass mu

/-- For probability vectors, the *absolute* signed mass difference on any
set is at most the TV. This is the B3 workhorse applied to both `p − q`
and `q − p`, packaged as an absolute value. -/
private theorem absSumLeTV [Fintype alpha] [DecidableEq alpha]
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
private theorem rowWeightBound
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
private theorem sumOnSEqWeighted [Fintype alpha] [DecidableEq alpha] [Fintype beta]
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

/-- The main Dobrushin contraction theorem for kernels: one application
of `K` contracts the TV by at most `dobrushin2 K`. -/
theorem dobrushin_contraction
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    [Nonempty alpha]
    (K : FiniteKernel alpha beta) (mu nu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu K) (FiniteKernel.apply nu K) ≤
    dobrushin2 K * Dist.tv mu nu := by
  classical
  let p : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply mu K) y
  let q : beta -> Rat := fun y => Dist.mass (FiniteKernel.apply nu K) y
  let S₀ := positiveSet p q
  let r : alpha -> Rat := fun x => Finset.sum S₀ (fun y => Dist.mass (K x) y)
  let x₀ : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have hpn : ∀ y, 0 ≤ p y := fun y => apply_mass_nonneg mu K y
  have hqn : ∀ y, 0 ≤ q y := fun y => apply_mass_nonneg nu K y
  have hp1 : Finset.sum (Finset.univ : Finset beta) p = 1 := apply_sum_mass mu K
  have hq1 : Finset.sum (Finset.univ : Finset beta) q = 1 := apply_sum_mass nu K
  have hsum0 : Finset.sum (Finset.univ : Finset alpha)
      (fun x => Dist.mass mu x - Dist.mass nu x) = 0 := by
    rw [Finset.sum_sub_distrib, Dist.sum_mass, Dist.sum_mass]
    norm_num
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
        (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - r x₀)) := by
      have h1 : Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) =
          Finset.sum (Finset.univ : Finset alpha)
            (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - r x₀)) +
          Finset.sum (Finset.univ : Finset alpha)
            (fun x => (Dist.mass mu x - Dist.mass nu x) * r x₀) := by
        have h2b : Finset.sum (Finset.univ : Finset alpha)
            (fun x => (Dist.mass mu x - Dist.mass nu x) * (r x - r x₀)) +
            Finset.sum (Finset.univ : Finset alpha)
              (fun x => (Dist.mass mu x - Dist.mass nu x) * r x₀) =
            Finset.sum (Finset.univ : Finset alpha)
              (fun x => (Dist.mass mu x - Dist.mass nu x) * r x) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
        exact h2b.symm
      have hD : Finset.sum (Finset.univ : Finset alpha)
          (fun x => (Dist.mass mu x - Dist.mass nu x) * r x₀) = 0 := by
        rw [← Finset.sum_mul]
        rw [hsum0]
        simp
      rw [h1, hD]
      simp
    _ ≤ Finset.sum (Finset.univ : Finset alpha)
        (fun x => |Dist.mass mu x - Dist.mass nu x| * |r x - r x₀|) := by
      refine Finset.sum_le_sum fun x _ => ?_
      calc
        _ ≤ |(Dist.mass mu x - Dist.mass nu x) * (r x - r x₀)| := le_abs_self _
        _ = |Dist.mass mu x - Dist.mass nu x| * |r x - r x₀| :=
            abs_mul _ _
    _ ≤ Finset.sum (Finset.univ : Finset alpha)
        (fun x => |Dist.mass mu x - Dist.mass nu x| * dobrushinCoeff K) := by
      refine Finset.sum_le_sum fun x _ => ?_
      apply mul_le_mul_of_nonneg_left
      · exact (rowWeightBound K S₀ x x₀).trans (rowTV_le_dobrushin K x x₀)
      · exact abs_nonneg _
    _ = dobrushinCoeff K *
        Finset.sum (Finset.univ : Finset alpha)
          (fun x => |Dist.mass mu x - Dist.mass nu x|) := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ dobrushin2 K * Dist.tv mu nu := by
      let Sabs : Rat := Finset.sum (Finset.univ : Finset alpha)
          (fun x => |Dist.mass mu x - Dist.mass nu x|)
      have h2c : 2 * dobrushinCoeff K * ((1 / 2) * Sabs) =
          dobrushinCoeff K * Sabs := by
        field_simp
      rw [dobrushin2, Dist.tv, vectorTV, h2c]

/-- Dobrushin coefficients are submultiplicative along composition. -/
theorem dobrushin2_submult
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma] [Nonempty alpha] [Nonempty beta]
    (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma) :
    dobrushin2 (FiniteKernel.comp K L) ≤ dobrushin2 K * dobrushin2 L := by
  simp only [dobrushin2]
  have hc : dobrushinCoeff (FiniteKernel.comp K L) ≤
      2 * dobrushinCoeff K * dobrushinCoeff L := by
    refine Finset.max'_le _ (pairDistances_nonempty (FiniteKernel.comp K L))
      (2 * dobrushinCoeff K * dobrushinCoeff L) ?_
    intro d hd
    rw [pairDistances] at hd
    rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
    have hcontra := dobrushin_contraction L (K ij.1) (K ij.2)
    rw [dobrushin2] at hcontra
    calc
      _ ≤ 2 * dobrushinCoeff L * rowTV K ij.1 ij.2 := hcontra
      _ ≤ 2 * dobrushinCoeff L * dobrushinCoeff K := by
        apply mul_le_mul_of_nonneg_left
        · exact rowTV_le_dobrushin K ij.1 ij.2
        · exact mul_nonneg (by norm_num) (dobrushinCoeff_nonneg L)
      _ = 2 * dobrushinCoeff K * dobrushinCoeff L := by ring
  calc
    _ = 2 * dobrushinCoeff (FiniteKernel.comp K L) := rfl
    _ ≤ 2 * (2 * dobrushinCoeff K * dobrushinCoeff L) := by
      apply mul_le_mul_of_nonneg_left
      · exact hc
      · norm_num
    _ = 2 * dobrushinCoeff K * (2 * dobrushinCoeff L) := by ring

/-- Iterated application: n steps of `K` contract the TV by `dobrushin2 K ^ n`. -/
theorem run_contraction
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (K : FiniteKernel alpha alpha) (n : Nat) (mu nu : Dist alpha) :
    Dist.tv (FiniteKernel.run K n mu) (FiniteKernel.run K n nu) ≤
    dobrushin2 K ^ n * Dist.tv mu nu := by
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
      _ ≤ dobrushin2 K * Dist.tv (FiniteKernel.run K n mu)
          (FiniteKernel.run K n nu) := h1
      _ ≤ dobrushin2 K * (dobrushin2 K ^ n * Dist.tv mu nu) := by
        apply mul_le_mul_of_nonneg_left
        · exact ih
        · exact dobrushin2_nonneg K
      _ = dobrushin2 K ^ (n + 1) * Dist.tv mu nu := by
        rw [pow_succ]
        ring

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
