import Shufflemath.Matrix
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Shufflemath

/-- Exact total-variation distance for two rational finite vectors. -/
def vectorTV {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : Rat :=
  (1 / 2 : Rat) *
    Finset.sum Finset.univ (fun x => |p x - q x|)

@[simp]
theorem vectorTV_self {alpha : Type*} [Fintype alpha]
    (p : alpha -> Rat) : vectorTV p p = 0 := by
  simp [vectorTV]

theorem vectorTV_comm {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : vectorTV p q = vectorTV q p := by
  unfold vectorTV
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm (p x) (q x)

theorem vectorTV_nonneg {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : 0 <= vectorTV p q := by
  unfold vectorTV
  positivity

/-- Triangle inequality: total variation is a metric on finite rational
vectors. Pointwise, `|p x - r x| = |(p x - q x) + (q x - r x)|` and `abs_add`;
then the sum splits over the two terms. -/
theorem vectorTV_triangle {alpha : Type*} [Fintype alpha]
    (p q r : alpha -> Rat) :
    vectorTV p r <= vectorTV p q + vectorTV q r := by
  have hterm : forall x, |p x - r x| <= |p x - q x| + |q x - r x| := by
    intro x
    have h : p x - r x = (p x - q x) + (q x - r x) := by ring
    calc
      |p x - r x| = |(p x - q x) + (q x - r x)| := by rw [h]
      _ <= |p x - q x| + |q x - r x| := by exact abs_add_le _ _
  unfold vectorTV
  calc
    (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - r x|) <=
        (1 / 2 : Rat) * (Finset.sum Finset.univ (fun x => |p x - q x|) +
          Finset.sum Finset.univ (fun x => |q x - r x|)) := by
      rw [← Finset.sum_add_distrib]
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hterm x))
      norm_num
    _ = vectorTV p q + vectorTV q r := by
      simp [vectorTV]
      ring

/-- Probability vectors are at total-variation distance at most one. -/
theorem vectorTV_le_one_of_probability
    {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat)
    (hp : forall x, 0 <= p x)
    (hq : forall x, 0 <= q x)
    (hp1 : Finset.sum Finset.univ p = 1)
    (hq1 : Finset.sum Finset.univ q = 1) :
    vectorTV p q <= 1 := by
  have hterm : forall x, |p x - q x| <= p x + q x := by
    intro x
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using
      (abs_add_le (p x) (-q x))
  have hsum :
      Finset.sum Finset.univ (fun x => |p x - q x|) <=
        Finset.sum Finset.univ (fun x => p x + q x) := by
    exact Finset.sum_le_sum (fun x _ => hterm x)
  calc
    vectorTV p q <=
        (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => p x + q x) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 1 := by
      rw [Finset.sum_add_distrib, hp1, hq1]
      norm_num

/-- Zero TV distance is exactly equality of the mass functions: a sum of
nonnegatives is zero iff every term is zero (`Finset.single_le_sum`). -/
theorem vectorTV_eq_zero {alpha : Type*} [Fintype alpha] (p q : alpha -> Rat) :
    vectorTV p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsum : Finset.sum Finset.univ (fun x => |p x - q x|) = 0 := by
      have h' : (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - q x|) = 0 := by
        unfold vectorTV at h
        exact h
      calc
        Finset.sum Finset.univ (fun x => |p x - q x|) =
            2 * ((1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - q x|)) := by ring
        _ = 2 * 0 := by rw [h']
        _ = 0 := by norm_num
    ext x
    have hterm : |p x - q x| = 0 := by
      apply le_antisymm
      · calc
          |p x - q x| <= Finset.sum Finset.univ (fun i => |p i - q i|) :=
            Finset.single_le_sum (fun i _ => abs_nonneg (p i - q i)) (Finset.mem_univ x)
          _ = 0 := hsum
      · exact abs_nonneg (p x - q x)
    rw [abs_eq_zero] at hterm
    exact sub_eq_zero.mp hterm
  · intro h
    rw [h, vectorTV_self]

namespace Dist

/-- Total variation on semantic exact finite distributions. -/
def tv {alpha : Type*} [Fintype alpha] (p q : Dist alpha) : Rat :=
  vectorTV (mass p) (mass q)

@[simp]
theorem tv_self {alpha : Type*} [Fintype alpha] (p : Dist alpha) :
    tv p p = 0 := by
  simp [tv]

theorem tv_comm {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q = tv q p := by
  exact vectorTV_comm _ _

theorem tv_nonneg {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    0 <= tv p q := by
  exact vectorTV_nonneg _ _

theorem tv_triangle {alpha : Type*} [Fintype alpha] (p q r : Dist alpha) :
    tv p r <= tv p q + tv q r := by
  simpa [tv] using vectorTV_triangle _ _ _

/-- Zero TV distance is exactly pointwise equality of the mass functions.
(Stated at mass level, not `p = q`: distinct `Dist` representations can
share the same mass function, e.g. weight zero on a point.) -/
theorem tv_eq_zero {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q = 0 ↔ ∀ x, mass p x = mass q x := by
  simp only [tv]
  rw [vectorTV_eq_zero]
  exact ⟨fun h => fun x => congrFun h x, fun h => funext h⟩

theorem tv_le_one {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q <= 1 := by
  apply vectorTV_le_one_of_probability
  · exact mass_nonneg p
  · exact mass_nonneg q
  · exact sum_mass p
  · exact sum_mass q

end Dist

namespace MatrixTV

variable {alpha : Type*}

/-- TV distance between two rows of a rational transition matrix. -/
def rowTV [Fintype alpha] (P : Matrix alpha alpha Rat) (i j : alpha) : Rat :=
  vectorTV (P i) (P j)

/-- The finite set of all pairwise row distances. -/
def pairDistances [Fintype alpha] [DecidableEq alpha]
    (P : Matrix alpha alpha Rat) : Finset Rat :=
  ((Finset.univ : Finset alpha).product Finset.univ).image
    (fun ij => rowTV P ij.1 ij.2)

theorem pairDistances_nonempty
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) : (pairDistances P).Nonempty := by
  classical
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  exact ⟨rowTV P x x, by simp [pairDistances, x]⟩

/-- Exact finite Dobrushin coefficient: maximum TV distance between matrix rows. -/
def dobrushinCoeff
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) : Rat :=
  (pairDistances P).max' (pairDistances_nonempty P)

theorem rowTV_le_dobrushin
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) (i j : alpha) :
    rowTV P i j <= dobrushinCoeff P := by
  unfold dobrushinCoeff
  apply Finset.le_max'
  simp [pairDistances]

@[simp]
theorem dobrushinCoeff_nonneg
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) :
    0 <= dobrushinCoeff P := by
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have h := rowTV_le_dobrushin P x x
  simpa [rowTV] using h

/-- A row-stochastic rational matrix has Dobrushin coefficient at most one. -/
theorem dobrushinCoeff_le_one
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat)
    (hP : P ∈ Matrix.rowStochastic Rat alpha) :
    dobrushinCoeff P <= 1 := by
  unfold dobrushinCoeff
  apply Finset.max'_le
  intro d hd
  rw [pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  apply vectorTV_le_one_of_probability
  · intro x
    exact Matrix.nonneg_of_mem_rowStochastic hP
  · intro x
    exact Matrix.nonneg_of_mem_rowStochastic hP
  · exact Matrix.sum_row_of_mem_rowStochastic hP ij.1
  · exact Matrix.sum_row_of_mem_rowStochastic hP ij.2

end MatrixTV
end Shufflemath
