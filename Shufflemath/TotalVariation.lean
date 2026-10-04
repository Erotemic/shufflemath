import Shufflemath.Matrix
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic

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

section PositiveSet

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The set of coordinates where `p` strictly exceeds `q`. -/
def positiveSet (p q : alpha -> Rat) : Finset alpha :=
  (Finset.univ : Finset alpha).filter (fun x => p x > q x)

/-- Total mass by which `p` exceeds `q`, counted only at the coordinates
where it is larger. For probability vectors this equals the TV distance
(vectorTV_eq_positive_set) and upper-bounds `\sum_S (p - q)` for every
`S` (vectorTV_sum_le_positive_set). -/
def positiveSum (p q : alpha -> Rat) : Rat :=
  Finset.sum (positiveSet p q) (fun x => p x - q x)

/-- Pointwise: the positive parts of `a - b` and `b - a` add to `|a - b|`
and differ by `a - b`. -/
private theorem maxDiffAbs {a b : Rat} :
    max 0 (a - b) + max 0 (b - a) = |a - b| := by
  cases le_total a b with
  | inl h =>
    have h1 : max 0 (a - b) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    have h2 : max 0 (b - a) = b - a := by
      exact max_eq_right (sub_nonneg_of_le h)
    rw [h1, h2]
    simpa only [zero_add, abs_sub_comm] using (abs_of_nonneg (sub_nonneg_of_le h)).symm
  | inr h =>
    have h1 : max 0 (a - b) = a - b := by
      exact max_eq_right (sub_nonneg_of_le h)
    have h2 : max 0 (b - a) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    rw [h1, h2]
    simpa only [add_zero] using (abs_of_nonneg (sub_nonneg_of_le h)).symm

private theorem maxDiffSub {a b : Rat} :
    max 0 (a - b) - max 0 (b - a) = a - b := by
  cases le_total a b with
  | inl h =>
    have h1 : max 0 (a - b) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    have h2 : max 0 (b - a) = b - a := by
      exact max_eq_right (sub_nonneg_of_le h)
    rw [h1, h2]
    simpa only [zero_sub] using neg_sub b a
  | inr h =>
    have h1 : max 0 (a - b) = a - b := by
      exact max_eq_right (sub_nonneg_of_le h)
    have h2 : max 0 (b - a) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    rw [h1, h2]
    simp only [sub_zero]

/-- The univ-sum of the positive part of `p - q` is exactly the positive
sum: off the positive set the positive part vanishes, and on it it is
`p - q` itself. (Probability hypotheses are only used to state the result
in TV-friendly form; the identity itself is pointwise. -/
private theorem sumPosPartEqPositiveSum
    (p q : alpha -> Rat) :
    Finset.sum Finset.univ (fun x => max 0 (p x - q x)) = positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  have hzero : forall x, x ∈ Finset.univ \ positiveSet p q -> u x = 0 := by
    intro x hx
    have hnot : ¬ p x > q x := by
      have hnot2 : x ∉ positiveSet p q := (Finset.mem_sdiff.mp hx).2
      intro hpos
      have hm : x ∈ positiveSet p q := by
        rw [positiveSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hpos⟩
      exact hnot2 hm
    have hle : p x <= q x := by
      exact not_lt.mp hnot
    change max 0 (p x - q x) = 0
    exact max_eq_left (sub_nonpos_of_le hle)
  have hzero2 : Finset.sum (Finset.univ \ positiveSet p q) u = 0 := by
    rw [Finset.sum_congr rfl (fun x hx => hzero x hx)]
    rw [Finset.sum_const_zero]
  rw [← Finset.sum_sdiff (Finset.subset_univ (positiveSet p q)), hzero2, zero_add,
      positiveSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hpos : p x > q x := by
    rw [positiveSet, Finset.mem_filter] at hx
    exact hx.2
  change max 0 (p x - q x) = p x - q x
  exact max_eq_right (le_of_lt (sub_pos_of_lt hpos))

/-- For probability vectors, the TV distance equals the excess mass of `p`
over `q` on the positive set (equivalently, the maximum of
`\sum_S (p - q)` over all `S`, attained at the positive set).

Proof: with `u x = max 0 (p x - q x)` and
`v x = max 0 (q x - p x)`, pointwise `|p x - q x| = u x + v x` and
`u x - v x = p x - q x`; since `\sum (p - q) = 0` the univ sums of `u` and
`v` coincide, so `\sum |p - q| = 2 * \sum u` and the factor `1 / 2` cancels.
-/
theorem vectorTV_eq_positive_set
    (p q : alpha -> Rat)
    (_hp : forall x, 0 <= p x) (_hq : forall x, 0 <= q x)
    (hp1 : Finset.sum Finset.univ p = 1) (hq1 : Finset.sum Finset.univ q = 1) :
    vectorTV p q = positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  let v := fun x => max 0 (q x - p x)
  have hterm : forall x, |p x - q x| = u x + v x := by
    intro x
    change |p x - q x| = max 0 (p x - q x) + max 0 (q x - p x)
    exact (maxDiffAbs (a := p x) (b := q x)).symm
  have hdiff : forall x, u x - v x = p x - q x := by
    intro x
    change max 0 (p x - q x) - max 0 (q x - p x) = p x - q x
    exact maxDiffSub (a := p x) (b := q x)
  have hsum0 : Finset.sum Finset.univ (fun x => u x - v x) = 0 := by
    rw [Finset.sum_congr rfl (fun x _ => hdiff x)]
    rw [Finset.sum_sub_distrib, hp1, hq1]
    norm_num
  have hsumuv : Finset.sum Finset.univ u = Finset.sum Finset.univ v := by
    rw [Finset.sum_sub_distrib] at hsum0
    exact sub_eq_zero.mp hsum0
  have hsumabs : Finset.sum Finset.univ (fun x => |p x - q x|) =
      2 * Finset.sum Finset.univ u := by
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    rw [Finset.sum_add_distrib]
    rw [hsumuv]
    ring
  unfold vectorTV
  rw [hsumabs]
  ring_nf
  exact sumPosPartEqPositiveSum p q

/-- For probability vectors, the signed mass `p - q` accumulated on any set
is at most the positive sum, i.e. at most the TV distance: this is the
max-event characterization `TV(p, q) = sup {\sum_S (p - q) | S}` with the
supremum attained at the positive set. (The inequality actually holds for
arbitrary `p q`; the probability hypotheses are kept so the statement
reads as the TV statement.) -/
theorem vectorTV_sum_le_positive_set
    (p q : alpha -> Rat)
    (_hp : forall x, 0 <= p x) (_hq : forall x, 0 <= q x)
    (_hp1 : Finset.sum Finset.univ p = 1) (_hq1 : Finset.sum Finset.univ q = 1)
    (S : Finset alpha) :
    Finset.sum S (fun x => p x - q x) <= positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  let v := fun x => max 0 (q x - p x)
  have hdiff : forall x, u x - v x = p x - q x := by
    intro x
    change max 0 (p x - q x) - max 0 (q x - p x) = p x - q x
    exact maxDiffSub (a := p x) (b := q x)
  have hsumu : Finset.sum Finset.univ u = positiveSum p q :=
    sumPosPartEqPositiveSum p q
  have hvn : 0 <= Finset.sum S v :=
    Finset.sum_nonneg fun _ _ => le_max_left 0 _
  -- Embed the `S`-sum as a `univ`-sum of an ite: the resulting fold is
  -- over `univ` (cheap) rather than over `univ \ S` (its sdiff fold
  -- whnfs badly in the kernel while `S` is a variable, and times out
  -- even with a raised heartbeat).
  have hite : Finset.sum S u = Finset.sum Finset.univ (fun x => if x ∈ S then u x else 0) := by
    simp
  have hpt : forall x, (if x ∈ S then u x else 0) <= u x := by
    intro x
    split_ifs with hx
    · exact le_rfl
    · change 0 <= max 0 (p x - q x)
      exact le_max_left 0 (p x - q x)
  calc
    Finset.sum S (fun x => p x - q x) = Finset.sum S u - Finset.sum S v := by
      have h1 : Finset.sum S (fun x => p x - q x) =
          Finset.sum S (fun x => u x - v x) :=
        Finset.sum_congr rfl fun x _ => (hdiff x).symm
      have h2 : Finset.sum S (fun x => u x - v x) =
          Finset.sum S u - Finset.sum S v :=
        Finset.sum_sub_distrib (fun x => u x) (fun x => v x)
      exact Eq.trans h1 h2
    _ <= Finset.sum S u :=
      sub_le_self _ hvn
    _ = Finset.sum Finset.univ (fun x => if x ∈ S then u x else 0) :=
      hite
    _ <= Finset.sum Finset.univ u :=
      Finset.sum_le_sum fun x _ => hpt x
    _ = positiveSum p q :=
      hsumu

end PositiveSet

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
