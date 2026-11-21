module

public import Shufflemath.Dobrushin
public import Shufflemath.TotalVariation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-- The maximum of a nonempty finite set of `Rat`s, every member of which is
    strictly below `1`, is itself strictly below `1` (the maximum is one of
    the members). -/
lemma max'_lt_one_of_all_lt_one (s : Finset Rat) (hne : s.Nonempty)
    (h : ∀ x ∈ s, x < 1) : s.max' hne < 1 := by
  have hmem : s.max' hne ∈ s := Finset.max'_mem _ hne
  exact h (s.max' hne) hmem

/-- **TV < 0.001 pipeline, Dobrushin-`<1` reduction.**  The Dobrushin
    contraction coefficient of a finite kernel is the maximum of the *finite*
    set of all pairwise row total variations (`pairDistances`).  A finite
    maximum is strictly below `1` iff every member is, so:

    if **every** pair of rows has total variation strictly below `1` (i.e. no
    two rows are mutually singular — equivalently every pair of rows has
    overlapping support), then `dobrushinCoeff K < 1`.

    This is the bridge the 99-card TV < 0.001 certificate needs: once the
    Bernoulli-Laplace exchange kernel is shown to have overlapping 1-step
    support for every pair of macrostates (which holds whenever the exchange
    window `2 k` dominates the state span `blHi - blLo`), the Dobrushin
    coefficient is a strict contraction `d < 1`, and `physicalExchange_dobrushinDecay`
    then bounds the physical `n`-exchange deck-TV by `d^n`, which tends to `0`. -/
theorem dobrushinCoeff_lt_one_of_allPairsLtOne
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) (h : ∀ i j, Dist.tv (K i) (K j) < 1) :
    Dobrushin.dobrushinCoeff K < 1 := by
  unfold Dobrushin.dobrushinCoeff
  apply max'_lt_one_of_all_lt_one _ (Dobrushin.pairDistances_nonempty K)
  intro d hd
  dsimp only [Dobrushin.pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  exact h ij.1 ij.2

/-- **TV < 0.001 pipeline, overlap lemma.**  Two probability measures
    (nonnegative mass functions each summing to `1`) that share a point of
    strictly positive mass have total variation **strictly** below `1`.

    `|p x - q x| ≤ p x + q x` pointwise (triangle inequality, both
    nonnegative), strict at the shared point `z` (since `|p z - q z| <
    p z + q z` when both masses are positive).  A finite sum that is
    pointwise `≤` and strict at one point is strictly smaller than the other
    sum, so `Σ |p x - q x| < Σ (p x + q x) = 2`, hence `vectorTV = (1/2) * Σ
    |…| < 1`.  Attaining `1` is exactly the mutually-singular (disjoint-
    support) case.  This is the per-pair engine behind
    `dobrushinCoeff_lt_one_of_allPairsLtOne`: showing two kernel rows overlap
    in support is enough to keep their TV below `1`. -/
theorem vectorTV_lt_one_of_commonPos
    {alpha : Type*} [Fintype alpha] (p q : alpha -> Rat)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsump : Finset.sum Finset.univ p = 1) (hsumq : Finset.sum Finset.univ q = 1)
    (z : alpha) (hpz : 0 < p z) (hqz : 0 < q z) :
    vectorTV p q < 1 := by
  have hle : ∀ x, |p x - q x| ≤ p x + q x := by
    intro x
    have h1 : p x - q x = p x + (-q x) := by ring
    rw [h1]
    calc
      |p x + (-q x)| ≤ |p x| + |(-q x)| := abs_add_le (p x) (-q x)
      _ = |p x| + |q x| := by rw [abs_neg]
      _ = p x + q x := by rw [abs_of_nonneg (hp x), abs_of_nonneg (hq x)]
  have hlt : ∃ x ∈ Finset.univ, |p x - q x| < p x + q x := by
    refine ⟨z, Finset.mem_univ z, ?_⟩
    by_cases hab : p z ≤ q z
    · have habs : |p z - q z| = q z - p z := by
        rw [← neg_sub, abs_neg]
        exact abs_of_nonneg (by linarith)
      rw [habs]
      linarith
    · have habs : |p z - q z| = p z - q z := by
        exact abs_of_nonneg (by linarith)
      rw [habs]
      linarith
  have hsumlt : Finset.sum Finset.univ (fun x => |p x - q x|)
      < Finset.sum Finset.univ (fun x => p x + q x) :=
    Finset.sum_lt_sum (fun x _ => hle x) hlt
  unfold vectorTV
  calc
    (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - q x|)
        < (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => p x + q x) := by
      apply mul_lt_mul_of_pos_left hsumlt
      norm_num
    _ = (1 / 2 : Rat) * (Finset.sum Finset.univ p + Finset.sum Finset.univ q) := by rw [Finset.sum_add_distrib]
    _ = (1 / 2 : Rat) * (1 + 1) := by rw [hsump, hsumq]
    _ = 1 := by norm_num

end Shufflemath
