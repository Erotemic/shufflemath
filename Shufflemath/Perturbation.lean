import Shufflemath.TotalVariation
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Shufflemath

/-!
## Perturbation bounds for kernel protocols

How much does one step of a protocol matter? If two kernels `K` and `L`
differ, then pushing the **same** distribution through each of them is
apart in total variation by at most the kernels' `kernelDiscrepancy`
(`apply_discrepancy_bound`) — the same weighted-Fubini argument as
`Dist.kernel_contraction` with one side fixed. `compList` composes a list
of kernels in execution order; the telescoping `hybridTelescope` bound
built on these (Priority C flagship, with D) quantifies how a one-step
perturbation of a protocol propagates through the remaining steps.
-/

variable {alpha beta : Type*}

private def kernelDiscrepancySet [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] (K L : FiniteKernel alpha beta) : Finset Rat :=
  (Finset.univ : Finset alpha).image (fun x => Dist.tv (K x) (L x))

theorem kernelDiscrepancySet_nonempty [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) :
    (kernelDiscrepancySet K L).Nonempty := by
  classical
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  exact ⟨Dist.tv (K x) (L x), by simp [kernelDiscrepancySet, x]⟩

/-- The maximum total-variation distance between the rows of two kernels at
the same input point: a one-step measure of how different the two protocols
are. Mirrors `MatrixTV.dobrushinCoeff` (which is the case `L = K` of the
same row-pairing construction) at the semantic kernel level. -/
def kernelDiscrepancy [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) : Rat :=
  (kernelDiscrepancySet K L).max' (kernelDiscrepancySet_nonempty K L)

/-- A single row-pair distance never exceeds the discrepancy. -/
theorem rowTV_le_kernelDiscrepancy [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) (x : alpha) :
    Dist.tv (K x) (L x) <= kernelDiscrepancy K L := by
  unfold kernelDiscrepancy
  apply Finset.le_max'
  simp [kernelDiscrepancySet]

@[simp]
theorem kernelDiscrepancy_nonneg [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) : 0 <= kernelDiscrepancy K L := by
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have h := rowTV_le_kernelDiscrepancy K L x
  have h2 : 0 <= Dist.tv (K x) (L x) := Dist.tv_nonneg (K x) (L x)
  simpa [kernelDiscrepancy] using le_trans h2 h

/-- Two kernels with rows that are distributions have discrepancy at most one. -/
theorem kernelDiscrepancy_le_one [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) : kernelDiscrepancy K L <= 1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  exact Dist.tv_le_one (K x) (L x)

private theorem double_sum_pullout [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] (a : beta → Rat) (b : alpha → beta → Rat) :
    (∑ i, ∑ j, a j * b i j) = ∑ j, a j * ∑ i, b i j := by
  classical
  have : (∑ i ∈ (Finset.univ : Finset alpha), ∑ j ∈ (Finset.univ : Finset beta), a j * b i j) =
        ∑ j ∈ (Finset.univ : Finset beta), a j * ∑ i ∈ (Finset.univ : Finset alpha), b i j := by
    classical
    induction (Finset.univ : Finset alpha) using Finset.induction with
    | empty => simp
    | insert c t hc ih =>
      rw [Finset.sum_insert hc]
      rw [ih]
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl fun j _ =>
          (mul_add (a j) (b c j) (Finset.sum t (fun i => b i j))).symm]
      rw [Finset.sum_congr rfl fun j _ =>
          congrArg (fun u => a j * u) (Finset.sum_insert hc (f := fun i => b i j)).symm]
  simpa using this

/-- Pushing one distribution through two different kernels: the TV distance
of the two outputs is at most the kernels' row discrepancy. This is the
one-step case of the protocol telescope — a single perturbation costs at
most the discrepancy, before any damping by subsequent steps. -/
theorem apply_discrepancy_bound [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha]
    (K L : FiniteKernel alpha beta) (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu K) (FiniteKernel.apply mu L) <= kernelDiscrepancy K L := by
  simp only [Dist.tv, vectorTV, FiniteKernel.apply_mass]
  have hdiff : ∀ (i : beta), (∑ j, Dist.mass mu j * Dist.mass (K j) i) -
      (∑ j, Dist.mass mu j * Dist.mass (L j) i) =
      ∑ j, Dist.mass mu j * (Dist.mass (K j) i - Dist.mass (L j) i) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl fun i _ => congrArg abs (hdiff i)]
  have hpointwise : ∀ (i : beta),
      |∑ j, Dist.mass mu j * (Dist.mass (K j) i - Dist.mass (L j) i)| ≤
      ∑ j, Dist.mass mu j * |Dist.mass (K j) i - Dist.mass (L j) i| := by
    intro i
    calc
      _ ≤ ∑ j, |(Dist.mass mu j * (Dist.mass (K j) i - Dist.mass (L j) i))| :=
          Finset.abs_sum_le_sum_abs
            (fun j => Dist.mass mu j * (Dist.mass (K j) i - Dist.mass (L j) i)) Finset.univ
      _ = ∑ j, Dist.mass mu j * |Dist.mass (K j) i - Dist.mass (L j) i| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (Dist.mass_nonneg mu j)]
  have htw : ∀ (j : alpha),
      ∑ i, |Dist.mass (K j) i - Dist.mass (L j) i| = 2 * Dist.tv (K j) (L j) := by
    intro j
    simp only [Dist.tv, vectorTV]
    ring
  have hΔ : ∀ (j : alpha), Dist.tv (K j) (L j) <= kernelDiscrepancy K L :=
    fun j => rowTV_le_kernelDiscrepancy K L j
  calc
    (1 / 2 : Rat) * ∑ i, |∑ j, Dist.mass mu j * (Dist.mass (K j) i - Dist.mass (L j) i)| ≤
        (1 / 2 : Rat) * ∑ i, ∑ j, Dist.mass mu j * |Dist.mass (K j) i - Dist.mass (L j) i| := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i _
        exact hpointwise i
      · norm_num
    _ = (1 / 2 : Rat) * ∑ j, Dist.mass mu j * ∑ i, |Dist.mass (K j) i - Dist.mass (L j) i| := by
      apply congrArg _
      rw [double_sum_pullout (fun j => Dist.mass mu j)
          (fun i j => |Dist.mass (K j) i - Dist.mass (L j) i|)]
    _ = (1 / 2 : Rat) * ∑ j, Dist.mass mu j * (2 * Dist.tv (K j) (L j)) := by
      apply congrArg _
      apply Finset.sum_congr rfl
      intro j _
      rw [htw j]
    _ ≤ (1 / 2 : Rat) * ∑ j, Dist.mass mu j * (2 * kernelDiscrepancy K L) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hΔ j) (by norm_num))
          (Dist.mass_nonneg mu j)
      · norm_num
    _ = (1 / 2 : Rat) * (2 * kernelDiscrepancy K L) * ∑ j, Dist.mass mu j := by
      rw [← Finset.sum_mul]
      ring
    _ = (1 / 2 : Rat) * (2 * kernelDiscrepancy K L) := by
      rw [Dist.sum_mass]
      ring
    _ = kernelDiscrepancy K L := by ring

/-- Compose a list of kernels in execution order: `compList [K1, K2]` runs
`K1` first, then `K2` (matching the `comp` convention). -/
noncomputable def compList (Ks : List (FiniteKernel alpha alpha)) : FiniteKernel alpha alpha :=
  List.foldr FiniteKernel.comp FiniteKernel.identity Ks

@[simp]
theorem compList_nil : compList [] = (FiniteKernel.identity : FiniteKernel alpha alpha) := by simp [compList]

@[simp]
theorem compList_cons (K : FiniteKernel alpha alpha) (Ks : List (FiniteKernel alpha alpha)) :
    compList (K :: Ks) = FiniteKernel.comp K (compList Ks) := by simp [compList]

/-- Applying a whole one-head protocol list is the head applied to the input,
then the tail protocol: the induction spine of `hybridTelescope`. -/
theorem apply_compList (mu : Dist alpha) (K : FiniteKernel alpha alpha)
    (Ks : List (FiniteKernel alpha alpha)) :
    FiniteKernel.apply mu (compList (K :: Ks)) =
    FiniteKernel.apply (FiniteKernel.apply mu K) (compList Ks) := by
  rw [compList_cons]
  exact (FiniteKernel.apply_comp mu K (compList Ks)).symm

end Shufflemath
