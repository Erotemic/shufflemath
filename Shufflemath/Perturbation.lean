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

/-- Telescoping sum for the perturbation bound: the one-step discrepancy at
position i is damped by `d` raised to the number of steps remaining after
it — the first step is damped the most, the last step not at all. -/
def telescopeBound (d : Rat) (Δ : List Rat) : Rat :=
  match Δ with
  | [] => 0
  | x :: xs => x * d ^ xs.length + telescopeBound d xs

@[simp]
theorem telescopeBound_nil (d : Rat) : telescopeBound d [] = 0 := rfl

@[simp]
theorem telescopeBound_cons (d : Rat) (x : Rat) (xs : List Rat) :
    telescopeBound d (x :: xs) = x * d ^ xs.length + telescopeBound d xs := rfl

/-- A whole protocol list contracts by at most the product of the
contraction bounds of its kernels: the later steps damp what the earlier
steps leave behind. -/
private theorem compList_contraction [Fintype alpha] [DecidableEq alpha]
    (Ks : List (FiniteKernel alpha alpha)) (d : Rat) (hd0 : 0 ≤ d)
    (hd : ∀ (K : FiniteKernel alpha alpha), K ∈ Ks →
      ∀ (r s : Dist alpha),
      Dist.tv (FiniteKernel.apply r K) (FiniteKernel.apply s K) ≤ d * Dist.tv r s)
    (p q : Dist alpha) :
    Dist.tv (FiniteKernel.apply p (compList Ks)) (FiniteKernel.apply q (compList Ks)) ≤
    d ^ Ks.length * Dist.tv p q := by
  induction Ks generalizing d hd0 p q with
  | nil =>
    simp [compList, Dist.tv]
  | cons K Ks ih =>
    rw [apply_compList p K Ks, apply_compList q K Ks]
    have htail : ∀ (K2 : FiniteKernel alpha alpha), K2 ∈ Ks →
      ∀ (r s : Dist alpha),
      Dist.tv (FiniteKernel.apply r K2) (FiniteKernel.apply s K2) ≤ d * Dist.tv r s :=
      fun K2 hK2 r s => hd K2 (List.mem_cons_of_mem K hK2) r s
    have hmem : K ∈ K :: Ks := by exact List.mem_cons_self
    calc
      _ ≤ d ^ Ks.length * Dist.tv (FiniteKernel.apply p K) (FiniteKernel.apply q K) :=
          ih d hd0 htail (FiniteKernel.apply p K) (FiniteKernel.apply q K)
      _ ≤ d ^ Ks.length * d * Dist.tv p q := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left
          (hd K hmem p q)
        exact pow_nonneg hd0 Ks.length
      _ = d ^ (Ks.length + 1) * Dist.tv p q := by rw [← pow_succ]

/-- **Hybrid perturbation bound (the C flagship).** Two protocols of equal
length over the same state space, starting from the same distribution, with
every kernel of both protocols contracting TV by at most `d` (nonnegative).
Then the TV distance of the final states is at most the telescoping sum:
the one-step discrepancy (max row-TV) of the two kernels at step i, times
`d` raised to the number of steps remaining after it. The proof is the
induction the doc sketch describes: the triangle inequality splits the
comparison into a *suffix-protocol* part (handled by the induction
hypothesis, since the same intermediate distribution feeds both suffixes)
and a *same-suffix, different-input* part (handled by the suffix
contraction and the one-step `apply_discrepancy_bound`). Stated with a
*uniform* `d` for both lists (the form the doc sketch uses, `d2`-style);
a per-step constant version follows from D's submultiplicativity.
A one-step protocol (`[K]` vs `[L]`) gives exactly `apply_discrepancy_bound`
(see `hybridTelescope_n1`). -/
theorem hybridTelescope [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (Ks Ls : List (FiniteKernel alpha alpha)) (hlen : Ks.length = Ls.length)
    (mu : Dist alpha) (d : Rat) (hd0 : 0 ≤ d)
    (hdK : ∀ (K : FiniteKernel alpha alpha), K ∈ Ks →
      ∀ (p q : Dist alpha),
      Dist.tv (FiniteKernel.apply p K) (FiniteKernel.apply q K) ≤ d * Dist.tv p q)
    (hdL : ∀ (K : FiniteKernel alpha alpha), K ∈ Ls →
      ∀ (p q : Dist alpha),
      Dist.tv (FiniteKernel.apply p K) (FiniteKernel.apply q K) ≤ d * Dist.tv p q) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) (FiniteKernel.apply mu (compList Ls)) ≤
    telescopeBound d (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
      kernelDiscrepancy p.1 p.2) (Ks.zip Ls)) := by
  induction Ks generalizing Ls mu d hd0 hdL with
  | nil =>
    cases Ls with
    | nil =>
      simp [compList, Dist.tv, vectorTV]
    | cons a as =>
      rw [List.length_cons] at hlen
      exfalso
      apply Nat.succ_ne_zero as.length
      exact hlen.symm
  | cons K0 Ks' ih =>
    cases Ls with
    | nil =>
      rw [List.length_cons] at hlen
      exfalso
      apply Nat.succ_ne_zero Ks'.length
      exact hlen
    | cons L0 Ls'' =>
      have hlen' : Ks'.length = Ls''.length := by
        rw [List.length_cons, List.length_cons] at hlen
        simpa using Nat.succ_inj.mp hlen
      set Δ' : List Rat :=
        List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
          kernelDiscrepancy p.1 p.2) (Ks'.zip Ls'') with hΔ'
      have hdK' := fun (K : FiniteKernel alpha alpha) (hK : K ∈ Ks') (p q : Dist alpha) =>
        hdK K (List.mem_cons_of_mem K0 hK) p q
      have hdL' := fun (K : FiniteKernel alpha alpha) (hL : K ∈ Ls'') (p q : Dist alpha) =>
        hdL K (List.mem_cons_of_mem L0 hL) p q
      have hIH := ih Ls'' hlen' (FiniteKernel.apply mu K0) d hd0 hdK' hdL'
      have hSuf := compList_contraction Ls'' d hd0 hdL'
        (FiniteKernel.apply mu K0) (FiniteKernel.apply mu L0)
      have hΔ0 := apply_discrepancy_bound K0 L0 mu
      rw [compList_cons, compList_cons, ← FiniteKernel.apply_comp mu K0 (compList Ks'),
          ← FiniteKernel.apply_comp mu L0 (compList Ls'')]
      let A := FiniteKernel.apply (FiniteKernel.apply mu K0) (compList Ks')
      let C := FiniteKernel.apply (FiniteKernel.apply mu K0) (compList Ls'')
      let B := FiniteKernel.apply (FiniteKernel.apply mu L0) (compList Ls'')
      calc
        _ ≤ Dist.tv A C + Dist.tv C B := Dist.tv_triangle A C B
        _ ≤ telescopeBound d Δ' + Dist.tv C B := by
          simpa only [← hΔ'] using add_le_add_left hIH (Dist.tv C B)
        _ ≤ telescopeBound d Δ' + d ^ Ls''.length *
            Dist.tv (FiniteKernel.apply mu K0) (FiniteKernel.apply mu L0) :=
          add_le_add_right hSuf (telescopeBound d Δ')
        _ ≤ telescopeBound d Δ' + d ^ Ls''.length * kernelDiscrepancy K0 L0 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hΔ0 (pow_nonneg hd0 Ls''.length))
            (telescopeBound d Δ')
        _ = telescopeBound d
            (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
              kernelDiscrepancy p.1 p.2) (List.zip (K0 :: Ks') (L0 :: Ls''))) := by
          rw [List.zip_cons_cons, List.map_cons, hΔ', telescopeBound_cons,
              List.length_map, List.length_zip]
          simp [hlen', min_self]
          ring

/-- The one-step instance of the telescope is exactly the discrepancy
bound: `[K]` vs `[L]` costs `kernelDiscrepancy K L`, undamped. -/
theorem hybridTelescope_n1 [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (K L : FiniteKernel alpha alpha) (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu (compList [K])) (FiniteKernel.apply mu (compList [L])) ≤
      kernelDiscrepancy K L := by
  simp [compList, FiniteKernel.comp_id_right]
  exact apply_discrepancy_bound K L mu

end Shufflemath
