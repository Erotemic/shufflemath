import Shufflemath.TotalVariation
import Shufflemath.Dobrushin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- The protocol theorems whnf `dobrushinCoeff (compList …)` (a max over all
-- row pairs of the composed kernel) while elaborating the telescoping
-- bounds; give the compiler room for that one-time definitional expansion.
set_option maxHeartbeats 400000

namespace Shufflemath

open Dobrushin

/-!
## Perturbation bounds for kernel protocols

How much does one step of a protocol matter? If two kernels `K` and `L`
differ, then pushing the **same** distribution through each of them is
apart in total variation by at most the kernels' `kernelDiscrepancy`
(`apply_discrepancy_bound`) — the same weighted-Fubini argument as
`Dist.kernel_contraction` with one side fixed. `compList` composes a list
of kernels in execution order.

Protocol-scale bounds, sharpest to crudest:

- `weightedTelescope` (flagship, no contraction hypothesis): same-length
  protocols from the same start are at most
  `∑_i Δ(K_i, L_i) · ∏_{j>i} δ(L_j)` — each one-step discrepancy damped by
  the product of the *actual* Dobrushin coefficients of the common L-side
  tail after it (`weightedTelescopeBound`). No hypothesis beyond equal
  lengths: the K side only ever enters through the one-step discrepancies,
  and every kernel's coefficient is ≤ 1 automatically.
- `hybridTelescope_uniform`: corollary damping the tail products by a
  common `d` to the tail length — the telescoping sum `telescopeBound d Δ`
  — under the single hypothesis that every L kernel has Dobrushin
  coefficient ≤ `d`.
- `crudeTelescope` (crudest): the `d := 1` case — the plain sum of the
  per-step discrepancies, with no hypothesis at all.
- `hybridTelescope`: the symmetric variant where both lists contract by a
  common `d` (contraction-form hypotheses); kept for the d-form statement,
  and follows from the uniform corollary.

The sharp form is the D-side payoff: `Dobrushin.dobrushinCoeff` and
`Dobrushin.dobrushinCoeff_submult` on the one side, and here
`compList_submult` — the coefficient of a composed list is at most the
product of the coefficients, so the product of per-step coefficients
bounds the whole-tail contraction.

The telescoping sum `telescopeBound d Δ = Δ₀·dⁿ⁻¹ + … + Δₙ₋₁` damps each
position by the number of steps remaining after it: the first step is
damped the most, the last not at all. A one-step protocol (`[K]` vs `[L]`)
reduces to `apply_discrepancy_bound` (`hybridTelescope_n1`).
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
    Dist.tv (K x) (L x) ≤ kernelDiscrepancy K L := by
  unfold kernelDiscrepancy
  apply Finset.le_max'
  simp [kernelDiscrepancySet]

@[simp]
theorem kernelDiscrepancy_nonneg [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) : 0 ≤ kernelDiscrepancy K L := by
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have h := rowTV_le_kernelDiscrepancy K L x
  have h2 : 0 <= Dist.tv (K x) (L x) := Dist.tv_nonneg (K x) (L x)
  simpa [kernelDiscrepancy] using le_trans h2 h

/-- Two kernels with rows that are distributions have discrepancy at most one. -/
theorem kernelDiscrepancy_le_one [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha] (K L : FiniteKernel alpha beta) : kernelDiscrepancy K L ≤ 1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  exact Dist.tv_le_one (K x) (L x)

/-- Pushing one distribution through two different kernels: the TV distance
of the two outputs is at most the kernels' row discrepancy. This is the
one-step case of the protocol telescope — a single perturbation costs at
most the discrepancy, before any damping by subsequent steps. -/
theorem apply_discrepancy_bound [Fintype alpha] [Fintype beta] [DecidableEq alpha]
    [DecidableEq beta] [Nonempty alpha]
    (K L : FiniteKernel alpha beta) (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu K) (FiniteKernel.apply mu L) ≤ kernelDiscrepancy K L := by
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
  have hΔ : ∀ (j : alpha), Dist.tv (K j) (L j) ≤ kernelDiscrepancy K L :=
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
      rw [Dist.double_sum_pullout (fun j => Dist.mass mu j)
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
then the tail protocol: the induction spine of the telescope bounds. -/
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

/-- The Dobrushin coefficient of a composed protocol is at most the product
of the coefficients: composing never amplifies contraction. -/
theorem compList_submult [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (Ks : List (FiniteKernel alpha alpha)) :
    dobrushinCoeff (compList Ks) ≤ (List.map dobrushinCoeff Ks).prod := by
  induction Ks with
  | nil =>
    calc
      _ = dobrushinCoeff (FiniteKernel.identity : FiniteKernel alpha alpha) := by
        simp [compList]
      _ ≤ 1 := dobrushinCoeff_le_one _
      _ = (List.map dobrushinCoeff []).prod := by simp
  | cons K Ks' ih =>
    calc
      _ = dobrushinCoeff (FiniteKernel.comp K (compList Ks')) := by rw [compList_cons]
      _ ≤ dobrushinCoeff K * dobrushinCoeff (compList Ks') :=
          dobrushinCoeff_submult K _
      _ ≤ dobrushinCoeff K * (List.map dobrushinCoeff Ks').prod := by
        apply mul_le_mul_of_nonneg_left
        · exact ih
        · exact dobrushinCoeff_nonneg K
      _ = (dobrushinCoeff K :: List.map dobrushinCoeff Ks').prod := by
        rw [← List.prod_cons]

/-- The contraction of a composed kernel is at most the product of the
per-kernel coefficients: the tail pushes the two starting distributions
closer by at most the product. -/
private theorem compList_contraction_prod [Fintype alpha] [DecidableEq alpha]
    [Nonempty alpha] (Ks : List (FiniteKernel alpha alpha)) (p q : Dist alpha) :
    Dist.tv (FiniteKernel.apply p (compList Ks)) (FiniteKernel.apply q (compList Ks)) ≤
    (List.map dobrushinCoeff Ks).prod * Dist.tv p q := by
  calc
    _ ≤ dobrushinCoeff (compList Ks) * Dist.tv p q :=
        dobrushin_contraction (compList Ks) p q
    _ ≤ (List.map dobrushinCoeff Ks).prod * Dist.tv p q := by
      apply mul_le_mul_of_nonneg_right
      · exact compList_submult Ks
      · exact Dist.tv_nonneg p q

/-- A list of nonnegative factors has nonnegative product. -/
private theorem list_prod_nonneg (l : List Rat) (h : ∀ (a : Rat), a ∈ l → 0 ≤ a) :
    0 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons]
    exact mul_nonneg (h x (List.mem_cons_self))
      (ih fun a ha => h a (List.mem_cons_of_mem x ha))

/-- A list of factors in `[0, d]` has product at most `d` raised to the
length. -/
private theorem list_prod_le_pow_of_le (l : List Rat) (d : Rat) (hd0 : 0 ≤ d)
    (h : ∀ (x : Rat), x ∈ l → 0 ≤ x ∧ x ≤ d) : l.prod ≤ d ^ l.length := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    calc
      _ = x * xs.prod := List.prod_cons
      _ ≤ x * d ^ xs.length := mul_le_mul_of_nonneg_left
          (ih (fun z hz => h z (List.mem_cons_of_mem x hz))) hx.1
      _ ≤ d * d ^ xs.length := mul_le_mul_of_nonneg_right hx.2 (pow_nonneg hd0 xs.length)
      _ = d ^ (xs.length + 1) := by rw [pow_succ']

/-- **Weighted perturbation bound: the sharp per-step form.**
`weightedTelescopeBound Δ δ` is the sum of each one-step discrepancy
`Δ_i` times the product of the Dobrushin coefficients of the L-side
kernels strictly *after* step `i` — the common tail through which the
discrepancy propagates. For protocols of length `n`, `δ` carries the
`n - 1` coefficients of the L-side tail: `δ j = δ(L_{j+1})`. -/
def weightedTelescopeBound (Δ δ : List Rat) : Rat :=
  match Δ with
  | [] => 0
  | Δ0 :: Δs => Δ0 * δ.prod + weightedTelescopeBound Δs (δ.drop 1)

@[simp]
theorem weightedTelescopeBound_nil (δ : List Rat) :
    weightedTelescopeBound [] δ = 0 := rfl

@[simp]
theorem weightedTelescopeBound_cons (Δ0 : Rat) (Δs δs : List Rat) :
    weightedTelescopeBound (Δ0 :: Δs) δs =
      Δ0 * δs.prod + weightedTelescopeBound Δs (δs.drop 1) := rfl

/-- Membership is preserved by `drop` (a dropped list is a suffix). -/
private theorem mem_of_mem_drop {l : List α} {n : Nat} {a : α}
    (h : a ∈ l.drop n) : a ∈ l := by
  induction n generalizing l with
  | zero => simpa only [List.drop_zero] using h
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons a' l' =>
      have h' : a ∈ l'.drop n := by
        simpa only [List.drop_succ_cons] using h
      exact List.mem_cons_of_mem a' (ih h')

/-- If every coefficient lies in `[0, d]`, every discrepancy is
nonnegative, and `δ` carries one coefficient per `Δ` slot except the
last, then the weighted bound is dominated by the uniform-`d` telescope:
termwise `Δ_i · ∏_{j≥i} δ_j ≤ Δ_i · d^{n-1-i}`. -/
private theorem wtB_le_uniform (Δ δ : List Rat) (d : Rat) (hd0 : 0 ≤ d)
    (hlen : δ.length = Δ.length - 1)
    (hd : ∀ (a : Rat), a ∈ δ → 0 ≤ a) (hdle : ∀ (a : Rat), a ∈ δ → a ≤ d)
    (hΔ : ∀ (a : Rat), a ∈ Δ → 0 ≤ a) :
    weightedTelescopeBound Δ δ ≤ telescopeBound d Δ := by
  induction Δ generalizing δ d hd0 hd hdle with
  | nil =>
    simp only [weightedTelescopeBound, telescopeBound]
    linarith
  | cons Δ0 Δs ih =>
    have hexp : (Δ0 :: Δs).length - 1 = Δs.length := rfl
    have hdrop : (δ.drop 1).length = δ.length - 1 := by
      cases δ with
      | nil => simp
      | cons a as =>
        rw [List.drop_succ_cons (i := 0), List.drop_zero, List.length_cons]
        omega
    have hlen' : (δ.drop 1).length = Δs.length - 1 := by
      rw [hdrop, hlen, hexp]
    have hexp2 : δ.length = Δs.length := by rw [hlen, hexp]
    have hprod : δ.prod ≤ d ^ δ.length :=
      list_prod_le_pow_of_le δ d hd0 fun a ha => ⟨hd a ha, hdle a ha⟩
    have hIH := ih (δ.drop 1) d hd0 hlen'
      (fun a ha => hd a (mem_of_mem_drop ha))
      (fun a ha => hdle a (mem_of_mem_drop ha))
      (fun a ha => hΔ a (List.mem_cons_of_mem Δ0 ha))
    calc
      _ = Δ0 * δ.prod + weightedTelescopeBound Δs (δ.drop 1) := by
        rw [weightedTelescopeBound_cons]
      _ ≤ Δ0 * d ^ δ.length + weightedTelescopeBound Δs (δ.drop 1) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left hprod
          exact hΔ Δ0 (List.mem_cons_self)
        · exact le_rfl
      _ = Δ0 * d ^ Δs.length + weightedTelescopeBound Δs (δ.drop 1) := by
        rw [hexp2]
      _ ≤ Δ0 * d ^ Δs.length + telescopeBound d Δs := by
        apply add_le_add
        · exact le_rfl
        · exact hIH
      _ = telescopeBound d (Δ0 :: Δs) := by rw [telescopeBound_cons]

/-- **Weighted perturbation bound (flagship).** Two protocols of equal
length from the same start: the TV distance of the final states is at
most the sum, over each step `i`, of the one-step discrepancy of the two
kernels at that step times the product of the Dobrushin coefficients of
the common L-side tail after it: `∑_i Δ(K_i, L_i) · ∏_{j>i} δ(L_j)`.

No contraction hypothesis at all: every kernel has coefficient in
`[0, 1]`, and the only inputs are the two protocol lists. Proof:
head-removal induction — the triangle inequality splits the comparison
at the head into a *same-input tail* part (the induction hypothesis, at
the intermediate starting distribution `μ·K_0`) and a *same-tail
different-input* part (the tail's contraction, submultiplicative over
the L-tail, times the head discrepancy). `hybridTelescope_uniform`
(common `d` damping), `crudeTelescope` (`d := 1`, the plain sum), and
the symmetric `hybridTelescope` are corollaries. -/
theorem weightedTelescope [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (Ks Ls : List (FiniteKernel alpha alpha)) (hlen : Ks.length = Ls.length)
    (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) (FiniteKernel.apply mu (compList Ls)) ≤
    weightedTelescopeBound
      (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
        kernelDiscrepancy p.1 p.2) (Ks.zip Ls))
      (List.map dobrushinCoeff (Ls.drop 1)) := by
  induction Ks generalizing Ls mu with
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
      have hIH := ih Ls'' hlen' (FiniteKernel.apply mu K0)
      set δs : List Rat := List.map dobrushinCoeff Ls'' with hδs
      have hSuf := compList_contraction_prod Ls'' (FiniteKernel.apply mu K0)
        (FiniteKernel.apply mu L0)
      have hΔ0 := apply_discrepancy_bound K0 L0 mu
      have hSuf2 : Dist.tv (FiniteKernel.apply (FiniteKernel.apply mu K0) (compList Ls''))
          (FiniteKernel.apply (FiniteKernel.apply mu L0) (compList Ls'')) ≤
          δs.prod * kernelDiscrepancy K0 L0 := by
        calc
          _ ≤ (List.map dobrushinCoeff Ls'').prod *
              Dist.tv (FiniteKernel.apply mu K0) (FiniteKernel.apply mu L0) := hSuf
          _ ≤ δs.prod * kernelDiscrepancy K0 L0 := by
            rw [hδs]
            apply mul_le_mul_of_nonneg_left hΔ0
            exact list_prod_nonneg δs fun a ha => by
              rcases List.mem_map.mp ha with ⟨K, _, rfl⟩
              exact dobrushinCoeff_nonneg K
      rw [compList_cons, compList_cons, ← FiniteKernel.apply_comp mu K0 (compList Ks'),
          ← FiniteKernel.apply_comp mu L0 (compList Ls'')]
      let A := FiniteKernel.apply (FiniteKernel.apply mu K0) (compList Ks')
      let C := FiniteKernel.apply (FiniteKernel.apply mu K0) (compList Ls'')
      let B := FiniteKernel.apply (FiniteKernel.apply mu L0) (compList Ls'')
      calc
        _ ≤ Dist.tv A C + Dist.tv C B := Dist.tv_triangle A C B
        _ ≤ weightedTelescopeBound Δ' (List.map dobrushinCoeff (Ls''.drop 1)) +
            Dist.tv C B := by
          simpa only [← hΔ'] using add_le_add_left hIH (Dist.tv C B)
        _ ≤ weightedTelescopeBound Δ' (List.map dobrushinCoeff (Ls''.drop 1)) +
            δs.prod * kernelDiscrepancy K0 L0 :=
          add_le_add_right hSuf2
            (weightedTelescopeBound Δ' (List.map dobrushinCoeff (Ls''.drop 1)))
        _ = weightedTelescopeBound
            (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
              kernelDiscrepancy p.1 p.2) (List.zip (K0 :: Ks') (L0 :: Ls'')))
            (List.map dobrushinCoeff ((L0 :: Ls'').drop 1)) := by
          rw [List.zip_cons_cons, List.map_cons, ← hΔ', weightedTelescopeBound_cons]
          dsimp only [List.drop, List.tail]
          simp only [List.map_drop, ← hδs]
          ring

/-- **Uniform perturbation bound.** Two protocols of equal length over the
same state space, starting from the same distribution, with every L kernel
having Dobrushin coefficient at most `d` (`0 ≤ d`). Then the TV distance of
the final states is at most the telescoping sum: the one-step discrepancy
of the two kernels at step `i`, times `d` raised to the number of L steps
remaining after it. Corollary of `weightedTelescope`: each L-tail product
is at most `d` to the tail length. The K side needs no contraction
hypothesis at all — it only ever enters through the one-step discrepancy.
With `d := 1` this is `crudeTelescope`. -/
theorem hybridTelescope_uniform [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (Ks Ls : List (FiniteKernel alpha alpha)) (hlen : Ks.length = Ls.length)
    (mu : Dist alpha) (d : Rat) (hd0 : 0 ≤ d)
    (hdL : ∀ (K : FiniteKernel alpha alpha), K ∈ Ls →
      dobrushinCoeff K ≤ d) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) (FiniteKernel.apply mu (compList Ls)) ≤
    telescopeBound d (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
      kernelDiscrepancy p.1 p.2) (Ks.zip Ls)) := by
  have hlen' : (List.map dobrushinCoeff (Ls.drop 1)).length =
      (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
        kernelDiscrepancy p.1 p.2) (Ks.zip Ls)).length - 1 := by
    simp only [List.length_map, List.length_zip, hlen, min_self]
    cases Ls with
    | nil => simp
    | cons a as =>
      rw [List.drop_succ_cons (i := 0), List.drop_zero, List.length_cons]
      omega
  apply le_trans (weightedTelescope Ks Ls hlen mu)
  apply wtB_le_uniform _ _ d hd0 hlen'
  · intro a ha
    rcases List.mem_map.mp ha with ⟨K, _, rfl⟩
    exact dobrushinCoeff_nonneg K
  · intro a ha
    rcases List.mem_map.mp ha with ⟨K, hK, rfl⟩
    exact hdL K (mem_of_mem_drop hK)
  · intro a ha
    rcases List.mem_map.mp ha with ⟨p, _, rfl⟩
    exact kernelDiscrepancy_nonneg p.1 p.2

/-- **Crude perturbation bound: no contraction hypothesis at all.** Two
protocols of equal length from the same start are at most the plain sum of
the per-step discrepancies `∑_i Δ(K_i, L_i)`. The `d := 1` case of the
weighted form: every kernel has Dobrushin coefficient ≤ 1. -/
theorem crudeTelescope [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (Ks Ls : List (FiniteKernel alpha alpha)) (hlen : Ks.length = Ls.length)
    (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) (FiniteKernel.apply mu (compList Ls)) ≤
    telescopeBound 1 (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
      kernelDiscrepancy p.1 p.2) (Ks.zip Ls)) := by
  have hlen' : (List.map dobrushinCoeff (Ls.drop 1)).length =
      (List.map (fun (p : FiniteKernel alpha alpha × FiniteKernel alpha alpha) =>
        kernelDiscrepancy p.1 p.2) (Ks.zip Ls)).length - 1 := by
    simp only [List.length_map, List.length_zip, hlen, min_self]
    cases Ls with
    | nil => simp
    | cons a as =>
      rw [List.drop_succ_cons (i := 0), List.drop_zero, List.length_cons]
      omega
  apply le_trans (weightedTelescope Ks Ls hlen mu)
  apply wtB_le_uniform _ _ 1 (by norm_num) hlen'
  · intro a ha
    rcases List.mem_map.mp ha with ⟨K, _, rfl⟩
    exact dobrushinCoeff_nonneg K
  · intro a ha
    rcases List.mem_map.mp ha with ⟨K, _, rfl⟩
    exact dobrushinCoeff_le_one K
  · intro a ha
    rcases List.mem_map.mp ha with ⟨p, _, rfl⟩
    exact kernelDiscrepancy_nonneg p.1 p.2

/-- **Symmetric uniform-d bound (kept for the d-form statement).** Both
protocol lists contract by a common `d`; the bound is the uniform-`d`
telescope. The contraction hypothesis is converted to a coefficient bound
per kernel, then the uniform corollary applies (the `K`-side hypothesis
`hdK` is not needed for the bound). -/
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
      kernelDiscrepancy p.1 p.2) (Ks.zip Ls)) :=
  let _ := hdK
  hybridTelescope_uniform Ks Ls hlen mu d hd0 (fun K hL => by
    unfold dobrushinCoeff
    apply Finset.max'_le
    intro r hr
    dsimp only [pairDistances, rowTV] at hr
    rcases Finset.mem_image.mp hr with ⟨ij, _, rfl⟩
    have h4 : Dist.tv (Dist.pointMass ij.1) (Dist.pointMass ij.2) ≤ 1 :=
      Dist.tv_le_one (Dist.pointMass ij.1) (Dist.pointMass ij.2)
    calc
      _ = Dist.tv (FiniteKernel.apply (Dist.pointMass ij.1) K)
          (FiniteKernel.apply (Dist.pointMass ij.2) K) := by
        rw [FiniteKernel.apply_pointMass, FiniteKernel.apply_pointMass]
      _ ≤ d * Dist.tv (Dist.pointMass ij.1) (Dist.pointMass ij.2) :=
        hdL K hL (Dist.pointMass ij.1) (Dist.pointMass ij.2)
      _ ≤ 1 * d := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right h4 hd0
      _ = d := by rw [one_mul])

/-- The one-step instance of the telescope is exactly the discrepancy
bound: `[K]` vs `[L]` costs `kernelDiscrepancy K L`, undamped. -/
theorem hybridTelescope_n1 [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (K L : FiniteKernel alpha alpha) (mu : Dist alpha) :
    Dist.tv (FiniteKernel.apply mu (compList [K])) (FiniteKernel.apply mu (compList [L])) ≤
      kernelDiscrepancy K L := by
  simp [compList, FiniteKernel.comp_id_right]
  exact apply_discrepancy_bound K L mu

end Shufflemath
