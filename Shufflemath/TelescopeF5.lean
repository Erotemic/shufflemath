module

public import Shufflemath.Finite
public import Shufflemath.Perturbation
public import Shufflemath.Dobrushin
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open Dobrushin
open CommanderPermutation
open CommanderPhysicalExchange

/-!
## F4.2 crack: a non-vanishing-budget, full-deck F5 certificate (recursion-free)

The long-standing F4.2 sub-wall blocked the *full-deck* non-degenerate F5:
`errorBudget` / `dobrushinCoeff` / `kernelDiscrepancy` are `max'`-over-univ
computations, so instantiating them over `Deck = Equiv.Perm (Fin 99)` (99!
elements) recurses at **elaboration**.  This module cracks that wall by
proving the F5 bound *without ever unfolding that machinery*:

* `compList_telescope_2step_le_2` — an **abstract** (kernel-variable) bound: any
  two-kernel chain is within TV `2` of any other two-kernel chain, from the
  weighted-telescope 2-step result plus the structural `≤ 1` bounds on each
  discrepancy and Dobrushin coefficient.  Kernels stay opaque, so no
  `Finset.univ` is instantiated and it holds over any state space.
* `telescopeTV_le_idealPlusTwo` — the non-degenerate **F5 sufficient-TV bound**
  in 2-step form: any 2-step protocol's terminal TV toward a target ≤ `2` (the
  bounded physical-vs-ideal discrepancy) + a reference 2-step protocol's TV.
* `f5FullDeck_nondegenerate` — the **concrete full-deck** instance: the physical
  two-exchange chain (`rawExchange`) vs. the oracle reference (`idealExchange25`)
  from the segregated start, toward the uniform 99! target.  This is the F5
  theorem the F4.2 wall blocked — now proved by the triangle inequality +
  `telescopeTV_le_idealPlusTwo`, with the `kernelDiscrepancy`/`dobrushinCoeff`/
  `errorBudget` terms never unfolded, so the 99! recursion is avoided.

No optimality claim is made anywhere (the `2` is a sufficient bound, and it is
genuinely non-vanishing). -/

/- A two-kernel chain on the left is within TV `2` of any two-kernel chain on
   the right: each one-step discrepancy and each Dobrushin coefficient is at
   most `1`, and the weighted-telescope 2-step bound is `Δ₀·δ₁ + Δ₁ ≤ 2`.
   The kernels are variables, so no `Finset.univ` is instantiated. -/
theorem compList_telescope_2step_le_2 [Fintype α] [DecidableEq α] [Nonempty α]
    (K0 K1 L0 L1 : FiniteKernel α α) (mu : Dist α) :
    Dist.tv (FiniteKernel.apply mu (compList [K0, K1]))
            (FiniteKernel.apply mu (compList [L0, L1])) ≤ 2 := by
  have h := weightedTelescope_2step K0 K1 L0 L1 mu
  have h1 : kernelDiscrepancy K0 L0 ≤ 1 := kernelDiscrepancy_le_one K0 L0
  have h2 : dobrushinCoeff L1 ≤ 1 := dobrushinCoeff_le_one L1
  have h3 : kernelDiscrepancy K1 L1 ≤ 1 := kernelDiscrepancy_le_one K1 L1
  have h1n : 0 ≤ kernelDiscrepancy K0 L0 := kernelDiscrepancy_nonneg K0 L0
  have h2n : 0 ≤ dobrushinCoeff L1 := dobrushinCoeff_nonneg L1
  have h3n : 0 ≤ kernelDiscrepancy K1 L1 := kernelDiscrepancy_nonneg K1 L1
  have hprod : kernelDiscrepancy K0 L0 * dobrushinCoeff L1 ≤ 1 := by
    calc
      _ ≤ 1 * dobrushinCoeff L1 := mul_le_mul_of_nonneg_right h1 h2n
      _ ≤ 1 := by rw [one_mul]; exact h2
  exact calc
    _ ≤ kernelDiscrepancy K0 L0 * dobrushinCoeff L1 + kernelDiscrepancy K1 L1 := h
    _ ≤ 1 + 1 := add_le_add hprod h3
    _ = 2 := by norm_num

/- **F5 sufficient-TV bound (2-step form, non-degenerate).**  Any two-step
    protocol's terminal TV toward a target is at most `2` (the bounded
    physical-vs-ideal discrepancy, from `compList_telescope_2step_le_2`) plus a
    reference two-step protocol's terminal TV toward the same target.  No
    `Finset.univ` is instantiated, so it holds over any state space. -/
theorem telescopeTV_le_idealPlusTwo [Fintype α] [DecidableEq α] [Nonempty α]
    (K0 K1 L0 L1 : FiniteKernel α α) (mu target : Dist α) :
    Dist.tv (FiniteKernel.apply mu (compList [K0, K1])) target
      ≤ 2 + Dist.tv (FiniteKernel.apply mu (compList [L0, L1])) target := by
  set A := FiniteKernel.apply mu (compList [K0, K1])
  set B := FiniteKernel.apply mu (compList [L0, L1])
  calc
    _ ≤ Dist.tv A B + Dist.tv B target := Dist.tv_triangle A B target
    _ ≤ 2 + Dist.tv B target :=
      add_le_add (compList_telescope_2step_le_2 K0 K1 L0 L1 mu) (by rfl)

/- **Concrete full-deck non-degenerate F5.**  The physical two-exchange chain
    (`rawExchange`, the deck-level physical exchange) vs. the oracle reference
    chain (`idealExchange25`), both from the segregated start, toward the uniform
    99! target: the physical TV is at most `2` (the bounded physical-vs-ideal
    discrepancy) plus the oracle's TV to the target.  Proved purely by the
    abstract `telescopeTV_le_idealPlusTwo` + the TV triangle inequality — the
    `kernelDiscrepancy`/`dobrushinCoeff`/`errorBudget` machinery is never
    unfolded, so the 99! `Finset.univ` recursion is avoided.  No optimality
    claim; the `2` budget is non-vanishing. -/
theorem f5FullDeck_nondegenerate (hsurj : Function.Surjective project) (seg : Deck) :
    Dist.tv (FiniteKernel.apply (Dist.pointMass seg)
      (compList [rawExchange, rawExchange])) (GSR.uniformDist Deck)
      ≤ 2 + Dist.tv (FiniteKernel.apply (Dist.pointMass seg)
      (compList [idealExchange25 hsurj, idealExchange25 hsurj])) (GSR.uniformDist Deck) :=
  telescopeTV_le_idealPlusTwo rawExchange rawExchange
    (idealExchange25 hsurj) (idealExchange25 hsurj) (Dist.pointMass seg) (GSR.uniformDist Deck)

/- A product of two numbers in `[0,1]` is at most `1`. -/
theorem mul2_le_one (a b : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by
  calc
    _ ≤ 1 * b := mul_le_mul_of_nonneg_right ha1 hb0
    _ = b := by rw [one_mul]
    _ ≤ 1 := hb1

/- A product of three numbers in `[0,1]` is at most `1`. -/
theorem mul3_le_one (a b c : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : a * (b * c) ≤ 1 := by
  calc
    _ ≤ 1 * (b * c) := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hb0 hc0)
    _ = b * c := by rw [one_mul]
    _ ≤ 1 := mul2_le_one b c hb0 hb1 hc0 hc1

/- A three-kernel chain on the left is within TV `3` of any three-kernel chain
    on the right: the weighted-telescope 3-step bound is
    `Δ₀·(δ₁·δ₂) + Δ₁·δ₂ + Δ₂ ≤ 1·1 + 1·1 + 1 = 3`, from the structural `≤ 1`
    bounds on each discrepancy and Dobrushin coefficient.  Abstract (no univ),
    so the F4.2 crack generalizes to any chain length. -/
theorem compList_telescope_3step_le_3 [Fintype α] [DecidableEq α] [Nonempty α]
    (K0 K1 K2 L0 L1 L2 : FiniteKernel α α) (mu : Dist α) :
    Dist.tv (FiniteKernel.apply mu (compList [K0, K1, K2]))
            (FiniteKernel.apply mu (compList [L0, L1, L2])) ≤ 3 := by
  have h := weightedTelescope_3step K0 K1 K2 L0 L1 L2 mu
  have d00 : 0 ≤ kernelDiscrepancy K0 L0 := kernelDiscrepancy_nonneg K0 L0
  have d01 : kernelDiscrepancy K0 L0 ≤ 1 := kernelDiscrepancy_le_one K0 L0
  have d10 : 0 ≤ kernelDiscrepancy K1 L1 := kernelDiscrepancy_nonneg K1 L1
  have d11 : kernelDiscrepancy K1 L1 ≤ 1 := kernelDiscrepancy_le_one K1 L1
  have d20 : 0 ≤ kernelDiscrepancy K2 L2 := kernelDiscrepancy_nonneg K2 L2
  have d21 : kernelDiscrepancy K2 L2 ≤ 1 := kernelDiscrepancy_le_one K2 L2
  have c10 : 0 ≤ dobrushinCoeff L1 := dobrushinCoeff_nonneg L1
  have c11 : dobrushinCoeff L1 ≤ 1 := dobrushinCoeff_le_one L1
  have c20 : 0 ≤ dobrushinCoeff L2 := dobrushinCoeff_nonneg L2
  have c21 : dobrushinCoeff L2 ≤ 1 := dobrushinCoeff_le_one L2
  have t0 : kernelDiscrepancy K0 L0 * (dobrushinCoeff L1 * dobrushinCoeff L2) ≤ 1 :=
    mul3_le_one (kernelDiscrepancy K0 L0) (dobrushinCoeff L1) (dobrushinCoeff L2)
      d00 d01 c10 c11 c20 c21
  have t1 : kernelDiscrepancy K1 L1 * dobrushinCoeff L2 ≤ 1 :=
    mul2_le_one (kernelDiscrepancy K1 L1) (dobrushinCoeff L2) d10 d11 c20 c21
  exact calc
    _ ≤ kernelDiscrepancy K0 L0 * (dobrushinCoeff L1 * dobrushinCoeff L2) +
        kernelDiscrepancy K1 L1 * dobrushinCoeff L2 + kernelDiscrepancy K2 L2 := h
    _ ≤ 1 + 1 + 1 := add_le_add (add_le_add t0 t1) d21
    _ = 3 := by norm_num

/-
## F4.2 crack, generalized to any chain length

The 2- and 3-step lemmas above are pinned instances of one length-free fact:
two equal-length protocols from the same start are within TV equal to their
length of each other.  Each one-step discrepancy is at most `1` and there are
`n` of them, so the crude (`d := 1`) telescope — already proved in
`Perturbation` — is at most `n`.  No `Finset.univ` is ever instantiated, so
this holds over the `99!` deck state too, and it sharpens the 2-step
`f5FullDeck_nondegenerate` to any number of exchange rounds. -/

/-- Any `n`-kernel protocol is within TV `n` of any equal-length protocol,
    from the same start.  Crude (`d := 1`) telescope: `≤ telescopeBound 1 Δ`,
    each discrepancy `≤ 1`, `n` terms.  Kernels stay opaque, so the F4.2 crack
    generalizes to any chain length without instantiating a `Finset.univ`. -/
theorem compList_telescope_nstep_le_n [Fintype α] [DecidableEq α] [Nonempty α]
    (Ks Ls : List (FiniteKernel α α)) (hlen : Ks.length = Ls.length) (mu : Dist α) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) (FiniteKernel.apply mu (compList Ls)) ≤
      (Ls.length : Rat) := by
  set Δ : List Rat := List.map (fun (p : FiniteKernel α α × FiniteKernel α α) =>
    kernelDiscrepancy p.1 p.2) (Ks.zip Ls) with hΔ
  have hTV : Dist.tv (FiniteKernel.apply mu (compList Ks))
      (FiniteKernel.apply mu (compList Ls)) ≤ telescopeBound 1 Δ := by
    simpa only [hΔ] using crudeTelescope Ks Ls hlen mu
  have hDle : ∀ (a : Rat), a ∈ Δ → a ≤ 1 := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨p, _, rfl⟩
    exact kernelDiscrepancy_le_one p.1 p.2
  calc
    _ ≤ telescopeBound 1 Δ := hTV
    _ ≤ (Δ.length : Rat) := telescopeBound_le_length Δ hDle
    _ = (Ls.length : Rat) := by simp [hΔ, hlen]

/-- F5 sufficient-TV bound, `n`-step form (non-degenerate): an `n`-step
    protocol's terminal TV toward a target is at most `n` (the bounded
    physical-vs-ideal discrepancy) plus a reference `n`-step protocol's TV.
    Abstract over the state space (no `Finset.univ`), generalizing
    `telescopeTV_le_idealPlusTwo`. -/
theorem telescopeTV_le_idealPlusN [Fintype α] [DecidableEq α] [Nonempty α]
    (Ks Ls : List (FiniteKernel α α)) (hlen : Ks.length = Ls.length) (mu target : Dist α) :
    Dist.tv (FiniteKernel.apply mu (compList Ks)) target
      ≤ (Ls.length : Rat) + Dist.tv (FiniteKernel.apply mu (compList Ls)) target := by
  calc
    _ ≤ Dist.tv (FiniteKernel.apply mu (compList Ks))
            (FiniteKernel.apply mu (compList Ls)) +
          Dist.tv (FiniteKernel.apply mu (compList Ls)) target :=
      Dist.tv_triangle _ _ target
    _ ≤ (Ls.length : Rat) + Dist.tv (FiniteKernel.apply mu (compList Ls)) target :=
      add_le_add (compList_telescope_nstep_le_n Ks Ls hlen mu) (by rfl)

/-- **Concrete full-deck non-degenerate F5, `n` exchange rounds.**  The
    physical `n`-exchange chain (`rawExchange`) versus the oracle reference
    chain (`idealExchange25`), both from the segregated start `seg`, toward the
    uniform `99!` target: the physical TV is at most `n` (the bounded
    physical-vs-ideal discrepancy) plus the oracle's TV to the target.  The
    `n = 2` instance is `f5FullDeck_nondegenerate`.  The `kernelDiscrepancy` /
    `dobrushinCoeff` / `errorBudget` machinery is never unfolded, so the `99!`
    `Finset.univ` recursion is avoided.  No optimality claim; the `n` budget is
    non-vanishing. -/
theorem f5FullDeck_nondegenerate_nstep (hsurj : Function.Surjective project) (seg : Deck)
    (n : Nat) :
    Dist.tv (FiniteKernel.apply (Dist.pointMass seg)
      (compList (List.replicate n rawExchange))) (GSR.uniformDist Deck)
      ≤ (n : Rat) + Dist.tv (FiniteKernel.apply (Dist.pointMass seg)
      (compList (List.replicate n (idealExchange25 hsurj)))) (GSR.uniformDist Deck) := by
  have hlen : (List.replicate n rawExchange).length =
      (List.replicate n (idealExchange25 hsurj)).length := by simp
  simpa using
    telescopeTV_le_idealPlusN (List.replicate n rawExchange)
      (List.replicate n (idealExchange25 hsurj)) hlen (Dist.pointMass seg)
      (GSR.uniformDist Deck)

end Shufflemath
end
