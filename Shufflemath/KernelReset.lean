module

public import Shufflemath.Perturbation

@[expose] public section

namespace Shufflemath

/-!
## Terminal-reset kernel identities (abstract)

Generic kernel-algebra lemmas for the terminal-reset deletion story (the
2026-11-26 evening finish-line guide, section A1).  All statements are
independent of concrete permutation types: they quantify over an arbitrary
finite carrier and arbitrary `FiniteKernel`s.

The three lemmas:

* `lastReset_run` — if a reset kernel `H` absorbs the composition of a
  swap kernel `S` with a reset (`H ; (S ; H) = S ; H`), then *all* the
  reset-`run`s collapse: running `S` for `t+1` steps and then applying one
  final `H` equals running the one-step kernel `comp S H` for `t+1` steps.
* `preserved_observation_step` — an intermediate kernel `J` whose effect on
  the observation map `P` is unchanged (`J ; P = P`) can be omitted from the
  start of a run without changing the observation law (`comp (comp J S) P =
  comp P Q` given `S ; P = P ; Q`).
* `apply_tv_of_row_bound` — pushing one distribution through two kernels whose
  rows are uniformly close costs at most that row discrepancy.

See `docs/planning/proof-strategies/2026-11-26-evening-terminal-reset-and-finish-line.md`
section A1 for the source (uncompiled) seeds this module was promoted from.
-/

/-- **Abstract deletion of intermediate ideal resets.** If `H` (the terminal
reset) absorbs `S ; H` (`comp H (comp S H) = comp S H`), then running `S` for
`t + 1` steps from `mu` and then applying one final `H` equals running the
comp `S ; H` for `t + 1` steps. Proof by induction on `t` using kernel
associativity and the one-step `run` recursion. -/
theorem lastReset_run {X : Type*} (S H : FiniteKernel X X)
    (h : FiniteKernel.comp H (FiniteKernel.comp S H) = FiniteKernel.comp S H)
    (mu : Dist X) (t : Nat) :
    FiniteKernel.apply (FiniteKernel.run S (Nat.succ t) mu) H =
      FiniteKernel.run (FiniteKernel.comp S H) (Nat.succ t) mu := by
  induction t with
  | zero =>
    rw [FiniteKernel.run_succ 0 S mu,
      FiniteKernel.run_succ 0 (FiniteKernel.comp S H) mu]
    change FiniteKernel.apply (FiniteKernel.apply mu S) H =
      FiniteKernel.apply mu (FiniteKernel.comp S H)
    exact FiniteKernel.apply_comp mu S H
  | succ t ih =>
    calc
      _ = FiniteKernel.apply (FiniteKernel.run S (Nat.succ t) mu)
          (FiniteKernel.comp S H) := by
            rw [FiniteKernel.run_succ (Nat.succ t) S mu, FiniteKernel.apply_comp]
      _ = FiniteKernel.apply (FiniteKernel.apply
          (FiniteKernel.run S (Nat.succ t) mu) H) (FiniteKernel.comp S H) := by
            rw [FiniteKernel.apply_comp, h]
      _ = FiniteKernel.apply (FiniteKernel.run (FiniteKernel.comp S H) (Nat.succ t) mu)
          (FiniteKernel.comp S H) := by rw [ih]
      _ = _ := (FiniteKernel.run_succ (Nat.succ t) (FiniteKernel.comp S H) mu).symm

/-- **Intermediate observation-preserving kernels can be omitted.** If the
intermediate kernel `J` preserves the observation (`comp J P = P`) and the
remaining run maps `P` to `P ; Q`, then `comp (comp J S) P = comp P Q`. -/
theorem preserved_observation_step {X Y : Type*} (J : FiniteKernel X X)
    (P : FiniteKernel X Y) (Q : FiniteKernel Y Y) (S : FiniteKernel X X)
    (hJ : FiniteKernel.comp J P = P)
    (hS : FiniteKernel.comp S P = FiniteKernel.comp P Q) :
    FiniteKernel.comp (FiniteKernel.comp J S) P = FiniteKernel.comp P Q := by
  calc
    _ = FiniteKernel.comp J (FiniteKernel.comp S P) :=
      FiniteKernel.comp_assoc J S P
    _ = FiniteKernel.comp J (FiniteKernel.comp P Q) := by rw [hS]
    _ = FiniteKernel.comp (FiniteKernel.comp J P) Q :=
      (FiniteKernel.comp_assoc J P Q).symm
    _ = _ := by rw [hJ]

/-- **Row discrepancy bounds the output TV.** If every row of `F` is within
`err` (TV) of the corresponding row of `H`, then pushing any distribution `mu`
through `F` and `H` costs at most `err` in total variation. -/
theorem apply_tv_of_row_bound {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (F H : FiniteKernel X Y) (mu : Dist X) (err : Rat)
    (h : ∀ x, Dist.tv (F x) (H x) ≤ err) :
    Dist.tv (FiniteKernel.apply mu F) (FiniteKernel.apply mu H) ≤ err := by
  apply le_trans (apply_discrepancy_bound F H mu)
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
  exact h x

end Shufflemath
