module

public import Shufflemath.FiniteDeck.Gate6Corrected
public import Shufflemath.FiniteDeck.Gate6Row
public import Shufflemath.Gate6K1Bridges

@[expose] public section

namespace Shufflemath.FinishHints

/-! Proposed proof candidates, not yet compiled by the reviewer. Keep the
abstract lemma independent of concrete permutation types. -/

/-- If a reset before an ideal round has no effect, all intermediate ideal
resets can be deleted. The final reset must remain. Execution-order comp. -/
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

/-- One can use any intermediate local operation J whose observation is
unchanged. This formulation uses no equality/decidability on the carriers. -/
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

/-- Propagate a bound on an abstract row discrepancy without expanding it. -/
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

/-- Arithmetic only: three exchange rounds, one final local reset. -/
theorem budget_final23 : q3 + δ1 < (1 : Rat) / 1000 := by
  norm_num [q3, δ1, Nat.choose_two_right]

theorem budget_final22 : q3 + (2401 : Rat) / 2^22 < (1 : Rat) / 1000 := by
  norm_num [q3]

theorem budget_final22_21 : q3 + (1225 : Rat) / 2^22 + (1176 : Rat) / 2^21 <
    (1 : Rat) / 1000 := by
  norm_num [q3]

end Shufflemath.FinishHints
