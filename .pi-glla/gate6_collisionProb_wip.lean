module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

@[expose] public section
namespace Shufflemath
namespace _ProbeGate6Collision
open Finset

/-! WIP scratch — the `collisionProb_le` headline assembly (Gate 6 §4, lemma 1 of 4).

STATUS: 4-step assembly written below; the ONE remaining wall is the
`hc` witness extraction (step 1) — reducing `(univ (Fin n × Fin n)).filter q
.Nonempty` for a *general* `n` hits the 200000-heartbeat WHNF limit. A
`set_option maxHeartbeats 0` placed in the *tactic block* does NOT lift it;
it must be set at the file/namespace level (before the theorem), or the
extraction must be moved into a standalone helper lemma proved via the
*structural* Finset lemmas (no `simp [collision]`), e.g.:

  lemma collision_true_iff_exists (n a : Nat) (f : Fin n → Fin a) :
      collision n a f ↔ ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ f p.1 = f p.2

proved by `Finset.Nonempty ↔ ∃ x ∈ s` + `Finset.mem_filter` WITHOUT normalizing
the univ. Once that helper exists, the main proof below goes through with no
heartbeat bump.

CONFIRMED DIAGNOSIS (Nov 21): a minimal probe of
`(univ (Fin n × Fin n)).filter (fun p => decide (p.1 ≠ p.2)).Nonempty` (NO `f`
in the predicate) builds cleanly with default heartbeats — but adding the
`&& decide (f p.1 = f p.2)` term (i.e. the real `collision` predicate, with `f`
a general `Fin n → Fin a`) times out at 200000 heartbeats. A `set_option
maxHeartbeats 0` placed in the *tactic block* does NOT lift it; the bump must be
at file/namespace scope. The `hg` line in the false-branch needs `lt_trichotomy`
(with a proper nested `cases`, not a chained `| inr h | inl h` one-liner).
So the path forward: (1) a tiny dedicated module with file-level
`set_option maxHeartbeats 0` proving `collision_true_iff_exists`; (2) the
assembly below then goes through; OR (3) prove the helper structurally.

The mechanical fixes already applied vs. the first attempt:
  - dropped the bogus `decide_and` simp lemma (not in Mathlib); `decide A &&
    decide B = true` reduces to `A ∧ B` by plain `simp` (may need
    `Bool.decide_and` / `decide_true_iff`).
  - `hg : p.2 < p.1` in the `¬(p.1 < p.2)` branch: use
    `lt_of_le_of_ne (not_lt_iff_le.mp hlt) hne.symm` (NOT `⟨by omega⟩` — the
    `Fin` `<` goal `(↑p.2).succ.le ↑p.1` has no single-ctor form for `⟨⟩`).
  - the `gcongr` step (Rat division monotonicity) and the `field_simp` final
    cancellation both need `a > 0` (`ha`).
-/

theorem collisionProb_le (n a : Nat) (ha : 0 < a) :
    ((collisionSet n a).card : Rat) / (a ^ n : Rat) ≤ (n.choose 2 : Rat) / a := by
  set_option maxHeartbeats 0  -- must be FILE-level to actually lift the WHNF limit
  -- (1) a colliding array has some ordered pair (i < j) whose pairEqSet contains it.
  have hsub : collisionSet n a ⊆ (ijPairs n).biUnion (fun p => pairEqSet n a p.1 p.2) := by
    intro f hf
    have hc : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ f p.1 = f p.2 := by
      rw [collisionSet] at hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, collision, Finset.Nonempty] at hf
      simpa [Finset.mem_filter, Finset.mem_univ] using hf
    obtain ⟨p, hne, heq⟩ := hc
    by_cases hlt : p.1 < p.2
    · refine Finset.mem_biUnion.mpr ⟨⟨p.1, p.2⟩, ?_, ?_⟩
      · simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlt
      · simp only [pairEqSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact heq
    · have hg : p.2 < p.1 := lt_of_le_of_ne (not_lt_iff_le.mp hlt) hne.symm
      refine Finset.mem_biUnion.mpr ⟨⟨p.2, p.1⟩, ?_, ?_⟩
      · simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hg
      · simp only [pairEqSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact heq.symm
  -- (2) union bound
  have hbound : (collisionSet n a).card ≤ (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) :=
    card_le_biUnion_sum _ _ _ hsub
  by_cases h2 : 1 < n
  · -- n ≥ 2: every ijPair (i < j) has i ≠ j, so cardPairEqSet applies
    have hsum : (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) =
        (n.choose 2) * a ^ (n - 1) := by
      calc _ = (ijPairs n).sum (fun _ => a ^ (n - 1)) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hlt : p.1 < p.2 := by
              simp only [ijPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              exact hp
            rw [cardPairEqSet n a ha p.1 p.2 (ne_of_lt hlt) h2]
        _ = (ijPairs n).card * a ^ (n - 1) := Finset.sum_const (ijPairs n) _
        _ = (n.choose 2) * a ^ (n - 1) := by rw [cardIjPairs n]
    have hnat : (collisionSet n a).card ≤ (n.choose 2) * a ^ (n - 1) := by
      calc _ ≤ (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) := hbound
          _ = (n.choose 2) * a ^ (n - 1) := hsum
    calc ((collisionSet n a).card : Rat) / (a ^ n : Rat)
        _ ≤ ((n.choose 2) * a ^ (n - 1) : Rat) / (a ^ n : Rat) := by
          gcongr
        _ = (n.choose 2 : Rat) / a := by
          have hpow : (a ^ n : Rat) = (a : Rat) * (a ^ (n - 1) : Rat) := by
            cases n with
            | zero => contradiction
            | succ n =>
              simp only [Nat.pow_succ, Rat.cast_mul]
              ring
          field_simp [hpow, Nat.cast_pos.mpr ha, Nat.pos_pow_of_pos n ha]
  · -- n ≤ 1: no two distinct positions, so collisionSet is empty
    have hempty : (collisionSet n a).card = 0 := by
      apply Finset.card_eq_zero.mpr
      intro f hf
      rw [collisionSet] at hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, collision, Finset.Nonempty] at hf
      by_contra h
      simpa [Finset.mem_filter, Finset.mem_univ] using hf
    simp [hempty, Nat.cast_zero, Rat.zero_div]
    norm_num [Nat.choose_eq_zero_iff, Nat.succ_le_iff]
end _ProbeGate6Collision
end Shufflemath
