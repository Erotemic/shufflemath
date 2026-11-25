module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.Perturbation

@[expose]
public section

namespace Shufflemath

/-!
## Gate 6 (3-round headline) — the `compList` ↔ `run` alignment bridge (sub-lemma B).

`FiniteKernel.run K 3 μ` is the `Nat.recOn` iteration (apply `K` three times to
`μ`); `apply μ (compList [K, K, K])` is the same three-fold application written
as the composition of the three-kernel protocol list. This theorem proves they
are equal — the `compList` ↔ `run` alignment the 3-round Gate-6 headline's
sub-lemma B needs (`TV(finiteRound^3 d0, U) ≤ q3`).

Proof: unroll `compList [K, K, K]` to the nested `comp` chain, then to the
triple `apply`, matching the three `run_succ` steps. Pure `FiniteKernel`
algebra (`compList_cons`, `compList_nil`, `comp_id_right`, `apply_comp`,
`run_succ`) — no equinumerosity, no `native_decide`, no oracle/`WHNF` wall.
-/

-- The one-card commander deck state, as a full deck permutation.
abbrev g6ThreeRoundDeck := Equiv.Perm (Fin 99)

/-- Applying a three-kernel `compList` protocol to `μ` is the three-fold
    `FiniteKernel.run` iteration: unrolling `compList [K, K, K]` to the nested
    `comp` chain, then to the triple `apply`, matches the three `run_succ`
    steps. The `compList` ↔ `run` alignment for the 3-round Gate-6 headline
    sub-lemma B. -/
theorem g6_threeRound_compList3_eq_run (K : FiniteKernel g6ThreeRoundDeck g6ThreeRoundDeck)
    (μ : Dist g6ThreeRoundDeck) :
    FiniteKernel.apply μ (compList [K, K, K]) = FiniteKernel.run K 3 μ := by
  have hL : FiniteKernel.apply μ (compList [K, K, K]) =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ K) K) K := by
    rw [compList_cons, compList_cons, compList_cons, compList_nil, FiniteKernel.comp_id_right,
        ← FiniteKernel.apply_comp, ← FiniteKernel.apply_comp]
  have hR : FiniteKernel.run K 3 μ =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ K) K) K := by
    rw [FiniteKernel.run_succ, FiniteKernel.run_succ, FiniteKernel.run_succ]
    simp [FiniteKernel.run]
  rw [hL, hR]

end Shufflemath
