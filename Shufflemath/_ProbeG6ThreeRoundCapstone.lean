module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.Perturbation
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.Gate6FiniteGSR
public import Shufflemath.Gate6Crux
public import Shufflemath.GSRDeckRound
public import Shufflemath._ProbeG6ThreeRoundKernelDelta
public import Shufflemath._ProbeG6ThreeRoundHeadline
public import Shufflemath._ProbeG6ThreeRound
public import Shufflemath.TelescopeF5

@[expose]
public section

namespace Shufflemath

open CommanderPermutation

/-!
## Gate 6 (G6.3, 3-round headline) — the physical 3-round TV < 1/1000 (final assembly).

`g6_threeRound_headline` proves that the 99-card **physical** three-round finite
shuffler — three iterations of the correct-order full round `comp (PAK swapLaw)
(PAK rho99Finite)` (swap, then the A3 perfect-shuffle round) — driven from the
fiber-uniform 49-segregated start, lands within total variation `< 1/1000` of the
uniform `99!` deck.

Assembled purely from already-proven pieces (no `99!` enumeration, no `native_decide`):

* **hAccum** — the length-free n-step telescope
  `compList_telescope_nstep_le_n_times_d` gives
  `TV (apply start (compList [K×3])) (apply start (compList [L×3])) ≤ 3·δ1`,
  the per-round collision budget, each row bounded by **sub-lemma A**
  (`g6_threeRound_kernelDiscrepancy_le_δ1`: `kd (comp (PAK S)(PAK F))
  (comp (PAK S)(PAK I)) ≤ δ1`).
* **hIdeal** — **sub-lemma B** (`g6_threeRound_finiteRun3_tv_le_q3`):
  `TV (apply start (compList [L×3])) (uniform) ≤ q3`, the exact three-round
  ideal residual (already proven, `three_physical_perfect_exchanges_uniform_unconditional`).
* **numeric close** — `gate6_headline_lt_thousandth : q3 + 3·δ1 < 1/1000`.

`K = g6ThreeRoundFiniteRound` (sub-lemma A) is the physical round;
`L = g6ThreeRoundFiniteKernel` (sub-lemma B) is the ideal round, equal to
`comp (PAK swapLaw) (PAK rho99Ideal)` by the bridge
(`g6_3round_idealKernel_eq_fullRound`).
-/

theorem g6_threeRound_headline :
    Dist.tv (FiniteKernel.apply g6ThreeRoundStart
        (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                  g6ThreeRoundFiniteRound]))
      (GSR.uniformDist Deck) < (1 : ℚ) / 1000 := by
  -- L = comp (PAK S)(PAK I); sub-lemma B's kernel `g6ThreeRoundFiniteKernel` = L (the bridge).
  have hL : g6ThreeRoundFiniteKernel =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
    dsimp only [g6ThreeRoundFiniteKernel]
    exact g6_3round_idealKernel_eq_fullRound
  -- hAccum: the 3-round finite run vs the 3-round ideal run — per-round budget `3·δ1`.
  have hAccum :
      Dist.tv (FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                    g6ThreeRoundFiniteRound]))
        (FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel])) ≤ 3 * δ1 := by
    exact compList_telescope_nstep_le_n_times_d
      [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound]
      [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel]
      (by simp) δ1 (by rw [δ1_eq_2401_over_8388608]; norm_num)
      (fun a ha => by
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        dsimp at hp
        rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_nil_iff] at hp
        rcases hp with h₁ | h₂ | h₃ | h₄
        · rw [h₁]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · rw [h₂]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · rw [h₃]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · exfalso; exact h₄)
      g6ThreeRoundStart
  -- hIdeal: the 3-round ideal run from the fiber-uniform start is `≤ q3` from uniform (sub-lemma B).
  have hIdeal :
      Dist.tv (FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]))
        (GSR.uniformDist Deck) ≤ q3 := g6_threeRound_finiteRun3_tv_le_q3
  -- Triangle inequality + the numeric close `q3 + 3·δ1 < 1/1000`.
  calc
    _ ≤ Dist.tv (FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                    g6ThreeRoundFiniteRound]))
          (FiniteKernel.apply g6ThreeRoundStart
            (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                      g6ThreeRoundFiniteKernel])) +
        Dist.tv (FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]))
          (GSR.uniformDist Deck) := by
      simpa only [Dist.tv] using Dist.tv_triangle
        (p := FiniteKernel.apply g6ThreeRoundStart
              (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                        g6ThreeRoundFiniteRound]))
        (q := FiniteKernel.apply g6ThreeRoundStart
              (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                        g6ThreeRoundFiniteKernel]))
        (r := GSR.uniformDist Deck)
    _ ≤ 3 * δ1 + q3 := add_le_add hAccum hIdeal
    _ < (1 : ℚ) / 1000 := by rw [add_comm]; exact gate6_headline_lt_thousandth

end Shufflemath
end
