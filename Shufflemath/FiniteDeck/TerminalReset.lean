module

public import Shufflemath.FiniteDeck.Gate6Corrected
public import Shufflemath.FiniteDeck.Gate6Row
public import Shufflemath.KernelReset

@[expose] public section

namespace Shufflemath
namespace TerminalReset

/-!
## The terminal-only 99-card certificate (A2)

The cheap 99-card protocol from the 2026-11-26 evening finish-line guide
(section A2): three independent 25-position exchanges between piles of sizes
50 and 49, **no local riffles between exchanges**, then one final
(orientation-corrected) finite kernel. The components are:

* `S` — the literal swap kernel (`PAK swapLaw`, the A3 exchange law);
* `H` — the ideal terminal reset (`PAK rho99Ideal`, the perfect-local reset
  law) — equal to the M5a/M5b local-reset kernel `idealLocalReset`
  (`k1_idealKernel_eq_membershipLift`);
* `F` — the corrected finite terminal kernel (`PAK correctedFiniteLaw99`);
* `L := comp S H` — the correct-order ideal full-round kernel — equal to
  `idealFullRound` (K1 swap-first) and to `g6ThreeRoundFiniteKernel`
  (`g6_3round_idealKernel_eq_fullRound`).

The headline `terminal23_anyDeck`: the terminal-only protocol from **any**
deterministic deck lands within total variation `< 1/1000` of the uniform
99! deck. Assembly (the guide's final paragraph):

* **Terminal-reset deletion** (`comp_H_L_eq_L`, `apply_run_S_succ_H_eq_run_L`) —
  `comp H L = L` by the M5b absorption identity, so running `S` for `t+1` steps
  and applying one final `H` equals running `comp S H` for `t+1` steps.
* **Ideal leg ≤ q3 from segDeck** (`ideal3_point_tv_le_q3`) — the ideal 3-round
  run from the reference segregated deck is `≤ q3` (the sub-lemma B assemble,
  re-isolated).
* **Ideal leg ≤ q3 for all d** (`ideal3_anyDeck_tv_le_q3`) — via
  `action_comp_eq_conv` (`L` as `PAK (conv S H)`) and `action_run_tv_noise`,
  every deterministic start has the same TV to uniform (the reference and any
  other start see the same `powConv … 3` law).
* **Single perturbation** (`rowTV_le_delta1`) — every row of `F` is within `δ1`
  of the same row of `H` (`permutationActionKernel_eq_map` +
  `tv_map_contraction`), so pushing one distribution through `F` vs `H` costs
  at most `δ1` (`apply_tv_of_row_bound`). No three-step `3·δ1` budget: the
  final kernel is applied once, after the run.

The concrete budget `q3 + δ1 < 1/1000` closes the headline (pure `norm_num`).

See `docs/planning/proof-strategies/2026-11-26-evening-terminal-reset-and-finish-line.md`
section A2 for the source (uncompiled) target.
-/

open FiniteDeck CommanderPermutation

/-- The literal 25-position exchange kernel — the swap law `swapLaw` pushed
through its deck action (`PAK`, `permutationActionKernel`). -/
noncomputable def S : FiniteKernel Deck Deck :=
  FiniteDeck.permutationActionKernel Gate6Crux.swapLaw

/-- The ideal terminal reset — the perfect-local reset law `rho99Ideal`. -/
noncomputable def H : FiniteKernel Deck Deck :=
  FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal

/-- The corrected finite terminal kernel — the orientation-corrected
stable-sort finite law `correctedFiniteLaw99`. -/
noncomputable def F : FiniteKernel Deck Deck :=
  FiniteDeck.permutationActionKernel correctedFiniteLaw99

/-- The ideal full-round kernel — three exchanges composed with the single
terminal reset, `comp S H`. -/
noncomputable def L : FiniteKernel Deck Deck :=
  FiniteKernel.comp S H

/-- **hH**: the ideal reset kernel is the M5a/M5b local reset `P ; U`. -/
theorem H_eq_idealLocalReset : H = idealLocalReset :=
  k1_idealKernel_eq_membershipLift

/-- **hL**: the ideal protocol is the M5b ideal full round (K1 swap-first). -/
theorem L_eq_idealFullRound : L = idealFullRound :=
  idealFullRound_eq_physicalIdealRound.symm

/-- **h**: the terminal reset absorbs the protocol — `comp H L = L`. Translated
from the M5b absorption identity `idealLocalReset_absorption`. -/
theorem comp_H_L_eq_L : FiniteKernel.comp H L = L := by
  rw [H_eq_idealLocalReset, L_eq_idealFullRound]
  exact idealLocalReset_absorption

/-- **Terminal-reset deletion** (the A1 abstract identity, instantiated):
running `S` for `t+1` steps and applying one final `H` equals running `comp S H`
for `t+1` steps. -/
theorem apply_run_S_succ_H_eq_run_L (mu : Dist Deck) (t : Nat) :
    FiniteKernel.apply (FiniteKernel.run S (Nat.succ t) mu) H =
      FiniteKernel.run L (Nat.succ t) mu :=
  lastReset_run S H comp_H_L_eq_L mu t

/-- **Isolation of the q3 ideal leg** (the `hbridge` block of
`corrected_threeRound_headline`, re-stated for the terminal protocol): the
3-round ideal run from the reference segregated deck is within `q3` of the
uniform deck. -/
theorem ideal3_point_tv_le_q3 :
    Dist.tv (FiniteKernel.run L 3 (Dist.pointMass segDeck)) (GSR.uniformDist Deck) ≤ q3 := by
  have H_is_g6 : L = g6ThreeRoundFiniteKernel := g6_3round_idealKernel_eq_fullRound.symm
  have hq := g6_threeRound_finiteRun3_tv_le_q3
  rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel)
      (μ := g6ThreeRoundStart)] at hq
  -- hq : TV (run g6ThreeRoundFiniteKernel 3 g6ThreeRoundStart) (uniformDist Deck) ≤ q3
  have hrun : ∀ μ : Dist Deck, FiniteKernel.run g6ThreeRoundFiniteKernel 3 μ =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ g6ThreeRoundFiniteKernel)
        g6ThreeRoundFiniteKernel) g6ThreeRoundFiniteKernel := by
    intro μ
    rw [FiniteKernel.run_succ, FiniteKernel.run_succ, FiniteKernel.run_succ]
    simp [FiniteKernel.run]
  have hbridge : FiniteKernel.run g6ThreeRoundFiniteKernel 3 (Dist.pointMass segDeck) =
      FiniteKernel.run g6ThreeRoundFiniteKernel 3 g6ThreeRoundStart := by
    rw [hrun, hrun]
    rw [apply_segDeck_idealKernel_eq]
  rw [H_is_g6, hbridge]
  exact hq

/-- **tL as a single action kernel.** Via the convolution bridge, `L` is the
permutation-action kernel of the convolution `conv S H`. -/
theorem L_eq_pak_conv :
    L = FiniteDeck.permutationActionKernel (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) :=
  action_comp_eq_conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal

/-- The ideal leg is the same TV for every deterministic start (the reference
segregated deck and any other start derive the same `powConv … 3` law). -/
theorem ideal3_anyDeck_tv_le_q3 (d : Deck) :
    Dist.tv (FiniteKernel.run L 3 (Dist.pointMass d)) (GSR.uniformDist Deck) ≤ q3 := by
  have h1 := action_run_tv_noise (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) 3 d
  have h2 := action_run_tv_noise (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) 3 segDeck
  rw [← L_eq_pak_conv] at h1 h2
  have h3 := h1.trans h2.symm
  rw [h3]
  exact ideal3_point_tv_le_q3

/-- **The local row bound** (a generic lemma extracted from the inner block of
`corrected_kernelDiscrepancy_le_δ1`): every row of the corrected finite terminal
kernel is within `δ1` of the same row of the ideal terminal reset. -/
theorem rowTV_le_delta1 (x : Deck) :
    Dist.tv (FiniteDeck.permutationActionKernel correctedFiniteLaw99 x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤ δ1 := by
  have h1 : Dist.tv (FiniteDeck.permutationActionKernel correctedFiniteLaw99 x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤
      Dist.tv correctedFiniteLaw99 Gate6Crux.rho99Ideal := by
    simpa only [FiniteDeck.permutationActionKernel_eq_map] using
      Dist.tv_map_contraction correctedFiniteLaw99 Gate6Crux.rho99Ideal (·.trans x)
  have h2 : Dist.tv correctedFiniteLaw99 Gate6Crux.rho99Ideal ≤ δ1 := by
    have h3 : Dist.tv correctedFiniteLaw99 Gate6Crux.rho99Ideal =
        Dist.tv correctedFiniteLaw99 correctedIdealLaw99 := by
      rw [correctedIdealLaw99_eq_rho99Ideal]
    rw [h3, correctedFiniteLaw99_tv_eq_rho99Finite, δ1_eq_2401_over_8388608]
    simpa only [Gate6Crux.rho99Finite, Gate6Crux.rho99Ideal] using oneRoundDeckTV_le_delta1
  exact h1.trans h2

/-- **The row bound for the 22-per-pile corrected law.**  Every row of the
    `2^22`-label corrected finite kernel is within `2401 / 2^22` of the same row
    of the ideal reset.  This is the `22+22` specialization of the generic
    per-pile transport bound: the corrected law's TV equals the uncorrected
    `rhoRoundFinite` TV (the `permInverseEquiv` bijection), then
    `rhoRoundTransport_le_twoPile` at `a = 2^22`, evaluated by `choose_two_right`. -/
theorem rowTV_22_22 (x : Deck) :
    Dist.tv (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)) x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤
      2401 / 2 ^ 22 := by
  have hideal : Gate6Crux.rho99Ideal =
      rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) := rfl
  have h1 : Dist.tv (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)) x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤
      Dist.tv (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)) Gate6Crux.rho99Ideal := by
    simpa only [FiniteDeck.permutationActionKernel_eq_map] using
      Dist.tv_map_contraction (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)) Gate6Crux.rho99Ideal (·.trans x)
  rw [hideal] at h1
  have hIdealEq := rhoRoundFiniteCorrected_tv_eq_rhoRoundFiniteIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)
  rw [hIdealEq] at h1
  have h3 := rhoRoundTransport_le_twoPile 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)
  exact h1.trans (le_trans h3 (by norm_num [Nat.choose_two_right]))

/-- **The row bound for the unequal-alphabets 22+21 corrected law.**  Every row of the
    `(2^22)`-left / `(2^21)`-right corrected finite kernel is within
    `1225 / 2^22 + 1176 / 2^21` of the same row of the ideal reset — the A3
    `22+21` specialization (the left pile of size 50 carries `2^22` labels, the
    right pile of size 49 carries `2^21` labels).  Proved from the generic
    unequal-alphabets transport `rhoRoundFiniteCorrectedU_tv_le`. -/
theorem rowTV_22_21 (x : Deck) :
    Dist.tv (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num)) x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤
      1225 / 2 ^ 22 + 1176 / 2 ^ 21 := by
  have hideal : Gate6Crux.rho99Ideal =
      rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) := rfl
  have h1 : Dist.tv (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num)) x)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal x) ≤
      Dist.tv (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num)) Gate6Crux.rho99Ideal := by
    simpa only [FiniteDeck.permutationActionKernel_eq_map] using
      Dist.tv_map_contraction (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num)) Gate6Crux.rho99Ideal (·.trans x)
  rw [hideal] at h1
  have h3 := rhoRoundFiniteCorrectedU_tv_le 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (2 ^ 21) (by norm_num) (by norm_num)
  exact h1.trans (le_trans h3 (by norm_num [Nat.choose_two_right]))

/-- **The general interface — any local law + its known error bound.**  The A2 terminal-only
    protocol driven by an arbitrary final kernel `F` whose rows are within `δ` of the ideal
    reset is within total variation `< 1/1000` of the uniform 99! deck, provided the
    arithmetic budget `q3 + δ < 1/1000`.  This is the single reusable assembly behind the
    23-per-pile (`terminal23_anyDeck`), 22+22, and 22+21 certificates — the mechanism the
    guide asks for as "the same proof from A2 now takes any local law". -/
theorem terminal_anyDeck_of_row_bound (F : FiniteKernel Deck Deck) (δ : Rat)
    (hrows : ∀ x : Deck, Dist.tv (F x) (H x) ≤ δ)
    (hbudget : q3 + δ < (1 : Rat) / 1000) (d : Deck) :
    Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  -- 1. The deletion identity collapses the final `H` after the run to the ideal run.
  have hrun3 : FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) H =
      FiniteKernel.run L 3 (Dist.pointMass d) :=
    apply_run_S_succ_H_eq_run_L (Dist.pointMass d) 2
  -- 2. The row bound `F` vs `H` costs at most `δ`.
  have hfirst : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) H) ≤ δ :=
    apply_tv_of_row_bound F H _ δ hrows
  rw [hrun3] at hfirst
  -- 3. The ideal leg is `≤ q3` (any deterministic start).
  have hq3 : Dist.tv (FiniteKernel.run L 3 (Dist.pointMass d)) (GSR.uniformDist Deck) ≤ q3 :=
    ideal3_anyDeck_tv_le_q3 d
  -- 4. Triangle inequality against the ideal leg, then `q3 + δ` closes the budget.
  have htotal : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) ≤
      Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
        (FiniteKernel.run L 3 (Dist.pointMass d)) +
      Dist.tv (FiniteKernel.run L 3 (Dist.pointMass d)) (GSR.uniformDist Deck) :=
    Dist.tv_triangle _ _ _
  have hle : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) ≤ δ + q3 :=
    le_trans htotal (add_le_add hfirst hq3)
  have hclose : δ + q3 < (1 : Rat) / 1000 := by
    rw [add_comm]
    exact hbudget
  exact lt_of_le_of_lt hle hclose

/-- **A3 certificate — 22+22 binary riffles.** Three literal exchanges and one final
    corrected finite kernel at the `2^22`-label alphabet (22 binary riffles per pile,
    44 total), driven from **any** deterministic deck, land within total variation
    `< 1/1000` of the uniform 99! deck.  This is `terminal_anyDeck_of_row_bound` with
    the row bound `rowTV_22_22` and the budget `q3 + 2401/2^22 < 1/1000`. -/
theorem terminal_22_22_anyDeck (d : Deck) :
    Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d))
        (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num))))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  apply terminal_anyDeck_of_row_bound
    (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num)))
    (2401 / 2 ^ 22)
    (fun x => rowTV_22_22 x)
  have hbudget : q3 + 2401 / 2 ^ 22 < (1 : Rat) / 1000 := by
    norm_num [q3]
  exact hbudget

/-- **A3 certificate — 22+21 binary riffles (unequal alphabets).** Three literal
    exchanges and one final corrected finite kernel with `2^22` labels on the left
    pile (size 50) and `2^21` labels on the right pile (size 49) — 22+21 = 43
    binary riffles — driven from **any** deterministic deck, land within total
    variation `< 1/1000` of the uniform 99! deck.  This is
    `terminal_anyDeck_of_row_bound` with the row bound `rowTV_22_21` and the budget
    `q3 + 1225/2^22 + 1176/2^21 < 1/1000`. -/
theorem terminal_22_21_anyDeck (d : Deck) :
    Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d))
        (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num))))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  apply terminal_anyDeck_of_row_bound
    (FiniteDeck.permutationActionKernel (rhoRoundFiniteCorrectedU 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 22) (by norm_num) (2 ^ 21) (by norm_num)))
    (1225 / 2 ^ 22 + 1176 / 2 ^ 21)
    (fun x => rowTV_22_21 x)
  have hbudget : q3 + (1225 / 2 ^ 22 + 1176 / 2 ^ 21) < (1 : Rat) / 1000 := by
    norm_num [q3]
  exact hbudget

/-- **A2 headline — the terminal-only 99-card protocol.** Three literal
exchange rounds and one final corrected finite kernel, driven from **any**
deterministic deck, land within total variation `< 1/1000` of the uniform 99! deck.
No intermediate local riffles are needed (the terminal-reset deletion identity);
the last kernel is a single perturbation of the ideal leg (`q3` from the
ideal protocol, `δ1` for the final kernel), not a three-step `3·δ1` budget. -/
theorem terminal23_anyDeck (d : Deck) :
    Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  -- 1. The deletion identity collapses the final `H` after the run to the ideal run.
  have hrun3 : FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) H =
      FiniteKernel.run L 3 (Dist.pointMass d) :=
    apply_run_S_succ_H_eq_run_L (Dist.pointMass d) 2
  -- 2. The row bound `F` vs `H` costs at most `δ1`.
  have hrows : ∀ x : Deck, Dist.tv (F x) (H x) ≤ δ1 := by
    intro x
    exact rowTV_le_delta1 x
  have hfirst : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) H) ≤ δ1 :=
    apply_tv_of_row_bound F H _ δ1 hrows
  rw [hrun3] at hfirst
  -- 3. The ideal leg is `≤ q3` (any deterministic start).
  have hq3 : Dist.tv (FiniteKernel.run L 3 (Dist.pointMass d)) (GSR.uniformDist Deck) ≤ q3 :=
    ideal3_anyDeck_tv_le_q3 d
  -- 4. Triangle inequality against the ideal leg, then the single `δ1` + `q3` budget.
  have htotal : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) ≤
      Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
        (FiniteKernel.run L 3 (Dist.pointMass d)) +
      Dist.tv (FiniteKernel.run L 3 (Dist.pointMass d)) (GSR.uniformDist Deck) :=
    Dist.tv_triangle _ _ _
  have hle : Dist.tv (FiniteKernel.apply (FiniteKernel.run S 3 (Dist.pointMass d)) F)
      (GSR.uniformDist Deck) ≤ δ1 + q3 :=
    le_trans htotal (add_le_add hfirst hq3)
  have hclose : q3 + δ1 < (1 : Rat) / 1000 := by
    norm_num [q3, δ1, Nat.choose_two_right]
  have hlt : δ1 + q3 < (1 : Rat) / 1000 := by
    rw [add_comm]
    exact hclose
  exact lt_of_le_of_lt hle hlt

end TerminalReset
end Shufflemath
