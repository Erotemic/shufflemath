module

public import Shufflemath.FiniteDeck.TerminalReset
public import Shufflemath.CommanderFullDeckDisintegration
public import Shufflemath.FiniteDeck.GeneralSchedule
public import Shufflemath.FiniteDeck.HandSecrecy

@[expose] public section

namespace Shufflemath
namespace TerminalResetLower

/-!
## The A4 lower bound: two exchanges cannot reach the 0.001 target

The 2026-11-26 evening finish-line guide (section A4) asks for a rigorous
*exchange-count lower bound*: **any schedule using at most two uniform
25-position exchanges between the same fixed piles, with any intervening
membership-preserving shuffles, fails the worst-case `1/1000` target**.
The guide states this suffices even at the segregated reference deck.

What is proven here (all compiled, `lake build
Shufflemath.FiniteDeck.TerminalResetLower`):

* **The exact ideal 2-exchange TV** (`q2`, `ideal2_segDeck_tv_eq_q2`,
  `ideal2_anyDeck_tv_eq_q2`) — the 2-exchange run of the terminal kernel
  `L = comp S H` from *any* deterministic start is at TV exactly `q2` — the
  value of `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional`
  (re-isolated from the fiber-uniform start via the same `ideal_reset_run_eq_point`
  bridge used for A2's q3, then deck-relabeling transport via
  `action_run_tv_noise`).
* **Numeric close** (`q2_gt_thousandth`, `ideal2_anyDeck_tv_eq_q2_gt`) —
  `q2 > 1/1000`, pure `norm_num`.
* **Fewer than two exchanges cannot beat it** (`ideal1_anyDeck_tv_ge_q2`,
  `ideal0_anyDeck_tv_ge_q2`) — `uniform` is stationary under `L`
  (`uniform_stationary_pak`/`uniform_stationary_L`, proved via the singleton-fiber
  kernel-averaging identity `mass_map_trans_single` and the weight-reindexing
  bijection `reindexWeights`), so TV contracts along `L`
  (`Dist.kernel_contraction`): the 1-exchange and 0-exchange protocols have TV
  *at least* `q2`.

What is **landed** here (the full A4 assembly for the positive-exchange
cases): the *general-schedule* lower bound — **any schedule using at most two
uniform 25-position exchanges between the same fixed piles, with any
intervening membership-preserving shuffles and at least one exchange, fails
the worst-case `1/1000` target** (`general_schedule_tv_gt_thousandth`). The
chain (`uniform_stationary_H`, `general_schedule_tv_ge_ideal`,
`general_schedule_tv_gt_thousandth`):

1. the deck-level H-erasure law for an arbitrary interspersed schedule —
   applying `H` to the output of `J_1, S_1, ..., J_t, S_t` erases only the
   within-pile order and leaves `run L t mu` — is proved in
   `Shufflemath.FiniteDeck.GeneralSchedule` (`membership_readback_schedule`,
   `schedule_then_H`, `run_L_succ`, composed into
   `general_schedule_H_erased`);
2. uniform decks are stationary under `H` (`uniform_stationary_pak` at
   `rho99Ideal`), so kernel contraction under `H` gives
   `TV(run L t mu, uniform) ≤ TV(apply mu (buildSchedule sch), uniform)`;
3. for `t = 2` (exactly `q2`) and `t = 1` (≥ `q2`), the ideal-run TV is at
   least `q2 > 1/1000`, so the schedule output fails the target.

What is **landed** here, too (the full A4 assembly for the zero-exchange
case): the *zero-exchange general-schedule* lower bound — **any schedule
whose only steps are membership-preserving shuffles, with at most two
exchanges and none in fact, from any deterministic start, fails the
worst-case `1/1000` target** (`zero_exchange_schedule_tv_gt_thousandth`).
The chain (`uniform_membership_mass`, `tv_pointMass`, `tv_map_contraction`):

1. the membership read-back of the schedule output is the initial membership
   read-back (`membership_readback_schedule` with `countExchanges = 0`
   reduces to the identity — the same `compPow idealMembershipKernel 0`
   identity used elsewhere);
2. uniform decks are uniform over the valid memberships (`uniform_membership_mass` —
   the fixed `Nat.choose 99 50` fiber count, bridged through the
   `leftCards`/`handSet` identity and `handSet_uniform_law`);
3. the membership pushforward is a TV non-expansion (`tv_map_contraction`),
   so the output's TV to the uniform deck is at least the membership-level TV;
4. the membership-level TV of the start point mass to the uniform membership
   law is `1 - 1/choose 99 50 > 1/1000` (`tv_pointMass` + `uniform_membership_mass`
   + `Nat.choose 99 50 ≥ 2`).

Together with the positive-exchange cases this is the **complete** A4
statement: any schedule using at most two uniform 25-position exchanges
between the same fixed piles, with any intervening membership-preserving
shuffles, fails the worst-case `1/1000` target.
-/

open FiniteDeck CommanderPermutation TerminalReset

/-- The exact two-round **ideal** TV constant, re-stated for the terminal
protocol: the value of `two_physical_perfect_exchanges_uniform_unconditional`. -/
def q2 : Rat :=
  (12255318415559330995522631403472464258192877 /
    4933350368865509640837610315994582805439728012 : Rat)

/-- The concrete budget's floor: `q2 ≥ 0.001`. Pure `norm_num`. -/
theorem q2_gt_thousandth : (1 : Rat) / 1000 < q2 := by
  norm_num [q2]

/-- **Reindexing helper**: the uniform reindex of the weights around a fixed
deck `y` runs over a bijection of the deck type, so the sum is the whole mass. -/
theorem reindexWeights (y : Deck) (noise : Dist Deck) :
    (∑ j : Deck, noise.weights (y.trans j.symm)) = 1 := by
  let e : Deck ≃ Deck := {
    toFun := fun j => y.trans j.symm
    invFun := fun k => (y.symm.trans k).symm
    left_inv := by
      intro j
      change (y.symm.trans (y.trans j.symm)).symm = j
      rw [← Equiv.trans_assoc]
      rw [Equiv.symm_trans_self, Equiv.refl_trans, Equiv.symm_symm]
    right_inv := by
      intro k
      change y.trans ((y.symm.trans k).symm).symm = k
      rw [Equiv.symm_symm]
      rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans] }
  have h : (∑ j : Deck, noise.weights (y.trans j.symm)) = ∑ z : Deck, noise.weights z :=
    Equiv.sum_comp e (fun j => noise.weights j)
  rw [h]
  exact (Dist.sum_mass noise : (∑ x, noise.weights x) = 1)

/-- Kernel-averaging height: the fiber of a single deterministic deck under
`noise.map (·.trans j)` is exactly the singleton `{y.trans j.symm}`. -/
theorem mass_map_trans_single (y j : Deck) (noise : Dist Deck) :
    Dist.mass (noise.map (fun p => p.trans j)) y = noise.weights (y.trans j.symm) := by
  rw [Dist.map_mass_eq_univ_fiber]
  rw [Finset.sum_eq_single (y.trans j.symm)]
  · have hc : (y.trans j.symm).trans j = y := by
      rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
    simp [hc]
    rfl
  · intro x _ hxne
    have hnc : ¬ (x.trans j = y) := by
      intro hx
      have hxeq : x = y.trans j.symm := by
        have h1 := congrArg (Equiv.trans · j.symm) hx
        rw [Equiv.trans_assoc] at h1
        rw [Equiv.self_trans_symm, Equiv.trans_refl] at h1
        exact h1
      exact hxne hxeq
    rw [ite_eq_right hnc]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **Uniform decks are stationary under any `permutationActionKernel`.** -/
theorem uniform_stationary_pak (noise : Dist Deck) :
    FiniteKernel.apply (GSR.uniformDist Deck) (FiniteDeck.permutationActionKernel noise) =
      GSR.uniformDist Deck := by
  classical
  ext y
  change Dist.mass (FiniteKernel.apply (GSR.uniformDist Deck) (FiniteDeck.permutationActionKernel noise)) y =
    Dist.mass (GSR.uniformDist Deck) y
  simp only [FiniteKernel.apply_mass, GSR.mass_uniformDist]
  rw [← Finset.mul_sum]
  have h1 : (∑ j : Deck, Dist.mass (noise.map (fun p => p.trans j)) y) =
      ∑ j : Deck, noise.weights (y.trans j.symm) :=
    Finset.sum_congr rfl (fun j _ => mass_map_trans_single y j noise)
  simp only [FiniteDeck.permutationActionKernel]
  rw [h1, reindexWeights]
  rw [mul_one]

/-- **Uniform decks are stationary under the full-round kernel `L`** (both
factors individually — `S` and `H`). -/
theorem uniform_stationary_L :
    FiniteKernel.apply (GSR.uniformDist Deck) L = GSR.uniformDist Deck := by
  have h1 := uniform_stationary_pak Gate6Crux.swapLaw
  have h2 := uniform_stationary_pak Gate6Crux.rho99Ideal
  show FiniteKernel.apply (GSR.uniformDist Deck)
    (FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)) = GSR.uniformDist Deck
  rw [← FiniteKernel.apply_comp]
  rw [h1]
  exact h2

/-- The ideal 2-exchange run from the reference segregated deck has TV exactly
`q2` — the value of the two-exchange unconditional theorem, re-isolated. -/
theorem ideal2_segDeck_tv_eq_q2 :
    Dist.tv (FiniteKernel.run L 2 (Dist.pointMass segDeck)) (GSR.uniformDist Deck) = q2 := by
  have hL : L = g6ThreeRoundFiniteKernel := g6_3round_idealKernel_eq_fullRound.symm
  have hbridge : FiniteKernel.run g6ThreeRoundFiniteKernel 2 (Dist.pointMass segDeck) =
      FiniteKernel.run g6ThreeRoundFiniteKernel 2 g6ThreeRoundStart := by
    rw [FiniteKernel.run_succ 1, FiniteKernel.run_succ 0, FiniteKernel.run_succ 1, FiniteKernel.run_succ 0]
    rw [show (FiniteKernel.run g6ThreeRoundFiniteKernel 0 (Dist.pointMass segDeck)) = Dist.pointMass segDeck from rfl,
        show (FiniteKernel.run g6ThreeRoundFiniteKernel 0 g6ThreeRoundStart) = g6ThreeRoundStart from rfl]
    rw [apply_segDeck_idealKernel_eq]
  rw [hL, hbridge]
  exact CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional

/-- **Every deterministic start has the same ideal 2-exchange TV** (the
reference and any other start see the same `powConv … 2` law), so the
two-exchange TV from any deck is exactly `q2`. -/
theorem ideal2_anyDeck_tv_eq_q2 (d : Deck) :
    Dist.tv (FiniteKernel.run L 2 (Dist.pointMass d)) (GSR.uniformDist Deck) = q2 := by
  have h1 := action_run_tv_noise (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) 2 d
  have h2 := action_run_tv_noise (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) 2 segDeck
  rw [← L_eq_pak_conv] at h1 h2
  have h3 := h1.trans h2.symm
  rw [h3]
  exact ideal2_segDeck_tv_eq_q2

/-- **A2/A4 heads — exactness of the ideal leg.** The ideal 2-exchange run
from any deterministic start is at TV exactly `q2 > 1/1000`. -/
theorem ideal2_anyDeck_tv_eq_q2_gt (d : Deck) :
    (1 : Rat) / 1000 < Dist.tv (FiniteKernel.run L 2 (Dist.pointMass d)) (GSR.uniformDist Deck) := by
  rw [ideal2_anyDeck_tv_eq_q2]
  exact q2_gt_thousandth

/-- **The 1-exchange protocol cannot beat the 2-exchange bound** (kernel
contraction along `L`, using uniform stationarity). -/
theorem ideal1_anyDeck_tv_ge_q2 (d : Deck) :
    q2 ≤ Dist.tv (FiniteKernel.run L 1 (Dist.pointMass d)) (GSR.uniformDist Deck) := by
  have hmono := Dist.kernel_contraction L (FiniteKernel.run L 1 (Dist.pointMass d)) (GSR.uniformDist Deck)
  rw [uniform_stationary_L] at hmono
  -- hmono : TV(run L 2 mu, uniform) ≤ TV(run L 1 mu, uniform)
  have hq := ideal2_anyDeck_tv_eq_q2 d
  have h2 := hmono
  rw [show (FiniteKernel.apply (L.run 1 (Dist.pointMass d)) L) = FiniteKernel.run L 2 (Dist.pointMass d) from
    FiniteKernel.run_succ 1 L (Dist.pointMass d)] at h2
  rw [hq] at h2
  exact h2

/-- **The 0-exchange protocol** (no exchanges at all: the start deck itself)
is at TV at least `q2`. -/
theorem ideal0_anyDeck_tv_ge_q2 (d : Deck) :
    q2 ≤ Dist.tv (Dist.pointMass d) (GSR.uniformDist Deck) := by
  have hmono := Dist.kernel_contraction L (Dist.pointMass d) (GSR.uniformDist Deck)
  rw [uniform_stationary_L] at hmono
  -- hmono : TV(run L 1 mu, uniform) ≤ TV(mu)
  have hq := ideal1_anyDeck_tv_ge_q2 d
  exact hq.trans hmono

/-- **Uniform decks are stationary under the terminal reset `H`** (the second
factor of the full-round kernel `L`). -/
theorem uniform_stationary_H :
    FiniteKernel.apply (GSR.uniformDist Deck) H = GSR.uniformDist Deck := by
  show FiniteKernel.apply (GSR.uniformDist Deck)
    (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) = GSR.uniformDist Deck
  exact uniform_stationary_pak Gate6Crux.rho99Ideal

/-- **The deck-level H-erasure contraction step** (the guide's A4 chain). For
a schedule with at least one exchange, the schedule output's TV to the uniform
deck is at least the ideal run's TV: kernel contraction under `H` (with
uniform stationarity) applied to the schedule output, composed with the
deck-level deletion identity `GeneralSchedule.general_schedule_H_erased`
(applying `H` to the schedule output leaves `run L t mu`). -/
theorem general_schedule_tv_ge_ideal (d : Deck) (sch : List GeneralSchedule.ScheduleStep)
    (ht1 : 1 ≤ GeneralSchedule.ScheduleStep.countExchanges sch) :
    Dist.tv (FiniteKernel.run L (GeneralSchedule.ScheduleStep.countExchanges sch) (Dist.pointMass d)) (GSR.uniformDist Deck) ≤
      Dist.tv (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch)) (GSR.uniformDist Deck) := by
  have herased := GeneralSchedule.general_schedule_H_erased (Dist.pointMass d) sch ht1
  have hmono := Dist.kernel_contraction H
    (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch)) (GSR.uniformDist Deck)
  rw [uniform_stationary_H] at hmono
  rw [herased] at hmono
  exact hmono

/-- **The general-schedule A4 lower bound.** Any schedule using **at most two**
uniform 25-position exchanges between the same fixed piles, with any
intervening membership-preserving shuffles and at least one exchange, fails
the worst-case `1/1000` target: the schedule output is at TV at least `q2 > 1/1000`
from the uniform deck. The zero-exchange case is not covered by this theorem
(the positive-length identity is not claimed there — see the module docstring). -/
theorem general_schedule_tv_gt_thousandth (d : Deck) (sch : List GeneralSchedule.ScheduleStep)
    (ht1 : 1 ≤ GeneralSchedule.ScheduleStep.countExchanges sch)
    (ht2 : GeneralSchedule.ScheduleStep.countExchanges sch ≤ 2) :
    (1 : Rat) / 1000 < Dist.tv
      (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch)) (GSR.uniformDist Deck) := by
  have hle := general_schedule_tv_ge_ideal d sch ht1
  have hcount : GeneralSchedule.ScheduleStep.countExchanges sch = 1 ∨
      GeneralSchedule.ScheduleStep.countExchanges sch = 2 := by omega
  have hq2 : q2 ≤ Dist.tv (FiniteKernel.run L
      (GeneralSchedule.ScheduleStep.countExchanges sch) (Dist.pointMass d)) (GSR.uniformDist Deck) := by
    rcases hcount with h | h
    · rw [h]
      exact ideal1_anyDeck_tv_ge_q2 d
    · rw [h]
      rw [ideal2_anyDeck_tv_eq_q2]
  calc (1 : Rat) / 1000 < q2 := q2_gt_thousandth
    _ ≤ Dist.tv (FiniteKernel.run L (GeneralSchedule.ScheduleStep.countExchanges sch) (Dist.pointMass d)) (GSR.uniformDist Deck) := hq2
    _ ≤ Dist.tv (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch)) (GSR.uniformDist Deck) := hle


/-! ## The zero-exchange general-schedule lower bound

The zero-exchange case of the A4 general-schedule bound — an arbitrary
schedule of membership-preserving shuffles with **no exchanges**. The
membership read-back of the output is exactly the initial membership
read-back (the positive-length identity is not claimed there; instead the
identity is the trivial `compPow idealMembershipKernel 0 = identity`), and
the uniform deck's membership law is uniform over the `Nat.choose 99 50`
valid memberships. TV contraction under the membership pushforward then
gives the bound `1 - 1/choose 99 50 > 1/1000`.
-/

/-- The uniform left-pile law: under the uniform deck law, the left-card set
(`leftCards`) is uniform over the 50-card subsets. -/
theorem uniform_leftCards_law (S : Finset (Fin 99)) (hS : S.card = 50) :
    Dist.mass ((GSR.uniformDist CommanderPermutation.Deck).map
      (fun d => CommanderPermutation.leftCards d)) S =
      (1 : Rat) / (Nat.choose 99 50 : Rat) := by
  have brid : (fun d => CommanderPermutation.leftCards d) =
      (fun d => FiniteDeck.handSet 99 50 (by decide) d) := by
    funext d
    ext x
    simp [CommanderPermutation.leftCards, CommanderPermutation.leftPosition,
      FiniteDeck.handSet, FiniteDeck.handPositions, Fin.castLE]
  rw [brid]
  exact FiniteDeck.handSet_uniform_law 99 50 (by decide) S hS

/-- The uniform membership law: under the uniform deck law, every valid
membership (50-card left-pile set) carries mass `1 / choose 99 50`. The
fiber count of a membership is the fiber count of its left-card set (the
membership is determined by the left-card set — `Subtype.ext`), so the
identity reduces to `uniform_leftCards_law`. -/
theorem uniform_membership_mass (m : CommanderMembershipKernels.Membership) :
    Dist.mass ((GSR.uniformDist CommanderPermutation.Deck).map
      CommanderMembershipKernels.membership) m =
      (1 : Rat) / (Nat.choose 99 50 : Rat) := by
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have hcount : ((Finset.univ : Finset CommanderPermutation.Deck).filter
      (fun d => CommanderMembershipKernels.membership d = m)).card =
      ((Finset.univ : Finset CommanderPermutation.Deck).filter
        (fun d => CommanderPermutation.leftCards d = m.1)).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro d _
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hcount]
  have hleft := uniform_leftCards_law m.1 m.2
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card] at hleft
  exact hleft

/-- The **zero-exchange general-schedule lower bound.** Any schedule whose
only steps are membership-preserving shuffles (no exchanges at all),
applied from any deterministic start, still fails the worst-case `1/1000`
target: the output's TV to the uniform deck is at least `1 - 1/choose 99 50`,
which exceeds `1/1000`.

The argument: the membership read-back of the output is the initial
membership read-back (`membership_readback_schedule` with `countExchanges = 0`
reduces to the identity — the same `compPow idealMembershipKernel 0` identity
as elsewhere), so the output's membership law is a point mass at the start
deck's membership. The membership pushforward is a TV non-expansion
(`tv_map_contraction`), so the output's TV to the uniform deck is at least the
TV of the two membership laws. The start membership law is a point mass whose
TV to the uniform membership law is `1 - 1/choose 99 50` by `tv_pointMass` and
`uniform_membership_mass`. -/
theorem zero_exchange_schedule_tv_gt_thousandth (d : CommanderPermutation.Deck)
    (sch : List GeneralSchedule.ScheduleStep)
    (h0 : GeneralSchedule.ScheduleStep.countExchanges sch = 0) :
    (1 : Rat) / 1000 < Dist.tv
      (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch))
      (GSR.uniformDist CommanderPermutation.Deck) := by
  -- The membership read-back of the schedule output is the initial one.
  have hmb := GeneralSchedule.membership_readback_schedule (Dist.pointMass d) sch
  rw [h0, FiniteKernel.compPow_zero, FiniteKernel.apply_id_left] at hmb
  -- TV contraction under the membership pushforward.
  have hcontract := Dist.tv_map_contraction
    (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch))
    (GSR.uniformDist CommanderPermutation.Deck)
    CommanderMembershipKernels.membership
  rw [← FiniteKernel.apply_deterministic_eq_map (FiniteKernel.apply (Dist.pointMass d)
      (GeneralSchedule.buildSchedule sch)) CommanderMembershipKernels.membership] at hcontract
  rw [hmb] at hcontract
  rw [FiniteKernel.deterministic_apply_pointMass] at hcontract
  -- The start membership law is a point mass; its TV to the uniform
  -- membership law is `1 - 1/choose 99 50`.
  have htv : Dist.tv (Dist.pointMass (CommanderMembershipKernels.membership d))
      ((GSR.uniformDist CommanderPermutation.Deck).map CommanderMembershipKernels.membership) =
      1 - 1 / (Nat.choose 99 50 : Rat) := by
    rw [Dist.tv_pointMass, uniform_membership_mass]
  -- Numeric close.
  have hc : (2 : Nat) ≤ Nat.choose 99 50 := by decide
  have hc2 : (2 : Rat) ≤ (Nat.choose 99 50 : Rat) := by exact_mod_cast hc
  have h1 : (1 : Rat) - 1 / (Nat.choose 99 50 : Rat) > 1 / 1000 := by
    have hle : (1 : Rat) / (Nat.choose 99 50 : Rat) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hc2
    nlinarith [hle]
  calc (1 : Rat) / 1000 < 1 - 1 / (Nat.choose 99 50 : Rat) := h1
    _ = Dist.tv (Dist.pointMass (CommanderMembershipKernels.membership d))
        ((GSR.uniformDist CommanderPermutation.Deck).map CommanderMembershipKernels.membership) := htv.symm
    _ ≤ Dist.tv
        (FiniteKernel.apply (Dist.pointMass d) (GeneralSchedule.buildSchedule sch))
        (GSR.uniformDist CommanderPermutation.Deck) := hcontract

end TerminalResetLower
end Shufflemath
