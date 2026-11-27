module

public import Shufflemath.FiniteDeck.TerminalReset
public import Shufflemath.CommanderFullDeckDisintegration

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

What is **not** landed here, and why: the *general-schedule* statement — any
protocol with arbitrary membership-preserving intermediate kernels (more than
the zero-intersperse terminal-only schedule used above) — needs the
observation-level deletion at the deck level, i.e. that applying the terminal
reset `H` to the output of `J_1, S_1, ..., J_t, S_t` erases only within-pile
order and leaves `run L t mu`. The abstract deletion identity `lastReset_run`
(`S^t ; H = L^t`) is landed and covers the zero-intersperse case; the
intermediate-`J` form is documented as the remaining A4 piece (see
`docs/lean_plan.md`), blocked on the concrete `Q` instantiation and the
H-erasure law for interspersed `J`s, both of which the repo does not yet
record as landed kernels. The 0-intersperse case — the terminal-only schedule
used throughout A2 — is fully covered above.
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

end TerminalResetLower
end Shufflemath
