module
public import Shufflemath.BernoulliLaplaceCommanderBridge
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.FiniteDeck.DobrushinDecay
public import Shufflemath.Dobrushin
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.PhysicalExchangeReduction
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

open BernoulliLaplaceGeneral

variable (p := commanderBLParams)

/-- The exact one-step Bernoulli-Laplace transition weight for the 99-card
Commander deck (50 special, 49 ordinary, 25 special in the first pile): the
probability that a draw of a card in state `x` moves the first pile to state `y`.
`997540809461453561581 / 6330095096149974879912 ≈ 0.15759` is the diagonal
`x = y = 25`. -/
def w50 (x y : Nat) : Rat := transitionWeight 99 50 50 25 x y

/-- The balanced state `25` of the 99-card Commander Bernoulli-Laplace chain
(`BLState 99 50 50 = {x // 1 ≤ x ≤ 50}`). -/
def state25 : BLState 99 50 50 := ⟨25, by decide⟩

/-- The exact value of the balanced-state diagonal of the 99-card exchange kernel:
`w50 25 25 = 997540809461453561581 / 6330095096149974879912 ≈ 0.15759` (a single
`native_decide` on the exact rational transition weight; this is the value the
Dobrushin coefficient `1 − w50 25 25` is computed from). -/
theorem w50_diag_eq : (w50 25 25 : Rat) = (997540809461453561581 : Rat) / 6330095096149974879912 := by
  native_decide

/-- **25 is the minimizer of the reach-to-25 column.** For every state
`x ∈ 1..50`, the one-step transition probability `x → 25` is at least the
diagonal `25 → 25`. This is the single structural fact that makes the Dobrushin
contraction coefficient computable: the tightest TV between two kernel rows is
governed by the smallest incoming mass, which is the diagonal at the balanced
state. Verified by `native_decide` (a 50-term finite check over the exact
rational transition weights). -/
theorem w50_25_min_reach : ∀ (i : Fin 50), (w50 25 25 : Rat) ≤ (w50 (i.val + 1) 25 : Rat) := by
  native_decide

/-- The mass of the Commander exchange kernel's row `x` at state `y` is the exact
transition weight `w50 (x.val) (y.val)`. (`dsimp` only delta-unfolds the
`ofFun`; the heavy 50-entry total-mass witness is never reduced, so this is
cheap and does not stall like a full `simp`.) -/
theorem blExchangeMass_eq_w50 (x y : BLState 99 50 50) :
    Dist.mass (blExchangeKernel commanderBLParams x) y = (w50 x.val y.val : Rat) := by
  dsimp only [blExchangeKernel, commanderBLParams, w50]
  rw [Dist.mass_ofFun]

/-- For any state `x` of the 99-card chain, the kernel's incoming mass at the
balanced state `25` from `x` is at least the diagonal: `w50 (x.val) 25 ≥ w50 25 25`.
Immediate from `w50_25_min_reach` by re-indexing `x.val ∈ 1..50` as a `Fin 50`. -/
theorem reach25_ge_diag (x : BLState 99 50 50) :
    (w50 25 25 : Rat) ≤ (w50 x.val 25 : Rat) := by
  have hlo : 1 ≤ x.val := x.2.1
  have hhi : x.val ≤ 50 := x.2.2
  have hlt : x.val - 1 < 50 := by omega
  have h := w50_25_min_reach (Fin.mk (x.val - 1) hlt)
  simpa [Nat.sub_add_cancel hlo, w50] using h

/-- **The 99-card Dobrushin coefficient has an explicit rational value.**
    `dobrushinCoeff (blExchangeKernel commanderBLParams) = 1 − w50 25 25` is
    bounded above by `1 − w50 25 25` (the overlap bound, applied at the balanced
    state `25`), and `w50 25 25 = 997540809461453561581 / 6330095096149974879912`
    (exact, via `w50_diag_eq`). Numerically `1 − w50 25 25 = 0.8424…` (the exact
    `1 − 0.15759` (the exact `997540809461453561581/6330095096149974879912` diagonal
    subtracted from `1`), matching the Python oracle
    `1.0 − p(25→25)`. -/
theorem blExchange_dobrushinCoeff_le :
    Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) ≤ (1 - w50 25 25 : Rat) := by
  unfold Dobrushin.dobrushinCoeff
  apply Finset.max'_le
  intro d hd
  rw [Dobrushin.pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  -- d = rowTV K ij.1 ij.2; bound each row pair at the balanced state 25
  have h1 : Dobrushin.rowTV (blExchangeKernel commanderBLParams) ij.1 ij.2 ≤
      1 - min (Dist.mass (blExchangeKernel commanderBLParams ij.1) state25)
              (Dist.mass (blExchangeKernel commanderBLParams ij.2) state25) :=
    Dobrushin.rowTV_le_one_sub_minMass (blExchangeKernel commanderBLParams) ij.1 ij.2 state25
  rw [blExchangeMass_eq_w50 ij.1 state25, blExchangeMass_eq_w50 ij.2 state25] at h1
  have hi : w50 25 25 ≤ w50 ij.1.val 25 := reach25_ge_diag ij.1
  have hj : w50 25 25 ≤ w50 ij.2.val 25 := reach25_ge_diag ij.2
  have hmin : w50 25 25 ≤ min (w50 ij.1.val 25) (w50 ij.2.val 25) := le_min hi hj
  calc
    _ = Dobrushin.rowTV (blExchangeKernel commanderBLParams) ij.1 ij.2 := by rfl
    _ ≤ 1 - min (w50 ij.1.val 25) (w50 ij.2.val 25) := h1
    _ ≤ 1 - w50 25 25 := by
      apply sub_le_sub_left
      exact hmin

/-- `0 ≤ b ⇒ 0 ≤ b^k` for `b : Rat` (small induction on `mul_nonneg`). -/
theorem pow_nonnegRat {b : Rat} (hb : 0 ≤ b) (k : Nat) : 0 ≤ b ^ k := by
  induction k with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; exact mul_nonneg ih hb

/-- **Base monotonicity of rational powers (non-expanding).** For `0 ≤ a ≤ b` and
`n`, `a^n ≤ b^n`. Proved by a direct induction on the exponent (one multiplication
per step), so — unlike `gcongr` — it never expands `^n` into `n` factors and cannot
hit the elaborator recursion limit even for `n = 41`. -/
theorem pow_le_pow_base_nonneg {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hnb : 0 ≤ b := le_trans ha hab
    have hbk : 0 ≤ b ^ k := pow_nonnegRat hnb k
    rw [pow_succ, pow_succ]
    calc
      _ = a ^ k * a := rfl
      _ ≤ b ^ k * a := mul_le_mul_of_nonneg_right ih ha
      _ ≤ b ^ k * b := mul_le_mul_of_nonneg_left hab hbk

/-- **The exact Dobrushin coefficient power is computable.**
`(1 − w50 25 25)^41 < 1/1000` on the exact rational `1 − w50 25 25 =
1 − 997540809461453561581/6330095096149974879912 ≈ 0.8424`. Stated standalone (not
inside the larger `dobrushinCoeff_41_lt_thousand` term) so the `native_decide` runs
in its own elaboration context with a fresh recursion budget. -/
theorem one_sub_w50diag_pow41_lt_thousand : ((1 : Rat) - w50 25 25) ^ 41 < (1 : Rat) / 1000 := by
  native_decide

/-- **Concrete decay.** The 99-card Commander exchange chain's Dobrushin
    contraction coefficient raised to the 41st power is strictly less than
    `1/1000`: `d^41 < 1/1000` where `d = 1 − w50 25 25`. Combined with
    `physicalExchange_dobrushinDecay`, this gives the headline that 41 physical
    perfect-exchange steps from the **fiber-uniform** start of macrostate `x0` drive
    the TV to uniform below `1/1000` (the arbitrary-ordered-deck strengthening is the
    open Gate-6 program; see `physicalExchange_decay_41_lt_thousand`). The final
    comparison is a `native_decide` on the exact rational
    `(1 − 997540809461453561581/6330095096149974879912)^41 < 1/1000`. -/
theorem dobrushinCoeff_41_lt_thousand :
    (Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) : Rat) ^ 41 <
      (1 : Rat) / 1000 := by
  have hle : Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) ≤ 1 - w50 25 25 :=
    blExchange_dobrushinCoeff_le
  have hnonneg : 0 ≤ Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) :=
    Dobrushin.dobrushinCoeff_nonneg _
  have hpow : (Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) : Rat) ^ 41 ≤
      (1 - w50 25 25) ^ 41 := pow_le_pow_base_nonneg hnonneg hle 41
  calc
    _ ≤ (1 - w50 25 25) ^ 41 := hpow
    _ < (1 : Rat) / 1000 := one_sub_w50diag_pow41_lt_thousand

/-- **99-card 41-step decay (fiber-uniform start).**  For any 99-card macrostate
    `x0`, 41 physical perfect-exchange steps (perfect-local resample around the
    physical exchange) driven **from the fiber-uniform distribution over decks with
    macrostate `x0`** — the lift `apply (pointMass x0) (comp UCFM localLift)`, i.e.
    uniformly over the count/membership fiber of `x0`, *not* a point mass on one
    specific ordered deck — drive the total variation toward the uniform
    distribution on the whole deck below `1/1000`.  This composes the already-proved
    `physicalExchange_dobrushinDecay` (the physical deck-TV from that fiber-uniform
    start is bounded by the 41st power of the BL macro-chain Dobrushin coefficient)
    with the concrete `dobrushinCoeff_41_lt_thousand`.

    *Scope (Nov-21 assessment, Finding 2):* this is a bound from the **fiber-uniform**
    start of `x0`, NOT from an arbitrary specific ordered 99-card deck — count-process
    mixing alone does not imply full-deck mixing from arbitrary microscopic states.
    The stronger "from any ordered deck" statement is the open Gate-6 arbitrary-deck
    program (the relabeling-invariance / right-convolution structural lemma that
    transports the bound from one segregated ordered deck to every start). -/
theorem physicalExchange_decay_41_lt_thousand (x0 : BLState 99 50 50) :
    Dist.tv
      (FiniteKernel.run
          (PhysicalExchangeReduction.exchangeThenLocalReset
            (membership 99 50 (Nat.le_of_lt commanderBLParams.hmn))
            (localLift 99 50 (Nat.le_of_lt commanderBLParams.hmn))
            (rawExchange commanderBLParams))
          41
          (FiniteKernel.apply (Dist.pointMass x0)
            (FiniteKernel.comp (uniformCountFiberMembership commanderBLParams)
              (localLift 99 50 (Nat.le_of_lt commanderBLParams.hmn)))))
      (GSR.uniformDist (Deck 99))
    < (1 : Rat) / 1000 := by
  have h := physicalExchange_dobrushinDecay commanderBLParams x0 41
  simpa [commanderBLParams] using h.trans_lt dobrushinCoeff_41_lt_thousand

end FiniteDeck
end Shufflemath
