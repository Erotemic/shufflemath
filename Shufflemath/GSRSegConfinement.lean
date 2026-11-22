module

public import Mathlib.Tactic
public import Shufflemath.GSR
public import Shufflemath.GSRDeckRound
public import Shufflemath.GSRDeckBridge
public import Shufflemath.GSRSegMembership
public import Shufflemath.CommanderPermutation
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath._ProbeBridgeStruct

@[expose] public section

namespace Shufflemath

open Finset
open scoped Nat
open CommanderPermutation

-- ============================================================================
-- Fiber confinement of the within-pile GSR round law.
--
-- The `rhoRoundIdeal` / `rhoRoundFinite` "round" from `GSRDeckRound` only
-- permutes *inside* the fixed 50/49 left/right split (a within-pile
-- `embed_m`); it never moves a card across piles.  Its law is therefore
-- supported on the segregated-left fiber `{d : leftCards d = segLeft}`, a
-- proper subset of the 99! deck space, and in particular it **cannot be the
-- uniform distribution** (nor anything close to it: its TV against uniform is
-- `1 - 50!·49!/99! ≈ 1`).
--
-- This is the precise sense in which the batch-4 "3-round" headline
-- (`gate6_headline_telescope`, whose "ideal" chain is `rhoRoundIdeal`) does not
-- by itself certify convergence to uniform: the `q3` constant it is telescoped
-- against (`Gate6FiniteGSR.q3`, the 3-round *Bernoulli-Laplace physical
-- perfect-exchange* residual ≈ 2.6e-05) belongs to the **cross-pile** exchange
-- chain, not to this fiber-confined within-pile chain.  A real
-- `TV < 1/1000` certification therefore needs the 25-position Bernoulli-Laplace
-- exchange that actually moves cards between piles (the `finiteRound` of the
-- Gate 6 plan, §7), on top of which this module's confinement result is the
-- clean structural prerequisite.
-- ============================================================================

/-- The 23 riffle positions per round (the Bernoulli/GSR parameter `a`). -/
def a23 : Nat := 2 ^ 23
/-- `a23 > 0`. -/
theorem ha23 : 0 < a23 := by norm_num [a23]

/-- The 0↔50 deck swap: the canonical card-mover across the left/right split. -/
def swapDeck : Equiv.Perm (Fin 99) := Equiv.swap (0 : Fin 99) (50 : Fin 99)

-- ---------------------------------------------------------------------------
-- The 50/49 split: which Fin 99 values are left positions.
-- ---------------------------------------------------------------------------

/-- Card `50` (a right-pile card) is not a left position: every element of
    `segregatedLeftSet = (univ : Finset (Fin 50)).image (Fin.castLE hm)` has value `< 50`. -/
theorem h50notLeft : (50 : Fin 99) ∉ segregatedLeftSet := by
  unfold segregatedLeftSet
  dsimp only [FiniteDeck.leftPositions]
  rw [Finset.mem_image]
  intro ⟨i, _, h⟩
  have hv : i.val = 50 := by
    calc
      i.val = (Fin.castLE hm i).val := (Fin.val_castLE _ _).symm
      _ = (50 : Fin 99).val := by rw [h]
      _ = 50 := rfl
  linarith [i.isLt, hv]

/-- Position `0` is a left position (it is `Fin.castLE hm` of the 0-th left index). -/
theorem h0inLeft : (0 : Fin 99) ∈ segregatedLeftSet := by
  unfold segregatedLeftSet
  dsimp only [FiniteDeck.leftPositions]
  rw [Finset.mem_image]
  refine ⟨(0 : Fin 50), by decide, ?_⟩
  dsimp only [Fin.castLE]
  rfl

-- ---------------------------------------------------------------------------
-- The swap deck moves a card across the split, so it is off the fiber.
-- ---------------------------------------------------------------------------

/-- In the swap deck (0 ↔ 50), position 0 holds card `50`, so `50 ∈ leftCards`. -/
theorem h50inSwap : (50 : Fin 99) ∈ FiniteDeck.leftCards 99 50 hm swapDeck := by
  unfold FiniteDeck.leftCards
  rw [Finset.mem_image]
  refine ⟨(0 : Fin 99), h0inLeft, ?_⟩
  simp [swapDeck, Equiv.swap_apply_left]

/-- The swap deck's left pile is not the segregated left set. -/
theorem leftCardsSwap_neq_segLeft :
    FiniteDeck.leftCards 99 50 hm swapDeck ≠ segregatedLeftSet := by
  intro h_eq
  have : (50 : Fin 99) ∈ segregatedLeftSet := h_eq ▸ h50inSwap
  exact h50notLeft this

/-- There is a deck whose left pile is **not** the segregated left pile. -/
theorem exists_deck_offSegLeft : ∃ (d : Equiv.Perm (Fin 99)), leftCards d ≠ segLeft := by
  refine ⟨swapDeck, ?_⟩
  rw [leftCards_reconcile, ← segregatedLeftSet_eq_segLeft]
  exact leftCardsSwap_neq_segLeft

-- ---------------------------------------------------------------------------
-- Confinement: the within-pile round law has zero mass off the fiber.
-- ---------------------------------------------------------------------------

/-- The within-pile ideal round law `rhoRoundIdeal 99 50` gives **zero mass** to
    any deck whose left pile is not exactly the segregated left pile: its
    support is confined to the segregated-left fiber (it can only permute
    within the fixed 50/49 split, never move a card across piles). -/
theorem rhoRoundIdeal_offLeft_zero (d : Equiv.Perm (Fin 99))
    (h : leftCards d ≠ segLeft) :
    Dist.mass (rhoRoundIdeal 99 50 hm (by decide) (by decide) a23 ha23) d = 0 := by
  unfold rhoRoundIdeal
  rw [Dist.map_mass_eq_univ_fiber]
  have hno (x : Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49)) :
      ¬ roundEmbedMap 99 50 hm x = d := by
    intro heq
    exact h (by
      have hleft : leftCards (roundEmbedMap 99 50 hm x) = segLeft := by
        rw [leftCards_reconcile, bridgeA_leftCards x.1 x.2, segregatedLeftSet_eq_segLeft]
      rw [← heq]
      exact hleft)
  refine Finset.sum_eq_zero ?_
  intro x _
  simp [ite_eq_right (hno x)]

/-- **The within-pile round law is not the uniform distribution.**  It is
    supported on the segregated-left fiber, so it has zero mass at an off-fiber
    deck while the uniform law `GSR.uniformDist` (full support) has positive
    mass there.  This is the concrete obstruction to reading the batch-4
    3-round within-pile chain as a `TV < 1/1000` uniform-convergence
    certificate: `q3` (the Bernoulli-Laplace cross-pile residual it is
    telescoped against) is not the TV of this law. -/
theorem rhoRoundIdeal_neq_uniform :
    rhoRoundIdeal 99 50 hm (by decide) (by decide) a23 ha23 ≠ GSR.uniformDist (Equiv.Perm (Fin 99)) := by
  obtain ⟨d, hd⟩ := exists_deck_offSegLeft
  have h0 : Dist.mass (rhoRoundIdeal 99 50 hm (by decide) (by decide) a23 ha23) d = 0 :=
    rhoRoundIdeal_offLeft_zero d hd
  have hpos : 0 < Dist.mass (GSR.uniformDist (Equiv.Perm (Fin 99))) d := by
    rw [GSR.mass_uniformDist]
    apply inv_pos.mpr
    apply Nat.cast_pos.mpr
    rw [Fintype.card_pos_iff]
    exact ⟨1⟩
  intro h_eq
  rw [← h_eq, h0] at hpos
  exact lt_irrefl _ hpos

end Shufflemath
