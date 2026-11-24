module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Shufflemath.TotalVariation
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath.ConvContractionLeft
public import Shufflemath.Gate6K1Swap
public import Shufflemath.K1Wall

@[expose]
public section

namespace Shufflemath

variable (d : Equiv.Perm (Fin 99))

abbrev Deck := Equiv.Perm (Fin 99)

/-! ## Gate-6 K1 — the **correct-order** capstone (promoted real module)

    The Gate-6 K1 headline states that the pushforward of the *state-independent*
    perfect full-round law by the deterministic deck action equals the A3
    exchange-then-local-reset kernel applied to the point mass at `d`.

    **Order matters (2026-12-30).**  `conv μ W` applies `μ` first, then `W`
    (`convAsApply` + `act_composition`), so the physical **swap-then-local** round
    is `conv swapLaw rho99Ideal` — *not* `conv rho99Ideal swapLaw` (which is
    local-then-swap and gives a false-looking fiber-symmetric residual).  In the
    correct order the ideal side carries the specific-deck exchange law all the way
    through, so the capstone is a direct consequence of `k1a_riffle_half` +
    `k1_swapMembership_eq_exchangeMembership` — **no 99! enumeration, no K1b
    counting, no recursion-limit bump.**  See
    `docs/planning/proof-strategies/2026-12-30-k1-correct-order-crack.md`.
-/

-- ------------------------------------------------------------------
-- Bookkeeping lemmas (promoted from the development probe `_ProbeGate6K1`;
-- identical content, now importing the real `K1Wall` module).
-- ------------------------------------------------------------------

/-- **The conv-push bookkeeping, generic in `N` (the wall-free core).**
   Pushing the one-step convolution `conv μ W` by the deterministic deck
   action `(·).trans d` equals the point mass at `d` run through the
   composed permutation-action kernels of `μ` and `W`.  Pure Finsupp/kernel
   bookkeeping — `convMapEqApplyMap` (the join–map commutation, already
   proved), `permutationActionKernel_eq_map` (definitional),
   `apply_pointMass`, `apply_comp` — and generic in `N` so no concrete
   99-card law reference ever enters the rewrite search.  Instantiating at
   `N = 99`, `μ = rho99Ideal`, `W = swapLaw` gives the K1 LHS normal form. -/
theorem convPush_eq_pointMassComp {N : Nat} (μ W : Dist (FiniteDeck.Deck N))
    (d : FiniteDeck.Deck N) :
    (FiniteDeck.conv μ W).map (fun p : FiniteDeck.Deck N => FiniteDeck.act p d) =
      FiniteKernel.apply (Dist.pointMass d)
        (FiniteKernel.comp (FiniteDeck.permutationActionKernel μ)
          (FiniteDeck.permutationActionKernel W)) := by
  -- Term-level composition (no rewrite search — the heavy 99! law refs never
  -- enter; μ W d are generic variables):
  --   step 1  convMapEqApplyMap.symm :  conv-push  =  apply (μ.map (·.act·d)) (PAK W)
  --   step 2  ← apply_comp            :  RHS  =  apply (apply (pointMass d) (PAK μ)) (PAK W)
  --   step 3  point-mass bridge       :  apply (μ.map (·.act·d)) (PAK W)
  --                                      =  apply (apply (pointMass d) (PAK μ)) (PAK W)
  --     [apply_pointMass, permutationActionKernel_eq_map — both rfl-level]
  --   step 4  act ≡ trans inside the push (rfl).
  refine (FiniteDeck.convMapEqApplyMap μ W d).symm.trans ?_
  rw [← FiniteKernel.apply_comp]
  congr
  rw [FiniteKernel.apply_pointMass, FiniteDeck.permutationActionKernel_eq_map]
  apply congrArg (fun f => μ.map f)
  funext p
  rfl

/-- **The ideal within-pile riffle, from a point-mass deck, is the uniform fiber
   at the deck's membership** (the K1 "ideal half").  Applying the ideal riffle
   kernel `PAK rho99Ideal` to the point mass at `d` gives the uniform fiber
   `localLift (membership d)`.  Proved by the per-deck orbit-fiber uniformity
   (`k1wall_riffle_push_mass_factorial` / `rho99Ideal_pairs` from `K1Wall`),
   keeping the pair-law as an *opaque term* so no 99! universe enters `whnf`. -/
theorem k1a_riffle_half (d : Equiv.Perm (Fin 99)) :
    FiniteKernel.apply (Dist.pointMass d)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      FiniteKernel.apply
        (Dist.pointMass (CommanderMembershipKernels.membership d))
        CommanderMembershipKernels.localLift := by
  ext1
  ext1 X
  rw [FiniteKernel.apply_pointMass, FiniteDeck.permutationActionKernel_eq_map,
      FiniteKernel.apply_pointMass]
  change (Dist.mass (Gate6Crux.rho99Ideal.map (fun p => Equiv.trans p d)) X) =
      (Dist.mass (CommanderMembershipKernels.localLift (CommanderMembershipKernels.membership d)) X)
  rw [CommanderMembershipKernels.localLift_mass,
      CommanderMembershipKernels.fiberSet_membership_card]
  have hBr : Gate6Crux.rho99Ideal = rho99Ideal_pairs := by rfl
  rw [hBr]
  -- The K1-wall mass fact as a *term* (no `rw`, whose normalisation would
  -- pull the pair-law's Fintype-instance wall into whnf);  `simpa` bridges
  -- the definitional gaps (lambda beta, ite condition) without reducing the
  -- `map` term.
  have hmass := k1wall_riffle_push_mass_factorial d X
  simpa using hmass

-- ------------------------------------------------------------------
-- The correct-order capstone
-- ------------------------------------------------------------------

-- The permutation-action kernel of the ideal riffle, at a deck `p`, is exactly
-- the uniform fiber at `membership p` — `k1a_riffle_half` restated at the kernel
-- level (each side is a kernel row, so `apply_pointMass` cancels the point mass).
theorem paK_rho99Ideal_eq_localLift (p : Deck) :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal p =
      CommanderMembershipKernels.localLift (CommanderMembershipKernels.membership p) := by
  rw [← (FiniteKernel.apply_pointMass p (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)),
      k1a_riffle_half p,
      FiniteKernel.apply_pointMass]

-- **Linearity of the ideal riffle.**  Applying the ideal within-pile riffle to any
-- deck-law `μ` gives the uniform fiber of `μ`'s *membership* distribution: the
-- riffle preserves the membership (it only reorders within piles) and uniformizes
-- within each fiber, so `apply μ (PAK rho99Ideal) = apply (μ.map membership) localLift`.
theorem riffleApply (μ : Dist Deck) :
    FiniteKernel.apply μ (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      FiniteKernel.apply (μ.map CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  unfold FiniteKernel.apply
  congr 1
  -- goal: μ.map (PAK rho99Ideal) = (μ.map membership).map localLift
  rw [Convexity.StdSimplex.map_map]
  congr 1
  funext p
  exact paK_rho99Ideal_eq_localLift p

-- The correct-order perfect full round: swap first, then within-pile ideal riffle.
noncomputable def fullRoundIdealCorrect : Dist Deck :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal

/-- **The physical (swap-then-local) finite full-round law** — the finite riffle
    `rho99Finite` convolved with the *common* literal-swap law `swapLaw` on the
    left (the correct physical order), the finite mirror of `fullRoundIdealCorrect`. -/
noncomputable def fullRoundFiniteCorrect : Dist Deck :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Finite

/-! **Gate-6 K1 capstone (correct order).**  The pushforward of the state-independent
    perfect full-round law (`conv swapLaw rho99Ideal`, swap-then-riffle) by the
    deterministic deck action `·.act d` equals the exchange-then-local-reset:
    `apply (rawExchangeMembership d) localLift`.  No 99! wall, no K1b counting. -/
theorem k1_capstone_correct :
    fullRoundIdealCorrect.map (fun (x : Deck) => FiniteDeck.act x d) =
      FiniteKernel.apply (CommanderPhysicalExchange.rawExchangeMembership d)
        CommanderMembershipKernels.localLift := by
  dsimp only [fullRoundIdealCorrect]
  rw [convPush_eq_pointMassComp Gate6Crux.swapLaw Gate6Crux.rho99Ideal d]
  rw [← FiniteKernel.apply_comp]
  rw [riffleApply]
  -- goal: apply ((apply (pointMass d) (PAK swapLaw)).map membership) localLift
  --       = apply (rawExchangeMembership d) localLift
  have hswapmap :
      (FiniteKernel.apply (Dist.pointMass d)
          (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)).map
          CommanderMembershipKernels.membership =
        FiniteKernel.apply (Dist.pointMass d) (CommanderPhysicalExchange.rawExchangeMembership) := by
    rw [← FiniteKernel.apply_deterministic_eq_map,
        FiniteKernel.apply_comp,
        k1_swapMembership_eq_exchangeMembership]
  rw [hswapmap]
  -- goal: apply (apply (pointMass d) (rawExchangeMembership)) localLift
  --       = apply (rawExchangeMembership d) localLift
  rw [FiniteKernel.apply_pointMass]

/-! **Gate-6 K1 finite headline (correct order).**  The physical and perfect
    *swap-then-local* full-round permutation laws — each `conv swapLaw rho99·` —
    are within the same per-round collision budget `TV ≤ 2401/8388608 = δ1`.
    The mirror of `Gate6Crux.gate6_crux` (which used the opposite, local-then-swap
    order via the right-contraction `convContraction`): here the fixed swap law is
    on the *left*, so the bound is the left-convolution contraction
    `ConvContractionLeft.convContractionLeft` composed with the committed G6.1
    `oneRoundDeckTV_le_delta1` — a three-step calc, no collision counting, no 99!. -/
theorem gate6_crux_correct :
    Dist.tv fullRoundFiniteCorrect fullRoundIdealCorrect ≤ (2401 : Rat) / 8388608 := by
  calc
    _ = tvFinsupp fullRoundFiniteCorrect fullRoundIdealCorrect :=
        tv_eq_tvFinsupp fullRoundFiniteCorrect fullRoundIdealCorrect
    _ = tvFinsupp (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Finite)
                  (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal) := by
        simp only [fullRoundFiniteCorrect, fullRoundIdealCorrect]
    _ ≤ tvFinsupp Gate6Crux.rho99Finite Gate6Crux.rho99Ideal :=
        ConvContractionLeft.convContractionLeft Gate6Crux.swapLaw
          Gate6Crux.rho99Finite Gate6Crux.rho99Ideal
    _ = Dist.tv Gate6Crux.rho99Finite Gate6Crux.rho99Ideal := by
        rw [← tv_eq_tvFinsupp]
    _ ≤ (2401 : Rat) / 8388608 := by
        simpa [Gate6Crux.rho99Finite, Gate6Crux.rho99Ideal] using oneRoundDeckTV_le_delta1

/-! **Deck-level finite corollary (correct order).**  One physical
    (swap-then-local) round starting from deck `d` — the pushforward of the
    state-independent round laws by the deterministic action `σ ↦ σ.trans d` —
    is within `δ1` of the perfect round: one `tv_map_contraction` applied to
    `gate6_crux_correct`.  Mirrors `Gate6Crux.fullRoundDeck_le_delta1` but in the
    correct (swap-then-local) order. -/
theorem fullRoundDeck_correct_le_delta1 :
    Dist.tv (fullRoundFiniteCorrect.map (fun x => x.trans d))
           (fullRoundIdealCorrect.map (fun x => x.trans d)) ≤ (2401 : Rat) / 8388608 := by
  exact (Dist.tv_map_contraction fullRoundFiniteCorrect fullRoundIdealCorrect
          (fun x => x.trans d)).trans gate6_crux_correct

end Shufflemath
