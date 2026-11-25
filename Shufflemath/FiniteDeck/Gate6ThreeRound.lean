module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.Perturbation
public import Shufflemath.GSR
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.CommanderFiberWitness
public import Shufflemath.FiberDisintegration
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderFullDeckDisintegration
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.FiniteDeck.Gate6FiniteGSR
public import Shufflemath.Gate6Crux
public import Shufflemath.Gate6K1Capstone
public import Shufflemath.Gate6K1Direct
public import Shufflemath.Gate6K1Swap
public import Shufflemath.GSRDeckRound
public import Shufflemath.TelescopeF5

@[expose]
public section

namespace Shufflemath

open CommanderPermutation
open BernoulliLaplace

/-!
## Gate 6 — the 3-round physical headline: `TV < 1/1000`.

The canonical home of the 99-card **physical** three-round finite-shuffler
headline (previously the scratch `_ProbeG6ThreeRound*` files) together with the
two K1 kernel-algebra bridges it reuses.

`g6_threeRound_headline` proves that three iterations of the **correct-order**
full round `comp (PAK swapLaw) (PAK rho99Finite)` (a uniform 25/25 exchange,
then the A3 perfect-shuffle round) driven from the fiber-uniform 49-segregated
start lands within total variation `< 1/1000` of the uniform `99!` deck.

The result is assembled purely from already-proven pieces (no `99!`
enumeration, no `native_decide`, no `maxHeartbeats` escalation):

* **`g6_threeRound_compList3_eq_run`** — the `compList [K,K,K]` ↔ `run K 3`
  alignment bridge (pure `FiniteKernel` algebra).
* **`k1_idealKernel_eq_membershipLift` / `K1_swapFirst_eq_exchangeLift`** — the
  K1 swap-first (correct-order) one-round assembly: the ideal round
  `comp (PAK swapLaw) (PAK rho99Ideal)` equals the A3
  `exchange-then-local-reset` kernel (the `q3` residual's kernel).
* **`g6_threeRound_kernelDiscrepancy_le_δ1`** (sub-lemma A) — the finite
  round's per-round kernel discrepancy against the ideal round is `≤ δ1`.
* **`g6_threeRound_finiteRun3_tv_le_q3`** (sub-lemma B) — the 3-round finite
  run from the fiber-uniform start is `≤ q3` from uniform (the exact
  three-round ideal residual).
* **`g6_3round_idealKernel_eq_fullRound`** — the A3 `q3` kernel equals the
  correct-order full-round ideal kernel (the bridge sub-lemma B and the
  capstone both use).
* **`g6_threeRound_headline`** — the final assembly: the length-free `n`-step
  telescope (`compList_telescope_nstep_le_n_times_d`, `≤ 3·δ1`) + sub-lemma B
  (`≤ q3`) + the numeric close `q3 + 3·δ1 < 1/1000`
  (`gate6_headline_lt_thousandth`).
-/

-- ============================================================================
-- 1. The `compList` ↔ `run` alignment bridge (sub-lemma B's kernel algebra).
-- ============================================================================

-- The 99-card commander deck state, as a full deck permutation.
abbrev g6ThreeRoundDeck := Equiv.Perm (Fin 99)

/-- Applying a three-kernel `compList` protocol to `μ` is the three-fold
    `FiniteKernel.run` iteration: unrolling `compList [K, K, K]` to the nested
    `comp` chain, then to the triple `apply`, matches the three `run_succ`
    steps. Pure `FiniteKernel` algebra (`compList_cons`, `compList_nil`,
    `comp_id_right`, `apply_comp`, `run_succ`) — no equinumerosity, no
    `native_decide`, no oracle/`WHNF` wall. -/
theorem g6_threeRound_compList3_eq_run (K : FiniteKernel g6ThreeRoundDeck g6ThreeRoundDeck)
    (μ : Dist g6ThreeRoundDeck) :
    FiniteKernel.apply μ (compList [K, K, K]) = FiniteKernel.run K 3 μ := by
  have hL : FiniteKernel.apply μ (compList [K, K, K]) =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ K) K) K := by
    rw [compList_cons, compList_cons, compList_cons, compList_nil,
        FiniteKernel.comp_id_right,
        ← FiniteKernel.apply_comp, ← FiniteKernel.apply_comp]
  have hR : FiniteKernel.run K 3 μ =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ K) K) K := by
    rw [FiniteKernel.run_succ, FiniteKernel.run_succ, FiniteKernel.run_succ]
    simp [FiniteKernel.run]
  rw [hL, hR]

-- ============================================================================
-- 2. The K1 swap-first (correct-order) one-round assembly.
-- ============================================================================

-- ideal (within-pile riffle) round kernel = membership then lift. From the
-- already-proved point-mass (fiber-row) fact `k1a_riffle_half`
-- (`Gate6K1Capstone`) via the generic `kernelOfFiberRows`.
theorem k1_idealKernel_eq_membershipLift :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal =
      FiniteKernel.comp (FiniteKernel.deterministic CommanderMembershipKernels.membership)
        CommanderMembershipKernels.localLift := by
  exact Gate6K1Direct.kernelOfFiberRows
    (H := FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)
    (f := CommanderMembershipKernels.membership)
    (L := CommanderMembershipKernels.localLift)
    k1a_riffle_half

-- K1 assembly, swap-first (correct) order:
--         comp (PAK swapLaw) (PAK rho99Ideal) = comp (rawExchangeMembership) localLift
--  Pure kernel algebra from the two proven halves + associativity.
theorem K1_swapFirst_eq_exchangeLift :
    FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
      FiniteKernel.comp CommanderPhysicalExchange.rawExchangeMembership
        CommanderMembershipKernels.localLift := by
  have hH := k1_idealKernel_eq_membershipLift
  have hK := k1_swapMembership_eq_exchangeMembership
  rw [hH, ← FiniteKernel.comp_assoc, hK]

-- ============================================================================
-- 3. Sub-lemma A: the per-round kernel-discrepancy bound (finite ≤ ideal).
-- ============================================================================

/-- The finite 3-round round kernel: swap (left shuffle) first, then the A3
    physical perfect-shuffle round (resample + exchange). -/
noncomputable def g6ThreeRoundFiniteRound : FiniteKernel Deck Deck :=
  FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
    (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)

/-- Sub-lemma A: the per-round kernel discrepancy between the finite round
    `comp (PAK swapLaw) (PAK rho99Finite)` and the ideal round
    `comp (PAK swapLaw) (PAK rho99Ideal)` is at most the per-round collision
    budget `δ1`. Each row decomposes through the `PAK` action law to exactly
    the A3 `apply_discrepancy_bound`, which is `≤ TV(rho99Finite, rho99Ideal)`
    by the deterministic-map contraction and `≤ δ1` by
    `oneRoundDeckTV_le_delta1`. -/
theorem g6_threeRound_kernelDiscrepancy_le_δ1 :
    kernelDiscrepancy g6ThreeRoundFiniteRound
      (FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)) ≤ δ1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  set νx := (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw) x with hνx
  have hK : g6ThreeRoundFiniteRound x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite) := by
    simp only [g6ThreeRoundFiniteRound, FiniteKernel.comp, FiniteKernel.apply, hνx]
  have hL : (FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
          (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)) x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
    simp only [FiniteKernel.comp, FiniteKernel.apply, hνx]
  rw [hK, hL]
  have hA1 := apply_discrepancy_bound
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) νx
  calc
    _ ≤ kernelDiscrepancy (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := hA1
    _ ≤ Dist.tv Gate6Crux.rho99Finite Gate6Crux.rho99Ideal := by
        unfold kernelDiscrepancy
        apply Finset.max'_le
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨y, _, rfl⟩
        simpa only [FiniteDeck.permutationActionKernel_eq_map]
          using Dist.tv_map_contraction Gate6Crux.rho99Finite Gate6Crux.rho99Ideal (·.trans y)
    _ ≤ δ1 := by
        rw [δ1_eq_2401_over_8388608]
        simpa only [Gate6Crux.rho99Finite, Gate6Crux.rho99Ideal] using oneRoundDeckTV_le_delta1

-- ============================================================================
-- 4. Sub-lemma B: the 3-round finite run is `≤ q3` from uniform.
-- ============================================================================

-- The 99-card 3-round finite kernel: exchange, then perfect-local reset.
noncomputable def g6ThreeRoundFiniteKernel : FiniteKernel Deck Deck :=
  PhysicalExchangeReduction.exchangeThenLocalReset
    CommanderMembershipKernels.membership
    CommanderMembershipKernels.localLift
    CommanderPhysicalExchange.rawExchange

-- The fiber-uniform start: the 49-segregated commander state lifted to its deck fiber.
noncomputable def g6ThreeRoundStart : Dist Deck :=
  FiniteKernel.apply (Dist.pointMass commanderSegregatedState)
    (FiberDisintegration.fiberLaw project project_surjective)

/-- Sub-lemma B: the three-round finite run from the fiber-uniform start is at
    total variation `≤ q3` from the uniform 99! deck. Two rewrites close it, no
    equinumerosity / `native_decide` / 99! enumeration: (1) the
    `compList↔run` bridge turns `apply μ (compList [L,L,L])` into
    `run L 3 μ`; (2) the already-proved
    `three_physical_perfect_exchanges_uniform_unconditional` states
    `TV (run L 3 μ) (uniform) = q3`. -/
theorem g6_threeRound_finiteRun3_tv_le_q3 :
    Dist.tv (FiniteKernel.apply g6ThreeRoundStart
                 (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                           g6ThreeRoundFiniteKernel]))
            (GSR.uniformDist Deck) ≤ q3 := by
  rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel)
       (μ := g6ThreeRoundStart)]
  dsimp only [g6ThreeRoundFiniteKernel, g6ThreeRoundStart]
  rw [CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional]
  simp [q3]

-- ============================================================================
-- 5. The ideal-kernel bridge: the A3 `q3` kernel = the correct-order full round.
-- ============================================================================

-- The `q3` ideal kernel (`exchangeThenLocalReset membership localLift rawExchange`,
-- the A3 exchange-then-local-reset kernel) = the correct-order full-round ideal
-- kernel `comp (PAK swapLaw) (PAK rho99Ideal)`.  Pure kernel algebra: unfold
-- the two defs, regroup by associativity, push the exchange through membership
-- (`rawExchange_membership_pushforward`), and fuse with the K1 swap-first
-- assembly.
theorem g6_3round_idealKernel_eq_fullRound :
    PhysicalExchangeReduction.exchangeThenLocalReset
        CommanderMembershipKernels.membership
        CommanderMembershipKernels.localLift
        CommanderPhysicalExchange.rawExchange =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
  unfold PhysicalExchangeReduction.exchangeThenLocalReset
  unfold PhysicalExchangeReduction.localReset
  rw [← FiniteKernel.comp_assoc, CommanderPhysicalExchange.rawExchange_membership_pushforward,
      ← K1_swapFirst_eq_exchangeLift]

-- ============================================================================
-- 6. The capstone: the physical 3-round TV < 1/1000 (final assembly).
-- ============================================================================

/-- **Gate 6 headline.** The 99-card **physical** three-round finite shuffler —
    three iterations of the correct-order full round
    `comp (PAK swapLaw) (PAK rho99Finite)` (swap, then the A3 perfect-shuffle
    round) — driven from the fiber-uniform 49-segregated start, lands within
    total variation `< 1/1000` of the uniform `99!` deck. Assembled purely from
    already-proven pieces: sub-lemma A (`≤ δ1` per round) + the `n`-step
    telescope (`≤ 3·δ1`) + sub-lemma B (`≤ q3`) + the numeric close
    `q3 + 3·δ1 < 1/1000` (`gate6_headline_lt_thousandth`). -/
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
