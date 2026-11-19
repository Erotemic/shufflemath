module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.FiberDisintegration
public import Shufflemath.Finite
public import Shufflemath.PhysicalExchangeReduction
public import Shufflemath.OracleRefinement
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Tactic

-- G2.8 / G2.10: the *generic* A3 kernel law and (next) the generic
-- two-physical-perfect-exchanges theorem.  The 99-card analogue is
-- `Shufflemath.CommanderMembershipExchange` / `CommanderA3KernelLaw`: the
-- physical exchange is a 25-position swap at the *deck* level, and its
-- membership-level effect is proved to equal the macro (count) exchange
-- kernel.  Here the same statement is proved for an arbitrary
-- `ExchangeAdmissible` `(N, m, r, k)` deck.
--
-- The construction: the deck-level physical k-exchange `rawExchange` reads the
-- deck's membership, performs the membership-level subset exchange
-- (`subsetExchangeMembershipKernel`, the T3/G4 kernel), and resamples a deck
-- uniformly inside the resulting membership (the deck-level `localLift`, the
-- type-generic `fiberLaw` for the membership observation).  Its membership-
-- level effect is therefore exactly `subsetExchangeMembershipKernel`, and the
-- A3 kernel law is a pure kernel-algebra reduction (associativity + the
-- perfect-local idempotence `localLift ⊳ det membership = id`) to the G4
-- macro-intertwining kernel equality `g4MacroIntertwining`.
@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-- The deck-level perfect-local resample: given an exact membership (left
  pile), resample a deck uniformly among all decks carrying that membership.
  This is the type-generic `fiberLaw` for the `membership` observation, the
  generic counterpart of `Shufflemath.CommanderMembershipKernels.localLift`
  (whose fiber has card `m! * (N - m)!` by `Fiber.fiberCount`). -/
noncomputable def localLift (N m : Nat) (hm : m ≤ N) :
    FiniteKernel (Membership N m) (Deck N) :=
  FiberDisintegration.fiberLaw (membership N m hm) (membership_surjective N m hm)

/-- A perfect-local resample preserves pile membership: applying `localLift`
  and then re-reading `membership` is the identity kernel.  This is the
  type-generic `fiberLaw_recovers`. -/
theorem localLift_preserves_membership (N m : Nat) (hm : m ≤ N) :
    FiniteKernel.comp (localLift N m hm) (FiniteKernel.deterministic (membership N m hm)) =
      FiniteKernel.identity := by
  dsimp only [localLift]
  exact FiberDisintegration.fiberLaw_recovers (membership N m hm) (membership_surjective N m hm)

/-- The deck-level physical `k`-exchange: read the membership, perform the
  membership-level subset exchange `subsetExchangeMembershipKernel`, and
  resample a deck uniformly in the resulting membership.  Its membership-level
  effect is exactly `subsetExchangeMembershipKernel` — the `det membership`
  read-back of the resampled deck collapses to the exchanged membership.  This
  is the generic counterpart of the 99-card `rawExchange` (the 25-position
  swap), with the perfect-local order randomization supplied by `localLift`. -/
noncomputable def rawExchange (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel (Deck p.N) (Deck p.N) := by
  let hm := Nat.le_of_lt p.hmn
  exact FiniteKernel.comp
    (FiniteKernel.comp (FiniteKernel.deterministic (membership p.N p.m hm))
        (subsetExchangeMembershipKernel p))
    (localLift p.N p.m hm)

/-- The full deck-level route (macro lift, perfect-local resample, physical
  exchange, membership read-back) collapses to the membership-level route
  (macro lift then the membership-level subset exchange): the two
  `localLift ⊳ det membership` sub-chains are each the identity by
  `localLift_preserves_membership`, leaving `A ⊳ K`.  This is the generic
  `hMembershipExchange_lhs_reduces` of the 99-card
  `CommanderMembershipExchange`. -/
theorem hMembershipExchange_lhs_reduces (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel.comp
      (FiniteKernel.comp (FiniteKernel.comp (uniformCountFiberMembership p)
          (localLift p.N p.m (Nat.le_of_lt p.hmn))) (rawExchange p))
      (FiniteKernel.deterministic (membership p.N p.m (Nat.le_of_lt p.hmn))) =
    FiniteKernel.comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p) := by
  let hm := Nat.le_of_lt p.hmn
  dsimp only [rawExchange, hm]
  have hBD : FiniteKernel.comp (localLift p.N p.m hm)
      (FiniteKernel.deterministic (membership p.N p.m hm)) = FiniteKernel.identity :=
    localLift_preserves_membership p.N p.m hm
  -- The inner (resample, re-read, exchange) sub-chain  B ⊳ (D ⊳ K)  =  K:
  --  re-associate to  (B ⊳ D) ⊳ K,  collapse  B ⊳ D  to the identity,  then
  --  identity ⊳ K = K.
  have hBK : FiniteKernel.comp (localLift p.N p.m hm)
      (FiniteKernel.comp (FiniteKernel.deterministic (membership p.N p.m hm))
        (subsetExchangeMembershipKernel p)) = subsetExchangeMembershipKernel p := by
    rw [← FiniteKernel.comp_assoc, hBD, FiniteKernel.comp_id_left]
  simp only [hBD, hBK, FiniteKernel.comp_assoc, FiniteKernel.comp_id_right]

-- The deck → macro projection: read the deck's membership, then the marked-card
-- count in the left pile (the Bernoulli-Laplace macro count).  Factors through
-- `membership` (project d = countInPile (membership d)).  This is the `project`
-- of the generic `run_tv_eq_macro_of_membership_exchange` (G2.10); note it lands
-- in `BLState N m r`, whose *range* is a proper sub-set of `{x // x ≤ N}` (the
-- count is bounded by `m`, `r`, `N`), so a generic `project` is not surjective
-- onto all of `BLState` — the headline uses the recovery-based framework
-- (`hrecover`), not the `fiberLaw project` route.
noncomputable def project (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (d : Deck p.N) :
    BernoulliLaplaceGeneral.BLState p.N p.m p.r := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  exact countInPile p.N p.m p.r hm hr (membership p.N p.m hm d)

/-- G2.8: the generic A3 kernel law.  The membership-level effect of the
  deck-level physical exchange, after the macro lift, equals the macro
  exchange kernel after the macro lift — exactly `g4MacroIntertwining` (G4)
  once the LHS collapses to the membership-level route.  This is the generic
  counterpart of the 99-card `hMembershipExchange_kernel`, and is the
  `hMembershipExchange` hypothesis of the generic
  `run_tv_eq_macro_of_membership_exchange` framework (G2.10). -/
theorem hMembershipExchange_kernel (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel.comp
      (FiniteKernel.comp (FiniteKernel.comp (uniformCountFiberMembership p)
          (localLift p.N p.m (Nat.le_of_lt p.hmn))) (rawExchange p))
      (FiniteKernel.deterministic (membership p.N p.m (Nat.le_of_lt p.hmn))) =
    FiniteKernel.comp (BernoulliLaplaceGeneral.blExchangeKernel p)
      (uniformCountFiberMembership p) := by
  rw [hMembershipExchange_lhs_reduces p, g4MacroIntertwining p]

/-! ## G2.10 — the recovery lemma `hrecover` and the two-physical-perfect-exchanges headline.

`run_tv_eq_macro_of_membership_exchange` (G2.10's framework) needs `hrecover :
comp (comp macroLift localLift) (det project) = identity`.  The whole recovery
reduces to one clean combinatorial lemma, `map_const_on_support`, applied twice:
- pushing `localLift m` through `project` is a point mass at `countInPile m`
  (`hK` below); `localLift m` is supported on the `membership`-fiber `m`, where
  `project = countInPile ∘ membership` is constant.
- pushing `uniformCountFiberMembership x` through `countInPile` is a point mass
  at `x` (`hU` below); that distribution is supported on the `countInPile`-fiber
  `x`, where `countInPile` is constant.

Chaining the two by kernel associativity gives `hrecover`; `hMembershipExchange_kernel`
(G2.8) supplies the other framework hypothesis.
-/

/-- A distribution pushed forward by a function that is **constant `c` on its
  positive-mass support** (every point with nonzero mass maps to `c`) is the
  point mass at `c`.  This is the single reduction behind `hrecover`. -/
theorem map_const_on_support [Fintype α] [Fintype β] [DecidableEq β]
    (mu : Dist α) (f : α → β) (c : β)
    (h : ∀ y, Dist.mass mu y ≠ 0 → f y = c) :
    mu.map f = Dist.pointMass c := by
  apply (Convexity.StdSimplex.weights_inj (f := mu.map f) (g := Dist.pointMass c)).mp
  ext z
  rw [← Dist.mass, ← Dist.mass]
  classical
  -- pushforward mass at z = the `mu`-weighted sum of the deterministic-row masses
  rw [← FiniteKernel.apply_deterministic_eq_map, FiniteKernel.apply_mass]
  -- LHS: ∑ j, mass j · (if z = f j then 1 else 0);  RHS: (if z = c then 1 else 0).
  simp only [FiniteKernel.deterministic, Dist.mass_pointMass]
  -- The RHS ite is a constant; rewrite it as the sum ∑ j, mass j · (if z = c),
  -- which equals (∑ mass j) · (if z = c) = 1 · (if z = c) = the same ite.
  have hRHS : (if z = c then 1 else 0 : Rat) =
      ∑ j, Dist.mass mu j * (if z = c then 1 else 0 : Rat) := by
    rw [← Finset.sum_mul, Dist.sum_mass, one_mul]
  rw [hRHS]
  -- Now both sides are sums; match the summands pointwise.
  rw [Finset.sum_congr rfl]
  intro j _
  by_cases h0 : Dist.mass mu j = 0
  · -- off the support the mass (hence the whole summand) is zero
    simp [h0]
  · -- on the support f j = c, so `z = f j ↔ z = c`: the summands agree
    rw [h j h0]

/-- A perfect-local resample `localLift m` pushed through the deck→macro
  `project` is the point mass at the macro count of `m`: the resample is
  supported on the `membership`-fiber `m`, where `project = countInPile ∘ membership`
  is the constant `countInPile m`.  This is the `hK` core for `hrecover`. -/
theorem localLift_project_map (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (m : Membership p.N p.m) :
    (localLift p.N p.m (Nat.le_of_lt p.hmn) m).map (project p) =
      Dist.pointMass (countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN m) := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  apply map_const_on_support
    (mu := localLift p.N p.m hm m) (f := project p)
    (c := countInPile p.N p.m p.r hm hr m)
  intro d hd
  -- hd : the resample puts nonzero mass only on decks reading membership `m`.
  have hmem : membership p.N p.m hm d = m := by
    by_contra hne
    dsimp only [localLift] at hd
    rw [FiberDisintegration.fiberLaw_mass (membership p.N p.m hm)
      (membership_surjective p.N p.m hm) m d] at hd
    -- hne : the fiber condition is false, so the mass is the `else` branch `0`.
    simp [hne] at hd
  simp only [project, hmem]

/-- Pushing `localLift` through the deterministic `project` equals the
  deterministic kernel that reads the macro count `countInPile`: the
  `hK` half of the recovery. -/
theorem hK (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel.comp (localLift p.N p.m (Nat.le_of_lt p.hmn))
      (FiniteKernel.deterministic (project p)) =
    FiniteKernel.deterministic
      (fun m : Membership p.N p.m =>
        countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN m) := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  classical
  funext m
  -- LHS = apply (localLift m) (det (project p)) = (localLift m).map (project p)
  have hLHS : FiniteKernel.comp (localLift p.N p.m hm) (FiniteKernel.deterministic (project p)) m =
      (localLift p.N p.m hm m).map (project p) := by
    dsimp only [FiniteKernel.comp]
    rw [← FiniteKernel.apply, FiniteKernel.apply_deterministic_eq_map]
  rw [hLHS, localLift_project_map p m]
  dsimp only [FiniteKernel.deterministic, FiniteKernel.identity]

/-- The macro count `countInPile` is constant on the support of
  `uniformCountFiberMembership x` (that distribution lives on the `x`-th
  count-fiber), so pushing it through `countInPile` is the point mass at `x`.
  This is the `hU` core for the recovery. -/
theorem ucfm_countInPile_map (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :
    (uniformCountFiberMembership p x).map
      (fun m : Membership p.N p.m => countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN m) =
      Dist.pointMass x := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  apply map_const_on_support
    (mu := uniformCountFiberMembership p x) (f := fun m : Membership p.N p.m => countInPile p.N p.m p.r hm hr m) (c := x)
  intro j hj
  -- hj : nonzero mass ⟹ countInPileVal j = x.val (the UCFM support is the x-th count-fiber).
  have hval : countInPileVal p.N p.m p.r hm hr j = x.val := by
    by_contra hne
    rw [uniformCountFiberMembership_mass_ite p x j] at hj
    simp [hne] at hj
  refine Subtype.ext ?_
  simp only [countInPile_val, hval]

/-- Pushing `uniformCountFiberMembership` through the deterministic `countInPile`
  equals the identity on macrostates: the `hU` half of the recovery. -/
theorem hU (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel.comp (uniformCountFiberMembership p)
      (FiniteKernel.deterministic
        (fun m : Membership p.N p.m => countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN m)) =
    FiniteKernel.identity := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  classical
  funext x
  have hLHS : FiniteKernel.comp (uniformCountFiberMembership p)
      (FiniteKernel.deterministic (fun m : Membership p.N p.m => countInPile p.N p.m p.r hm hr m)) x =
      (uniformCountFiberMembership p x).map
        (fun m : Membership p.N p.m => countInPile p.N p.m p.r hm hr m) := by
    dsimp only [FiniteKernel.comp]
    rw [← FiniteKernel.apply, FiniteKernel.apply_deterministic_eq_map]
  rw [hLHS, ucfm_countInPile_map p x, FiniteKernel.identity]
  rfl

/-- The **recovery** hypothesis for `run_tv_eq_macro_of_membership_exchange`:
  macro-lifting then perfect-local resampling, read back through the deck→macro
  `project`, is the identity on macrostates.  Follows from associativity plus the
  two halves `hK` and `hU`.  (The `hrecover` required by G2.10's framework.) -/
theorem hrecover (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel.comp
      (FiniteKernel.comp (uniformCountFiberMembership p)
        (localLift p.N p.m (Nat.le_of_lt p.hmn)))
      (FiniteKernel.deterministic (project p)) = FiniteKernel.identity := by
  rw [FiniteKernel.comp_assoc, hK p, hU p]

/-- **G2.10 headline.**  For any Bernoulli-Laplace parameters, the total
  variation between two *physical* perfect-exchange steps (perfect local
  resampling sandwiched around the physical exchange) run from a macrostate,
  and the macrostate stationary law, equals the total variation between the
  corresponding two steps of the Bernoulli-Laplace *macro* chain from that
  macrostate.  This is the two-step, two-physical-exchanges version of the
  G4 macro-intertwining, proven purely from the membership-exchange kernel
  equality `hMembershipExchange_kernel` (G2.8) and the recovery `hrecover` —
  no deck fiber counts are needed.  (99-card instantiation: `p` the 11-pile
  admissible, `x0` the segregated state.) -/
theorem two_physical_perfect_exchanges_uniform
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x0 : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (n : Nat) :
    Dist.tv
      (FiniteKernel.run
          (PhysicalExchangeReduction.exchangeThenLocalReset
            (membership p.N p.m (Nat.le_of_lt p.hmn))
            (localLift p.N p.m (Nat.le_of_lt p.hmn)) (rawExchange p)) n
          (FiniteKernel.apply (Dist.pointMass x0)
            (FiniteKernel.comp (uniformCountFiberMembership p)
              (localLift p.N p.m (Nat.le_of_lt p.hmn)))))
      (FiniteKernel.apply (BernoulliLaplaceGeneral.blStationaryDist p)
          (FiniteKernel.comp (uniformCountFiberMembership p)
            (localLift p.N p.m (Nat.le_of_lt p.hmn)))) =
      Dist.tv
        (FiniteKernel.run (BernoulliLaplaceGeneral.blExchangeKernel p) n (Dist.pointMass x0))
        (BernoulliLaplaceGeneral.blStationaryDist p) := by
  let hm := Nat.le_of_lt p.hmn
  exact PhysicalExchangeReduction.run_tv_eq_macro_of_membership_exchange
    (macroLift := uniformCountFiberMembership p) (localLift := localLift p.N p.m hm)
    (membership := membership p.N p.m hm) (exchange := rawExchange p)
    (macroK := BernoulliLaplaceGeneral.blExchangeKernel p) (project := project p)
    (hrecover := hrecover p) (hMembershipExchange := hMembershipExchange_kernel p)
    (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p) n

/-- **G2.3 / G2.5 headline (oracle).**  For any Bernoulli-Laplace parameters and
  any number of steps `n`, the total variation between `n` *oracle* exchanges — each
  a fresh uniform draw inside the count fiber after the macro (count) transition,
  i.e. `oracleStep (project p) lift (blExchangeKernel p)` — run from a macrostate,
  and the lifted macrostate stationary law, equals the total variation between the
  corresponding `n` steps of the Bernoulli-Laplace *macro* chain from that
  macrostate.

  This is the type-generic oracle counterpart of the physical G2.10 headline
  above: it follows purely from the recovery `hrecover` (no deck fiber counts,
  and no deck-level surjectivity, which is false generically — `project`'s range
  is the admissible sub-range, not all of `BLState`) via the type-generic
  `OracleRefinement.run_tv_eq_macro`.  The 99-card instantiations are `n = 2`
  (G2.3) and `n = 3` (G2.5). -/
theorem two_oracle_exchanges_uniform
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x0 : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (n : Nat) :
    Dist.tv
      (FiniteKernel.run
          (OracleRefinement.oracleStep
            (project p)
            (FiniteKernel.comp (uniformCountFiberMembership p)
              (localLift p.N p.m (Nat.le_of_lt p.hmn)))
            (BernoulliLaplaceGeneral.blExchangeKernel p)) n
          (FiniteKernel.apply (Dist.pointMass x0)
            (FiniteKernel.comp (uniformCountFiberMembership p)
              (localLift p.N p.m (Nat.le_of_lt p.hmn)))))
      (FiniteKernel.apply (BernoulliLaplaceGeneral.blStationaryDist p)
          (FiniteKernel.comp (uniformCountFiberMembership p)
            (localLift p.N p.m (Nat.le_of_lt p.hmn)))) =
      Dist.tv
        (FiniteKernel.run (BernoulliLaplaceGeneral.blExchangeKernel p) n (Dist.pointMass x0))
        (BernoulliLaplaceGeneral.blStationaryDist p) := by
  let hm := Nat.le_of_lt p.hmn
  exact OracleRefinement.run_tv_eq_macro
    (project := project p)
    (lift := FiniteKernel.comp (uniformCountFiberMembership p) (localLift p.N p.m hm))
    (hrecover := hrecover p)
    (macroK := BernoulliLaplaceGeneral.blExchangeKernel p)
    (Dist.pointMass x0) (BernoulliLaplaceGeneral.blStationaryDist p) n

end FiniteDeck
end Shufflemath
