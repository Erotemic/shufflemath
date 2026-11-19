module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.FiberDisintegration
public import Shufflemath.Finite
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

end FiniteDeck
end Shufflemath
