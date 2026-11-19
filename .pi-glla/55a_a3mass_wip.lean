module
-- ============================================================================
-- 55th-session WIP — A3 part (i) inner-sum: `rawExchange_membershipCount_mass`
-- ============================================================================
-- TARGET theorem (not yet proven — see DIAGNOSIS below):
--
--   theorem rawExchange_membershipCount_mass (d : Deck) (c : Nat) :
--       Finset.sum ((Finset.univ : Finset Membership).filter (fun m => membershipCount m = c))
--         (fun m => Dist.mass (rawExchangeMembership d) m)
--         = (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat) /
--           (transitionDenominator 99 50 25 : Rat)
--
-- i.e. the total mass of the post-exchange membership law `rawExchangeMembership d`
-- into the membership-count fiber `c` equals the Bernoulli--Laplace transition prob.
--
-- PROVEN & COMMITTED this session (prerequisites now in the library):
--   * `fiberSum_eq_preimageCard`            (FinsetCombinatorics.lean)  — the double-count
--   * `rawExchangeMembership_pointMass`      (A3ExchangePushforward)    — mass = (1/#X)·#{fiber}
--   * `exchangeChoice_equiv_lr`              (A3ExchangePushforward)    — choice ≃ flat (L,R) (NEW)
--   * `membershipCount_newMembership`        (CommanderMembershipKernels)
--   * `newLeftCount_eq_transitionNumerator`  (A3ExchangePushforward)
--   * `exchangeChoice_card_eq_transitionDenominator` (CommanderA3Count)
--
-- DIAGNOSIS (the blocker for the assembly):
--   `exchangeChoice` has `#exchangeChoice = choose 50 25 * choose 49 25 ≈ 1.6e28` elements.
--   Any proof step that COMPUTES `Fintype.card` of a subtype over `exchangeChoice`
--   (or over the flat product `{p // p.1 ∈ leftChoices ∧ p.2 ∈ rightChoices}`) by
--   normalization is intractable (heartbeat timeout at 200000).  `simp [Fintype.card_subtype]`
--   triggers that computation instead of RELATING the two cards.  The structural lemmas
--   (`exchangeChoice_card_eq_transitionDenominator`, `newLeftCount_eq_transitionNumerator`)
--   succeed because they use `choose`-based counts (via `card_product`/`card_powersetCard`),
--   never enumerating.
--
--   => The assembly must relate the two sides by PURE Bijections / card-relations
--      (`Fintype.card_congr` on an `Equiv`, explicit `Fintype.card_subtype (p := ...)`),
--      NEVER by computing an intractable `Fintype.card`.
--
-- KEY BRIDGE IDEAS (worked out; not yet assembled cleanly):
--   * `countPred (j : exchangeChoice) : Prop := memF d j ∈ cFib`  (a LOCAL let referencing the
--     local `cFib`) — then `{j // memF d j ∈ cFib}` and `{j // countPred j}` are the SAME subtype
--     (definitionally), so the double-count's final equality is `rfl`, not a finset-ext.
--   * `memF (d) (j) : Membership := newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)`
--     (the `.map` argument of `rawExchangeMembership`).
--   * `flatPred (d) (c) (p : Finset (Fin 50) × Finset (Fin 49)) : Prop :=
--       (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = c`  (matches newLeftCount's predicate).
--   * transport: `countPred j ↔ flatPred (exchangeChoice_equiv_lr j).1`  (definitional, via
--     membershipCount_newMembership — see `_ProbeEq` pattern: dsimp all defs then rw membershipCount_newMembership).
--   * `hToFlat : Fintype.card {j // countPred j} = Fintype.card {p // p.1 ∈ lc ∧ p.2 ∈ rc ∧ flatPred p}`
--     by `Fintype.card_congr` on the equiv `{j // countPred j} ≃ {p // ...}` (a Bijection, no compute).
--   * `hFinset : Fintype.card {p // p.1 ∈ lc ∧ p.2 ∈ rc ∧ flatPred p} = ((lr).filter flatPred).card`
--     via `p.1 ∈ lc ∧ p.2 ∈ rc ↔ p ∈ lr` (mem_product) THEN explicit `Fintype.card_subtype (p := ...)`.
--   * `hNum : ((lr).filter flatPred).card = transitionNumerator 99 50 25 (leftOriginalCount d) c`
--     via newLeftCount_eq_transitionNumerator (structural).
--   * calc: Σ_{m∈cFib} mass(m) = Σ (1/nX)·fc m = (1/nX)·Σ fc m = (1/nX)·#{j//countPred j}
--           = (1/nX)·transitionNumerator = transitionNumerator / transitionDenominator.
--     (nX = #exchangeChoice = transitionDenominator;  Σ fc m = #{j//countPred j} via fiberSum.)
--
-- NEXT STEPS (fresh turn):
--   1. Rebuild `_ProbeA3Mass.lean` with `countPred` as a local let (referencing local `cFib`),
--      so `h3` (the {j//memF∈cFib} = {j//countPred j}) is `rfl`.
--   2. Make `hFinset` use mem_product THEN explicit `Fintype.card_subtype (p := ...)`, NOT
--      `simp [Fintype.card_subtype]` (which computes).  Keep `flatPred` opaque (never dsimp it into
--      the simp set) so `newLeftCards` is never normalized.
--   3. Confirm every `Fintype.card {…}` relation goes through `card_congr`/`card_subtype` (relate,
--      not compute).  A scoped `set_option maxRecDepth 1000000` (top of the probe) is a fallback,
--      but the relational path should avoid it entirely.
--   4. If it proves: promote to CommanderA3ExchangePushforward.lean (after the equiv), delete the
--      probe, full build + verify, commit, update the handoff/WIP, tally.
-- ============================================================================

public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderA3Kernel
public import Shufflemath.CommanderA3ExchangePushforward
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderMembershipExchange
open CommanderMembershipKernels
open CommanderPermutation
open CommanderPhysicalExchange
open CommanderA3Kernel
open CommanderA3ExchangePushforward
open FinsetCombinatorics
open Finset
open Fin

end Shufflemath
