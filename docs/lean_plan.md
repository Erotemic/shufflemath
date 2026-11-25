# Lean formalization roadmap (current)

Status date: **2026-11-17**. This is the **single active mathematical task list**.
For a new agent, begin with [agent_handoff.md](agent_handoff.md). Historical
phase notes are linked at the end; they do not override this plan. Read
`AGENTS.md` before modifying code.

> **Gate 6 status (this session):** batch 1 (`Gate6BadLabels`: bad-label union
> bound + `badLabels_uniform_bound`), batch 2 (a)-(e) (`Gate6TieRank`: `tieRank`
> law = uniform, Key fact B, `tv_maps_le_mismatch`) and **batch 2 (f)** are all
> LANDED. The (f) headline is now the canonical module **`Shufflemath/Gate6F`**
> (in the verified build): `TV(ν_{n,a}, U_{S_n}) ≤ #badLabels/a^n` and
> `≤ choose(n,2)/a`. **Batch 3 (in progress, 2026-02-10):** the three reusable
> TV lemmas for the one-round local-error bound are now all landed — (1)
> `tv_eq_tvFinsupp` (Fintype↔Finsupp TV bridge, `TotalVariation`); (2)
> `tv_map_contraction` (a deterministic pushforward is a TV non-expansion,
> `TotalVariation`); (3) `twoPilePermutationTV_bound` (the two within-pile GSR
> permutation laws' product is within `choose(m,2)/a_L + choose(N-m,2)/a_R` of
> the uniform product, `Gate6F`); (4) `oneRoundTwoPileTV_le_delta1` (that bound
> instantiated at `N=99, m=50, a=2^23`, RHS evaluated to `2401/8388608 = δ1`,
> `Gate6F`). **G6.1 deck-level transport (also this session)** — new module
> `Shufflemath/GSRDeckRound.lean`: `roundEmbedMap N m (pl,pr) = embed_m N m hm pl pr`
> (the deterministic map embedding a within-pile permutation pair into a full-deck
> permutation — note this is `embed_m`, *not* the deck-conjugation `act_d`); 
> `rhoRoundFinite`/`rhoRoundIdeal` push the two-pile product laws (GSR / uniform)
> through it; and `rhoRoundTransport_le_twoPile` + `oneRoundDeckTV_le_delta1` show
> the **deck-level** (full-deck-permutation) one-round finite-vs-ideal TV is within
> the same per-pile collision budget `choose(m,2)/a + choose(N-m,2)/a` (concretely
> `2401/8388608 = δ1`), via `tv_map_contraction` composed with `twoPilePermutationTV_bound`
> — a one-line `le_trans` of the two batch-3 lemmas. **Honest scope note:** 
> `rhoRound` uses `embed_m` + the within-pile `gsrPermutationLaw`; whether it exactly
> equals the *physical* one-round finite-GSR deck law (which may additionally involve a
> left-right `swapPerm` or a different finite-GSR rank model) is a separate modeling
> question — the transport **bound** holds regardless. **Batch 4 building block (also this
> session):** the parameterized telescope in `TelescopeF5.lean` —
> `telescopeBound_le_n_times_d` (generalizes `telescopeBound_le_length` with `1` → a
> parameter `δ`) and `compList_telescope_nstep_le_n_times_d` (two equal-length
> `FiniteKernel` protocols from the same start are within `n·δ` TV when every per-step
> discrepancy is `≤ δ`). **Remaining (batch 4 headline):** instantiate that with the
> per-round discrepancy `δ1` (the GSR round expressed as a `FiniteKernel`, via
> `oneRoundDeckTV_le_delta1`) to get `TV(K³ d0, L³ d0) ≤ 3δ1`, add the ideal 3-round
> chain's residual `q3 = TV(L³ d0, U)` via the triangle inequality, and show
> `3δ1 + q3 < 1/1000` (`gate6_headline_lt_thousandth`). **Landed this batch:** sub-part (a) —
> `gsrRound99_discrepancy_le_δ1` (per-round discrepancy as `kernelDiscrepancy ≤ δ1`) and
> `gate6_headline_telescope` (`TV(K³ d0, U) ≤ q3 + 3·δ1`, conditional on
> `hq3 : TV(L³ d0, U) ≤ q3`), both in `GSRGate6Telescope.lean`. **Batch-3 step-4 CRUX LANDED (this session, `Shufflemath/Gate6Crux.lean` in the verified build):** `TV(fullRoundFinite, fullRoundIdeal) ≤ δ1 = 2401/8388608` for the full-round laws `conv rho99· swapLaw` (common literal-swap factor). Accepted architecture (no `maxHeartbeats 0`, builds in ~6 s): `convAsApply` (convolution with `W` = application of the *same* `permutationActionKernel W`, via `convMapEqApplyMap` at the identity deck) + `convContraction` (one application of the Fintype-free `kernel_apply_lipschitz`) + the committed G6.1 `oneRoundDeckTV_le_delta1` — a 3-step calc, no new collision counting, every lemma generic in `N` except the final specialization. **Sole remaining open
> sub-part: (b) / `hq3`** — FALSE for the state-independent within-pile ideal
> (`gsrRound99Ideal`, TV ≈ 1 ≫ q3; its 3-round chain is one within-pile round, essentially
> singular with uniform); the fulfillable mixing ideal is the state-dependent full-round
> kernel, which is now **Finsupp-representable**: repeated physical rounds are
> `FiniteKernel.run (permutationActionKernel W) t (pointMass d) =
> (powConv W t).map (·.trans d)` (`FiniteDeck.powConvRunEq`, already proved) — no
> constant-output kernel, no `ofFun` joint. The old 10^316 wall (ce0ba37) bound the
> `ofFun` Fintype carrier; the Finsupp `join`/`map` carrier (used by `gate6_crux`)
> stays symbolic in `N`. The on-mission `TV < 1/1000` headline is met
> independently by
> `DobrushinDecay99` (41 perfect exchanges, any macrostate, fiber-uniform start).
> See [agent_handoff.md](agent_handoff.md) and the 2026-11-21 Gate 6 hint doc §5/§6.

> **Gate 6 batch-4 K1 bookkeeping (2026-12-16 session):** the K1 normal-form
> lemmas now BUILD in `Shufflemath/_ProbeGate6K1.lean` (the 3-lemma chain's
> K1 step): (1) `convPush_eq_pointMassComp` — *generic in `N`*:
> `(conv μ W).map (·.act·d) = apply (pointMass d) (comp (PAK μ) (PAK W))`,
> proved by term-level composition of the committed `convMapEqApplyMap` / `←
> apply_comp` / `apply_pointMass` / `permutationActionKernel_eq_map` (no
> rewrite search — the wall-free core); (2) `k1_lhs_bookkeeping` — the 99-card
> instance (`fullRoundIdeal.map (·.act·d)` = point-mass through the composed
> `rho99Ideal`-then-`swapLaw` action kernels); (3) `k1_rhs_bookkeeping` —
> `apply (pointMass d) (exchangeThenLocalReset …) = apply (rawExchangeMembership
> d) localLift` (apply_comp / apply_pointMass / associativity /
> `localLift_preserves_membership` → identity). The **K1 statement**
> assembles with both bookkeeping rewrites; its single remaining `sorry` is
> the known **per-deck orbit-fiber uniformity wall**: at each deck `d`, the
> two-step action kernel `comp (PAK rho99Ideal) (PAK swapLaw)` must equal the
> oracle-exchange + fiber-resample kernel `rawExchangeMembership d |>.map
> localLift` (candidate route: the batch-5b headline machinery adapted to
> kernel equality, or fiber-cardinality equinumerosities F3-style). Key
> proof-engineering lessons (cost a failed build each, recorded in
> `.pi-glla/gate6k1_status.md`): concrete 99!-laden law references must never
> enter an `rw` pattern-search goal (prove generic in N, instantiate by
> `exact`); `act` and `Equiv.trans` are two whnf forms — keep one form per
> proof, bridge by `congrArg + funext + rfl`; fold trailing rewrites into one
> `rw […` list (a separate later tactic errors when an earlier `rw`
> auto-closed the goal). **UPDATE (2026-12-30, 77th session):** this batch-4 K1 was the
> **opposite (local-then-swap) order** — `conv rho99Ideal swapLaw` applies the riffle
> first. The goal's physical round is **swap-then-local** = `conv swapLaw rho99Ideal`,
> whose ideal capstone **`k1_capstone_correct` now builds** in
> `Shufflemath/_ProbeK1correctOrder.lean` (no 99! wall, no K1b counting) — see
> `docs/planning/proof-strategies/2026-12-30-k1-correct-order-crack.md`. The orbit-fiber
> wall / K1b `k1b_count_split` (2b) are symptoms of the wrong order and are moot. Next:
> the finite version, the one-round TV bound, and promotion to a committed module.

> **Toolchain note (2026-02-10):** the library now uses Lean 4.34's `module`
> system (`module` header + `public import` + `@[expose] public section`). See
> `agent_handoff.md` §"Lean 4 module-system migration" for the exact recipe
> (dual `public import`/`public meta import` for `native_decide`, no `private`
> in `@[expose]` sections, EOF scope auto-close). The math and proof content is
> unchanged by this migration.

> **54th session (2026-11-18) — A3 kernel, the double-count's missing lemma found.**
> The active build is the **A3 kernel** (the `hMembershipExchange` capstone, per the
> handoff; G1–G4 and F1/F2 are done). Point-mass (`rawExchangeMembership_pointMass`) and
> part-(i) normalization (`uniformPushforward_pointMass`) are committed. The last blocker
> to `rawExchange_membershipCount_mass` is the general fiber-sum / double-count
> identity `∑ m ∈ S, #{x : f x = m} = #{x : f x ∈ S}`. The 54th session found the
> missing tool: **`Fintype.card_sigma`** (`Data/Fintype/Defs.lean:161`, a `@[simp]`
> lemma `Fintype.card (Σ i, α i) = ∑ i, Fintype.card (α i)`), which the 53rd session's
> grep missed (it only searched `Basic.lean`). The fiber-product-`Equiv` route now works
> except its `right_inv` second component, which is an **`HEq`** over two
> *propositionally*-equal fiber types (`Subtype.ext rfl` is an `Eq`, so it does not
> typecheck). Next: fix that `HEq` (transport into a common fiber type first), or
> avoid the sigma entirely with **`Finset.card_biUnion`** (exists — `Slice.lean:152`).
> Full detail + last-compiling probe: `.pi-glla/53_fiberSum_wip.lean` (54th section);
> resume point: [`agent_handoff.md`](agent_handoff.md).

> **Disintegration session (2026-11-19+) — G3 `bernoulliLaplace_disintegration`
> (LHS + RHS) PROVEN in a WIP probe.** The G3 fiber-disintegration /
> measure-factorization headline — the `bernoulliLaplace` distribution on `Deck N`
> factors as `Dist.uniform (Membership N m) → FibDist (FibType N m) → Deck N`, with
> the pushforward recovering the uniform distribution on `Deck N` — is now **fully
> proved** in a first-class module (`Shufflemath/FiniteDeck/BLDisintegration.lean`,
> target `Shufflemath.FiniteDeck.BLDisintegration`, committed `2c64e78` then renamed), no `sorry`/`admit`. The LHS
> (`Dist.mass (blUniform N m r hm hr) A = 1 / #Membership`) reduces via
> `countFiber_blStationary` + `countFiber_eq_countFiberMemb` + the singleton fiber-sum
> simplification to `#cfMemb · #cfMemb⁻¹ / #choose`, closed by `field_simp` once
> `#cfMemb > 0` is established via the **choose-product form**
> `#cfMemb = choose r c · choose (N-r) (m-c)` with `c = (countInPile A).val` (both
> binomials positive by the `countInPile_admissible` bounds — `Nat.choose_pos` +
> `omega`). The RHS (`Dist.mass (FiberDisintegration.marginalLaw membership) A = 1 / #Membership`)
> follows from `deckCard_eq_membershipFiber` + `field_simp`. This required new
> A3KernelLaw counting-core lemmas (committed `30d49e3`): `countFiber`,
> `countFiberMemb`, `countInPileVal`, `countFiber_blStationary`, `membershipCount`,
> `deckCard_eq_membershipFiber`, and the `blLo`/`blHi` bounds.
> **Next (session 92, 2026-12-16) — G2.9/G2.13 deck-uniform-target DONE (generic).**
> `bernoulliLaplace_disintegration` is promoted to the first-class module
> `Shufflemath/FiniteDeck/BLDisintegration` (`52fbdc9`). On top of it, the **bridge**
> `apply_blStationary_ucfm_locallift_eq_uniformDeck` (`5fd84ac`) proves
> `apply (blStationaryDist p) (comp (UCFM p) localLift) = GSR.uniformDist (Deck p.N)`
> (by `← apply_comp` + the LHS `blStationary_ucfm_eq_marginalMembership` + the
> `FiberDisintegration.marginal_comp_fiber_eq_uniform` recovery — the membership-based
> route that avoids the `project_surjective` wall). And the **generic G2.9/G2.13
> headline** `two_physical_perfect_exchanges_uniform_deck` (`de7638a`) proves, for any
> `n`, `TV(run (physical 2..n-exchange, lifted) n (lifted x0), GSR.uniformDist (Deck N)) =
> TV(run (blExchangeKernel) n (x0), blStationaryDist)` — the 99-card G2.9 (n=2) / G2.13
> (n=3) instantiations. (Session 92's "remaining 99-card-only" pointer here is superseded:
> see session 93 below — both the 99-card two- and three-exchange *unconditional* headlines
> are discharged and in the tree.)
> **Next (session 93, 2026-12-16) — 99-card three-exchange DONE (G2.13 / G3.6).**
> Added `three_physical_perfect_exchanges_uniform_of_counts` +
> `three_physical_perfect_exchanges_uniform_unconditional` to
> `Shufflemath/CommanderFullDeckDisintegration` — the 99-card three-physical-perfect-exchange
> exact-rational headline (TV = `172379525755689183991816396516567920780192827919620440221147749 /
> 6691837923759692633601708022649918108038775216019298375918637677488`), a direct parallel of the
> two-exchange pair (n=2 → n=3: `run … 3`, the 3-step `FiberLifting.run_tv_eq_macro`,
> `commander_tv_after_three_semantic`; the same A3 `hMembershipExchange_kernel` discharges the
> per-shuffle premise — no new exchange hypothesis). Completes G2.9/13 in **both** the generic
> (session 92) and 99-card exact-rational forms, and G3.6. **F4.2 permutation-law wall RESOLVED (this session):** the GSR's law is now a genuine
> `Dist (Equiv.Perm (Fin n))` — `GSRPermutationLaw.gsrPermutationLaw` (the `ν_{n,a}` of the
> `2026-11-20` Section 3 "transport") plus `idealShuffle_canonical_eq_permPushforward` /
> `idealShuffle_canonical_eq_permLaw`, and the pointwise capstone
> `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition` (the `List (Fin n) →
> Equiv.Perm (Fin n)` transport). **Next deep item:** the F5 `perDeckBridge` →
> `uniformFiber_intertwines` (WIP `_Probe47u.lean`). **Gate 8's Dobrushin half DONE (this
> audit):** the non-degenerate full-deck Dobrushin coefficient now has a concrete rational
> bound — see the F5 section (`DobrushinDecay99.blExchange_dobrushinCoeff_le`:
> `dobrushinCoeff (blExchangeKernel commanderBLParams) ≤ 1 − w50 25 25 ≈ 0.8424`, and the
> headline `physicalExchange_decay_41_lt_thousand`: 41 exchanges → TV < `1/1000`). Gate 8's
> bounded-optimization half stays deferred (competitor lower bounds). per the `2026-11-24`
> review follow-up check-off.
> **G1 edge cases DONE (`f3fc08f`):** new module `Shufflemath/FiniteDeck/G1EdgeCases`
> (imports only the generic G1 modules `TwoPile`/`TwoPileFiber` + Mathlib — no
> `Commander*`) records that the boundary parameter values are well-formed and
> non-degenerate: `#(Deck 0) = 1`, `#(Membership N 0) = 1`, `#(Membership N N) = 1`,
> `#(Membership 0 0) = 1` — the goal's G1 edge-case acceptance item. **Remaining
> item 4:** T2 (generic `Membership N m` histogram-fiber = `choose r marked · choose
> (N-r) unmarked`) and T3-to-BL (`count ∘ subsetExchange = blExchange N m r k`).

## Objective and model boundary

Produce a theorem for a *specified finite physical protocol* on 99 individually
identified cards: an explicit upper bound on total variation from uniform,
with an explicit physical-action cost. Eventually certify a minimum-cost
protocol in a declared finite action class. Do not confuse these statements:

1. **50-state Bernoulli--Laplace (BL) count chain:** remembers only how many
   of the original 50 left cards are in the 50-card left pile.
2. **Canonical oracle:** projects a full permutation to the count, takes a BL
   step, then resamples an arbitrary deck uniformly from the new count fiber.
3. **Physical perfect-local operation:** exchanges *selected positions* across
   piles and subsequently randomizes order *within each existing pile*.
4. **Finite-GSR physical operation:** the previous operation with finite
   independent-label riffles instead of uniform within-pile permutations.

The canonical oracle is not pointwise equal to the physical perfect-local
kernel on arbitrary ordered decks. The relevant physical theorem is an
**intertwining after a fiber-uniform input**, mediated by named-card pile
membership. See [full_deck_oracle_bridge.md](full_deck_oracle_bridge.md) and
[commander_fiber_disintegration.md](commander_fiber_disintegration.md).

## Implemented foundations (do not reimplement)

| Area | File(s) | Actual result and scope |
|---|---|---|
| Finite exact probability | `Finite`, `Matrix`, `TotalVariation` | `StdSimplex Rat`, kernels, stochastic-matrix bridge, exact TV |
| Kernel error/composition | `Perturbation`, `Dobrushin`, `ProtocolCertificate`, `Cost` | Weighted TV telescope, contraction and generic cost/error interfaces |
| BL macro chain | `BernoulliLaplace`, `BernoulliLaplaceGeneral`, `BernoulliLaplaceFiber`, `BernoulliLaplaceCommanderBridge` | General normalization, stationarity, reversibility, first centered eigenfunction and Commander specialization; exact 2-/3-step TV values |
| Array/semantic bridge | `BernoulliLaplaceSemantic` | Exact array runs and semantic `FiniteKernel` runs agree |
| Inverse GSR | `GSR` | **Complete.** `productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b)` is proved (`productLabelShuffle_uniform_eq_ideal`), from the joint-distribution bridge, the `labelReparam` pushforward, and sorting compatibility |
| Generic macro/micro TV | `FiberLifting`, `OracleRefinement` | Recoverable-lift TV isometry and canonical oracle intertwining, including schedule results |
| Physical refinement interface | `PhysicalRefinement` | Conditional full-deck physical TV bound using a perfect-local reference and weighted row error |
| Actual 99-card deck | `CommanderPermutation`, `CommanderFiberWitness` | `Equiv.Perm (Fin 99)`, count projection, explicit witness for each of the 50 fibers |
| Uniform fiber algebra | `FiberDisintegration` | Fiber law, marginal law, recovery, and generic unequal-fiber disintegration |
| Physical exchange reduction | `PhysicalExchangeReduction` | Conditional membership-level exchange implies macro-to-full intertwining |
| Commander full-deck consequences | `CommanderFullDeckDisintegration` | Exact 2-/3-step oracle-to-*uniform* theorems **assuming `HasCommanderFiberCounts`**; physical theorem has further explicit membership premises |

**Verification status, not mathematical scope:** The October 21
fiber/disintegration tranche, including the final `FiberDisintegration.lean`
v3 correction, is **compiled and verified by the user's established local
workflow**. Moving to the documentation handoff confirms completion: the
user reports build errors explicitly, rather than pasting every successful
build. Do not reopen this compilation question without concrete contrary
evidence. The 35 passing Python regression tests supplement the Lean work;
they do not establish the separate, still-open F1-F5 theorems.

`Shufflemath.lean` does **not** import every optional target, so a plain
`lake build` alone is insufficient to check the full-deck modules. The costly
`dev/BernoulliLaplacePairOptimality.lean` proof is also intentionally opt-in.

## Current entry point

> **G5 / Gate-6-A thread (session 85, commit `10d9bef`):** the operator-supplied qwen1125
> candidate building blocks are now integrated — `Shufflemath/FiniteDeck/Partition.lean`
> (B1 partition/Sigma/gluing) and `Shufflemath/Gate6K1Bridges.lean` (A0–A4 Gate-6 generic
> bridges) — both in the aggregator and `./dev/verify_next_phase.sh` (green, 37 tests).
> **Next on that thread:** write the A1–A4 / B1–B4 theorems on top of those blocks, per
> `docs/planning/proof-strategies/2026-11-25-gate6-and-multipile-executable-handoff.md`
> (B1 is now largely satisfied by `Partition.lean`; B2 fiber bijection → `twoPile_equivFiber`+
> `glueBlocks`; B3 histogram counting; B4 multi-pile TV). The parallel session-83/84 Gate-6
> three-round thread below is unchanged.

> **Status (session 83, 2026-12-30 build):** **Gate 6 is complete** — the three-round
> *physical* headline `g6_threeRound_headline` (`TV(finiteRound³ start, uniform) < 1/1000`)
> is proved in `Shufflemath/_ProbeG6ThreeRoundCapstone.lean` (sub-lemmas A + B + the
> ideal-kernel bridge + the n-step telescope + `gate6_headline_lt_thousandth`; the
> `Eq.subst`/`hL ▸ t` trick avoids the `exchangeThenLocalReset` elaboration recursion).
> **Next real item:** the batch-5b within-pile headline `rhoRoundIdeal 99 50 … =
> localLift segMembership` (`GSRSegHeadline`) — remaining piece is the support equivalence
> `d ∈ image (roundEmbedMap 99 50) ↔ membership d = segMembership`, a known elaboration-level
> wall (never put the `(fiberOrbit_equiv …).val` deck in a goal; route via
> `Finset.image_ofInjective` + `map_mass_eq_univ_fiber` + `localLift_mass`). Full detail in
> [`agent_handoff.md`](agent_handoff.md).

**F1–F5 and G1–G4 are complete** (no sorries in the A3/F5/G4 modules). The
G4 arbitrary-finite-deck generalization (the 2026-11-15 pivot) is done:
`Shufflemath/FiniteDeck/*` (G1 `TwoPile`, G2 `Fiber`, G3 `SubsetExchange`,
G4 `BLRefinement`) closes with the kernel-equality capstone
`g4MacroIntertwining`, discharging the Commander A3 physical-exchange reduction
(`hMembershipExchange_kernel`, `CommanderA3KernelLaw`) at the 99-card parameters.
F5 certificates (`f5FullDeck_certificate` / `f5Nondegenerate_certificate`,
`CommanderCostedCertificate.lean`) are assembled, with the optimization
quantifiers stated separately in the `## F5-B` section (feasibility proved;
bounded-surrogate + actual-TV optimality stated, not claimed).
**F4.2 is fully resolved** (the permutation law `GSRPermutationLaw.lean` —
`gsrPermutationLaw` / `idealShuffle_canonical_eq_perm*` as a `Dist (Equiv.Perm (Fin n))` —
plus session 93's `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition`): the GSR is a
genuine rearrangement of the deck, not merely set-equal. *Note (2026-11-20):* the
direct *multiset-level* formulation of that fact (`stableBuckets_nodup`: the bucketed
deck is `Nodup`) was explored and found a **redundant parallel formulation** of the
already-proven `orderByNewPosition`/`Equiv.Perm` result — not pursued further (this
Mathlib's `BEq`/`==`-based `List.filter`/`count` API blocks the direct count route;
the `orderByNewPosition` route avoids it). *Packaging (2026-11-20, commit `891a5a7`):* the ~1,070-line `section firstMode` block (the first centered eigenfunction `blFirstModeFunc`, `blConditionalMean`, the hypergeometric means, `gProd`/`gSplit`) was split out of `BernoulliLaplaceGeneral.lean` into a new `Shufflemath/BernoulliLaplaceFirstMode.lean` — a build-granularity win (editing `blConditionalMean` no longer forces a recompile of the 12-module BL-General surface); the declarations keep their `BernoulliLaplaceGeneral.*` names (the section is naming-transparent) and all 37 Python tests pass. **The remaining deep work is now **Gate 6** (see "Next after F5" below); the prior
(i) — F5 `perDeckBridge` → `uniformFiber_intertwines` — is **done** (`perDeckBridge`
committed in `Shufflemath/FiniteDeck/CommanderPerDeckKernel.lean`; `uniformFiber_intertwines`
+ the G4 capstone `g4MacroIntertwining` in `Shufflemath/FiniteDeck/BLRefinement.lean`);
the last F5 piece, Section 3 of
`planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md` — **and (ii)
the F4.2-deferred non-degenerate full-deck budget certificate**, now realized at any
exchange count `n` by `Shufflemath/TelescopeF5.f5FullDeck_nondegenerate_nstep`
(length-free crude-telescope F4.2 crack; see the F5 section), with only the optional
Dobrushin-contraction sharpening left as a refinement. **Next after F5 (2026-12-17):** (a) is **done** — `perDeckBridge` is committed in `Shufflemath/FiniteDeck/CommanderPerDeckKernel.lean` and the pointwise `uniformFiber_intertwines` + the G4 capstone `g4MacroIntertwining` are proved in `Shufflemath/FiniteDeck/BLRefinement.lean`; and (b) **Gate 6** — *the next item*, started 2026-12-17 (continued): the exact target bound `q3 + δ3 < 1/1000` is now pinned in the new module `Shufflemath/FiniteDeck/Gate6FiniteGSR.lean` (`norm_num`), and the remaining construction is to — specialize the now-proved F4.2 n-step abstract telescope (`Shufflemath/TelescopeF5.telescopeTV_le_idealPlusN` / `compList_telescope_nstep_le_n`) to a concrete 99-card finite-GSR protocol (the `Deck` with the 50/49 split in `Shufflemath/CommanderDeckGSR.lean`, the `idealShuffle`/`gsrProductKernel` machinery in `Shufflemath/GSR.lean`, the schedule machinery in `Shufflemath/PhysicalRefinement.lean`) — via the deck-valued `finiteRound` kernel (25-choice + fixed swap + 23 per-pile inverse-GSR riffles) and the per-round physical-vs-ideal TV ≤ `δ1 = 2401/8388608` collision bound — to obtain the explicit symbolic/rational TV-against-uniform terminal bound the qwen engineering review asks for (one concrete protocol, explicit initial/target; a short calc chain per the deep-structural hints — *no* Dobrushin/full-deck maxima needed). The F5 bounded-optimization (Gate 8) stays deliberately deferred (competitor lower bounds). The exact
resume point is in [`agent_handoff.md`](agent_handoff.md); the campaign roadmap
is
[`planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`](planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md).
For new Lean work, run `lake exe cache get` followed by the affected module's
`lake build`; run `./dev/verify_next_phase.sh` when finishing a tranche. This
is a regression workflow, not an extra gate on the existing results.

## Work queue in dependency order

### F1. Prove the exact Commander fiber count -- COMPLETE

**Proved goal:** discharge
`CommanderFullDeckDisintegration.HasCommanderFiberCounts`, already defined
in `Shufflemath/CommanderFullDeckDisintegration.lean`:

```lean
forall x : BernoulliLaplace.CommanderState,
  Dist.mass BernoulliLaplace.commanderStationary x =
    ((FiberDisintegration.fiberSet CommanderPermutation.project x).card : Rat) /
      (Fintype.card CommanderPermutation.Deck : Rat)
```

This **cannot be proved solely** by `CommanderPermutation.project_surjective`: an
inhabited fiber need not have the right *cardinality*. Build a structural
counting proof, without evaluating a type containing `99!` permutations.

> **Progress (F1 complete, 2026-11):** All of F1a-F1d are proved and
> committed (`12e66df`). F1a (`decksWithLeft_card = 50! * 49!`) lives in
> `Shufflemath/CommanderFiberCount.lean`. F1b (`fiberMembershipSets_card =
> choose 50 k * choose 49 (50 - k)`), F1c, and F1d live in
> `Shufflemath/CommanderFiberMembership.lean` and
> `Shufflemath/CommanderFullDeckDisintegration.lean`:
> - **F1c:** `fiberSet_card` proves the fiber at state `x` has exactly
>   `choose 50 (x.val + 1) * choose 49 (50 - (x.val + 1)) * 50! * 49!` decks.
>   Proof shape: the macro fiber `fiberFin k` is reindexed by the section map
>   `d -> (leftCards d, d)` (injective on the fiber), which is exactly the
>   fiber-sigma `(fiberMembershipSets k).sigma leftCardsFin`; `Finset.card_sigma`
>   (Fubini) then reduces the count to the F1b sum times the F1a per-membership
>   count. The dependent-Sigma finset is stated over the Sigma type directly
>   (`Prod` and `Sigma` are distinct in Lean 4.34); the pair equality in the
>   image lemma is closed with `Sigma.ext` plus `HEq.refl`.
> - **F1d:** `commander_fiber_counts : HasCommanderFiberCounts` is unconditional.
>   The hypergeometric stationary mass equals the normalized fiber count because
>   `99! = choose 99 50 * 50! * 49!` (exact rational arithmetic, `native_decide`).
>   The two-/three-exchange uniformity corollaries and
>   `commander_uniform_disintegration_unconditional` follow.
> Verified with `./dev/verify_next_phase.sh` (35 Python tests).

Split into small compilable subresults, preferably in a new dedicated
`Shufflemath/CommanderFiberCount.lean` importing only what is needed:

1. **F1a: fixed membership:** for any valid 50-card subset of `Fin 99`,
   count complete ordered decks with exactly that left-membership set as
   `50! * 49!`. A bijection with independent left/right orderings is the
   preferred proof; avoid brute-force `native_decide` on `Deck`.
2. **F1b: count memberships:** for `x.val + 1` originally-left cards in the
   left pile, count allowed membership sets as
   `Nat.choose 50 (x.val + 1) * Nat.choose 49 (49 - x.val)`.
3. **F1c: combine and normalize:** prove
   `|fiber x| = choose(50,x+1)*choose(49,49-x)*50!*49!`, divide by `99!`,
   and rewrite into the existing exact hypergeometric `commanderStationary`.
4. **F1d: consume the theorem:** export a theorem of type
   `HasCommanderFiberCounts` with no extra premises, then use it in
   `commander_uniform_disintegration` and the existing conditional oracle
   2-/3-step results to give unconditional **ideal-oracle** results.

**Acceptance:** compile the dedicated counting module and
`CommanderFullDeckDisintegration`; check that the exported theorem has no
unproven counting assumptions. Existing `tests/test_commander_fiber_witness.py`
provides exact numeric regression evidence, not a substitute for Lean.
No need to change the already verified BL certificates.

### F2. Define the concrete membership and perfect-local kernels -- COMPLETE

**Dependency:** The compiled `CommanderPermutation` and fiber/disintegration
foundations. F2 can develop independently of F1's arithmetic, but needs F1
for uniform targets.

1. Define `Membership` as the subtype of 50-element subsets of card identities
   in `Fin 99` (or an equivalent bijective type).
2. Define `membership : Deck -> Membership`, and prove that its marked-card
   count agrees with `CommanderPermutation.project`.
3. Define `localLift : FiniteKernel Membership Deck` as uniform orderings of
   the *given membership set*, and prove
   `localLift.comp (FiniteKernel.deterministic membership) = identity`.
4. Define `membershipLift : FiniteKernel CommanderState Membership` as the
   uniform law among memberships with a specified marked count. Prove
   `membershipLift.comp localLift = FiberDisintegration.fiberLaw project
   project_surjective` (or first prove a generic version and specialize).

**Acceptance:** compile new modules and a small-deck exact reference test.
Neither `localLift` nor a physical local shuffle may change pile membership.
Do not confuse `localLift` with the canonical oracle's count-fiber reset.

> **Progress (F2, 2026-11): COMPLETE.** In `Shufflemath/CommanderMembershipKernels`:
> items 1–2 (`Membership`, `membership`, `membershipCount`, and the
> count-agreement `membershipFiber_iff`), item 3 (`localLift` +
> `localLift_preserves_membership`), and item 4 (`membershipLift` +
> `apply_mass_eq_sum` + the F2c-iv-b capstone
> `membershipLift_localLift_eq_fiberLaw`) are all proved. The F2 disintegration
> layer is done.
>
**New preferred intervention (Nov 11):** Model `localLift` as the already
proved generic `FiberDisintegration.fiberLaw membership membership_surjective`.
Its mass law and recovery theorem eliminate the blocked `Finsupp.mapDomain`
pushforward proof. Use the existing `leftCardsFin`/`decksWithLeft` cardinality
bridge from `CommanderFiberMembership.fiberFin_card`; details and proof order
are in [`f2_fiberlaw_unblock.md`](f2_fiberlaw_unblock.md). This is a proposed
route, not a theorem already in the tree.

> **COMPLETE (F2c-iv-b, the capstone, Nov 12):** the two-layer equality
> `membershipLift.comp localLift = FiberDisintegration.fiberLaw project
> project_surjective` is **proved** (commit `19d417c`), in the full
> *kernel* form — not just the point-mass form. With this, **all of F2 is
> complete**.
>
> *How the wall actually broke (revising the Nov 12 difficulty note):* the
> recursion was **not** a fundamental normalisation wall. It was the **default
> `simp` set** (and `field_simp`, which uses it) unfolding `membership` / `leftCards`
> (which depend on `d : Equiv.Perm (Fin 99)`). Once the proof is written with
> `simp only` over an *explicit* lemma list (never the default set),
> `if_pos`/`if_neg`-style `ite` reductions (`ite_eq_left`/`ite_eq_right`), and
> `by_cases` on the `Membership`/`Nat` equalities, none of the `Rat`/`Finset`
> arithmetic recurses. The kernel-level lift is then just
> `StdSimplex.weights_inj` + `Finsupp.ext` (both confirmed non-recursing over
> `Finsupp Deck`), applied to the point-mass equality.
>
> The earlier "point-mass is the deliverable / kernel form is blocked" framing
> in this file and in [`f2c_ivb_sum_collapse.md`](f2c_ivb_sum_collapse.md) is
> **superseded**: the kernel-equality form is proved. That difficulty note is
> kept as a record of the diagnosis but no longer reflects the open work.

### F3. Prove the 25-position physical-exchange membership law

> **Route change (2026-11-15 pivot):** the route to item 3 (A3) is now the
> **G1–G4 generic finite-deck theory** (see `docs/agent_handoff.md`,
> 2026-11-15 pivot + 44th-session note), from which the 99-card A3 kernel
> equality is a specialization at `(99,50,50,25)`. The 99-only A3 counting
> (`commanderExchange25_countMass`) is documented below but parked pending the
> generic route; it is not the next action. The 25th-session machinery
> (`map_equiv_mass`, `distUniform_ofInvariantTransitive`,
> `membershipFiber_card`, `membershipLift_count`, `commanderCountFiber_card`)
> remains committed and usable.

> **Progress (F3, 2026-11-12):** In `Shufflemath/CommanderPhysicalExchange`:
> **(item 1, done)** the post-exchange left-pile membership `newLeftCards d L R`
> and the macro-count transition `newLeftOriginalCount_eq`.
> **(item 2, done, commits `b25d5f4`)** the deck-level `rawExchange : FiniteKernel
> Deck Deck` kernel, built as the composition of the membership-level exchange law
> `rawExchangeMembership` (pushforward of a uniform 25+25 `(L,R)` choice to its
> post-exchange membership `newLeftCards d L R`) and the uniform membership-fiber
> lift `localLift`; with the push-through lemma
> `rawExchange_membership_pushforward` (`comp rawExchange (deterministic membership)
> = rawExchangeMembership`).
> **(item 3a, done, commit `958d5f5`)** the structural reduction
> `hMembershipExchange_lhs_reduces`: the `hMembershipExchange` premise's left-hand
> side equals `comp (fiberLaw project) rawExchangeMembership` (via `comp_assoc` +
> the F2 capstone + the push-through). So the core law is
> `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25 membershipLift`.
>
> **(item 3 core, OPEN — the hard counting identity):** prove
> `comp (FiberDisintegration.fiberLaw project project_surjective) rawExchangeMembership
> = comp commanderExchange25 membershipLift`. Both sides are
> `FiniteKernel CommanderState Membership`. Mass-at-`m` (from input `x`) reduces to the
> exact counting identity
> `|{ (d,(L,R)) : project d = x, newLeftCards d L R = m }| / (|fiber project x| * choose 50 25 * choose 49 25)
>  = transitionWeight 99 50 25 (count x) (count m) / |{m' : count m' = count m}|`.
> This has two parts: (i) the new-count distribution of the physical exchange equals
> the Bernoulli--Laplace `transitionWeight` hypergeometric sum, and (ii) *given* the new
> count, the new membership is *uniform* over that count's fiber (a symmetry/group-action
> statement). Part (ii) is the harder half. This is on the critical path for item 4 and
> F4.5.
> **4th-session reduction (2026-11-12):** the underlying counting identity
> `overlap_count (n m r k) x y = transitionNumerator (n m r k) y x` now reduces to a
> single new **fiber-counting lemma (CL)** —
> `fiberSum p x y = choose(r, y) * choose(N - r, m - y) * overlap_count (N m r k) x y`
> — plus the already-proved `fiberSum_swap` and `fiberSum_eq` (the stationary `choose`
> factors cancel by pure algebra). **CL is verified on all three small decks**
> (`ExchangeOverlap.fiberCounting_{6321,7442,8431}`); the single remaining piece is the
> general (symbolic) proof of CL (reindex the 7-way `fiberSum` sum to the `(S, T)`
> double count). See `docs/qwen_unblock_nov12.md` §3.
> **6th-session progress (2026-11-14, `d55b69d`):** the **S1-side** of the CL is
> proven symbolically: `s1Fiber_choose` gives `|s1Fiber x t T1| =
> choose |T1| t * choose (|stars|-|T1|) (x-t)` for any `ExchangeAdmissible`, via
> `s1Fiber_biUnion` + `fiberA_card` (dependent `Finset.card_bij`) + `s1Fiber_card`
> (`card_biUnion` + sum-of-constant). This is the marked-side half of the 4-bin
> count for a *fixed* `T`; the remaining assembly is the mirrored plain/target
> (S2) side and the `choose(r,y)*choose(N-r,m-y)` target-choice factor, then
> `fiberSum_swap`/`fiberSum_eq` to close the full `fiberSum` identity.
> **7th-session progress (2026-11-14, `6ae278f`/`08a864b`/`19892fa`):** (a) the
> parameter-free **`Shufflemath.FinsetFiberCount`** module was extracted from
> `ExchangeOverlap.lean` (`sFiber`/`sFiberA`/`sFiber_biUnion`/`sFiberA_card`/
> `sFiber_card`/`sFiber_choose`, only `[DecidableEq α]` needed), so the marked
> and plain sides both instantiate one general lemma.  (b) Since `fiberSum_eq`
> and `fiberSum_swap` are already proven, the general CL was **sharply reduced
> to a single pure-`Nat`/`choose` identity** `transitionNumerator (N m r k) y x
> = overlap_count (N m r k) x y` (only `native_decide` small-deck versions exist
> today).  The `ExchangeOverlap.lean` section comment records the concrete
> reindexing `t = y - a` under which the four transition factors match the four
> overlap factors (two by `Nat.choose` symmetry), and characterizes the one
> remaining difficulty as the **boundary** (`if`-guards / `Nat`-saturated
> `y - a` vs `chooseSigned = 0` out of range) — a pure reindexing with no
> `Finset` API.
> **8th-session progress (2026-11-14, `0811eb6`):** the target was corrected
> to a **sum** identity (the pointwise `g(a) = h(y-a)` is *false* for `a > y`,
> where Nat-saturating `t := y-a` to `0` makes `h(0)` potentially nonzero
> while `g(a)=0`). The precise statement is
> `transitionNumerator (N m r k) y x = overlap_count (N m r k) x y` as a
> finite-sum equality; the `ExchangeOverlap.lean` comment records the exact
> factor structures of both sums and the exact common support
> `[max (0, y-k), min y (m-k)]` under `t := y-a`. This is a
> **generalized Vandermonde / hypergeometric convolution** between the two
> 4-factor decompositions (no Mathlib Vandermonde lemma exists; it must be
> proven from scratch — a combinatorial double-counting or an iterated
> Vandermonde manipulation). The S1-side counting (`FinsetFiberCount`) is
> complete; the remaining step is this one hypergeometric sum identity.
> **11th-session progress (2026-11-15, `2f93a91`/`135968c`/`b95f389`):** all
> **four** summand factor matches are now proven — `F1match`/`F2match` (9th),
> `F3match` (10th), and **`F4match`** (this session, via the new
> `intSub_eqCast`/`intSubSubAdd_eqCast` `Int`-no-saturation bridges) — plus the
> **summand assembly `tterm_eq_oterm`** (`tterm (N m r k) x y a = oterm (N m r k)
> x y (y-a)` in the admissible regime, by `rw [F1match, F2match, F3match,
> F4match]` + one `omega` base identity + `ring`) and the **definitional
> decomposition `transitionNumerator_eq_sum_tterm`** (the transition is the sum
> of `tterm` over `a ∈ [0,k]`, by `rfl`).  Combined with
> `overlap_eq_sum_oterm` (overlap = sum of `oterm` over `t ∈ [0,m-k]`), the
> general CL is reduced to the **final step: the `t = y-a` `Finset` sum
> reindexing** between the `a`-sum and the `t`-sum, aligning the supports on
> `[max (0, y-k), min y (m-k)]` where `oterm = 0` outside.  No `Finset`-API
> 2-bin products are involved.  Then (item 4) the 2-exchange TV follows from the
> CL + `fiberSum_eq`.
> **12th-session — COMPLETE (2026-11-15, `tterm_eq_oterm_all` / `oterm_sum_clip_eq`
> / `generalCL` commits):** the general CL is **proven symbolically**.
> `tterm_eq_oterm_all` gives the pointwise all-`a` equality `tterm (N m r k) x y a
> = oterm (N m r k) x y (y-a)` (three cases: both guards hold → `tterm_eq_oterm`;
> the F4 guard fails / the F2 guard fails → the corresponding `oterm` factor has a
> negative index and the product is `0`, via `chooseSigned_zero_neg` + the
> single-cast `let t := y-a` representation trick).  `transition_eq_sum_oterm_ySuba`
> reindexes the `a`-sum over `[0,k]` to the `t`-sum over `[y-k,y]` (`a ↦ y-a` is a
> bijection for `k ≤ y`, via `Finset.sum_image` + `rangeImage_ySuba_eq_Icc`).
> `oterm_sum_clip_eq` then clips *both* the transition and overlap `oterm`-sums to
> the common range `[y-k, min (y, m-k)]` (oterm is `0` outside, via
> `oterm_zero_below`/`above_mk`/`above_y` — the F3 factor `choose (m-y) (m-k-t)` and
> the F1 factor `choose y t` are off-range), so they are equal.  **`generalCL`**
> assembles these into `transitionNumerator N m r k y x = overlap_count N m r k x y`
> for the admissible regime (`k ≤ y ≤ m`, `y ≤ r`, `m+r ≤ N`, `r-y ≤ N-m`).  Also
> proved: **`fiberSum_eq_overlap`** — the fiber-level CL
> `fiberSum p x y = choose r y * choose (N-r) (m-y) * overlap_count (N m r k) x y`
> (compose `fiberSum_swap` + `fiberSum_eq` + `generalCL`).
>
> **m + r > N regime — RESOLVED this session.**  The 4th-factor base subtlety
> (`N - m - r + y` (left-saturated `Nat`) = `y` vs `(N-m) - (r-y)` = `y - 1` for
> the Commander) is fixed by using the **non-saturating** base `(N-m) - (r-y) =
> (N-r) - (m-y)` (equal, both = `N-m-r+y` as an `Int`, nonnegative for
> `y ≥ blLo = max (r-(N-m)) 0`).  The chain `baseInt_eqNatCast` → `F4match_ns` →
> `tterm_eq_oterm_ns` → `tterm_eq_oterm_all_ns` → `transition_eq_sum_oterm_ySuba_ns`
> → **`generalCL_ns`** proves the counting identity **without** `m + r ≤ N`, and
> **`generalCL_cmdr_2525`** proves the 25-25 Commander transition **symbolically**
> (no `native_decide`).  Together with `generalCL` (`m + r ≤ N`: 6321, 8431) the
> counting identity `transitionNumerator N m r k y x = overlap_count N m r k x y`
> now holds for **every valid deck**, including the Commander (99 50 50 25) and
> 7442.  **The F3 item 3 counting core is COMPLETE in both regimes.**
> **(item 4 / item 3 core — part (ii) COMPLETE, commit `43f845f`):** the
> member-level uniformity (part (ii)) is now proved: `membershipFiber_transitive`
> shows any two same-count memberships are related by a deck bijection `orbitMap`
> preserving the left pile and carrying `m.1` onto `m'.1`.  The counting (part (i))
> was already done, so the remaining half of the kernel equality
> `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
> membershipLift` is **part (ii): given the new count `m`, the new membership is
> uniform over `{μ : membershipCount μ = m}`** — a symmetry/group-action statement
> (the physical-exchange law, averaged over the uniform `project`-fiber, treats all
> same-count memberships equally).  This is the "harder half" per the original
> F3 note; it is a member-level uniformity, distinct from the count-level CL.
> **16th-session progress (groundwork):** `Shufflemath/CommanderMembershipOrbits.lean`
> proves the well-typed range `1 ≤ membershipCount m ≤ 50` for every membership
> (`membershipCount_pos` + `membershipCount_le_50`), plus the `leftOrigSet`/
> `rightOrigSet` disjoint-cover identities the orbit construction (Spec A1) needs.
> **17th–18th-session progress (orbit primitive):** the building block
> `equiCardFinsets_bij` (`{x//x∈s} ≃ {x//x∈t}` when `#s = #t`, via
> `Fintype.card_ofFinset` + `Fintype.equivFinOfCardEq`) is committed. The core
> lemma `finsetType_perm` (a `s ≃ s` sending `A ↦ A'` and `s \ A ↦ s \ A'`, for
> `#A = #A'`) is **~90% built**: the **injective half is complete** (all four
> cases: same-piece via `Subtype.ext` + `eAB/eCD.injective`; cross-piece via the
> `A' ∩ (univ \ A') = ∅` disjointness contradiction), and the **surjective half
> has three tiny mechanical walls** documented with one-line fixes
> (`docs/agent_handoff.md`, 18th-session section: final `rfl` blocked by a `have`
> abbreviation; a `rw`-at-hypothesis motive; `rename_i` grabbing a `DecidableEq`
> typeclass). Once `finsetType_perm` closes, `membershipFiber_transitive` (two
> calls on the left/right pieces, agreeing on the disjoint cover `leftOrigSet ⊎
> rightOrigSet = univ`) is bookkeeping, and Specs A2/A3 follow.
> **21st–22nd-session progress (COMPLETE):** `finsetType_perm` is **COMPLETE**
> (commit `a637cee`); the constructive witness `orbitMap : Fin 99 → Fin 99` is
> **built** (commit `55c07b5`): four `equiCardFinsets_bij` piece-equivs
> (`orbitEquivA/B/C/D`) composed piecewise over the four-part partition (marked /
> unmarked × left/right pile), on top of the equi-card lemmas
> (`partCard_eqA/B/C/D`), pile-cover lemmas (`leftCoverPieces`/`rightCoverPieces`),
> and the apply-lemmas (`orbitMap_apply_partA/B/C/D`). The three conjuncts are all
> now proved: the `⊆` image directions (`orbitMap_preservesLeft`,
> `orbitMap_mapsM1`), the `⊇` image directions (`left_subset_fimageLeft`,
> `right_subset_fimageRight`, `m1p_subset_fimageM1`), surjectivity
> (`orbitMap_surjective`), and — the hard piece — **injectivity**
> (`orbitMap_injective`, via the 4 image lemmas, the 12 pairwise-disjointness
> lemmas, and the 4 preimage lemmas `orbitMap_preimagePartX`: equal images force the
> two sources into the same piece, and the piece-equiv is injective). The image
> equalities `orbitMap_imageLeft`/`orbitMap_imageM1` and the capstone
> `membershipFiber_transitive` close it (commit `43f845f`).
> **Gate (F3-a): the combinatorial/orbit ingredients of F3 item 3 are complete**
> (the symbolic counting part (i) core in `generalCL`/`fiberSum_eq_overlap` and
> the member-uniformity part (ii) orbit/transitivity `membershipFiber_transitive`),
> and `newLeftCards_conjugate` (below) gives the equivariance they need.
> **Gate (F3-b) is still open:** the *concrete* membership-kernel equality (A3)
> `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
> membershipLift` has not been proved; it must be assembled from these
> ingredients (part (i) count-total + part (ii) within-count uniformity) and then
> discharged in the physical-perfect corollary.  See
> `docs/planning/reviews/2026-11-15-qwen-proof-engineering-review.md` (R1) for the
> two-gate distinction.
> **47b/47c-session progress (A3 RHS, both forms):** `commanderExchange25_mass`
> (the `commanderExchange25` transition bridge), `hMembershipExchange_rhs_mass`
> (the pointwise mass of `comp commanderExchange25 membershipLift`, commit
> `c276eda`), and `commanderExchange25_countMass` (the count-level companion: the
> mass at `(x, c)` of `comp commanderExchange25 (det commanderLeftCount)` is
> `transitionWeight 99 50 25 (count x) c` for feasible `c`, commit `a7fabd3`) are
> in `Shufflemath/CommanderMembershipExchange.lean` — the *RHS* half of (A3) is
> now pointwise established in both the membership and count formulations.
> Next: the LHS counting core `rawExchangeMembership_count` (part (i)).
> **47d-session progress (Route B unblocker):** the GPT-6 route's `exchangePair_exists`
> (the Nov-12 5-conjunct `isExchangePair` wall) is now **committed** in
> `Shufflemath/FinsetCombinatorics.lean` (commit `9b693f3`), together with the two
> pure set-identities `sdiff_sdiff_inter` (`S \ (S \ T) = S ∩ T`) and
> `sdiff_sdiff_union_eq` (`(S \ (S \ T)) ∪ (T \ S) = T`, the 5th conjunct). The
> canonical pair `(S \ T, T \ S)` is a valid 25/25 exchange `S → T` when
> `|S| = |T| = 50` and `|S∩T| = 25`. Next on Route B: the membership-level mass
> identity via `BernoulliLaplaceFiber.lean`'s `detailedBalance` + the
> `BernoulliLaplaceCommanderBridge` (gives the point mass `= transitionWeight/F(y)`
> and, as a consequence, within-count uniformity — bypassing part (ii)).
> **47e-session progress (A3 ingredient — reversibility):** `commanderDetailedBalance`
> is **committed** (`BernoulliLaplaceCommanderBridge.lean`, commit `e84fe7e`): the
> Commander `commanderStationary` + `commanderExchange25` satisfy detailed balance
> (`π(i) W(i,j) = π(j) W(j,i)`), a two-line transport of the general
> `blDetailedBalance` across the two bridge theorems. This is one of the two A3
> ingredients (the macro-kernel reversibility); the other is the stationary
> count distribution (`commanderStationary_matches_blStationary` already committed).
> **47e (hypergeometric invariance):** `commanderStationary_is_stationary` +
> `commanderStationaryRun` committed (`f7976d2`, same file) — the third macro-kernel
> A3 ingredient (fixed-point under the kernel).
> **47g-session progress (25-overlap preservation):** in
> `Shufflemath/CommanderPhysicalExchange.lean` (commit `9b5a45a`):
> `leftCards_disjoint_rightImage` (the original left pile is disjoint from the
> selected-right-card part of `newLeftCards`), `newLeftCards_inter_leftCards` (the
> post-exchange left pile intersects the original exactly in the unselected 25
> left cards), and `newMembership_overlap_25` (for a valid 25/25 exchange, the
> original and post-exchange left piles share exactly 25 cards — the `|S ∩ T| = 25`
> fiber that the mass-identity steps are indexed by). Proven by a light `rw`
> (distributivity + the disjointness helper + subset); a `Finset.ext`/`mem_union`
> case analysis hit the 200000-heartbeat `whnf` timeout — avoid that shape.
> **NEXT (the genuinely hard half):** the *physical* membership-level mass identity
> — `rawExchangeMembership : FiniteKernel Deck Membership` has point mass
> `1/(choose(50,25)·choose(49,25))` on the `|S∩T|=25` fiber, then `=
> transitionWeight/F(y)` via the fiber `detailedBalance` + bridge — building toward
> the `hMembershipExchange` capstone. Start with the **count-transition LHS**
> `comp (comp (fiberLaw project) rawExchangeMembership) (det membershipCount) =
> comp commanderExchange25 (det commanderLeftCount)` (RHS =
> `commanderExchange25_countMass`): a multi-lemma development, more tractable than
> the full membership-level mass because it only tracks `membershipCount`.
> `CommanderState = Fin 50` (a *count*) is
> distinct from the physical `Membership = {S : Finset (Fin 99) // S.card=50}`.
> Full step-by-step spec: `docs/agent_handoff.md` → "NEXT ACTION — F3 item 3".
> **47h-session progress (step 2 "unique half" building blocks):** in
> `Shufflemath/CommanderPhysicalExchange.lean` (commit `45dd4b7`, additive after
> `newMembership_overlap_25`): `image_injective_eq` (injective `f` ⇒ equal images ⇒
> equal sets — the general recovery engine), `newLeftCards_leftPart` (the
> left-position part of the post-exchange pile `= newLeftCards d L R ∩ leftCards d`),
> `newLeftCards_rightPart` (the selected-right part `= newLeftCards d L R ∩
> (R.image fR)`, a light RHS), and `newLeftCards_injective_L` (a fixed deck's `L` is
> recovered from the post-exchange pile: equal piles ⇒ equal `L`); **`cbc61e8`** —
> `leftCards_disjoint_rightCards` (a deck's left-position and right-position cards are
> disjoint — the key fact the `R`-recovery was blocked on); **`a5abd2b`** —
> `leftImg_disjoint_rightFull` (the unselected-left part is disjoint from the deck's
> full right-position set); **`1c7b46e`** — **`newLeftCards_injective`** (the capstone:
> the full `(L,R)↦T` **injectivity** — equal post-exchange left piles force equal `L`
> and equal `R`), completing the unique half of the deck-level bijection (F3 item 3,
> step 2). Next: step 1 (deck-independence), then step 3 (point mass) — see
> `docs/agent_handoff.md`.
> **53rd-session progress (A3 part (i) normalization, general + concrete, `e0b6ebe` +
> `0bf218a`):**
> `Shufflemath/CommanderA3UniformPushforward.lean` proves
> **`uniformPushforward_pointMass`** — for a finite nonempty `X` and any
> `f : X → Y`, `Dist.mass ((GSR.uniformDist X).map f) y = (1/card X) · #{j : f j = y}`
> — the A3 part (i) normalization in *fully general* form, plus the pure-`Finset`
> helper **`sumConstIte`**. The route *sidesteps the 52nd-session `.map`-on-`Dist` /
> `Finsupp.mapDomain` rabbit hole entirely*: pushforward `= apply U (deterministic f)`
> (`apply_deterministic_eq_map`) → `apply_mass` opens the `Fintype` sum → each summand
> is `GSR.mass_uniformDist j` **as a term** (not `rw`/`simp` — re-unfolding
> `GSR.uniformDist`'s total-mass proof was the earlier heartbeat blocker) times the
> deterministic point mass (`Dist.mass_pointMass`), directional `ite`s reconciled by
> `if_congr`, sum collapsed by `mul_sum` + `Finset.sum_boole`. Then
> **`Shufflemath/CommanderA3ExchangePushforward.lean`** applies it to the concrete
> exchange: **`rawExchangeMembership_pointMass`** — `Dist.mass (rawExchangeMembership d)
> m = (1/#exchangeChoice) · #{j : exchangeChoice | newMembership d j.1.1 (leftCard25
> j.1.2) j.2.1 (rightCard25 j.2.2) = m}` (via `dsimp [rawExchangeMembership]; apply
> uniformPushforward_pointMass`). **Next:** the fiber-sum double-count
> `Σ_{m : count m = c} #{j : F j = m} = #{j : count (F j) = c}` — use the **fiber-product
> equiv** (NOT `biUnion`/`sum_ite`; see `.pi-glla/53_fiberSum_wip.lean`) — then the
> `exchangeChoice ≃ leftChoices ×ˢ rightChoices` equiv + `newLeftCount_eq_transitionNumerator`
> + `exchangeChoice_card_eq_transitionDenominator` bridges give
> `rawExchange_membershipCount_mass` (see `docs/agent_handoff.md`).
> **51st-session progress (A3 `hTrans` bridge, part (ii) constancy, part (i)
> normalization + count connection):** in
> `Shufflemath/CommanderMembershipExchange.lean`, four `hMembershipExchange` inputs
> are proved. **`membershipFiber_transitive_asEquiv`
> (`de1d4b0`)** is the `hTrans` bridge — it wraps the bare bijection `f : Fin 99 → Fin 99`
> from `membershipFiber_transitive` as a `Deck` (`Equiv.ofBijective`) so the orbit map is
> exactly `relabelMembership_equiv (g) g.bijective`, the `E`-form equiv
> `distUniform_ofInvariantTransitive` needs; its `.val`-field equality is a `Finset.ext`
> iff bridged to the Set image equality via a direction-controlled `rw` chain
> (`← Finset.mem_coe` / `← hSet` / `← Finset.coe_image` / `Finset.mem_coe`) — solving the
> 48th/49th-session Finset/Set-coercion wall. **`mu_x_constant_on_countFiber`
> (`0259ab2`)** is the part (ii) core — `μ_x` is constant on each membership-count fiber
> (invariance + transitivity ⇒ equal mass on the orbit = the fiber). **
> `exchangeChoice_card_eq_transitionDenominator` (`a82673b`)** is the part (i)
> normalization — `#exchangeChoice = choose 50 25 * choose 49 25 = transitionDenominator
> 99 50 25`. **`membershipCount_newMembership` (`1be4918`)** is the part (i) count
> connection — `membershipCount (newMembership d L R …) =
> (newLeftCards d L R ∩ leftOrigSet).card` (`dsimp [membershipCount, newMembership]`).
> **Next: the part (i) inner-sum** `rawExchange_membershipCount_mass` (total mass of
> the raw exchange into the `c`-fiber = `transitionNumerator (count x) c /
> transitionDenominator 99 50 25`) — all counting inputs are now in the library; only
> the Finsupp/measure bookkeeping remains (WIP skeleton `.pi-glla/52_innerSum_wip.lean`; avoid
> `.map`-on-`Dist`, compute the fiber-sum as a `Finset.sum` over `exchangeChoice`). Then
> the fiber-average collapse to `rawExchangeMembership_count`, then combine with part (ii)
> to discharge `hMembershipExchange` (see `docs/agent_handoff.md`).
> **56th-session finding (the part-(i) bridge is a hard wall):** every route that
> transports the `exchangeChoice` **Fintype** count to the 47v-kernel **×ˢ-filter
> Finset** card recurses — (i) `exact Finset.mem_product.mpr`, (ii) a direct Fintype
> fiber-card, and (iii) the explicit identity `Equiv` the 55a note proposed (both
> `mem_product.mpr` and `.mp` hit max-recursion).  Root cause is a Fintype↔Finset
> asymmetry: `exchangeChoice`'s subtypes sit over `powersetCard` (~10^14 elements), so
> any fiber-card or membership proof over it unfolds the powersetCard and recurses, while
> the 47v kernel only works because it stays at the relational Finset-card/sum level
> (`pairCountByConstSub` over generic finsets) and never proves a specific membership.  The
> A3 target LHS is a Fintype-card (its support is `exchangeChoice`), so the transport
> needs the recursive membership.  **Landed this session (wall-free):** the pointwise
> `count_exchangeChoice_eq_markedCount` (the step-iii count connection, committed in
> `CommanderMembershipExchange`).  **Next (see `docs/planning/proof-strategies/55a_a3mass_wip.lean`)**:
> either re-prove the 47v fiber-sum directly over the `exchangeChoice` Fintype (route A —
> first probe whether a `Fintype.card_biUnion` over powersetCard-filtered fibers recurses),
> or pivot to the A3 discharge via the *generic* T4 theorem `uniformFiber_intertwines`
> (`19d964d`), which may yield a hypothesis-free 2-exchange theorem without the concrete
> `hMembershipExchange` capstone.
> **50th-session progress (A3 within-count invariance, `67a4efc`):** in
> `Shufflemath/CommanderMembershipExchange.lean`, four building blocks assembling the
> *within-count* invariance the A3 capstone needs from `distUniform_ofInvariantTransitive`
> (part (ii) — the stabilizer side of the orbit-stabilizer uniformity argument): `deckRelabel`
> (the deck relabeling `d ↦ d.trans g` as an `Equiv Deck Deck`, proved injective/surjective via
> `Equiv.ext` + `g.injective`/`g.apply_symm_apply`), `h6_fiberLaw_fixed` (a uniform `project` fiber
> law is fixed by the *deterministic* deck-relabeling kernel — a two-line `apply_deterministic_eq_map`
> + `fiberLaw_invariant_underFiberEquiv` + `project_conjugate` transport), `comp_L_detM_eq_comp_detE_L`
> (kernel-composition equivariance `comp L (det M) = comp (det E) L`, both sides reducing to
> `rawExchangeMembership (d.trans g)`), and `mu_x_map_invariance` — the 7-step kernel-monad calc
> (`apply_deterministic_eq_map` unit → `apply_comp` associativity → the comp-equivariance →
> `h6_fiberLaw_fixed` → back) showing the post-exchange membership law at fiber `x` is fixed by the
> `leftOrigSet`-preserving deck relabeling `g`. This is the within-count invariance input; the LHS
> group-uniformity (part (i)) and the LHS=RHS equality (part (iii)) still stand.
> **23rd–24th-session progress (Spec A2 core + A3 scaffold):**
> `newLeftCards_conjugate` (`CommanderPhysicalExchange.lean`, commit `6ccae33`)
> proves the **pointwise** equivariance of the post-exchange left set under any
> deck relabeling `f`: `newLeftCards (d.trans f) L R = (newLeftCards d L R).image
> f` (via `leftOrigSet_image` + `Equiv.trans_apply`) — the distributional-invariance
> building block for part (ii).  (A 23rd-session Python-splice truncation lost the
> file once; restored from `958d5f5` and re-merged, `dd221fd` — see the splice-safety
> warning in `docs/agent_handoff.md`.)  The **A3 target module**
> `Shufflemath/CommanderMembershipExchange` (commit `74f5dab`) scaffolds the kernel
> equality `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
> membershipLift` with its two-stage proof plan.
> **(item 4 / Spec C — remaining):** (A3) prove that equality.  It splits into (i)
> **counting** (the fiber-average post-exchange `membershipCount` = the
> `commanderExchange25` transition — the counting core is DONE in
> `generalCL`/`fiberSum_eq_overlap`; the fiber average over *decks* needs a
> deck-level orbit/transitivity argument) and (ii) **within-count uniformity**
> (given the count, the membership is uniform over its fiber), which follows from
> **`newLeftCards_conjugate`** (equivariance) + **`membershipFiber_transitive`
> (transitivity)**.  Then F3 item 4 (the 2-exchange TV theorem
> `two_physical_perfect_exchanges_uniform_of_counts`) instantiates with this proved
> `hMembershipExchange`.  F4.2 item 4 (Dobrushin contraction / `Equiv.Perm (Fin
> 99)` lift) and F5 remain downstream; do not re-attempt the `List.mem_bind`/
> `toMultiset` sub-wall.

**Dependency:** F2 (satisfied: `membershipLift_localLift_eq_fiberLaw`, commit `19d417c`).

1. Specify the raw operation exactly: choose 25 distinct positions from each
   pile uniformly; swap the selected positions in a fixed bijective pairing.
   Randomness is in the chosen subsets, not an unspecified human procedure.
2. Implement `rawExchange : FiniteKernel Deck Deck` and verify the
   corresponding transition on named-card membership after a fiber-uniform
   input. Use counting/symmetry rather than enumerating permutations.
3. Discharge the `hMembershipExchange` premise of
   `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_of_counts`
   through `PhysicalExchangeReduction.intertwining_of_membership_exchange`.
4. Combine with F1 to state the **unconditional physical-perfect-local**
   2-exchange TV theorem. The 3-exchange variant can follow the generic
   run/intertwining theorem; do not duplicate a giant kernel calculation.

**Acceptance:** no new abstract exchange hypothesis at the final exported
Commander theorem; exact small-deck checks in
`experiments/full_deck_oracle.py` and
`experiments/commander_fiber_witness.py` continue passing.
Do **not** try to prove pointwise equality of raw physical and canonical
oracle kernels: it is false in the documented 5-card example.

### F4. Quantify finite-GSR versus physical-perfect-local error

**Dependency:** F2 and F3 for the full 99-card statement; the standalone GSR
algebra can advance in parallel.

1. Extend `GSR.idealShuffle_comp`'s product-label theorem to the numeric
   uniform `Fin (a*b)` label alphabet via an explicit encoding and proof
   of pushed-forward uniformity. The present theorem is not this result.

   *Progress (clean dedicated pass):* the single-label core is done in
   `GSR.lean`: `encodeLabel`/`decodeLabel` give the lexicographic split of a
   `Fin (a*b)` label into a `Fin b` major and `Fin a` minor (a bijection,
   `encodeLabel_decodeLabel`/`decodeLabel_encodeLabel`); `combineLabels`/
   `splitLabels` lift this per-card to label arrays and assemble the
   `labelReparam` `Equiv`; `map_bijective_uniformDist` (a bijection carries
   the uniform law to the uniform law on the target) plus
   `productLabels_pushforward_uniform` prove the `(a*b)`-alphabet GSR label
   law equals the pushforward of the independent product of a `b`- and an
   `a`-alphabet law. The mixed-radix arithmetic is in place:
   `mixedRadix_unique` (`x*a + y = j*a + i`, with `y < a`, `i < a`, forces
   `x = j ∧ y = i`, proved via `Nat.add_mod`/`Nat.mod_eq_of_lt`/`Nat.mul_mod_right`/
   `Nat.add_right_inj`/`Nat.mul_left_cancel`) and `combinedLabel_pred`
   (per-card: `major c * a + minor c = j*a + i ↔ major c = j ∧ minor c = i`).
   *Remaining:* the **kernel equality**
   `productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b)` — a
   joint-distribution bridge (the sorting-compatibility lemma is now DONE:
   `stableBuckets_combine_eq_lex` + the per-card `Bool`/`==`/`&&` bridge
   `combineVal_filter_eq`). **DONE:** the kernel equality
   `productLabelShuffle_uniform_eq_ideal` is proved (`GSR.lean`, `17ffab6`)
   via the joint-distribution bridge (iterated uniform `apply` = uniform
   product law, `apply_uniform_uniform_eq_product`) + the `labelReparam`
   pushforward + `stableBuckets_combine_eq_lex`. The bridge and
   `map_uniform_mass` were relaxed (codomain needs only `DecidableEq`, not
   `Fintype`, via `Finite.lean`'s `apply_mass_dom`) so they apply at the
   deck level (`α = List (Fin n)`). **F4.1 is complete.**
2. Define a permutation-preserving local-GSR kernel for the ordered cards in
   each *fixed* pile. Prove it cannot change the membership state.

   *Progress:* `CommanderLocalGSR.lean` defines the within-pile relabeling
   `pileRelabelFn pl pr` (a left position `leftPosition i` goes to
   `leftPosition (pl i)`, a right position `rightPosition j` to
   `rightPosition (pr j)`; it never moves a card between piles), with
   `pileRelabelFn_left`/`pileRelabelFn_right`. The central F4.2 fact
   `permutedLeftCards_eq` proves the left-card set of the permuted deck equals
   `leftCards d` (reindexing the 50 left positions by a bijection leaves the
   image of `univ` unchanged, `univImage_reindex`), i.e. a local shuffle
   **cannot change the membership state**. The bijection is now DONE via
   `pileRelabelEquiv` (`Fin.sumFinEquiv` + `Equiv.sumCongr` + `Equiv.trans`,
   building the `Fin 99 ≃ Fin 99` by construction) and `reorderedDeck` /
   `reorderedDeck_leftCards`. *Progress (5th session, `4e1b76f`):* **`gsrProductKernel (nL nR a b)`**
   (`CommanderLocalGSR.lean`) is now in the library — it applies the F4.1
   `GSR.idealShuffle` independently to the left and right piles (a
   `FiniteKernel` on the pile-list product), and **`gsrLocal_preserves_pile`**
   proves a within-pile GSR output holds exactly the pile's original cards
   (via `stableBuckets_set`), i.e. a local GSR cannot change the membership
   state. *Remaining:* lift the pile-list kernel to the full `Deck`
   (`Equiv.Perm (Fin 99)`) — the distributional multiset/permutation fact
   (output is a genuine rearrangement, not merely set-equal) is the sub-wall
   (`List.mem_bind`/`length_filter`/`toMultiset` absent in this build).
   *Progress (19th session, `0b7460a`/`f097fec`):* new `Shufflemath/CommanderDeckGSR.lean`
   establishes the Fintype-free **structural identification** the deck-level lift
   rests on: a *membership-preserving* deck permutation (one that sends the 50 left
   positions to left cards and the 49 right positions to right cards, i.e.
   `preservesPiles σ`) is **exactly** a within-pile relabeling.  Proven:
   `pileRelabelEquiv_pairInjective` (a within-pile pair is recovered from its `Deck`
   action by reading the left/right components on the position maps),
   `pileRelabelEquiv_image` (any `preservesPiles` `σ` equals `pileRelabelEquiv` of
   its components, via `leftPermOf`/`rightPermOf` + `Equiv.ofBijective` +
   `Finite.surjective_of_injective`), and the capstone
   `preservesPiles_iff_pileRelabel : preservesPiles σ ↔ ∃ p, pileRelabelEquiv p.1 p.2 = σ`.
   Together `pileRelabelEquiv` is a bijection `Equiv.Perm (Fin 50) ×
   Equiv.Perm (Fin 49) ≃ {σ : Deck // preservesPiles σ}` — the deck-level GSR
   support, built without `List.mem_bind`/`toMultiset`.
   *Progress (F4.2 last-wall, this session):* new **`Shufflemath/GSRF42.lean`**
   resolves the *sorted-key rank* half of the last wall — turning
   `GSR.idealShuffle`'s output (ordered by the lex `(label, position)` key) into a
   **genuine finite permutation** of the deck positions.  The blocker was that this
   Mathlib has no `DecidableRel` for the lexicographic `<` on a product type, so
   the rank cannot be defined by `Finset.filter` on the lex order directly; the fix
   **flattens the lex key to one `Nat`**: `keyNat i = (ℓ i).val * n + i.val`, whose
   `<` is exactly the lex order (proved as `keyNat_lex`, the algebraic core) and is
   decidable.  Established: `keyNat_injective` (equal keys force equal indices,
   via mod-

 `n` uniqueness), `rankVal` (rank = size of the below-set) with
   `rankVal_rankEquivSymm`, and the capstone ingredients **`rankEquiv : Equiv
   (Fin n) (Fin n)`** (a real permutation, via `Equiv.ofBijective` +
   `Finite.surjective_of_injective`), `rankEquiv_symm_apply` (symm recovers the
   rank-ordered deck), `rankEquiv_eq_orderByNewPosition` (the only remaining list
   equality), `rankOrderKeyList_sortedLT` (the GSR output is a *sorted* key
   sequence), `rankOrderKeys_nodup`, and `map_inj_eq` (injective maps reflect list
   equality).  The single remaining sub-lemma for the full capstone
   `stableBuckets a ℓ (finRange n) = (finRange n).map rankEquiv.symm` is the
   `SortedLT` of the stable-bucketed deck's key image (hL): each label bucket
   `[i·n + pos | pos increasing]` is a strictly-increasing run and consecutive
   buckets are disjoint/ordered (`keyNat_lex`), so the `flatMap` is `SortedLT` by
   induction on the bucket count via `List.sortedLT_append` — but a single bucket
   is `(finRange n).filter …`, and this Mathlib exposes **no filter/subsequence-

 sortedness and no filter-`get`** lemma, so the bucket's `SortedLT` must be
   proved by a manual element-wise `get` induction (or a small added
   `IsSublist ⇒ SortedLT` lemma).  That is the exact, isolated next step; the
   module documents it in full.
   *Resolved (this session, `93fd7a2`):* the hL sub-lemma **landed** and the
   full capstone **proves** in new **`Shufflemath/GSRF42KeyOrder.lean`**.
   `bucketKeys_sortedLT` (the hL sub-lemma) is proved by the induction just
   derived: `List.SortedLT.flatMap_cons` gives that a filtered-then-mapped list
   (mapped by the *per-label strictly-increasing* key `keyNat`,
   `keyNat_strictMono`) is `SortedLT` exactly when its `flatMap`-tail is, and
   each bucket's `head.SortedLT` is `List.SortedLT.nodup` (the key image is
   `Nodup` because `keyNat` is strictly increasing inside a label).  Chaining
   the `flatMap` over the `finRange` labels gives **`stableBuckets_keySortedLT`**
   (the stable-bucket deck is `SortedLT` on the new key); combined with
   `rankOrderKeyList_sortedLT` and `List.SortedLT.eq_of_mem_iff` (both key
   images are `SortedLT` and carry the same membership — both decks contain
   every card, `keyNat` a fixed card→key map) this yields the **F4.2 sorting
   identity `stableBuckets_keys_eq_rankOrderKeyList`**: the keys emitted by
   `GSR.stableBuckets` are *exactly* `rankOrderKeyList`, i.e. the keys in the
   unique order by `(label, position)`.  This is "stableBuckets = order by new
   position" at the key level — the heart of F4.2.
   *Preserve the law (this session):* new **`Shufflemath/GSRPermutationLaw.lean`**
   names the GSR's law as `gsrPermutationLaw : Dist (Equiv.Perm (Fin n))` (the `ν_{n,a}`
   of the `2026-11-20` Section 3 "transport") and proves
   `idealShuffle_canonical_eq_permPushforward` / `idealShuffle_canonical_eq_permLaw` —
   the GSR on the canonical deck is that permutation law pushed through "apply the
   permutation to the deck" (via `Convexity.StdSimplex.map_map`). **F4.2 is now fully
   resolved** (both the "turn into a permutation" and "preserve the law" halves).
3. Establish the row-wise bound against *physical perfect-local* shuffling:
   for each deck, the TV discrepancy is no greater than the sum of the two
   local GSR-versus-uniform errors (49-card and 50-card working sets).
   *Progress (5th session, `87cc71f`/`104fd5e`):* the general reusable core is
   proven — `Finite.distProduct` (the independent product distribution, with
   the `distProduct_mass` simp-lemma) and
   `TotalVariation.distProduct_tv_subadditive` (`TV(μ⊗ν, μ'⊗ν') ≤ TV(μ,μ') +
   TV(ν,ν')` — the two-pile subadditivity). *Remaining:* connect the concrete
   `gsrProductKernel` to `distProduct` — `gsrProductKernel (L,R)` (a nested
   `map`/`join`) should equal
   `distProduct (GSR.idealShuffle nL a _ L) (GSR.idealShuffle nR b _ R)`, then
   `distProduct_tv_subadditive` gives the per-pile bound. **Wall:** the mass
   reduction normally uses `apply_mass_dom`, which requires a `Fintype`
   *domain*, but `idealShuffle : FiniteKernel (List (Fin n)) (List (Fin n))`
   and `List (Fin n)` is **not** a `Fintype`. Prove the point-mass equality
   directly from the `Finsupp` `map`/`join` weight definitions instead.
4. Use the existing `PhysicalRefinement.finite_local_uniform_bound` and
   `ProtocolCertificate` weighted telescope to compose these errors over a
   schedule. Use a named initial law and an explicit 99-card uniform target.

   *Progress (6th session, Fintype-free route — the `List (Fin n)` pile-list
   space is not a `Fintype`, so the `Finset.univ`-sup Dobrushin telescope has no
   direct Finsupp analog; a stochastic kernel is instead 1-Lipschitz on TV,
   which needs no finiteness):* `Finite.apply_mass_finsupp` (Fintype-free
   `apply_mass_dom` over the support), `TotalVariation.kernel_apply_lipschitz`
   (Fintype-free 1-Lipschitz kernel contraction), `TotalVariation.mixtureTV_le`
   (a mixture is no further from a reference than its component average),
   `CommanderLocalGSR.gsrOneStep_terminalTV_bound` (one two-pile GSR step keeps
   TV from the two-pile product reference within the start-weighted per-pile
   GSR-vs-reference errors — the 49+50 one-step terminal bound),
   `TotalVariation.run_nonexpansive` + `CommanderLocalGSR.gsrRunNonexpansive`
   (multi-step non-expansiveness for GSR schedules). *Remaining / blocked:* the
   fully *contractive* decay to the uniform target needs a Dobrushin coefficient
   (a `Fintype` supremum) — available only after the F4.2 Deck-level GSR lift to
   the Fintype space `Equiv.Perm (Fin 99)` (the `List.mem_bind`/`toMultiset`
   sub-wall); deferred.

**Acceptance:** a Lean-checked numeric or symbolic full-deck terminal TV
upper bound for one explicit physical finite-GSR protocol, with every model
assumption stated. Python's `experiments/oracle_gsr_budget.py` may propose a
candidate, but its output is not a Lean certificate.

### F5. Attach measured/parametric costs; certify a bounded optimizer

**Dependency:** F4 for a realistic finite-GSR protocol.

Re-use `Cost.lean`; specify the action alphabet, cost units (local riffle,
exchange, split/recombine), admissible schedules, and target TV threshold.
First prove the candidate's cost and **sufficient** TV upper bound; only then
address finite-class minimum-cost claims. A search over conservative upper
bounds is not proof that the candidate minimizes actual TV unless competing
candidates have suitable lower bounds or exact TV values.

*Progress (5th session, `e203310`/`ec68b71`):* the model-agnostic halves are
in. **`ProtocolCertificate.costed_terminalTV_le`** proves a costed schedule's
terminal TV ≤ its step kernels' weighted perturbation budget + the
ideal-reference TV (the "sufficient TV upper bound" half; reuses
`terminalTV_le_reference_add_budget`, so no F4 protocol instance is required).
**`Cost.protocolCost_nonneg`** (a schedule of nonnegative-cost actions has
nonnegative total cost) and the **`ActionKind`** action alphabet
(`localRiffle`/`exchange`/`splitRecombine`) supply the "cost" and "action
class" halves. *Remaining:* assemble these into the full F5 theorem over an
explicit finite-GSR protocol, and state the optimization quantifiers
separately. **DONE (79th+ session, this audit):** the full F5 certificates
are assembled in `Shufflemath/CommanderCostedCertificate.lean` —
`macroCountExchange_costedCertificate`, the recursion-free
`f5FullDeck_certificate` (over `Deck = Equiv.Perm (Fin 99)`, budget-free via
the exact F3 value), the non-degenerate `f5Nondegenerate_certificate`, and
`f5Nondegenerate_riffle` — each with model, action class, initial state,
target, terminal bound, and cost all explicit. The **optimization quantifiers
are stated separately** in the module's `## F5-B` section: claim (i) certified
feasibility is **proved** (the certificates above); claim (ii) bounded
(surrogate) optimality (min `protocolCost` among bound-passing protocols, via a
finite `argmin` — `f5OptCost` names the objective) is **stated, not proved**;
claim (iii) actual-TV optimality (needs competitor lower bounds) is **stated,
not proved, and deliberately not claimed**. A non-degenerate *full-deck*
budget certificate (over the 99! `Finset.univ`) is now realized at any exchange
count `n`: **`Shufflemath/TelescopeF5.f5FullDeck_nondegenerate_nstep`** (backed by
the abstract `compList_telescope_nstep_le_n` / `telescopeTV_le_idealPlusN` and the
`d := 1` `Perturbation.telescopeBound_le_length`) generalizes the existing 2-/3-step
telescope lemmas to any `n` through the length-free crude telescope, so no
`Finset.univ` is instantiated and the F4.2 wall is avoided. It bounds the physical
`n`-exchange TV toward `GSR.uniformDist` by `n` (the per-step physical-vs-ideal
discrepancy, each `≤ 1`) plus the oracle chain's TV toward uniform. The
*Dobrushin-contraction* sharpening has landed at the **macro** level (2026-11-24,
this session): `Shufflemath.BernoulliLaplaceCommanderBridge.blExchangeKernel_dobrushinCoeff_lt_one`
proves `Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) < 1` — every
`BLState 99 50 50` macrostate reaches the mid-window state `25` in one exchange
(`blExchangeKernel_allStatesReach25`, via the uniform surviving summands `a = 1` for
`x ≤ 26` and `a = 25` for `x ≥ 27` of the 6-arg `transitionNumerator`, isolated with the
correct 2-arg `Finset.single_le_sum`), so every row-pair shares that positive-mass
successor and `tv < 1` throughout, hence the max over `pairDistances` is `< 1`. This is
*qualitative* (the macro-chain is irreducible / sub-maximally contracting); the
quantitative `< 1/1000` objective still needs a concrete rational `d < 1` with
`d^n < 1/1000` (the 50×50 macro-`tv` sup, then `dobrushinCoeff ≤ d`, fed to
`physicalExchange_dobrushinDecay`). The `n` budget in the telescope certificate above
is non-vanishing, so no optimality is claimed (F5-B (ii)/(iii) stay deferred).

**Quantitative bound landed (`DobrushinDecay99`, this audit).** The `d < 1` /
`d^n < 1/1000` objective above is now PROVED with an explicit rational `d`.
`Shufflemath/FiniteDeck/DobrushinDecay99.lean` gives
`blExchange_dobrushinCoeff_le : dobrushinCoeff (blExchangeKernel commanderBLParams)
≤ 1 − w50 25 25`, where `w50 25 25 = 997540809461453561581 / 6330095096149974879912
≈ 0.15759`, so `d = 1 − w50 25 25 ≈ 0.8424` (matching the Python oracle
`1 − P(25→25) = 0.8424…`). This is *not* the `< 1` irreducibility argument: it rests
on two reusable lemmas — `TotalVariation.tv_overlap_identity` (Theorem A: the TV of
two probability laws is `½·Σ|μ k − ν k|`) and `Dobrushin.rowTV_le_one_sub_minMass`
(Theorem B: `rowTV K i j ≤ 1 − min (mass (K i) y, mass (K j) y)` for any state `y`),
plus the structural fact `w50_25_min_reach` (state `25` minimizes the incoming mass
to `25` over all `50` states — a `native_decide` over the exact weights). Applying
Theorem B at `y = 25` to every row pair then bounds `dobrushinCoeff` by `1 − w50 25 25`.
`one_sub_w50diag_pow41_lt_thousand` : `(1 − w50 25 25)^41 < 1/1000` is a single
`native_decide` on the exact rational (stated standalone to keep the `^41` reduction
in its own elaboration context), and the headline
`physicalExchange_decay_41_lt_thousand (x0)` composes this with the existing
`physicalExchange_dobrushinDecay` to state: **41 physical perfect-exchange steps from
any 99-card deck drive the TV to `GSR.uniformDist (Deck 99)` below `1/1000`.** The
tightest available `d` is `1 − w50 25 25`; a smaller one via the true max-rowTV pair
is possible but not needed for the `< 1/1000` objective.

**Acceptance:** theorem with model, action class, initial state, target,
terminal bound, and cost all explicit; separately state any optimization
quantifiers and their proof source.

### Optional / deferred tracks

- **P1: two-exchange exact optimum.** `dev/BernoulliLaplacePairOptimality.lean`
  is opt-in (`./dev/verify_next_phase.sh --pair`). Its source expresses the
  2,401-row objective. This optional certificate is independent of F1-F5.
  Prove variable-exchange-size semantics before
  presenting it as an operational schedule theorem. Do not make it a default
  library-build dependency.
- **GSR exact finite TV tables / Bayer--Diaconis permutation formula.** Useful
  for tighter F4 bounds; not a prerequisite for proving F1-F3.
- **Human bias, clumping, correlated labels, spectral higher modes.** Defer
  until a physical-perfect result and one finite-GSR bound are certified.
- **Presentation work.** The 155-scene Manim study deck is independent of
  Lean correctness. It has had LaTeX/build issues; do not count an authored
  deck or successful preflight as a completed full render without local
  evidence. See `visualizations/README.md` for build commands.

## Verification and completion rules

- Build only touched Lean targets first. **Always** run `lake exe cache get`
  before `lake build`, and run `./dev/verify_next_phase.sh` before handing
  off a tranche. That script intentionally builds modules missing from
  `Shufflemath.lean` imports. The legacy `dev/verify.sh` runs `lake update`
  and is not the preferred incremental verification path.
- Maintain current hypotheses in theorem statements until proved. Never
  silently promote a conditional theorem to an unconditional result, or
  replace proof obligations with `sorry`, `admit`, or opaque axioms.
- Exact Python tests are useful independent checks, **not** Lean proofs.
- Follow the quiet, targeted compilation policy in `AGENTS.md`; do not add
  unrelated proof-audit checks to normal build or CI workflows.
- Do not block a mathematically verified result on cosmetic linter warnings.
  Fix related warnings when editing a proof, not as an independent campaign.
- Update this file's status and `agent_handoff.md` after each completed
  tranche, recording tested targets and the next single task.

## Reference / history (not active task lists)

- [commander_fiber_disintegration.md](commander_fiber_disintegration.md):
  the concrete 99-card fiber and membership architecture.
- [full_deck_oracle_bridge.md](full_deck_oracle_bridge.md): three kernel
  models, numerical counterexample, and exact-count formula.
- [formalization_next_phase.md](formalization_next_phase.md): October 20
  source tranche and GSR/protocol rationale.
- [autonomous_lean_build.md](autonomous_lean_build.md) and
  [lean_build_history.md](lean_build_history.md): historical October 4-12
  autonomous-session record, **not current instructions**.
- [formalization_dependency_audit.md](formalization_dependency_audit.md):
  architectural background from before the `StdSimplex` migration.
