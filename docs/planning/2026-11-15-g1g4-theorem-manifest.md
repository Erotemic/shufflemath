# G1–G4 theorem manifest (2026-11-15)

**Status (2026-11-24 audit):** **G1, G3, G4 are complete**; **G2 is the
remaining generalization.**

* **G1 — DONE** (99-card fiber disintegration + 2/3-exchange TV), all in
  `Shufflemath/CommanderFullDeckDisintegration`: `commander_fiber_counts`,
  `commander_uniform_disintegration`, `two_oracle_exchanges_uniform{,_unconditional}`,
  `three_oracle_exchanges_uniform{,_unconditional}`,
  `two_physical_perfect_exchanges_uniform{,_unconditional}`.
* **G3 — DONE** (the F3 membership-exchange kernel law discharged as a concrete
  instance): `hMembershipExchange_kernel` (`Shufflemath/CommanderA3KernelLaw`)
  + `two_physical_perfect_exchanges_uniform_unconditional`
  (`Shufflemath/CommanderFullDeckDisintegration`) — no exchange-law hypothesis
  remains in the exported theorem.
* **G4 — DONE** (the BL refinement fully parameterized by `(N,m,r,k)`),
  `Shufflemath/FiniteDeck/BLRefinement`: `countFiber_card`,
  `countFiber_blStationary`, `countFiber_transitive`, `countInPile_*`,
  `yMoves_card_eq_transitionNumerator`, … The "Commander A3 as an instance"
  row is the F3 discharge above.
* **G2 — PARTIAL.** The **disintegration / counting / kernel-algebra /
  fiber-intertwining layer is already generic**: `FiberDisintegration` is fully
  type-generic (`marginal_comp_fiber_eq_uniform`, `stationary_disintegrates_of_mass`,
  `fiberLaw_recovers` — any finite `β`), `FiniteDeck/{Fiber,SubsetExchange,BLRefinement}`
  are `(N,m[,k,r])`-parameterized (fiber counts, `subsetExchangeKernel`/`blExchange`
  kernels, `uniformFiber_intertwines`), `CommanderMembershipExchange.distUniform_ofInvariantTransitive`
  is type-generic, and `Shufflemath/Finite` carries the Fintype-free kernel algebra.
  **Two rows remain 99-card-only (as of session 83):** the physical /
  three-physical-perfect-exchange **deck-uniform-target** TV (G2.9/13), which are
  surjectivity-blocked generically (`project : Deck → BLState` is not onto `BLState`).
  The 2/3-exchange TV (G2.3/5) is **DONE (generic, TV-equality form, session 83
  `7ae899e`)**: `A3KernelLaw.two_oracle_exchanges_uniform`, a one-line
  `OracleRefinement.run_tv_eq_macro` on the G2.10 `hrecover`. The A3 kernel
  law (G2.8) and the headline **G2.10** (generic two-physical-perfect-exchanges,
  objective item 3) are **DONE**: G2.8 at session 80 (`9181bff`), G2.10 at session 82
  (`11f099f`/`ff34501`, `A3KernelLaw.two_physical_perfect_exchanges_uniform`).

This is the theorem manifest (the plan's *source → target* map). The
**target-name column** below is the original plan's proposed naming; the
realized declarations are cited in each section's status above. The *current
single next action* and the do-not-stop rule remain in `docs/agent_handoff.md`
/ `docs/lean_plan.md`.

---

### G1. 99-card specialization — close the existing `Commander*` modules

**Status: DONE** (all five rows, `Shufflemath/CommanderFullDeckDisintegration`).
Target module: the existing `Shufflemath/Commander*` modules (no new `Finite*`
file needed for G1).

| # | Target theorem (99-card) | Source theorem to derive it from | Status |
|---|---|---|---|
| 1 | `hasCommanderFiberCounts` (99-card `HasCommanderFiberCounts`) | `CommanderFiberCount` (fiber count) | DONE (`commander_fiber_counts`) |
| 2 | `uniformDisintegration` (99-card, via `commander_fiber_counts`) | `CommanderFiberCount` + `FiberDisintegration.fiberLaw` | DONE (`commander_uniform_disintegration`) |
| 3 | `twoExchangeUniform` (99-card) | G1.2 + `PhysicalExchangeReduction` count-exchange + `TotalVariation` TV + the 99-card count-exchange kernel | DONE (`two_oracle_exchanges_uniform`) |
| 4 | `threeExchangeUniform` (99-card) | G1.3 + one more count-exchange | DONE (`three_oracle_exchanges_uniform`) |
| 5 | `physicalTwoExchange` (99-card, F3 perfect-local) | G1.3 + F3 `hMembershipExchange` + `FiberLifting` | DONE (`two_physical_perfect_exchanges_uniform`) |

---

### G2. Generic finite-deck versions (arbitrary `N, m, r, k` parameters)

**Status: 13/13 generic** — the disintegration / counting / kernel-algebra / fiber-
intertwining / oracle-2/3-exchange **TV** layer and the physical-perfect-exchange
**deck-uniform-target** TV (G2.9/13) are all **generic**. The deck-uniform-target headline
`FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck` (session 92 `de7638a`)
proves, for any `n`, `TV(run (physical n-exchange, lifted) n (lifted x0), GSR.uniformDist (Deck N)) =
TV(run (blExchangeKernel) n (x0), blStationaryDist)` — the *membership*-based route that avoids the
`project_surjective` wall (`project : Deck → BLState` is not onto `BLState` generically).
Target modules:
the **fully type-generic** `Shufflemath/FiberDisintegration` (works for *any*
finite `β`, not just the 99-card deck), the `(N,m[,k,r])`-parameterized
`Shufflemath/FiniteDeck/{Fiber, SubsetExchange, BLRefinement}`, and the
Fintype-free kernel algebra `Shufflemath/Finite`.

| # | Target theorem (generic) | Realized by (existing declaration) | Status |
|---|---|---|---|
| 1 | `hasFiberCounts` (fiber-card counting) | `FiniteDeck/Fiber.fiberSet_card`, `fiberSum_eq_permCard`, `fiberCount` | **DONE (generic)** |
| 2 | `uniformDisintegration` (marginal × uniform-fiber = uniform) | `FiberDisintegration.marginal_comp_fiber_eq_uniform`, `stationary_disintegrates_of_mass` (type-generic) | **DONE (generic)** |
| 3 | `twoExchangeUniform` (2-exchange TV) | `A3KernelLaw.two_oracle_exchanges_uniform` (generic, session 83 `7ae899e`; TV-equality form, n=2) | **DONE (generic)** |
| 4 | `countExchangeKernel` | `FiniteDeck/SubsetExchange.subsetExchangeKernel_*`, `BLRefinement.blExchangeKernel_mass` | **DONE (generic)** |
| 5 | `threeExchangeUniform` (3-exchange TV) | `A3KernelLaw.two_oracle_exchanges_uniform` (generic, session 83 `7ae899e`; TV-equality form, n=3) | **DONE (generic)** |
| 6 | `fiberCountEq` | `FiniteDeck/Fiber.fiberSet_card`, `fiberSum_eq_permCard` | **DONE (generic)** |
| 7 | `uniformPushforwardEq` | `FiberDisintegration.fiberLaw_recovers` (type-generic) | **DONE (generic)** |
| 8 | `membershipExchangeLaw` (A3 kernel law) | `A3KernelLaw.hMembershipExchange_kernel` (generic, session 80 `9181bff`) | **DONE (generic)** |
| 9 | `physicalTwoExchange` | `FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck` (n=2, generic); 99-card exact-rational: `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional` | **DONE (generic + 99-card)** |
| 10 | `twoPhysicalPerfectUniform` ← **headline (objective item 3)** | `A3KernelLaw.two_physical_perfect_exchanges_uniform` (generic, session 82 `11f099f`/`ff34501`) | **DONE (generic)** |
| 11 | `uniformFiberIntertwines` | `BLRefinement.uniformFiber_intertwines` | **DONE (generic)** |
| 12 | `distUniformOfInvariantTransitive` | `CommanderMembershipExchange.distUniform_ofInvariantTransitive` (type-generic) | **DONE (generic)** |
| 13 | `physicalThreeExchange` | `FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck` (n=3, generic) | **DONE (generic)** — 99-card n=3 exact-rational: `three_physical_perfect_exchanges_uniform_unconditional` (immediate next) |

**G2.9/13 (deck-uniform-target) — now DONE (generic).** Both were once flagged
**surjectivity-blocked** generically — `project : Deck → BLState` is not onto `BLState` (its
range is the admissible sub-range `max(0, m-(N-r))…min(m,r)`), so the `hfactor`
(`comp lift = fiberLaw project`, which requires `project_surjective`) fails generically.
Session 92 cracked it via the **membership-based route**: the bridge
`apply_blStationary_ucfm_locallift_eq_uniformDeck` shows the lifted macrostationary target
`apply (blStationaryDist) (comp (UCFM) localLift)` **equals** `GSR.uniformDist (Deck N)`, so
`two_physical_perfect_exchanges_uniform_deck` states the deck-uniform-target TV for any `n`
(99-card G2.9 = n=2, G2.13 = n=3) without the surjectivity premise. The 99-card *two*-exchange
exact-rational (`two_physical_perfect_exchanges_uniform_unconditional`) is already in the tree;
the 99-card *three*-exchange exact-rational (`three_physical_perfect_exchanges_uniform_unconditional`,
also the G3.6 reference) is the one remaining 99-card-specific item — the immediate next step.
The generic **G2.3/5** oracle TV-equality headline is **DONE (session 83 `7ae899e`)** —
`A3KernelLaw.two_oracle_exchanges_uniform`, a one-line `OracleRefinement.run_tv_eq_macro`.
The headline **G2.10** (generic two-physical-perfect-exchanges, objective item 3) is **DONE (session 82)** —
`A3KernelLaw.two_physical_perfect_exchanges_uniform` on the recovery-based
`run_tv_eq_macro_of_membership_exchange` framework, using the generic G2.8
`hMembershipExchange_kernel` + the new `hrecover` (`map_const_on_support` twice).

---

### G3. F3 membership-exchange law generalized (arbitrary deck size)

**Status: DONE.** Target module: existing `Shufflemath/CommanderMembershipExchange`
(F3) → generalized to arbitrary deck size.

| # | Target theorem (generic F3) | Source theorem to derive it from | Status |
|---|---|---|---|
| 1 | `membershipExchangeKernelLaw (N m r k)` | G2.4 + G2.6 + G2.7 | DONE (99-card: `hMembershipExchange_kernel`) |
| 2 | `membershipExchangeCount (N m r k)` | G2.4 + `BernoulliLaplaceGeneral` count-transition | DONE (99-card) |
| 3 | `membershipExchangeUniform (N m r k)` | G2.8 + `membershipFiber_transitive` (99-card) + `distUniform_ofInvariantTransitive` | DONE (99-card: `hMembershipExchange_kernel`) |
| 4 | `physicalMembershipExchange (N m r k)` | G2.9 + G2.12 | DONE (99-card: `hMembershipExchange_kernel`) |
| 5 | `twoPhysicalPerfectUniform (N m r k)` | G2.3 + G3.4 + G2.11 | DONE (99-card: `two_physical_perfect_exchanges_uniform_unconditional`) |
| 6 | `physicalThreeExchange (N m r k)` | G2.10 + G3.5 | **immediate next** — 99-card exact-rational `three_physical_perfect_exchanges_uniform_unconditional` (added next); generic via the G2.10 deck headline n=3 |

---

### G4. BLRefinement generalized (arbitrary deck size)

**Status: DONE.** Target module: existing `Shufflemath/BLRefinement` (BL law)
→ generalized to arbitrary deck size. **G4's real deliverable is to discharge
the Commander A3 theorem as an instance of the generalized F3 theorem, not to
re-prove the count-exchange kernel or the membership-exchange law.**

| # | Target theorem (generic BL) | Source theorem to derive it from | Status |
|---|---|---|---|
| 1 | `countProjectionEq (N m r k)` | G2.6 | DONE (`countFiber_card` / `countInPile_*`) |
| 2 | `countProjectionEquivariant (N m r k)` | G2.8 + G2.7 | DONE (count-equivariance in `BLRefinement`) |
| 3 | `countProjectionUnderExchange (N m r k)` | G2.4 + G4.1 + G4.2 | DONE (`countFiber_blStationary`) |
| 4 | `commanderA3Instance (N m r k)` | **G3.1 (the generalized F3 membership-exchange kernel law)** — this is the discharge: the 99-card `hMembershipExchange` is an instance of the generic law | DONE (the F3 discharge) |
| 5 | `physicalTwoExchange (N m r k)` | G4.4 + G2.3 + G2.11 | DONE (99-card: `two_physical_perfect_exchanges_uniform_unconditional`) |
| 6 | `twoExchangeUniform (N m r k)` | G4.4 + G2.3 + `FiberDisintegration` | DONE (99-card: `two_oracle_exchanges_uniform_unconditional`) |
| 7 | `threeExchangeUniform (N m r k)` | G4.5 + one more count-exchange | DONE (99-card: `three_oracle_exchanges_uniform_unconditional`) |
| 8 | `fullDisintegration (N m r k)` | G4.6 + G2.11 + `commander_fiber_counts` | DONE (99-card: `commander_uniform_disintegration`) |

---

## After G4 is green

Do the **P2/P3** work from the 2026-11-15 qwen proof-quality review *only after*
G4 has a green build, in this order (P2 first, then P3):

- **P2 (build-performance):**
  - Split `BernoulliLaplaceFirstMode` out of `BernoulliLaplaceGeneral.lean`
    (the first-mode / eigenfunction block, `section firstMode`, into a new
    `Shufflemath/BernoulliLaplaceFirstMode.lean`). This is the clearest
    build-granularity win: 12 downstream modules import the general module,
    and editing `blConditionalMean` (385 lines) currently forces a recompile of
    the whole general module.
  - Extract the product/mixture TV machinery out of `TotalVariation.lean`
    (1,085 lines, 26 downstream importers) into a
    `Shufflemath/TotalVariationProducts` companion. Do this only after P2's
    Bernoulli split, and only with measured before/after build times.
- **P3 (proof-quality / deduplication):**
  - Deduplicate the two subset-fiber counting constructions
    (`ExchangeOverlap.lean:332-522` `s1Fiber`/`fiberA` vs.
    `FinsetFiberCount.lean:20-185` `sFiber`/`sFiberA`) — keep one generic
    interface, make the specialized one a wrapper.
  - Unify the restricted `generalCL` and the stronger `generalCL_ns` overlap
    identity chains in `ExchangeOverlap.lean` — keep one, make the other a
    corollary.
  - Share the schedule-intertwining induction between `OracleRefinement.lean`
    and `PhysicalRefinement.lean` (both prove the same list-induction
    composition/transport fact).

These are **not** part of G1–G4 and should not be started before G4 is green.

## Do-not-stop reminder

The active do-not-stop rule lives in `docs/agent_handoff.md`
(`**Active do-not-stop rule:** …`), *not* here. This manifest is the theorem
list only.
