> ⚠️ **DO NOT STOP — READ FIRST (re-read after every compaction).**
> **Autonomous build active until: Wed 2026-11-24 23:59:59 EST** (the user may
> extend this — if a later dated note gives a later date, that one wins).
> **Do not stop, ask, or end the session before that deadline.** Compaction is
> NOT a stopping signal. Never emit a "session summary" / "state of the world"
> / "ready to continue" as terminal output — that reads as a stop; instead end
> each turn by committing and immediately starting the next proof step.
> **Goal: complete everything in `docs/planning` (the G1–G4 arbitrary-finite-deck
> generalization, then the Commander A3 discharge, then F5) before the deadline.**
> After compaction, in order: (1) read THIS banner + this whole file, (2) `git
> log --oneline -15` + `git status --short`, (3) confirm the tree is green with
> the targeted `lake build`s, (4) resume at the exact next lemma named below
> ("Exactly where to resume"). Continue lemma-by-lemma; the only legal stops
> are the stuck-protocol (rule 8) and the deadline itself.

# Agent handoff: next Shufflemath task

**Updated:** (G4 **68th session — A3 part (i) COMPLETE: the general `fintypeCard_subtypeCongr` lemma + the `rawExchange_membershipCount_mass` count-mass bridge are committed; next is the A3 capstone `hMembershipExchange`**).

- **A3 part (i) count-mass bridge — COMPLETE (68th session):** the 56th-session target
  `rawExchange_membershipCount_mass` is now **proved and committed** in `Shufflemath/CommanderA3Mass.lean`.
  The 67th session had closed all but the final Fintype-card bridge — the wall: the two subtypes
  `{j // F j ∈ S}` and `{j // Q j}` are `Iff`-equal (`hP`) but not definitionally equal, so `rfl` / `congr`
  / a Membership-context `Equiv` all recursed or type-mismatched. **The clean fix:** a *general* lemma,
  proved in the shallow `Shufflemath/FinsetCombinatorics.lean`,
  `fintypeCard_subtypeCongr : (∀ a, P a ↔ Q a) → Fintype.card {a // P a} = Fintype.card {a // Q a}`
  (built as a subtype `Equiv` whose injectivity/surjectivity close by `Subtype.ext; rfl` — shallow, no
  `Membership`-Finset reduction) and applied here with `hP`. The full calc chain: point-mass
  (`rawExchangeMembership_pointMass`) → indicator → fiber-sum (`Finset.sum_filter`) → preimage-card
  (`fiberSum_eq_preimageCard`) → Fintype-card bridge (`fintypeCard_subtypeCongr`). `CommanderA3Mass`
  is now in the `dev/verify_next_phase.sh` build list and the tranche stays green (37 tests).

- **Exactly where to resume (68th session): the A3 capstone `hMembershipExchange` (F3-b gate).**
  Part (i) (count-total: `rawExchange_membershipCount_mass`) and part (ii) (within-count uniformity:
  `mu_x_constant_on_countFiber`) are both done. Per the capstone plan (the A3 section below): (1) the
  fiber-average collapse `rawExchangeMembership_count = commanderExchange25_countMass`
  (`newLeftCount_deckIndependent` + `project_count`); (2) **combine** — for `m` in the `c`-fiber, `μ_x m`
  = (part (i) count mass at `c`) / `membershipFiber_card`, which equals `hMembershipExchange_rhs_mass`
  at `(x, m)`, so the kernel equality `hMembershipExchange` follows by `FiniteKernel.ext` (pointwise in
  `x, m`); (3) instantiate `two_physical_perfect_exchanges_uniform_of_counts`.

  **Immediate next lemma — the count bridge `exchangeCount_preimage_eq_transitionNumerator`**
  (WIP at `Shufflemath/_ProbeA3Cap.lean`, statement compiles, body `sorry`):
  `Fintype.card {j : exchangeChoice // membershipCount (newMembership d j.1.1 (leftCard25 j.1.2)
  j.2.1 (rightCard25 j.2.2)) = c} = transitionNumerator 99 50 25 (leftOriginalCount d) c`.
  Chained with `exchangeChoice_card_eq_transitionDenominator` it turns
  `rawExchange_membershipCount_mass`'s RHS into the `transitionWeight`. **Proof chain:**
  (a) `exchangeChoice ≃ ↑(leftChoices ×ˢ rightChoices)` (via `exchangeChoice_equiv_lr` +
  `Finset.mem_prod`), (b) predicate bridge `membershipCount (newMembership d L R) =
  (newLeftCards d L R ∩ leftOrigSet).card` (`membershipCount_newMembership` / `newLeftOriginalCount_eq`),
  (c) `newLeftCount_eq_transitionNumerator` (`(leftChoices ×ˢ rightChoices).filter (…)`'s card =
  `transitionNumerator`). **Recursion diagnosis (FOUR walls, all at maxRecDepth 4000 — the 99-card
  powerset types are too big for Fintype-card computation):**
  (1) `Fintype.card` of the *named* Fintype `exchangeChoice` and `Finset.card` of the *concrete*
  Finset `leftChoices ×ˢ rightChoices` both elaborate fine (the target statement compiles; this is
  why `newLeftCount_eq_transitionNumerator` counts over `(leftChoices ×ˢ rightChoices).filter …`).
  (2) `Fintype.card` of the **anonymous** product `{p : Finset (Fin 50) × Finset (Fin 49) // …}`
  recurses — never restate the count over the raw product.
  (3) `Fintype.card` of the Finset-subtype `{p : ↑(leftChoices ×ˢ rightChoices) // …}` (whose
  `Fintype` comes from `Finset.fintype`) recurses in the PROOF (`unfold Fintype.card;
  simp [Finset.fintype, …]` forces the anonymous-product reduction).
  (4) **Found this session:** even the *named*-Fintype bridge `Fintype.card {j : exchangeChoice // P j}
  = Finset.card (Finset.univ (j : exchangeChoice) | P j)` recurses under `simp [Fintype.card,
  Finset.fintype]` (simp over-expands `Fintype.univ`/`card_univ` of the powerset Fintype).
  **The escape (route, next session):** every wall is triggered by *computing* a `Fintype.card` from
  the default elaborated instance on a huge type.  The fix is to use `Fintype/Card.lean`'s
  *instance-specific* lemmas, which state the card without expanding the default instance: `Fintype.card_ofFinset`
  / `Fintype.card_of_subtype` / `Fintype.card_subtype` give `Fintype.card (ofFinset s H …) = Finset.card s`
  for `H : x ∈ s ↔ P x`.  So: LHS `Fintype.card {j : exchangeChoice // P j}` = (instance-independence,
  `Fintype.card_unique`/`Fintype.card_eq` — a single `rw`, NOT `simp`) `Fintype.card (ofFinset
  (Finset.univ.filter P) (mem_filter_univ))` = (card_ofFinset) `Finset.card (Finset.univ (j : exchangeChoice) | P j)`;
  then push that **Finset** by the bijection `exchangeChoice ≃ ↑(leftChoices ×ˢ rightChoices)`
  (`exchangeChoice_equiv_lr` + `Finset.mem_prod`) to `Finset.card ((leftChoices ×ˢ rightChoices).filter P')`,
  `P' p = (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = c` (`membershipCount_newMembership`);
  then `= transitionNumerator 99 50 25 (leftOriginalCount d) c` (`newLeftCount_eq_transitionNumerator`).
  **First probe to run next session:** does the instance-independence step
  `Fintype.card {j : exchangeChoice // P j} = Fintype.card (ofFinset (Finset.univ.filter P) (mem_filter_univ))`
  close by a single `rw [Fintype.card_unique]`/`Fintype.card_eq` (no `simp`)?  If yes, the rest is
  Finset bookkeeping. **`imports that work** (all in `namespace Shufflemath`; `CommanderFiberCount`
  has NO sub-namespace so `leftOrigSet` is used unqualified; `FinsetCombinatorics.*` qualified;
  `Finset.card_product`, NOT `card_prod`): `FinsetCombinatorics`, `BernoulliLaplace`,
  `CommanderPermutation` (`leftOriginalCount`), `CommanderA3Kernel` (`newLeftCount_eq_transitionNumerator`,
  `newLeftCount_deckIndependent`), `CommanderMembershipKernels` (`membershipCount`),
  `CommanderMembershipExchange` (`membershipCount_newMembership`), `CommanderPhysicalExchange`
  (`newMembership`, `newLeftCards`, `leftChoices`/`rightChoices`, `leftCard25`/`rightCard25`),
  `CommanderA3ExchangePushforward` (`exchangeChoice_equiv_lr`).
  `CommanderFiberCount` (`leftOrigSet`); all in `namespace Shufflemath`, `FinsetCombinatorics.*`
  qualified, and `Finset.card_product` (not `card_prod`) for the prod card.

- **A3 part (i) count-mass bridge** — the 56th-session A3 part-(i) target
  `rawExchange_membershipCount_mass` is 95% complete (the (a)+(b) core was already done; this session
  closed two more sub-steps). The 4th calc step (fiber-sum → preimage-card) now CLOSES with targeted
  `rw [← Nat.cast_sum]; rw [hNat]` (the earlier `simpa [Nat.cast_sum]` recursed on the deep `Membership`
  structure; a single `rw` does not). The predicate equality `hP : F j ∈ S ↔ Q j` — the whole
  mathematical substance of the final step — WORKS via
  `simp only [S, Finset.mem_filter, Finset.mem_univ]; dsimp [F]; simp only [and_true, true_and]`
  (shallow: reduces `F j ∈ S` to `True ∧ count (F j) = c` → `Q j`, no `newMembership` unfolding).
  The ONE remaining step is the Fintype-card bridge
  `(Fintype.card {j // F j ∈ S} : Rat) = (Fintype.card {j // Q j} : Rat)`: the two subtypes are
  `Iff`-equal (`hP`) but NOT definitionally equal (the predicate `F j ∈ (univ.filter (count·=c))` needs
  a simp step, not WHNF, to become `Q j`), so `rfl` / `congr` / `congrArg Fintype.card (Subtype.ext hP)`
  (type mismatch) / a manual `Equiv` + `Fintype.card_congr` (its injectivity `ext` leaves a deep
  `a✝ ∈ ↑(...).2` Membership-internal subgoal) all fail.

  **Next (clean fix):** prove ONCE in `Shufflemath/FinsetCombinatorics.lean` (shallow context, not the
  Membership-heavy A3 file) the general bridge
  `Fintype.card {a : α // P a} = Fintype.card {a : α // Q a}` from `h : ∀ a, P a ↔ Q a` — first check
  whether Mathlib already provides it (`Fintype.card_congr` from a subtype `Equiv`, or a
  `Finset.ncard` / `Finset.card_congr` formulation). Apply it here with `hP` to close the 5th calc step
  (`rw [hXY]; rfl`); drop the `maxRecDepth` guard if the bridge no longer reduces the Membership Finset.
  Then extract the whole lemma into `Shufflemath/CommanderA3Mass.lean` (new file; add to the
  `Shufflemath.lean` module list after `CommanderA3Count`), delete the probe, verify green, commit.
  The WIP file (full lemma + this banner) is `.pi-glla/66b_a3count_wip.lean`.

- **A3 part (i) count-mass bridge** — the 56th-session A3 part-(i) target
  `rawExchange_membershipCount_mass` (per the 56th-session 4-step plan) is 95% written in
  `.pi-glla/56_rawExchangeMembership_count_wip.lean`.  State:
  - **(a) point mass → fiber count** — `hA`:
    `(if count m = c then (rawExchangeMembership d) m else 0) = (1/#EC) · (if count m = c then
    Fintype.card {j // F j = m} : Rat) else 0)`, via
    `CommanderA3ExchangePushforward.rawExchangeMembership_pointMass` + `Fintype.card_subtype`
    (Finset-filter card ↔ Fintype-card fiber).  DONE.
  - **`if` indicator → the `c`-fiber `S`** and **`← mul_sum`** (factor `1/#EC` out of the sum) and
    **`Finset.sum_filter`** (univ-sum with the `c`-indicator = sum over the `c`-fiber `S`).  DONE.
  - **(b) fiber sum = preimage** — `FinsetCombinatorics.fiberSum_eq_preimageCard` (+ `Nat.cast_sum` /
    `congrArg` for the Nat→Rat bridge) = `Fintype.card {j // F j ∈ S}`.  DONE.
  - **Only remaining step (c)**: reduce `F j ∈ S` (`S` = the `c`-fiber) to
    `membershipCount (newMembership d j…) = c` and close.  **`dsimp [F, S, …]; rfl` recurses**
    because `F` = `newMembership` is a deep def (`addMembership` over `Finset.succImage` / `mem`).
    The WIP banner gives the exact close: `congr 1` +
    `funext j; simp only [F, S, Finset.mem_filter, Finset.mem_univ]` (a *shallow* `set F` let-reduction,
    never unfolding `newMembership`'s body), then `Fintype.card_congr` / `congrArg`.
    **This is a one-step fix, not a new theorem.**
  - **Extraction target: `CommanderA3ExchangePushforward.lean`** (NOT
    `CommanderMembershipExchange.lean` — that would be an import cycle, since
    `CommanderA3ExchangePushforward` already imports `CommanderMembershipExchange`).  After it lands,
    plug into the A3 part-(i) fiber-average / `transitionNumerator` reconciliation (steps 2–3 of the
    56th plan) and toward `hMembershipExchange`.
- **Note:** the 65th block's "resume at 66th" suggested the G4→concrete wiring; the 66th was instead
  assigned the A3 part-(i) count-mass bridge (per the session task).  The G4→concrete + F5 path
  (`docs/planning/proof-strategies/2026-11-18-g4-macro-intertwining-plan.md`) remains available as an
  alternative next thread.  No new *library* lemmas this session (the 65th membership-lift bridge
  `9b8ce3e` is still the last library commit); the only new tracked artifact is the WIP file.
  Full tranche green.

- **Exactly where to resume (67th session):** open `.pi-glla/56_rawExchangeMembership_count_wip.lean`,
  apply the final-step fix from its banner (`congr 1` + shallow `funext`/`simp` on the predicate,
  then `Fintype.card_congr`), confirm it compiles, and **extract the lemma into
  `Shufflemath/CommanderA3ExchangePushforward.lean`** (delete the WIP file; add the lemma after
  `rawExchangeMembership_pointMass`).  Then continue A3 part (i) (the fiber average / `transitionNumerator`
  reconciliation) and the `hMembershipExchange` capstone in `CommanderMembershipExchange.lean`.

**Updated:** (G4 **65th session — membership-lift identification bridge committed**: the concrete `membershipLift` / `membershipCount` / `membershipFiberCount` are the general `uniformCountFiberMembership` / `countInPile` / `countFiberMemb` at `(99, 50)`).

- **The membership-level concrete↔general bridge is proven** — 5 lemmas landed in
  `Shufflemath/BernoulliLaplaceCommanderBridge.lean` (builds clean; full tranche 37 tests OK).
  The 99-card concrete membership machinery of `CommanderMembershipKernels` is exactly the
  arbitrary-finite general `BLRefinement` machinery at the Commander parameters `(99, 50, 50)`:
  1. `leftOrigSet_eq_markedSet99_50` — the 50 initially-left card identities = `markedSet 99 50`
     (both are `Fin 50`'s image into `Fin 99`; just `rw [markedSet, leftOrigSet_eq_image]; rfl`).
  2. `membershipCount_eq_countInPile` — a membership's marked-card count = the general
     `countInPile` (via `#(S.1 ∩ leftOrigSet) = #(S.1 ∩ markedSet 99 50)`).
  3. `membershipFiberCount_eq_countFiberMemb` — the concrete fiber size = `countFiberMemb`
     (both `choose (N-r) r`).
  4. `commanderToBL_val_eq_commanderLeftCount` — the state's general marked-count =
     `commanderLeftCount` (both `x.val + 1`).
  5. `membershipLift_matches_uniformCountFiber` — **the capstone of this bridge**: the concrete
     resample kernel's mass = the general `uniformCountFiberMembership`'s mass, proved by
     `simp [membershipLift, Dist.mass_ofFun]` (LHS) + `rw [uniformCountFiberMembership_mass,
     membershipCount_eq_countInPile, commanderToBL_val_eq_commanderLeftCount,
     membershipFiberCount_eq_countFiberMemb]` (RHS). This is the **"uniform-fiber half"** of the
     membership-level bridge — the resample kernel, count, fiber size, and marked-count all agree.
  - Key discovery: `leftOrigSet` is definitionally `markedSet 99 50` after `rw [markedSet,
    leftOrigSet_eq_image]` (the two `Fin.castLE` / `⟨i.val, _⟩` maps are the same term), so the
    finset identification is `rw; rfl`.
  - Probe `_ProbeMemLift.lean` deleted (extracted into the bridge file).

- **Exactly where to resume (66th session):** connect `g4MacroIntertwining` to the concrete
  99-card Commander objects — show the concrete exchange kernel (`commanderExchange25` /
  `commanderMembershipExchange`) equals the macro-intertwined general one, per
  `docs/planning/proof-strategies/2026-11-18-g4-macro-intertwining-plan.md` (the "G4 → concrete"
  wiring). Use the membership-lift bridge just proved + `commanderExchange25_matches_blExchange`
  + `uniformCountFiberMembership`. Then **F5** (the arbitrary-finite-deck generalization capstone)
  per `docs/lean_plan.md`.

**Updated:** (G4 **64th session — G4 COMPLETE: `g4hDB` bridge + `g4MacroIntertwining` capstone both committed**).

- **G4 is done.** Two lemmas landed in `Shufflemath/FiniteDeck/BLRefinement.lean` this session
  (full tranche green, 37 tests OK):
  1. `g4hDB` (commit `f60adc3`) — the detailed-balance bridge in the count-fiber form:
     `#countFiberMemb x · TN(x, y) = #countFiberMemb y · TN(y, x)` for two admissible macrostates,
     via `countFiberMemb_card` + `fiberSum_eq` + `fiberSum_swap` (the already-proved general
     `detailedBalance` in `BernoulliLaplaceFiber`, reconciled to the `#countFiberMemb · TN` form).
  2. `g4MacroIntertwining` (commit `a59c6c1`) — **the G4 kernel-equality capstone**:
     `uniformCountFiberMembership ⊳ subsetExchangeMembershipKernel =
     blExchangeKernel ⊳ uniformCountFiberMembership` (a `FiniteKernel` equality). Pointwise it
     is `g4LHS_mass_sum = g4RHS_mass_sum`; after `apply_mass` × 2 + the two mass-sum collapses
     + `field_simp [nonzero fiber, nonzero denominator]`, the residual equality is the cast of
     `g4hDB` (`congrArg (fun n => (n : Rat)) (g4hDB p x yc)` + `mul_comm`).

- This discharges the **Commander A3** physical-exchange reduction by specialization at the
  99-card parameters (the `hMembershipExchange` kernel equality at the count level).

- **What remains (next):** connect `g4MacroIntertwining` to the concrete 99-card Commander
  objects (`commanderExchange25` / `commanderLeftCount`) — i.e. show the concrete exchange
  kernel equals the macro-intertwined general one, per the roadmap line 9/68 of this file and
  `docs/planning/proof-strategies/2026-11-18-g4-macro-intertwining-plan.md`. Then **F5** (the
  arbitrary-finite-deck generalization capstone) per `docs/lean_plan.md`.

- Support committed this session: `reachSet_symm` (the reverse-flow / reach-set symmetry seed).
  Also note the earlier "genuinely hard half" framing is resolved: detailed balance was already
  proved in `BernoulliLaplaceFiber` (`fiberSum_swap` 877 → `detailedBalance` 909 →
  `blStationaryDist_is_stationary`); `g4hDB` is the small reconciliation to the count-fiber form.

**Updated:** (G4 **63rd session — `g4RHS_mass_sum` committed; BOTH LHS+RHS mass formulas
now done; the reversible-flow identity is next**). The G4 **RHS mass-sum collapse** is
proved and in `Shufflemath/FiniteDeck/BLRefinement.lean` (builds clean, 3223 jobs; full
tranche 3214 jobs):
`∑_y (blExchangeKernel p x) y · (uniformCountFiberMembership p y) S
   = TN(x.val → c) / (D · #fiber(c))`  where `c = countInPileVal S`, `D = transitionDenominator`.
The long-standing **`Finset.sum_ite` / singleton-fiber** blocker is solved: the fiber
`{y ∈ univ // c = y.val}` is the singleton `{⟨c, _⟩}` (a `BLState` is unique per count), so
after `rw [Finset.sum_ite]` the surviving fiber-sum collapses to one term via
`Finset.sum_singleton`; the only side-goal is the trivial decidable-pred condition
`y ∈ Un → True` (`intro _; exact True.intro`). The mass-body product telescopes to
`ite(c = y.val, transitionWeight/FC_y, 0) = A y` (Rat division is definitional, so the
pos-case is `dsimp` + `rfl`; the neg case is `0 = 0`).
With this, **both** G4 mass formulas are in the library: LHS `g4LHS_mass_sum`
(`∑_j (UCFM x) j·(SE j) S = TN(c, x.val)/(#fiber(x)·D)`, `dc20848`) and RHS
`g4RHS_mass_sum` (this session). **Exactly where to resume:** the **reversible-flow
(detailed-balance) identity** — the "genuinely hard half" — which ties the two sides into
the `hMembershipExchange` kernel equality:
`TN(c, x.val)·#fiber(c) = TN(x.val, c)·#fiber(x)`
(equivalently `comp (comp (fiberLaw project) rawExchangeMembership) (det membershipCount) =
comp commanderExchange25 (det commanderLeftCount)` at the count level). See
`docs/planning/proof-strategies/2026-11-18-g4-macro-intertwining-plan.md`. The scratch
probe `Shufflemath/_ProbeG4RHS.lean` is deleted (extracted into BLRefinement).

**Updated:** 2026-11-18 (A3 **54th session — cracked the double-count's missing lemma**:
`Fintype.card_sigma` exists (`Data/Fintype/Defs.lean:161`), so the fiber-product route
only needs its `right_inv` `HEq` fixed (or switch to `Finset.card_biUnion`, which
exists). Point-mass + part (i) normalization done; the double-count is the last blocker
to `rawExchange_membershipCount_mass`.)
- **`uniformPushforward_pointMass`** (`Shufflemath/CommanderA3UniformPushforward.lean`,
  `e0b6ebe`): for a finite nonempty `X` and any `f : X → Y`,
  `Dist.mass ((GSR.uniformDist X).map f) y = (1/card X) · #{j : f j = y}`. This is
  the **A3 part (i) normalization** in fully general form, and it *sidesteps the
  52nd-session `.map`-on-`Dist` / `Finsupp.mapDomain` rabbit hole entirely*: the
  route is pushforward `= apply U (deterministic f)` (`apply_deterministic_eq_map`)
  → `apply_mass` opens the `Fintype` sum → each summand is
  `GSR.mass_uniformDist j` **used as a term** (not `rw`/`simp` — re-unfolding
  `GSR.uniformDist`'s expensive total-mass proof was the earlier heartbeat blocker)
  times the deterministic point mass (`Dist.mass_pointMass`), with the two
  directional `ite`s reconciled by `if_congr`; the sum collapses by `mul_sum` +
  `Finset.sum_boole` to `(1/card) · #{j : f j = y}`. The companion pure-`Finset`
  helper **`sumConstIte`** (`∑ x, c · 1_p x = c · #{x : p x}`) is in the same file.
  Because `rawExchangeMembership d` *is* `(GSR.uniformDist exchangeChoice).map (…)`
  (its own def, line 670), this general lemma applies to it **directly** — no `apply`
  or `.map`-on-`Dist` construction is needed. Added to `dev/verify_next_phase.sh`;
  full tranche builds, 37 python tests green.

**Updated:** 2026-11-24 (A3 **51st session — `hTrans` bridge + part (ii) constancy
in the main library**) — the two remaining *inputs* to the `hMembershipExchange`
capstone are now proved in `Shufflemath/CommanderMembershipExchange.lean`:
- **`membershipFiber_transitive_asEquiv`** (`de1d4b0`): the **`hTrans` bridge** —
  wraps the bare bijection `f : Fin 99 → Fin 99` from `membershipFiber_transitive`
  as a `Deck` (`Equiv.ofBijective`) so the orbit map is exactly the `E`-language
  equiv `relabelMembership_equiv (g) g.bijective` that `distUniform_ofInvariantTransitive`
  needs. Solves the 48th/49th-session **Finset/Set-coercion wall**: the `.val`-field
  equality `m.1.image f = m'.1` is a `Finset.ext` pointwise iff bridged to the Set
  image equality `hImg` via a direction-controlled `rw` chain
  (`← Finset.mem_coe` / `← hSet` / `← Finset.coe_image` / `Finset.mem_coe`) — the
  iff direction on the first `mem_coe` was the previous session's blocker.
- **`mu_x_constant_on_countFiber`** (`0259ab2`): **part (ii) core** — the
  post-exchange membership law `μ_x` is *constant on each membership-count fiber*
  (invariance `mu_x_map_invariance` + transitivity `membershipFiber_transitive_asEquiv`
  force equal mass on the orbit, and the orbit is the count fiber). Its `hConst` step
  mirrors `distUniform_ofInvariantTransitive`'s own `hConst`. Both lemmas build clean
  (3211 jobs); the 37-test verify gate is green.

**Prior 50th session** (A3 within-count invariance, `67a4efc`): `μ_x`
invariance's missing piece **`hE`** is in the main library (`CommanderPhysicalExchange.lean`):
- **`leftOriginalCount_conjugate`**: `(leftOrigSet).image g = leftOrigSet →
  leftOriginalCount (d.trans g) = leftOriginalCount d` — the long-blocked 48th/
  49th-session target, now compiling clean.
- **`project_conjugate`** (the **`hE`**): `(leftOrigSet).image f = leftOrigSet →
  project (d.trans f) = project d` — the exact premise step 1 of the `μ_x`
  invariance assembly needs (`fiberLaw_invariant_underFiberEquiv`).
- **`hGpart`** (standalone theorem, both directions) + the light `origLeft_L50` /
  `leftOrigSet_eq_L50` / `hgL_L50` helpers it rides on.

**The wall is gone.** The 48th/49th diagnosis: the `Fin 99` *filter* form of
`leftOrigSet` whnf-explodes on `.image g` (200000-heartbeat timeouts, even at 2M).
The fix is the **frameshift to the 50-element index set** (strategy (a)): (1) route
every heavy image step through the light `Fin 50` *image* form
`origLeft_L50 := (Finset.univ : Fin 50).image leftPosition`; (2) prove the
partition-preservation iff `hGpart` as a **standalone top-level theorem** — its
`whnf` cost is paid **once, at its own compilation** (module builds 3224 jobs, exit
0, full 37-test suite green); (3) in the final filter-card assembly, **reference
`hGpart` by name** (a single `hGpart d g hgL (d (leftPosition i))`) so the expensive
reduction is never re-run in the deep context. Referencing a compiled theorem by
name is cheap; the earlier failures (47ax `hGf`/`hGb` defs, 47az inline `hpart`)
all **re-ran the heavy body at the call site**. A standalone reference module is
`Shufflemath/_Probe47b0.lean`.

**G4 generic-kernel status (56th session):** the fiber-uniform membership kernel
`uniformCountFiberMembership` is now in `BLRefinement` (commit `8343334`) — the
"uniform count-fiber membership" half of the G4 macro-intertwining kernel equality
(the roadmap "discharge Commander A3 by instantiation" route). Next on the *generic*
route: the `subsetExchangeMembershipKernel` wrapper (Membership to Membership, over
`subsetExchangeKernel`) plus the full kernel equality
`uniformCountFiberMembership comp subsetExchangeMembershipKernel = blExchangeKernel comp uniformCountFiberMembership`
(pointwise-mass; see `/tmp/note_g4_kernel_eq.md` and the G4 row of the theorem
manifest). The concrete 99,50,50,25 route below is the parallel path to the same
A3 discharge.

**Exactly where to resume: the A3 capstone `hMembershipExchange` — part (i) count
total, then the full kernel equality.** Both *inputs* to the within-count
uniformity (part (ii)) are now in the library: `mu_x_map_invariance` (invariance)
and `membershipFiber_transitive_asEquiv` (transitivity / `hTrans`), and
`mu_x_constant_on_countFiber` already combines them into the **within-fiber
constancy**. For **part (i)** the normalization bridge is now done:
`exchangeChoice_card_eq_transitionDenominator` (`a82673b`) shows
`#exchangeChoice = transitionDenominator 99 50 25`, so the raw-exchange
normalization is the BL transition denominator, and
`membershipCount_newMembership` (`1be4918`) gives the count connection
`membershipCount (newMembership d L R …) = (newLeftCards d L R ∩ leftOrigSet).card`
(the `dsimp [membershipCount, newMembership]` one-liner). The remaining **specific
next lemma** is the **inner-sum** (WIP skeleton at `.pi-glla/52_innerSum_wip.lean`):
  1. **Part (i) inner-sum — `rawExchange_membershipCount_mass`:** for a deck `d`
     and count `c`, the *total mass of the raw exchange into the `c`-fiber* equals
     the BL transition probability:
     `Σ_{m : membershipCount m = c} Dist.mass (rawExchangeMembership d) m
        = (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat)
          / (transitionDenominator 99 50 25 : Rat)`.
     **Step (a) is now done** by the 53rd-session `uniformPushforward_pointMass`
     (`e0b6ebe`): since `rawExchangeMembership d = (GSR.uniformDist
     exchangeChoice).map (newMembership d ·)` (its own def), the point mass at `m`
     is `(1/#exchangeChoice) · #{j : exchangeChoice | newMembership d (j as (L,R)) =
     m}` — **no `.map`-on-`Dist` construction, no Finsupp bookkeeping** (the 52nd
     session's `StdSimplex.map`/`Finsupp.mapDomain` route is superseded).
     **The concrete-exchange instance is now also in the library:**
     `rawExchangeMembership_pointMass` (`Shufflemath/CommanderA3ExchangePushforward.lean`,
     `0bf218a`) applies that general lemma to `rawExchangeMembership d`'s own `.map`
     def (`dsimp [rawExchangeMembership]; apply uniformPushforward_pointMass (fun c =>
     newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)) m`) — the
     exchange's point mass at `m` is `(1/#exchangeChoice) · #{j : newMembership d
     j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2) = m}`.
     What remains: (b) fiber-sum → preimage-sum, i.e.
     `Σ_{m : count m = c} #{j : F j = m} = #{j : count (F j) = c}` (the double-count
     over the exchange choices, where `F j = newMembership d (j as (L,R))` and
     `count (F j) = (newLeftCards d j ∩ leftOrigSet).card` via
     `membershipCount_newMembership`); (c)+(d) that preimage count =
     `transitionNumerator` via the `exchangeChoice ≃ leftChoices ×ˢ rightChoices`
     bridge + `newLeftCount_eq_transitionNumerator`; (e) normalize by
     `exchangeChoice_card_eq_transitionDenominator` (`#exchangeChoice =
     transitionDenominator`).
     **On (b) — the double-count (54th session, updated):** the 53rd session thought
     no "sigma card = sum of fiber cards" lemma existed, but **it does —
     `Fintype.card_sigma`** (a `@[simp]` lemma, `Data/Fintype/Defs.lean:161`:
     `Fintype.card (Σ i, α i) = ∑ i, Fintype.card (α i)`; the 53rd grep only searched
     `Basic.lean`, which is why it was missed).  So the fiber-product route is:
     `Fintype.card {x // f x ∈ S} = Fintype.card (Σ (m : ↥S), {x // f x = m.val})`
     (via the `Equiv` `toF ⟨x,hx⟩ = ⟨⟨f x,hx⟩, ⟨x,rfl⟩⟩` / `invF ⟨m,x⟩ = ⟨x.1, by…⟩`),
     then `rw [Fintype.card_sigma]`.  **The ONLY remaining blocker** is the `right_inv`
     second component, which is an **`HEq (≍)`** between two *propositionally*-equal
     fiber types (`{y // f y = f (x.1)}` vs `{y // f y = m.val}`); `Subtype.ext rfl`
     (an `Eq`) does not typecheck.  Two next paths, in preference order: (i) make that
     second component an `Eq` by first transporting it into a common fiber type (use
     `x.2 : f (x.1) = m.val`), then `rfl`; or (ii) **avoid the sigma/HEq entirely with
     `Finset.card_biUnion`** (exists — used in `Slice.lean:152`): write the preimage as
     the disjoint `biUnion` of the fibers `F m = univ.filter (f · = m)` over `m ∈ S` and
     use `Finset.card_biUnion` + `Finset.sum_subtype_eq_sum_filter` (both exist).  Full
     detail + the exact last-compiling probe: `.pi-glla/53_fiberSum_wip.lean` (54th section).
     **Concrete next step:** prove `rawExchange_membershipCount_mass` in
     `CommanderMembershipExchange.lean` = `rawExchangeMembership_pointMass` (the
     point-mass term) + the (b) fiber-product double-count + the (c)–(e) count
     bridges (`membershipCount_newMembership` → the `exchangeChoice ≃ leftChoices ×ˢ
     rightChoices` equiv → `newLeftCount_eq_transitionNumerator` →
     `exchangeChoice_card_eq_transitionDenominator`).
  2. **Part (i) fiber-average collapse:** the fiber-average over the project fiber of
     `x` of the (deck-independent) inner-sum is unchanged (`newLeftCount_deckIndependent`
     + `project_count`), giving `rawExchangeMembership_count` =
     `commanderExchange25_countMass` (the count-level equality).
  3. **Combine part (i) + part (ii):** for `m` in the `c`-fiber, `μ_x m` =
     (part (i) count mass at `c`) / `#(c`-fiber`)`, where the divisor is
     `membershipFiber_card`. This equals `hMembershipExchange_rhs_mass` at `(x, m)`,
     so the kernel equality `hMembershipExchange` follows by `FiniteKernel.ext`
     (pointwise in `x`, `m`).
  4. **Instantiate** `two_physical_perfect_exchanges_uniform_of_counts` with
     `hMembershipExchange` discharged, closing F3.

Prior fiber-level milestones, all still in the library:
- **`rawExchangeMembership_conjugate`** (`Shufflemath/CommanderPhysicalExchange.lean`,
  `commit 6a45608`): the **distribution-level** kernel equivariance
  `rawExchangeMembership (d.trans g) = (rawExchangeMembership d).map
  (relabelMembership (g : Fin 99 → Fin 99) g.bijective)` (the exchange membership
  law is equivariant under the deck-relabeling group). Its proof (right after the
  `rawExchangeMembership` def) used `Convexity.StdSimplex.map_map` + `funext` + the
  pointwise `newMembership_conjugate`.
- **`hMembershipExchange_lhs_reduces`** (`Shufflemath/CommanderPhysicalExchange.lean`):
  the premise's LHS reduces to
  `comp (fiberLaw project project_surjective) rawExchangeMembership`, i.e. the
  post-exchange membership law `μ_x = (·) x`.
- **`fiberLaw_invariant_underFiberEquiv`**
  (`Shufflemath/CommanderMembershipExchange.lean`, `commit 7cbc3e6`): the
  **general** fiber-level invariance — the uniform project-fiber law
  `fiberLaw observe h x` is fixed by any equiv `e` of the fiber space that commutes
  with the observation (`∀ b, observe (e b) = observe b`), because `e` permutes the
  fiber `{ b | observe b = x }` onto itself. Proved via `map_equiv_mass`
  (`Dist.mass = .weights`) + `fiberLaw_mass`. This is the distributional "uniform is
  invariant under the fiber's symmetry group" fact — the invariance input to
  `distUniform_ofInvariantTransitive`.

**[50th session — SUPERSEDED by the 51st-session resume above; kept for the assembly
detail.]** The
SPECIFIC post-exchange membership-law invariance `μ_x.map (relabelMembership_equiv f hf) = μ_x`
for `μ_x = comp (FiberDisintegration.fiberLaw project project_surjective)
rawExchangeMembership x` is now **DONE (50th session, `67a4efc`)** — committed in
`Shufflemath/CommanderMembershipExchange.lean` as `mu_x_map_invariance`, assembled from
`deckRelabel` (the `Equiv Deck Deck` form of `d ↦ d.trans g`), `h6_fiberLaw_fixed`, and
`comp_L_detM_eq_comp_detE_L` (the 7-step kernel-monad calc; `apply_deterministic_eq_map`
`a9839fd` supplies the monad unit). **Next: the A3 capstone** — feed `mu_x_map_invariance`
+ `distUniform_ofInvariantTransitive` to show the LHS law is group-uniform (part (i)), then
prove the LHS=RHS equality (part (iii)) to close `hMembershipExchange`. (The invariance lives
in `CommanderMembershipExchange.lean`, not the blueprint's `CommanderPhysicalExchange.lean`;
it compiles there with `Equiv.trans`/`Equiv.symm`/`Equiv.coe_ofBijective` spelled explicitly, so
the blueprint's `.trans` dot-notation concern did not materialize.)
With the deck-equiv `e : Deck ≃ Deck` given by `e d = d.trans f` (a bijection), the
proof composes pieces now in the library:
  1. `(fiberLaw project h x).map e = fiberLaw project h x` by
     **`fiberLaw_invariant_underFiberEquiv`**, needing `hE : ∀ d, project (d.trans f) = project d`;
  2. `rawExchangeMembership (d.trans f) = (rawExchangeMembership d).map
     (relabelMembership f f.bijective)` by **`rawExchangeMembership_conjugate`**;
  3. push the exchange through the equiv: the `.map`/`.join`/`.apply`/`comp`
     associativity (in `Shufflemath/Finite.lean`: `apply_comp`, `comp_assoc`).
**[50th session] The full 7-step `calc` assembly is now DONE (committed `67a4efc` as `mu_x_map_invariance` in `CommanderMembershipExchange.lean`)** — it was BLUEPRINTED at
`.pi-glla/47b1_membership_invariance_wip.lean` (out of the build graph). It composes:
`μ_x.map M = apply μ (det M) [apply_deterministic_eq_map] = apply (apply (K x) L) (det M)
= apply (K x) (comp L (det M)) [apply_comp] = apply (K x) (comp (det e) L)
[comp_L_Mk_eq_comp_E_L, via rawExchangeMembership_conjugate] = apply (apply (K x) (det e)) L
[apply_comp] = apply (K x) L [step 1: fiberLaw_invariant_underFiberEquiv + project_conjugate]
= μ_x`. **Both lemmas below are now proven** (`apply_deterministic_eq_map` = `a9839fd`; `comp_L_Mk_eq_comp_E_L` = `comp_L_detM_eq_comp_detE_L` in `67a4efc`); the `calc` is committed:
  (1) **`apply_deterministic_eq_map`** (put in `Finite.lean`): `apply μ (deterministic f) =
      μ.map f` — `ext y` + the Finsupp pushforward-sum simp set; the 47b1 probe already
      reduced the LHS to `Σ_{a, f a = y} μ a`, the only open step is not over-reducing the
      RHS `μ.map f` (drop `Convexity.StdSimplex.map` from the set, then close by the `map`
      pushforward def).
  (2) **`comp_L_Mk_eq_comp_E_L`**: `comp L (det M) = comp (det (fun d => d.trans g)) L`,
      by `funext d` + `rawExchangeMembership_conjugate` (the Equiv's toFun IS
      `relabelMembership g g.bijective`).
  A `deckTransEquiv g : Equiv Deck Deck` (the `Equiv` form of `fun d => d.trans g`, via
  `Equiv.ofBijective` + `Equiv.trans_assoc`/`trans_self_symm`/`trans_one`) is needed because
  `fiberLaw_invariant_underFiberEquiv` takes an `Equiv`, not a bare function. NOTE: integrate
  into `CommanderPhysicalExchange.lean` (`.trans`/`.symm` on `Deck` resolve there; an isolated
  probe fails on `Equiv.trans` dot-notation without the full import context).
*Historical 47th-session reduction of `hE` (superseded — `hE` is now proven by
`project_conjugate` above; kept for reference):* the `hE` premise
`f '' leftOrigSet = leftOrigSet` (a deck map preserving the originally-left set, so
it commutes with `project`) — since `project d = ⟨leftOriginalCount d - 1, _⟩`, this
reduces (Subtype `ext` on the proof component) to
**`leftOriginalCount (d.trans f) = leftOriginalCount d`**. A near-complete recipe
is saved at `.pi-glla/47ak_leftOriginalCount_wip.lean`: reindex the 50 left positions
`S := (Finset.univ : Finset (Fin 50))` to `leftOrigSet` via
`hUnivImg : S.image leftPosition = leftOrigSet`; a left-position-preserving injective
map keeps the `p := (fun x => (d x).val < 50)`-filtered-card invariant (`hCard`, via
`Finset.filter_image` + `Finset.card_image_of_injective` + `Finset.image_comp`).
**The `Fin 99` proof-component equality in `hUnivImg` is SOLVED**
(`apply Fin.ext; simp only [leftPosition]` — same as `leftPosition_injective`).
**The REAL remaining blocker (verified 2026-11-20)** is a Mathlib API mismatch:
`Finset.filter p s` / `Finset.image f s` are *function-first* (f/p first, Finset 2nd);
the theorems `filter_image`/`image_comp`/`card_image_of_injective` are stated in *dot
notation* (`s.image f`, `s.filter p`); and `Finset.univ.filter p` (as in the
`leftOriginalCount` def) reduces to a *set-builder* `#{i | p i}`, so a naive
`change` to the `Finset.filter (P ∘ f) S` form does **not** fire.  **Cleanest fix**:
prove `hLHS`/`hRHS` as *set-card* equalities `# {x ∈ leftOrigSet | P x}` via
`Finset.card_congr` + `leftOrigSet_eq_image` (avoids the filter/set-builder mismatch
entirely), or bridge `#{i | p i} ↔ Finset.filter p S` explicitly.  **Deadline
Wed 2026-11-24 23:59:59 EST.** *(Superseded 2026-11-21: the true wall was a `whnf`
explosion on the `Fin 99` filter form of `leftOrigSet`, not a filter/set-builder API
mismatch — see the 2026-11-21 note below.)*

**Updated 2026-11-21 (48th session) — the `hGpart` partition-preservation lemma
now COMPILES; only the final assembly to `leftOriginalCount_conjugate` remains.**
The blocker above was reframed: the real `whnf` wall is that the `Fin 99` *filter*
form of `leftOrigSet` (`(Finset.univ : Fin 99).filter (·.val < 50)`) whnf-explodes
on `.image g` operations (`rw`/`rcases`/`Finset.mem_image.mpr`) when `g : Equiv.Perm
(Fin 99)` (200000-heartbeat `whnf` timeouts, even after raising the ceiling). The
*light `Fin 50` image* form `L50 := (Finset.univ : Fin 50).image leftPosition` does
not. Routing every heavy step through `L50` (a `simp` of `leftOrigSet_eq_L50` / the
L50-form `hL` is cheap; the direct `leftOrigSet` is not) makes the **partition-
preservation lemma compile**:
`hGpart (d g) (hgL : (leftOrigSet).image g = leftOrigSet) (y) : y ∈ leftOrigSet ↔ g y ∈ leftOrigSet`
(both directions: → forms the image membership via `Finset.mem_image.mpr`, ← builds
the image membership by `simp` of the L50-form equality then decomposes the explicit
existential + `g.injective`). Verified this session: a standalone module with
`L50` + `leftOrigSet_eq_L50` + `hgL_L50` + `hGpart_fwd`/`hGpart_bwd`/`hGpart` builds
clean (3205 jobs, exit 0). **Recipe saved at `.pi-glla/47ao_hGpart_wip.lean`**
(copy it to `Shufflemath/_ProbeX.lean` and `lake build` to re-verify). **`hGpart` is now PROVEN and COMMITTED (49th session, `d6dc0dc`):** the
`.pi-glla/47ao_hGpart_wip.lean` module (`L50` + `leftOrigSet_eq_L50` + `hgL_L50` +
`hGf`/`hGb`/`hGpart`) compiles clean. Copy it to `Shufflemath/_ProbeX.lean` to reuse;
`leftCards_conjugate` and the `ext`-based `hInt` are also assembled there.

**Updated 2026-11-24 (49th session) — the FULL assembly is blocked by a GENUINE
whnf explosion, NOT a tunable threshold.** The `hGpart` directions (`hGf`/`hGb`,
both L50-routed) compile standalone and the → direction of the set-equality
`hInt : (leftCards d).image g ∩ leftOrigSet = (leftCards d ∩ leftOrigSet).image g`
compiles. But the ← direction of `hInt` (the branch that calls `hGf` to turn
`y ∈ leftOrigSet` into `x = g y ∈ leftOrigSet`) **times out at `whnf` even with a
local `set_option maxHeartbeats 2000000` (10× the default)** — so it is a real
combinatorial blowup in `whnf` of the `L50` image
(`(Finset.univ : Fin 50).image leftPosition`) nested inside `.image g` and cast
through `hL : L50.image g = L50`, *in the deep `hInt` context* — not a threshold
that a heartbeat raise can clear (and the → vs ← asymmetry is context-dependent,
so more L50-image tweaking is unlikely to close it). Closest assembled form saved at
`.pi-glla/47ax_leftOriginalCount_wip.lean`. **This is a PERFORMANCE wall (the
statement is correct and all sub-lemmas compile individually); the fix is a
representation change, not more force.** Next-session strategies, in order of
promise: **(a) frameshift to `Fin 50`** — prove the card equality on the 50-element
*index* set (both `leftCards d` and `leftOrigSet` are 50-card `Fin 50` images) with
`g` as a `Fin 50` bijection, avoiding the `Fin 99` image `whnf` entirely; **(b)**
prove `hInt` as its *own* compiled theorem (isolating the one heavy `whnf`) so the
main proof only references it; **(c)** introduce a *light explicit* Finset for the
50 left positions (not via `.image`) and prove `hGpart`/`hInt` against it, bridging
back to the library `leftOrigSet` via `leftOrigSet_eq_L50`. **Deadline Wed
2026-11-24 23:59:59 EST.**

**Earlier (2026-11-22, part (ii) group action):**
**Updated:** 2026-11-22 (A3 **part (ii) group action** session) — the
**deck-symmetry group action on memberships** is now in the main library
(`Shufflemath/CommanderMembershipOrbits.lean`, commit `89eb06c`):
`relabelMembership f hf M` (apply a bijective deck map `f` to a 50-card
membership), `relabelMembership_count` (a deck map fixing the left pile as a
set preserves the membership count), and `relabelMembership_equiv
: Membership ≃ Membership` (the relabel is a **bijection** on the membership
fiber — injective + surjective — hence an `Equiv`). This is the `E
: Set (Equiv Membership)` element for `distUniform_ofInvariantTransitive`.
**This is the assembly-plan part (ii) path** (orbitMap transitivity +
`newLeftCards_conjugate` equivariance → invariance → within-fiber uniformity),
which is the *correct* next route to the A3 capstone `hMembershipExchange` —
prefer it over the older 25-overlap-surjectivity detour (still valid, still in
below, but not on this critical path). **Next concrete action: the invariance
lemma** — the LHS post-exchange membership distribution is invariant under
`relabelMembership_equiv` (via `newLeftCards_conjugate` + `map_equiv_mass`);
see "Exactly where to resume" → "47th session (continued)" item 3.

**Updated:** 2026-11-22 (A3 **count kernel** session) — the F3 A3 **count half is
now in the main library**: `Shufflemath/CommanderA3Kernel.lean` proves
`newLeftCount_eq_transitionNumerator` (the post-exchange count of `(L,R)` pairs
= `transitionNumerator 99 50 25 (leftOriginalCount d) n`) and
`newLeftCount_deckIndependent` (same source count ⇒ same post-exchange count
distribution) — the fiber-average collapse for the `rawExchangeMembership_count`
LHS, the exact "remaining step" in the `hMembershipExchange` assembly plan
(commit `8e4106d`, in the build list + verify script; 24 modules + 37 tests
green). Also done this stretch: the 47y **existence halves for BOTH piles**
(`newLeftCards_exists` / `newRightCards_exists` in `CommanderPhysicalExchange`).
**Next: F3 item 3 step 3 (point mass at the fiber), then A3's *measure* half,
then the `hMembershipExchange` capstone** — see the F3 item 3 section below for
the full resume detail. **Deadline Wed 2026-11-24 23:59:59 EST.**

**Earlier (46th/47th sessions):** the **T4 counting core** (`card_biUnion_pd` +
`yMoves_card_eq_sum` `ae26aed`, capstone `yMoves_card_eq_transitionNumerator`
`#yMoves = transitionNumerator N m r k x y` `1cd40b0`, `Shufflemath/FiniteDeck/BLRefinement.lean`)
and the T4 **measure** half's count-fiber machinery (`countFiberMemb` `Finset` over
`Membership`), `countFiberMemb_equiv` (marked/unmarked-split bijection),
`countFiberMemb_card` (hypergeometric), `countFiberMemb_nonempty`,
`yMoves_uniformOnFiber`, `fiberPushforward_count`, and the capstone
`uniformFiber_intertwines` (commit `19d964d`). The T4 projection was already
in the library (`countInPile` L426 = `⟨countInPileVal, countInPile_admissible⟩`
+ `countInPile_val`/`_countFiber`), so the 46th note's projection item is done.
**New resume point: the Commander F3 A3 discharge by instantiation at
(99, 50, 50, 25)** (in `Shufflemath/CommanderMembershipExchange.lean`). **47b/47c:
the A3 *RHS* is committed in both its forms** — `commanderExchange25_mass` (the
`commanderExchange25` transition bridge), `hMembershipExchange_rhs_mass` (pointwise
mass of `comp commanderExchange25 membershipLift`, `c276eda`), and
`commanderExchange25_countMass` (the count-level companion: the mass at `(x, c)`
of `comp commanderExchange25 (det commanderLeftCount)` is
`transitionWeight 99 50 25 (count x) c` for feasible `c`, `a7fabd3`). **47e:**
`commanderDetailedBalance` (`e84fe7e`) and
`commanderStationary_is_stationary` + `commanderStationaryRun` (`f7976d2`) —
the reversibility and hypergeometric fixed-point A3 ingredients. **47g:** the
25-overlap preservation lemmas (`newMembership_overlap_25` et al., `9b5a45a`) in
`CommanderPhysicalExchange.lean`. **47v (this session): the F3 A3 transition kernel is
PROVED in both forms** (0 `sorry`). (a) `_Probe47v.transitionNumerator_eq_fiberProduct
(d : Deck) (n : Nat) : transitionNumerator 99 50 25 (leftOriginalCount d) n =
# {(L, R) : (leftOriginalCount d - markedInLeft d L) + markedInRight d R = n}` — the
marked/const-sub form, built from `fiberSum_extendsTo_range26` (the range-26 domain
extension: the marked-left image ⊆ range 26, so the image-fiber sum equals the range-26
sum) and `fiberSummand_eq_transitionIntegrand` (each range-26 fiber summand equals the
Bernoulli-Laplace transition integrand). (b) `_Probe47u.perDeckBridge` (the physical
`newLeftCards`-count form) is a clean two-lemma composition: `newLeftOriginalCount_eq`
(physical → marked const-sub) ∘ the 47v kernel (marked → transition numerator). This
completes the 47j counting-kernel goal: the per-deck A3 count mass equals
`transitionWeight 99 50 25 (count x) n`. **Next: the physical membership-level mass
identity** (the "genuinely hard half") — start with the count-transition LHS
`comp (comp (fiberLaw project) rawExchangeMembership) (det membershipCount) =
comp commanderExchange25 (det commanderLeftCount)`** (a multi-lemma development;
see the 47f NEXT ACTION in "Exactly where to resume"). T3/T5 remain.)

**47x** (this session): **deck-independence, unique half** (`CommanderPhysicalExchange`)
— `leftPosCard_image_injective` / `rightPosCard_image_injective` (the selected-left /
selected-right card-set determines the selected positions, via `image_injective_eq` and
`d.injective.comp {left,right}Position_injective`) and `newLeftCards_leftPart_in_leftPile`
(the selected-left cards sit in the left pile). Together with 47i's
`newLeftCards_as_sdiff_union`, this makes the post-exchange membership
`(leftCards d \ Lc) ∪ Rc` a function of the source membership `leftCards d` (and its
complement = the right pile, since the deck is a permutation) and the chosen card-sets —
independent of the deck's position arrangement.

**47y (this session — the position↔card EXISTENCE half, BOTH piles done).**
`leftCardImage_has_preimage` and `rightCardImage_has_preimage` in `CommanderPhysicalExchange`:
for `A ⊆` (the left / right pile) with `A.card = 25`, there is exactly one 25-position-set
`L = (univ : Finset (Fin 50 | 49)).filter (fun p => (d ∘ {left,right}Position) p ∈ A)`
with `L.card = 25` and `L.image (d ∘ …Position) = A` (injective map → `card_image_of_injective`).
Combined with 47x's unique halves, 25-position-subsets **biject** with 25-card-subsets for
BOTH piles — the membership-level deck-independence the A3 kernel (`s50` × `t49`, both
`powersetCard 25`) needs. **Friction resolved:** the `let`-bound witness set is opaque to
`simp`/`dsimp`/`unfold` — fix is `change p ∈ (Finset.univ : Finset (Fin 50 | 49)).filter (fun p =>
f p ∈ A) at h` to expose the `.filter` before `simp only [Finset.mem_filter]` (note
`mem_filter` is `@[simp, grind =]` — grind-gated, so a bare `simp` won't fire it unless
listed); `Finset.subset` is a raw `∀` (use `hAsub hx`, NOT `.mpr`); `card_image_of_injective
(s) (H : Injective f)` takes the SET first, the injectivity second (function implicit). **Next:**
F3 item 3 step 3 — the point-mass statement: a uniform choice of 25 left positions × 25 right
positions (each `1 / (choose 50 25)·(choose 49 25)`) induces a uniform choice of the new left-
pile card-set, so the transition mass to a new membership depends only on the `|S∩T|` fiber
and not the deck arrangement — then the `hMembershipExchange` capstone discharging A3.

The
2026-11-15
review + arbitrary-finite-deck roadmap pivoted the build to the **G1–G4
generic finite-deck theory**, from which Commander A3 is a specialization.
**Done:** P0/Commit A (native_decide → `.symm`); **G1** complete
(`FiniteDeck/TwoPile`); **G2** core (`membershipCount = choose N m`, the four
fintype-card blocks, and BOTH fiber-restriction bijections `fiberRestrictL/R`
in `FiniteDeck/Fiber`); **G3** foundation (`ReachSet/Lset/Rset` + card lemmas
in `FiniteDeck/SubsetExchange`). **The G2/T1 fiber count**
(`#Fiber(A) = m!·(N-m)!`) is on the **transitive orbit-count route** (see the
`Fiber.lean` doc-comment): **`fibTransitive` is now PROVEN** — for any two
`m`-piles `A, B`, a `Perm (Fin N)` sends `A` onto `B`, glued from equicardinal
`Fintype.equivOfCardEq` bijections `A→B` and `Aᶜ→Bᶜ`, proved surjective
(2 cases) and hence bijective via `Finite.injective_iff_surjective`. **ALL
FOUR supporting fiber lemmas are now PROVEN:** `fibTransitive`,
**`fibersEqual`** (`#Fib(A)` is independent of `A`, from a `fibTransitive`-witness
fiber-bijection), **`leftImageIsMembership`** (every perm's sent pile is a valid
`m`-pile — the cover half of the fiber partition), and **`fibersUnique`** (a
perm has a unique sent pile — the disjointness half). **The G2/T1 capstone
`fiberCount`** (`(choose N m)·#Fib(A) = N!` ⟹ `#Fib(A) = m!·(N-m)!`) is the last
G2 lemma; its two assembly routes (Sigma-bijection vs Finset-fiber-partition —
the Finset route avoids the `Subtype.cast` wall that blocks the Sigma route)
and every gotcha are documented in the `Fiber.lean` doc-comment. **The next
concrete action is G3's `subsetExchangeCount`** (the `Finset.card_bij'` bijection
`ReachSet S ≃ Lset S × Rset S` giving `# ReachSet S = choose m k · choose (N-m) k`).
**F4.1 COMPLETE** (`17ffab6`) and
**F4.2 GSR product is now in the library** (`4e1b76f`): `gsrProductKernel`
(independent within-pile GSR riffles on the left and right piles, as a
`FiniteKernel` on the pile-list product) + `gsrLocal_preserves_pile` (a
within-pile GSR output holds exactly the pile's cards, via
`stableBuckets_set`). **F5 model-agnostic pieces landed** (`e203310`,
`ec68b71`): `ProtocolCertificate.costed_terminalTV_le` (a costed schedule's
terminal TV ≤ ideal-reference error + weighted perturbation budget — the
"sufficient TV bound" half of F5) and `Cost.protocolCost_nonneg` + the
`ActionKind` action alphabet (the "cost" half). **F3 item 3** is reduced to
the symbolic **fiber-counting lemma (CL)** `fiberSum p x y = choose(r,y)·
choose(N-r,m-y)·overlap_count (N m r k) x y`; the clean derivation
`(CL) + fiberSum_swap + fiberSum_eq (y x)` → `overlap_count (N m r k) x y =
transitionNumerator (N m r k) y x` is recorded in `ExchangeOverlap.lean`
(`ef93f8d`) along with this build's Finset API walls. Remaining: the general
(symbolic) CL, F3 item 4, the F4.3 `gsrProductKernel = distProduct` point-mass
connection (wall: `apply_mass_dom` needs a Fintype domain, but `idealShuffle`
is over the non-Fintype `List (Fin n)`), F4.5 full-deck terminal bound, and the
F5 full theorem / optimization quantifiers. `docs/lean_plan.md` is the
authority; `docs/qwen_unblock_nov12.md` has the routes. This is an
*operational handoff*. `lean_plan.md` is the authority for overall scope and
priority; `AGENTS.md` governs repository behavior.

## Standing rules for the agent reading this document (non-negotiable)

1. **Do not stop, ask, or end the session before Wed Nov 24 23:59:59 EST 2026.**
   (Deadline extended at the user's request: originally Thu Nov 12 22:27:06
   EST, then Wed Nov 18 23:59:59 EST, now Wed Nov 24 23:59:59 EST — the latest
   extension was given on the Nov 17 session.) This is a long autonomous build.
   You **will be compacted multiple times**; compaction is normal and is not
   a stopping signal.
   **"Do not stop" includes never presenting a status.** A "session summary",
   "state of the world", progress recap, or "here is where things stand" output
   **is a stop** (the user has flagged presenting one as a stop). Do not emit
   such a report at the end of a turn. The turn ends only by (a) the stuck
   protocol (rule 8) or (b) the deadline — never on a status update (rule 10).
   If you are tempted to summarize, instead take the next concrete proof
   action in the same turn.
2. **After every compaction, do exactly this, in order:**
   a. Read this document top to bottom, then `AGENTS.md` and
      `docs/lean_plan.md`.
   b. Run `git log --oneline -10` and `git status --short` in
      `/home/joncrall/code/shufflemath`.
   c. Run the targeted `lake build` commands listed in `AGENTS.md` to confirm
      the tree is green (if red, fix before anything else).
   d. Resume at the current F2 intervention in this file and the next
      unchecked item in `docs/lean_plan.md`.
3. **Small batches only.** One batch = 1–3 related lemmas/theorems in one
   file. Each batch must end with: targeted `lake build` green → `git add`
   + `git commit`. Never let the working tree carry more than one batch of
   uncommitted work.
4. **Commit trailer (exact):** one `Co-authored-by` trailer naming the
   **current** model only (see `AGENTS.md`; never the October session's model
   name). Subject line: short imperative, e.g.
   `Add fiber count over membership sets`.
5. **Every commit must build.** The affected modules must pass `lake build`
   before you commit. `./dev/verify_next_phase.sh` must pass at the end of
   each tranche (F1, F2, …) in `docs/lean_plan.md`. The legacy
   `./dev/verify.sh` (which runs `lake update`) is **not** the verification
   path.
6. **Keep this document updated.** After each commit, tick the item in
   "Exactly where to resume", update `docs/lean_plan.md`, and adjust the next
   action. This file is the only thing a compacted/fresh agent can trust; the
   conversation is not.
7. **Do not stop early even if the current tranche is all done.** Fall
   through to the next item in `docs/lean_plan.md` (F2, F3, F4, F5), then to
   the verification pass (re-run `./dev/verify_next_phase.sh`, audit
   docstrings, re-check regression values), until the deadline.
8. **Stuck protocol.** If a single proof resists ~2 build iterations, write a
   `-- TODO(proof): <sketch>` comment at the exact location, commit what
   builds, move to the next item, and return later. Never leave a broken
   build, never leave a `sorry` or `admit`.
9. **Taste rules:** exact `Rat` arithmetic only; no
   `set_option maxHeartbeats 0`; no floating point in proofs; docstring on
   every nontrivial theorem; no sweeping refactors of existing names.
10. **No intermediate status reports — commit and move on.** Do not write
   progress/status/"ready to continue" summaries to the user; those look like
   stopping and tempt the session to end. The safety mechanism is a **commit**
   plus continuing to the next proof step in the same turn. After each batch:
   targeted `lake build` green → `git add` + `git commit` → immediately begin
   the next item. A turn ends only on the stuck-protocol (rule 8) or the
   deadline, never on a status update.

## Lean 4 module-system migration (done this session)

Every library `.lean` file (24 `Shufflemath/*` + the `Shufflemath.lean`
aggregator) and `dev/BernoulliLaplacePairOptimality.lean` were migrated from the
old `import`-only style to Lean 4.34's **`module`** system. `lakefile.lean` was
left as-is (Lake DSL files stay plain `import Lake`). The whole graph is
atomic: a `module` file cannot `import` a non-`module` file in the same
package, so all-or-nothing was required.

The working per-file recipe (do NOT deviate):

* Header: `module` on its own line, blank line, then imports.
* **Every** `import X` → **`public import X`**. A plain `import` makes the name
  "imported privately" and it will not resolve inside an `@[expose]` section
  (the compiler says *"consider adding `public import …`"*).
* Wrap the body in `@[expose] public section … end`. `@[expose]` (not bare
  `public`) is what makes declarations **transparent across the module
  boundary** — bare `public` exports by name but leaves them **opaque**
  (consumer `rfl`/`simp`/`dsimp` cannot unfold them, which breaks this codebase's
  heavy `simp [ … ]`/`change` usage).
* **No `private` declarations inside an `@[expose]` section.** `@[expose]` +
  `private` makes the decl vanish (even to later decls in the same namespace).
  The 88 `private` decls were converted to plain `def`/`theorem`/`abbrev`/
  `instance`/`lemma` (now exposed by the section).
* Files that previously relied on Lean 4's **implicit end-of-file scope
  close** (no explicit `end`, e.g. `BernoulliLaplaceCommanderBridge`,
  `BernoulliLaplaceFiber`) must NOT get an appended bare `end` — let EOF close
  the section. Files that already had balanced explicit `end`s keep the one
  appended `end` that closes the section.
* **`native_decide` needs a dual import**: files whose `native_decide` proves a
  fact about another module's `def` (`BernoulliLaplace` → `TotalVariation`'s
  `vectorTV`; `CommanderFiberWitness` → `CommanderPermutation`'s `project`;
  `dev/BernoulliLaplacePairOptimality` → `BernoulliLaplace`) need both
  `public import M` *and* `public meta import M` for that module `M`. The
  term-level `public import` keeps `Finset.range`/`Rat.addCommMonoid`/etc.
  usable in computable defs; the `meta import` lets the generated `_native`
  code reference the target. A lone `meta import` demotes the re-exported
  Mathlib names to meta-only and breaks the computable defs.

Verified: `./dev/verify_next_phase.sh` (builds the next-phase overlay + 35
Python tests, OK) and `./dev/verify_next_phase.sh --pair` (the 2,401-pair
certificate via `lake env lean dev/…`, EXIT 0).

## Current F2 intervention (2026-11-11)

**Read [`f2_fiberlaw_unblock.md`](f2_fiberlaw_unblock.md) before attempting
`localLift_mass` again.** The existing generic
`FiberDisintegration.fiberLaw membership membership_surjective` supplies the
perfect-local kernel *with a pointwise mass theorem already proved*. Use it
instead of re-deriving the pushforward of `uniformDist` through `Subtype.val`.
This is a proposed proof strategy, not a completed Lean result; compile each
step. The longer `mapDomain`/`DecidableEq` diagnosis below records prior
attempts, but is no longer the recommended route.

`./dev/verify_next_phase.sh` now lists both currently active modules
`Shufflemath.CommanderMembershipKernels` and
`Shufflemath.CommanderPhysicalExchange`; retain them when extending the script.

## Exactly where to resume

### 47th session (continued) — A3 count kernel + 50+49 partition fact (done; **superseded by the top resume section**)

> The actual current resume point is the **top** "Exactly where to resume" section
> above (the specific `μ_x` post-exchange membership-law invariance, whose one missing
> piece is `leftOriginalCount (d.trans f) = leftOriginalCount d`). Everything in this
> 47th-session-continued block is now **done** (A3 count kernel, 50+49 partition, the
> two part-(ii) equivariances, and the general `fiberLaw_invariant_underFiberEquiv`).

Two milestones landed this continuation of the 47th session:

1. **The A3 count kernel is DONE** (`48e601b`, `Shufflemath/CommanderA3Count.lean`).
   `a3CountKernel` proves the pointwise count identity: the fiber-averaged
   post-exchange membership count equals the `commanderExchange25` transition
   (the A3 counting half, part (i)). The LHS core `rawExchangeMembership_count`
   is a *pointwise* identity (the 47s per-deck bridge `newLeftOriginalCount_eq`
   is the engine: each deck's post-exchange original-card count is exactly
   `transitionNumerator`, the 47v kernel proving numerator = `transitionWeight`
   = `commanderTransitionWeight`). The fiber average is then a plain `simp` +
   `map_mul`. `./dev/verify_next_phase.sh` passes 37 tests.

2. **The 50+49 deck-position partition is proven** (`_Probe47ad.lean`, targeted
   build green): `leftCards_union_rightCards_univ` (`leftCards d ∪ rightCards d
   = univ`), `leftCards_disjoint_rightCards'`, and `univ_sdiff_leftCards_eq_rightCards`
   (`univ \ leftCards = rightCards`). **Key finding:** the per-element
   `Equiv.Perm (Fin 99)` surjectivity route (one-element-at-a-time onto the
   image) triggers **WHNF timeouts** even at high heartbeats; the **cardinality
   route** (subset + equal size via `card_image_of_injective` +
   `card_union_of_disjoint` + `card_sdiff_of_disjoint`) is the robust one. Keep
   that recipe for the next lemmas.

3. **The deck-symmetry group action on memberships is committed** (item in
   `Shufflemath/CommanderMembershipOrbits.lean`, `89eb06c`, build green at
   3208 jobs): `relabelMembership f hf M := ⟨M.1.image f, card-preserved⟩` (apply
   a bijective deck map to the 50-card set), `relabelMembership_count` (a deck
   map fixing the left pile as a set preserves `membershipCount`),
   `relabelMembership_injective` / `_surjective` (the relabel is a bijection on
   the membership fiber), and `relabelMembership_equiv : Membership ≃ Membership`
   (via `Equiv.ofBijective`). **This is the `E` for part (ii).** The transitivity
   witness `membershipFiber_transitive` (already in this file) supplies, for any
   two same-count `m m'`, a bijective `f` with `f '' leftOrigSet = leftOrigSet`
   and `f '' m.1 = m'.1`; combining it with `relabelMembership_equiv` gives
   `∃ e ∈ E, e m = m'` — the `hTrans` for `distUniform_ofInvariantTransitive`.

**Next concrete action — the invariance lemma (part (ii), step A3)**,
`postExchangeMembership_invariant` (new file `Shufflemath/CommanderA3Kernel.lean`
or a fresh `Shufflemath/CommanderMembershipInvariance.lean`): for a fixed source
macro state `x`, the LHS post-exchange membership distribution
`μ_x := comp (fiberLaw project project_surjective) rawExchangeMembership x` is
**invariant under every `relabelMembership_equiv f hf`**, i.e.
`μ_x.map (relabelMembership_equiv f hf) = μ_x`, for any bijective deck map `f`.
Proof: push the equivariance `newLeftCards_conjugate` (`newLeftCards (d.trans f) L R
= (newLeftCards d L R).image f`) through the fiber average — the relabel `f`
permutes the deck-fiber and the `(L,R)`-choice space by an `Equiv`, so
`map_equiv_mass` carries the pushed kernel to an equal one. Concretely you need
(1) the deck-fiber bijection `d ↦ d.trans f` over the source count-fiber (it is
involutive/bijective), and (2) the `(L,R)`-choice space is carried to itself by
`f` (or shown mass-preserving). **Build the count-level bridge first** (the
`membershipCount` is preserved by `relabelMembership_count`, already proved),
then the full kernel equality. Once invariance is in, part (ii) = apply
`distUniform_ofInvariantTransitive` with `S =` the `c`-fiber, `E =`
`{relabelMembership_equiv f hf | hf, hfL}`, `hTrans` from
`membershipFiber_transitive`, to get `mass μ_x m = 1 / #fiber` for `m` in the
`c`-fiber; that equals the RHS `hMembershipExchange_rhs_mass` and discharges
`hMembershipExchange`.

**Alternate (older) next action — the surjectivity onto the 25-overlap fiber**,
`newMembership_surjective_onto_fiber (d) (T) (hT : (membership d).1 ∩ T.1).card = 25
: ∃ L (hL : L.card = 25) R (hR : R.card = 25), newMembership d L hL R hR = T`.
**Place it in `Shufflemath/CommanderMembershipExchange.lean`** (or
`CommanderPhysicalExchange.lean`), NOT a `_Probe*` scratch file: in a scratch file
the bare `Membership` resolves to **Mathlib's `Membership` typeclass**
(`outParam (Type u) → …`) instead of the `Shufflemath` abbrev, and
`Shufflemath.Membership` is reported unknown (an `@[expose]`/import-order subtlety).
In `CommanderMembershipExchange.lean` the bare `Membership` resolves correctly
(it already uses `∑ m : Membership, …`). The body (developed and checked piece
by piece this session — it only failed on that name-resolution point, every
sub-lemma built green):

```lean
theorem newMembership_surjective_onto_fiber (d : Deck) (T : Membership)
    (hT : ((membership d).1 ∩ T.1).card = 25) :
    ∃ (L : Finset (Fin 50)) (hL : L.card = 25) (R : Finset (Fin 49))
      (hR : R.card = 25), newMembership d L hL R hR = T := by
  classical
  have hm1 : (membership d).1 = leftCards d := membership_leftCards d
  set A := T.1 ∩ leftCards d
  have hAcard : A.card = 25 := by
    have h : (membership d).1 ∩ T.1 = T.1 ∩ (membership d).1 := Finset.inter_comm _ _
    rw [← h, hm1] at hT
    simpa using hT
  have hAsub : A ⊆ leftCards d := Finset.inter_subset_right _ _
  set Lsel := leftCards d \ A
  have hLsub : Lsel ⊆ leftCards d := Finset.sdiff_subset_left _ _
  have hLcard : Lsel.card = 25 := by
    rw [Finset.card_sdiff_of_subset hAsub, leftCards_card d, hAcard]
    norm_num
  obtain ⟨L, hL, hLimg⟩ : ∃ L : Finset (Fin 50), L.card = 25 ∧
      L.image (fun l => d (leftPosition l)) = Lsel :=
    leftCardImage_has_preimage d Lsel hLsub hLcard
  set B := T.1 ∩ rightCards d
  have hBsub : B ⊆ rightCards d := Finset.inter_subset_right _ _
  have hBcard : B.card = 25 := by
    unfold B
    have hU : leftCards d ∪ rightCards d = (Finset.univ : Finset (Fin 99)) :=
      leftCards_union_rightCards_univ d
    have hdisj : Disjoint (leftCards d) (rightCards d) := leftCards_disjoint_rightCards' d
    have hTsplit : T.1 = (T.1 ∩ leftCards d) ∪ (T.1 ∩ rightCards d) := by
      rw [← Finset.inter_univ, hU, Finset.inter_union_distrib_left]
    have hdisjT : Disjoint (T.1 ∩ leftCards d) (T.1 ∩ rightCards d) := by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.ext, iff_self]
      intro x
      by_contra hx
      simp only [Finset.mem_inter] at hx ⊢
      have hmem : x ∈ leftCards d ∩ rightCards d := Finset.mem_inter.mpr ⟨hx.1.2, hx.2.2⟩
      simpa [Finset.disjoint_iff_inter_eq_empty.mp hdisj] using hmem
    have hsum : (T.1 ∩ leftCards d).card + (T.1 ∩ rightCards d).card = T.1.card := by
      rw [← hTsplit, Finset.card_union_of_disjoint hdisjT]
    rw [hAcard, T.2] at hsum
    omega
  obtain ⟨R, hR, hRimg⟩ : ∃ R : Finset (Fin 49), R.card = 25 ∧
      R.image (fun r => d (rightPosition r)) = B :=
    rightCardImage_has_preimage d B (by simpa [rightCards] using hBsub) hBcard
  refine ⟨L, hL, R, hR, ?_⟩
  subst hLimg hRimg
  have hnew : newLeftCards d L R = T.1 := by
    have hAunion : leftCards d \ (leftCards d \ A) = A := by
      rw [Finset.sdiff_sdiff, Finset.inter_sdiff_eq_empty _ _]
      simpa using hAsub
    have hAB : A ∪ B = T.1 := by
      unfold A B
      have hU : leftCards d ∪ rightCards d = (Finset.univ : Finset (Fin 99)) :=
        leftCards_union_rightCards_univ d
      rw [Finset.union_inter_distrib_left, hU, Finset.inter_univ]
    calc
      newLeftCards d L R = (leftCards d \ L.image (fun l => d (leftPosition l))) ∪
          R.image (fun r => d (rightPosition r)) :=
        newLeftCards_as_sdiff_union d L R
      _ = A ∪ B := by simpa [hLimg, hRimg, hAunion]
      _ = T.1 := hAB
  unfold newMembership
  subst hnew
  exact Subtype.ext (by rfl)
```

**Note:** `leftCards_union_rightCards_univ`, `leftCards_disjoint_rightCards'`, and
`univ_sdiff_leftCards_eq_rightCards` live in `_Probe47ad.lean` — if the
surjectivity goes into `CommanderMembershipExchange.lean`, first promote those
three partition lemmas into a named module (e.g. `CommanderPhysicalExchange.lean`
where `leftCards`/`rightCards` are defined) so the surjectivity can see them.
Once green, this + `newLeftCards_injective` (47h) + `newMembership_overlap_25`
make the `(L,R)↦newMembership` map a **bijection onto the fiber**, so the
uniform choice pushes forward to the uniform fiber law (the A3 point-mass
statement).

**Then** — the A3 point-mass/measure bridge in
`Shufflemath/CommanderMembershipExchange.lean` (prove `comp (fiberLaw project)
rawExchangeMembership = comp commanderExchange25 membershipLift`), using
`map_equiv_mass` + the count kernel + the surjectivity.

**Below — the earlier (47th-session) T4-count-fiber-machinery note, kept for the
historical breakdown; its "next action" (the count kernel) is now DONE above.**

The T4 *measure* half's count-fiber machinery is **DONE and committed**
(`19d964d`, `Shufflemath/FiniteDeck/BLRefinement.lean`): `countFiberMemb` (the
membership count-fiber as a `Finset`), `countFiberMemb_equiv` (the
marked/unmarked-split bijection to the powerset-card product),
`countFiberMemb_card` (hypergeometric fiber cardinality),
`countFiberMemb_nonempty`, `yMoves_uniformOnFiber`, `fiberPushforward_count`,
and the capstone `uniformFiber_intertwines` (fiber-uniform kernel = the
`blExchange` pushforward). Targeted build green.

**Correction to the 46th note:** the T4 projection it lists as open is already
in the library — `countInPile` (L426) = `⟨countInPileVal,
countInPile_admissible⟩ : BLState`, plus `countInPile_val` /
`countInPile_countFiber` (L430/436). So the projection item is DONE.

**Next concrete action — the Commander F3 A3 discharge** at `(99, 50, 50, 25)`
in `Shufflemath/CommanderMembershipExchange.lean`: prove
`comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
membershipLift` (A3) by instantiating the G4 theory (`uniformFiber_intertwines`
+ `countInPile`). Two parts: (i) counting — the post-exchange membership count,
averaged, is the `commanderExchange25` transition; (ii) within-count uniformity
— conditioned on landing count `c`, the membership is uniform over the `c`-fiber
(equivariance + transitivity). Supporting ingredients already exist
(`map_equiv_mass`, `distUniform_ofInvariantTransitive`, `membershipFiber_card`,
`membershipLift_count`, `commanderCountFiber_card`, and the **A3 RHS** —
`commanderExchange25_mass`, `hMembershipExchange_rhs_mass` (`c276eda`, the
pointwise mass of `comp commanderExchange25 membershipLift`), and
`commanderExchange25_countMass` (`a7fabd3`, the count-level companion)); read
that module's doc-comment for the assembly plan. The **next concrete lemma is
the LHS counting core `rawExchangeMembership_count`** (part (i)): the
fiber-average post-exchange `membershipCount` equals the `commanderExchange25`
transition (RHS already `commanderExchange25_countMass`). **47d (Route B):** the
GPT-6 route's `exchangePair_exists` wall is now closed (commit `9b693f3`, with
`sdiff_sdiff_inter` + `sdiff_sdiff_union_eq` in `FinsetCombinatorics.lean`); next
is the membership-level mass identity via `BernoulliLaplaceFiber.lean`
`detailedBalance` + the `BernoulliLaplaceCommanderBridge` (gives the point mass
`transitionWeight/F(y)` and within-count uniformity, bypassing part (ii)).
**47e:** `commanderDetailedBalance` committed (`e84fe7e`,
`BernoulliLaplaceCommanderBridge.lean`) — reversibility of the macro kernel, one of
the two A3 ingredients. **`commanderStationary_is_stationary` +
`commanderStationaryRun` committed (`f7976d2`)** — the hypergeometric
fixed-point/invariance ingredient.

**47g:** `leftCards_disjoint_rightImage`, `newLeftCards_inter_leftCards`, and
`newMembership_overlap_25` committed (`9b5a45a`,
`Shufflemath/CommanderPhysicalExchange.lean`). The **25-overlap preservation**
(`newMembership_overlap_25`: the post-exchange left pile shares exactly 25 cards
with the original) is the structural core of the 25/25 exchange — the `|S ∩ T| = 25`
fiber that steps 2–4 below are indexed by. Proven via a light `rw` (distributivity +
`leftCards_disjoint_rightImage` + subset); a `Finset.ext`/`mem_union` case analysis
on the union hit the 200000-heartbeat `whnf` timeout, so avoid that shape.
**Session 47g close:** the 12-module Commander tranche builds clean and
`./dev/verify_next_phase.sh` passes (37 tests OK). The next development is
multi-lemma, so it starts fresh from the resume point below rather than being
forced into this session's remaining budget.

**47h:** step 2 "unique half" building blocks committed, all in
`Shufflemath/CommanderPhysicalExchange.lean` (purely additive after
`newMembership_overlap_25`), all build clean: **`45dd4b7`** — `image_injective_eq`
(injective `f` ⇒ equal images ⇒ equal sets — the general recovery engine),
`newLeftCards_leftPart` (the left-position part of the post-exchange pile `=
newLeftCards d L R ∩ leftCards d`), `newLeftCards_rightPart` (the selected-right part
= newLeftCards d L R ∩ (R.image fR)`, a light RHS), `newLeftCards_injective_L`
(a fixed deck's left-position choice `L` is recovered from the post-exchange pile:
equal piles ⇒ equal `L`); **`cbc61e8`** — `leftCards_disjoint_rightCards` (a deck's
left-position and right-position cards are disjoint — a card sits at one position;
**the key fact the `R`-recovery was blocked on**); **`a5abd2b`** —
`leftImg_disjoint_rightFull` (the unselected-left part is disjoint from the deck's
full right-position set).

**47h capstone DONE (`1c7b46e`): `newLeftCards_injective`** — the full
`(L,R)↦T` **injectivity**: `newLeftCards d L R = newLeftCards d L' R' → L = L' ∧
R = R'` (proven via `newLeftCards_rightPart_deck` + `newLeftCards_injective_L` +
`image_injective_eq` with the `Fin.val_injective` bridge). This completes the **unique
half** of the deck-level `(L,R)↦T` bijection (F3 item 3, step 2; the existence half
is the abstract `exchangePair_exists`).

**47i (`d8b4abd`): first deck-independence lemma** — `newLeftCards_as_sdiff_union`:
`newLeftCards d L R = (leftCards d \ L.image (d ∘ leftPosition)) ∪ R.image (d ∘
rightPosition)` (via `Finset.image_sdiff` + deck injectivity). The post-exchange pile
depends on `d` only through `leftCards d` and the chosen card-sets.

**47y: existence halves for BOTH piles** (in `CommanderPhysicalExchange`):
`newLeftCards_exists` (`L=leftChoices, R=∅` gives a valid pair) and
`newRightCards_exists` (`L=∅, R=rightChoices`). The deck-level `(L,R)↦T` bijection is
now complete on both halves (unique via 47h; existence for both piles).

**47ab (`8e4106d`): A3 COUNT KERNEL lands in the main library**
(`Shufflemath/CommanderA3Kernel.lean`, added to the AGENTS.md build list +
`dev/verify_next_phase.sh`; full verify gate — 24 modules + 37 tests — green):
- `newLeftCount_eq_transitionNumerator`: `# {(L,R) : (newLeftCards d L R ∩ leftOrigSet).card = n} =
  transitionNumerator 99 50 25 (leftOriginalCount d) n` — assembled from
  `newLeftOriginalCount_eq` (count = source − markedInLeft + markedInRight) and the 47v
  fiber-product kernel over the same `(L,R)` product (bridged by
  `leftChoices`/`rightChoices = s50`/`t49` extensionally).
- `newLeftCount_deckIndependent`: two decks with the same source count induce the same
  post-exchange count distribution. **This is the fiber-average collapse for the
  `rawExchangeMembership_count` LHS — the exact "remaining step" the
  `hMembershipExchange` assembly plan names** — now proven in the main library.

**NEXT:** F3 item 3 step 3 (point mass at the fiber) — the deck-level distribution
identity over the whole fiber (the 47u/47v route already has the per-`x` transition
numerator); then A3's *measure* half (replace the count law by the point-mass law,
`commanderExchange25_mass`/`hMembershipExchange_rhs_mass`); then the capstone
`hMembershipExchange`. The count-half kernel is now a building block for both.

**47j (this session): the A3 count half is reduced to one reusable counting
kernel + a trivial fiber-average (analysis done; the kernel's Lean proof is the
next concrete step).**

The A3 count half is `rawExchangeMembership_count`:
`comp (comp (fiberLaw project project_surjective) rawExchangeMembership)
(det membershipCount) = comp commanderExchange25 (det commanderLeftCount)`.
Both sides are `FiniteKernel CommanderState Nat`. The reduction:

- **LHS at `(x, n)`** = the uniform fiber-average (over `fiberSet project x`,
  weight `1/|fiber|` each) of the **per-deck** 25/25-exchange count mass. This
  is just `apply_mass_eq_sum` twice + `fiberLaw_mass` + kernel associativity,
  with the `det membershipCount` pushing a count indicator through.
- **The per-deck count mass is count-invariant.** By `newLeftOriginalCount_eq`
  (`(newLeftCards d L R ∩ leftOrigSet).card = (leftOriginalCount d -
  markedInLeft d L) + markedInRight d R`), a deck `d` with count
  `x = leftOriginalCount d` has post-exchange count `x - X + Y`, where
  `X = markedInLeft d L` and `Y = markedInRight d R`. As `L` (a 25-subset of
  the 50 left positions, of which `x` are marked) and `R` (a 25-subset of the
  49 right positions, of which `50 - x` are marked, since the right pile holds
  `50 - x` marked and `x - 1` unmarked) range uniformly, `X ~ HG(50, x, 25)`
  and `Y ~ HG(49, 50 - x, 25)` — **functions of `x` only, independent of the
  deck's internal arrangement**. So the per-deck count mass at `n` is the same
  for every deck of count `x`.
- **It equals `transitionWeight 99 50 25 x n`** (the 99-card
  `BernoulliLaplace.lean` transition): the 5-arg `transitionNumerator
  (99 50 25 x n)` is exactly the count of `(L, R)` grid choices landing on
  count `n` — its four `choose` factors split as
  `choose(x,a)·choose(50-x,25-a)` (`X = a`) times
  `choose(50-x,b)·choose(x-1,25-b)` (`Y = b`) with `b = n - x + a`, matching
  the `X` and `Y` hypergeometric counts. Dividing by
  `transitionDenominator (99 50 25) = choose(50,25)·choose(49,25) =
  #exchangeChoice` gives the per-deck mass.
- **Conclusion:** the LHS fiber-average of a fiber-constant per-deck mass is
  just that mass = `transitionWeight 99 50 25 (count x) n` = the RHS
  (`commanderExchange25_countMass`, `a7fabd3`). The **only** remaining proof
  content is the counting kernel below; everything after it is assembly.

**The counting kernel — `powersetCard_markedContent`** (add to
`Shufflemath/FinsetCombinatorics.lean`; the reusable foundation for both pile
counts):

    theorem powersetCard_markedContent {α : Type*} [Fintype α] [DecidableEq α]
        (U M : Finset α) (hM : M ⊆ U) (k a : Nat) (ha : a ≤ k) :
        (∑ S ∈ U.powersetCard k, if (S ∩ M).card = a then 1 else 0) =
          Nat.choose M.card a * Nat.choose (U.card - M.card) (k - a)

**REVISED primary approach (47j addendum) — REUSE the committed `countFiberMemb` machinery, do not re-prove it.** `Shufflemath/FiniteDeck/BLRefinement.lean` already contains `countFiberMemb_equiv N m r hm hr x` (a proven `Equiv`) between `{S : Membership N m // (S.1 ∩ markedSet N r hr).card = x.val}` and the marked/unmarked-split product `{p // p.1 ∈ (markedSet N r hr).powersetCard x.val ∧ p.2 ∈ (markedComp N r hr).powersetCard (m - x.val)}`, and `countFiberMemb_card` (`(countFiberMemb N m r hr x).card = choose r x.val * choose (N - r) (m - x.val)`). Both build. So prove `powersetCard_markedContent` by **adapting that `Equiv.mk f g` structure** to an arbitrary `(U, M)` with `M ⊆ U`: `f` splits `S ↦ (S ∩ M, S ∩ (U \ M))`, `g` recombines `(A, B) ↦ A ∪ B`, recovery `(A ∪ B) ∩ M = A` / `(A ∪ B) \ M = B`, and `g ∘ f = id` from `S = (S ∩ M) ∪ (S ∩ (U \ M))` (the `U`-generalization of the committed `markSplit`). This is the *proven-to-build* structure — the `×ˢ`/product/image/injectivity approach below (and the 47j implementation reverted against it) is the fiddly path to avoid. After the general kernel, both pile counts (1)+(2) are direct instances; alternatively (2a) reuse `countFiberMemb_card` for the canonical `markedSet` + a small permutation-invariance bridge. 

**Proof plan (union-bijection):** `X := U \ M`,
`P := M.powersetCard a ×ˢ X.powersetCard (k - a)` (the **`×ˢ` /
`Finset.product`** syntax — there is **no** `Finset.prod`), `f (A, B) :=
A ∪ B`. Show (i) `A ∪ B` (for `A ⊆ M`, `B ⊆ X`, disjoint) is a `k`-subset of
`U` with exactly `a` marked elements; (ii) every such `S` splits as
`(S ∩ M) ∪ (S ∩ X)` with the right cards, so
`{S ∈ U.powersetCard k // (S ∩ M).card = a} = f '' P`; (iii) `f` is injective
on `P` (recovery `A = (A ∪ B) ∩ M`, `B = (A ∪ B) ∩ X`). Then
`card (f '' P) = card P = choose(M.card, a) · choose(X.card, k - a)` by
`Finset.card_image_of_injective` + `Finset.prod_card` +
`Finset.card_powersetCard`, and `X.card = U.card - M.card` by
`Finset.card_sdiff_of_subset`. The LHS sum is the cardinality of the filter by
`Finset.sum_ite` + `Finset.sum_const`.

**Mathlib name pitfalls hit in 47j (do not repeat):** `mem_powersetCard` is a
`@[simp]` lemma — unfold a membership with `Finset.mem_powersetCard.mp h`
(not `h.2.1` after a bare `simp at *`); there is **no**
`Finset.mem_union_of_left`/`_of_right` — use `Finset.mem_union.mpr (Or.inl
·)`/`(Or.inr ·)` or `simp [Finset.mem_union]`; there is **no**
`Finset.sum_ones` — use `Finset.sum_const` (`∑ _x ∈ s, 1 = s.card`);
`M` and `U \ M` are disjoint by `Finset.inter_sdiff_self`; `simp only [...]
at * ⊢` is **not** valid syntax (the `⊢` after `at *` is rejected) — `rcases`
the membership instead. A first implementation of the kernel hit six build
iterations on exactly these names and was reverted; the statement and plan
above are sound, only the name/rewrite details remain.

**47m (this session): the A3 *count half* is committed in a new standalone
module `Shufflemath/CommanderA3Count.lean` (builds; in the verify-script build
list).** The module pins down, for a single deck `e`, the *composition of the
left pile after an exchange*: of the 50 left-pile positions, exactly
`leftOriginalCount e` hold a marked (originally-left) card and the rest —
`50 − leftOriginalCount e` — hold an unmarked (originally-right) card.
Definitions: `leftMarked e i` (the card at left index `i` is marked, i.e.
`e (leftPosition i) ∈ leftOrigSet`), `leftIdxFinset e` (the 50 left indices
holding a marked card — definitionally `markedLeftPos e`), `rightIdxFinset e`
(`Fin 50` \ `leftIdxFinset e`, the originally-right cards that landed in the
left pile). Two theorems: `leftIdxFinset_card`
(`#leftIdxFinset e = leftOriginalCount e`, by `markedLeftPos_card`) and the
**count half** `leftUnmarkedCardCount`
(`#rightIdxFinset e = 50 − leftOriginalCount e`), the latter a 4-line proof
via `Finset.card_sdiff_of_subset` + `Finset.filter_subset` + `by decide`
(`#(Fin 50) = 50`). This is the per-deck **count-invariance fact** the 47j
analysis reduces the A3 count half to: the post-exchange count depends on the
deck only through `x = leftOriginalCount d`, and the number of marked cards
displaced into the right pile is `50 − x` (so the right pile gains `50 − x`
marked and the left pile gains `50 − x` unmarked, symmetrically). It is the
foundation for **build-order item 3** (the per-deck Vandermonde bridge
connecting `transitionNumerator` to the per-deck `(L, R)` count): the next
step is to prove `powersetCard_markedContent` (the 47j kernel, via the
`countFiberMemb_equiv` structure) and show the per-deck count mass at `n`
equals `transitionWeight 99 50 25 x n`, so the fiber-average fiber-constant
mass = the `commanderExchange25` transition (`commanderExchange25_countMass`).
The `CommanderA3Count` module is purely additive (imported by no other
module); `./dev/verify_next_phase.sh` passes with it in the build list (37
tests OK).

**Build order to finish the A3 count half (after the kernel):**
1. `leftPileCount25`: `#(L ∈ leftChoices, markedInLeft d L = a) =
   choose(x, a)·choose(50 - x, 25 - a)` — kernel instance with
   `U = (univ : Finset (Fin 50))`, `M = markedLeftPos d`, `x =
   leftOriginalCount d`.
2. `rightPileCount25`: `#(R ∈ rightChoices, markedInRight d R = b) =
   choose(50 - x, b)·choose(x - 1, 25 - b)` — kernel instance with
   `U = (univ : Finset (Fin 49))`, `M = markedRightPos d` (right pile has
   `50 - x` marked, `x - 1` unmarked).
3. `exchangeCountAt`: `#(c ∈ exchangeChoice, membershipCount (newMembership d
   c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)) = n) =
   transitionNumerator 99 50 25 x n` — grid decomposition by `(a, b)` with
   `n = x - a + b` + (1)+(2) + the `transitionNumerator` definition.
4. `rawExchangeMembership_countMass` (per-deck): the per-deck count mass =
   `(if 1 ≤ n ∧ n ≤ 50 then transitionWeight 99 50 25 x n else 0)` (`#grid =
   transitionDenominator (99 50 25)`).
5. **`rawExchangeMembership_count`** (the A3 count half): the fiber-average of
   the fiber-constant per-deck mass = `commanderExchange25_countMass` (RHS).

**NEXT ACTION — F3 item 3, step 1 (deck-independence):** show `newMembership d L R`
(and hence `rawExchangeMembership d`) depends on `d` only through `membership d`
(`markedLeftPos d`, `markedRightPos d`) — so the "membership transition" is well-defined
as a function of the source membership `S`. Then step 3 (point mass on the
`|S∩T|=25` fiber). See the numbered build order below.


**NEXT ACTION — F3 item 3, the physical membership-level mass identity
(the "genuinely hard half"; a multi-lemma development, not a single
batch).** Target: `hMembershipExchange` (the F3 capstone in
`CommanderMembershipExchange.lean`). Build toward it in this order:
1. **Deck-independence**: `newMembership d L R` (and hence
   `rawExchangeMembership d`) depends on `d` only through `membership d`
   (i.e. through `markedLeftPos d` and `markedRightPos d`) — makes the
   "membership transition" well-defined as a function of the source
   membership `S`.
2. **Deck-level `(L,R) ↦ T` bijection**: for fixed `d` with membership `S`,
   the map over the `choose(50,25)·choose(49,25)` uniform choices is a
   bijection onto `{T : Membership // |S ∩ T| = 25}` — the deck-level
   instance of the abstract `(A,B)↦T` bijection already committed
   (`exchangePair_unique_B/_A` + `exchangePair_exists`), with
   `A = L ∩ markedLeftPos d`, `B` the marked cards entering, `T =
   newMembership d L R`.
   **(47h DONE: the full `(L,R)↦T` injectivity `newLeftCards_injective` is committed
   (`1c7b46e`) — the unique half of the deck-level bijection. Next: step 1
   (deck-independence), then step 3 (point mass).)**
3. **Point mass**: from (1)+(2), `rawExchangeMembership d` has mass
   `1/(choose(50,25)·choose(49,25))` at each `T` on the `|S∩T|=25` fiber,
   `0` off it.
4. **Detailed-balance connection**: identify the overlap with
   `transitionNumerator(99,50,50,25,·,·)` and use `BernoulliLaplaceFiber.lean`
   `detailedBalance` + the commander bridge to write the mass as
   `transitionWeight(...)/F(y)`, `F(z) = choose(50,z)·choose(49,50-z)`.
5. **Capstone**: assemble `hMembershipExchange` (LHS already reduces via
   `hMembershipExchange_lhs_reduces` to `comp (fiberLaw project)
   rawExchangeMembership`).

**Structural fact confirmed 47e:** `CommanderState = Fin 50` (a *count*
state, `commanderLeftCount x = x.val+1`) is NOT the physical
`Membership = {S : Finset (Fin 99) // S.card=50}`. The physical kernel is
`rawExchangeMembership : FiniteKernel Deck Membership`
(`CommanderPhysicalExchange.lean:376`), point map `newMembership d L R =
⟨newLeftCards d L R, …⟩` (`:370`); no `FiniteKernel Membership Membership`
exists yet. **Smallest tractable first lemma (DONE in 47g):** the 25-overlap preservation
`|(membership d) ∩ (newMembership d L R).1| = 25` for a valid 25/25 exchange
(`newMembership_overlap_25`). **Next concrete lemma:** the **count-transition LHS**
`comp (comp (fiberLaw project) rawExchangeMembership) (det membershipCount) =
comp commanderExchange25 (det commanderLeftCount)` (RHS already
`commanderExchange25_countMass`): push the physical exchange to the macro *count*
level and show its project-fiber average is the hypergeometric transition. This is
more tractable than the full membership-level mass identity because it only tracks
`membershipCount` (a `Fin 50` value), not the specific 50-card set.
**Gotchas:** default `simp`/`field_simp` recurse into `membership`/`leftCards`
(`Equiv.Perm (Fin 99)` terms) — use `simp only` with explicit lemma lists; do
not `native_decide` over `99!`.

### 45th session (2026-11-17) — prior resume point (bootstrap notes below stay in force for this VM)

New agent, new AIVM VM, **deadline extended to Wed 2026-11-24 23:59:59 EST**
at the user's request (banner + rule 1 updated; `AGENTS.md` and
`docs/lean_plan.md` re-pointed at the G1–G4 campaign). Environment bootstrap
done and verified:

- `git submodule` already checked out; `leanq`/`aiq-lean`/`lake-build-report`
  **reinstalled from this repo's** `submodules/aiq-lean-formalization-tools`
  (the pre-existing editable install pointed at *another* repo's checkout;
  note `python` is absent on this VM — use `python3 -m pip install -e …
  --break-system-packages`, PEP 668).
- `.lake` bind-mounted to `/var/cache/lake/shufflemath/.lake` (this machine had
  **no** shufflemath cache — the Oct-3 one is gone; first build is cold).
- `lake exe cache get` fetched the public mathlib4 cache (3 files / 8908
  oleans; 3 private shufflemath files 404 — expected).
- The 10-module targeted build from `AGENTS.md` is **green** (3214 jobs).

**New bind-mount gotcha (hit 2026-11-17):** running
`sudo submodules/…/setup-lake-cache.sh …` makes the script's internal
`sudo chown "$(id -u):$(id -g)"` evaluate `id` in the *sudo* context (→
`0:0`), so `/var/cache/lake/<repo>/.lake` is left `root:root 755` and `lake`
dies with `permission denied … .lake/config`. The owner marker is written
correctly either way. **Fix:** run the script **without the leading `sudo`**
(it sudo's `mkdir`/`chown`/`mount` internally, and `$(id -u)` then evaluates
as the calling user) — use that form for the post-reboot `--all` re-apply too
(plus `--force` if the device-number-changed gotcha below also bites). One-off
repair if already bit: `sudo chown -R $(id -u):$(id -g) /var/cache/lake/<repo>`.

**Resume point unchanged: `card_biUnion_pd`** (the 44th-session note below:
statement, proof skeleton, and the 7 recorded blockers), then
`yMoves_card_eq_sum`, then the T4 sum-to-`transitionNumerator` assembly.

### 44th session (2026-11-16) — prior detailed state (its 7 blocker notes remain the reference for `card_biUnion_pd`)

**Environment pre-step (once per fresh machine / clone):** `git submodule update --init submodules/aiq-lean-formalization-tools` then `python -m pip install -e submodules/aiq-lean-formalization-tools` (that submodule provides `leanq`/`aiq-lean`/`lake-build-report` **and** `scripts/setup-lake-cache.sh`); then `lake exe cache get`, and if the repo is a virtiofs share re-apply the local build cache with `sudo submodules/aiq-lean-formalization-tools/scripts/setup-lake-cache.sh --all` (the `.lake` bind mount does not survive a reboot). See the AGENTS.md "Lean tooling" + "Build cache" sections.

**Known bind-mount gotcha (hit 2026-11-16):** the recorded cache
`/var/cache/lake/shufflemath/owner` still holds `id=103:7870669`, but the live
repo's `stat -c '%d:%i'` is now `104:7870669` — the **inode is unchanged**
(`7870669`), only the virtiofs **device number** changed across a
reboot/remount. Because the script keys its owner-marker on `device:inode`,
`setup-lake-cache.sh --all` will `die "cache ... belongs to another tree"`
unless you pass `--force`. This is *not* a different repo adopting another
repo's oleans (the inode proves it is the same tree) — so re-apply with
`sudo .../setup-lake-cache.sh --all --force`, or just edit the `id=` line in
/var/cache/lake/shufflemath/owner to `104:7870669` and re-run `--all`. Note the
recorded cache's oleans date from Oct 3, so the first build after remounting
will re-elaborate heavily before it goes incremental.
**Sister gotcha (2026-11-17, the chown one):** invoke the script *without the
leading `sudo`* — under a leading `sudo`, its internal
`sudo chown "$(id -u):$(id -g)"` evaluates `id` as root and leaves the cache
`root:root`, breaking `lake` with `permission denied .lake/config`. See the
45th-session note in "Exactly where to resume".

Everything from the 2026-11-15 G1–G4 pivot down through the **G4 counting core
and most of the T4 transition-formula infrastructure** is now **PROVEN AND
COMMITTED**. Concrete completed set:

- **G1** `FiniteDeck/TwoPile`, **G2/T1** `FiniteDeck/Fiber` (`fiberCount` capstone done),
  **G3/T3** `FiniteDeck/SubsetExchange` (`subsetExchangeCount`, kernel + symmetry +
  row/col-one + stationarity, `subsetExchangeKernel_equivariant`), **G4** `FiniteDeck/BLRefinement`.
- **BLRefinement (G4/T4) now contains**, all committed: `markedSet`, `markedComp`,
  `countFiber`(+`_card`,`_blStationary`), `powersetCard_markedSplit`(+3 helpers),
  `permFinsetTransitive`, `countFiber_transitive`, `countInPile`(transparent),
  `countAB`, **`filterProduct`**, **`reachMoves`**, **`filterCardProduct`**,
  **`pieceCount`** (one reachable-move summand = 4-factor choose product, 0 in the
  guard-failure regimes), **`markedPileCards`** (`(S∩M).card=x`, `(S\M).card=m-x`,
  `((univ\S)∩M).card=r-x`, `((univ\S)\M).card=(N-m)-(r-x)`), **`yMoves`** (moves
  landing at macro count `y`), **`yMoves_biUnion`** (`yMoves = ⋃_{a∈0..k} Pa(a)`),
  **`Pa`** (moves removing exactly `a` marked, landing at `y`), **`Pa_disjoint`**
  (distinct `a` ⇒ disjoint), **`yMoves_fiberCard`** (filtering `yMoves` on
  `(p.1∩M).card=a` gives `Pa(a)`).

**The single next lemma: `card_biUnion_pd`** — a general *disjoint-union card*
lemma, then `yMoves_card_eq_sum` (`#yMoves = Σ_{a∈0..k} #Pa(a)`). `card_biUnion_pd`:
```
theorem card_biUnion_pd [DecidableEq ι] [DecidableEq α] {s : Finset ι} {t : ι → Finset α}
    (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Finset.card (s.biUnion t) = Finset.sum s (fun i => Finset.card (t i)) := by
  induction s using Finset.induction_on
```
Then `yMoves_card_eq_sum` = `yMoves_biUnion` (so `#yMoves = #biUnion (Ico 0 (k+1)) Pa`)
+ `card_biUnion_pd` with `h = Pa_disjoint`. That yields the count-level transition
formula's left side; summing `pieceCount` over `a` and matching to
`transitionNumerator` (via `markedPileCards`) completes T4.

**Blockers already hit (do NOT rediscover) while writing `card_biUnion_pd`:**
1. The `Finset.induction_on` nonempty case is named **`insert`** (not `ins`).
2. There is **no `Finset.bind_empty` / `Finset.biUnion_empty`** simp lemma — the
   empty case `#(∅.biUnion t) = 0` did not close with
   `simp only [Finset.biUnion, Finset.bind_empty, Finset.card_empty, Finset.sum_empty]`
   (left `∅.val.bind ….toFinset.card = 0` open). Try proving `(∅.biUnion t) = ∅` by
   `ext`/`simp [Finset.mem_biUnion]` first, or add `haveI := Classical.decEq ι` and
   retry, or avoid induction and instead prove `#yMoves = Σ #Pa` directly via
   `yMoves_fiberCard` + a fiber-count sum.
3. The **`#` notation does not accept `#(t i)`** (an application) — it fails with
   "unexpected token '#'". Write **`Finset.card (t i)`** explicitly everywhere.
4. The induction needs `[DecidableEq ι]`; an unsolved `DecidableEq ι` goal appears
   otherwise.
5. There is **no `Finset.biUnion_insert`**; prove
   `(insert i s).biUnion t = t i ∪ s.biUnion t` by
   `ext x; simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union]; tauto`.
6. Disjointness of `t i` from `s.biUnion t`:
   `rintro x hx ⟨j, hj, hzj⟩; exact h i j (Ne.ofMem hmem hj) hx hzj` (with
   `hmem : i ∉ s`).
7. Disjoint-union card: `Finset.card_union_add_card_inter (a b) : #a + #b = #(a∪b) +
   #(a∩b)`; with `#(a∩b)=0` (via `Finset.card_eq_zero` +
   `Finset.disjoint_iff_inter_eq_empty` + the `Disjoint`) close the `a∪b`/`a`/`b`
   goal by `omega`.

**Alternative (if induction keeps fighting):** `Finset.card_biUnion_le` exists (no
disjointness) for the `≤` direction; the reverse `≥` follows because `yMoves ⊆
⋃ Pa` with the `Pa` covering `yMoves` exactly (`yMoves_biUnion`), so
`#yMoves = #biUnion Pa ≤ Σ #Pa`, and `yMoves_fiberCard` gives equality of each
fiber — but the induction is the cleaner single lemma.

**Key API gotchas confirmed this session (44th):**
- `Finset.card_biUnion [DecidableEq M] {t : ι → Finset M} (h : (s : Set ι).PairwiseDisjoint t) :
  #s.biUnion t = Σ u ∈ s, #t u` — the hypothesis is a **`Set.PairwiseDisjoint`**, and
  `Set.Pairwise s r` for a binary `r` is `∀ i ∈ s, ∀ j ∈ s, r i j` (**all** pairs, the
  `i=j` case included), so `PairwiseDisjoint` for *nonempty* fibers is too strong to
  prove directly — that is exactly why the `∀ i ≠ j, Disjoint` induction route above is
  preferred over `Finset.card_biUnion`.
- `Finset.card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι}
  {t : Finset M} (H : (s : Set ι).MapsTo f t) : #s = Σ b ∈ t, #{a ∈ s | f a = b}` —
  the `#{a ∈ s | …}` **set-comprehension-card** notation did **not** parse in a scratch
  (`# {` vs `#{`); if you use this lemma you must bridge that fiber notation to
  `#(s.filter …)` (via `yMoves_fiberCard`) rather than write `#{}` yourself.
- `Finset.mem_inter` / `Finset.mem_sdiff` / `Finset.mem_union` leave **opaque
  `Quot.lift`** membership; destructure only with `rw [Finset.mem_…]` then `rcases`
  the resulting `∧`, or use `simp only [Finset.mem_filter, Finset.mem_product]` +
  `tauto` for product-filter equalities.
- The **`×˓`** (Finset product) character is U+00D7 U+02E2; in **type annotations**
  (lambda `fun p : Finset (Fin N) × Finset (Fin N)`) use plain `×` (U+00D7 only),
  while in **expression** positions it is `×˓`. Heredoc scripts can emit the wrong
  second codepoint — verify with `cat -A`.
- `set M := …` (a local `def`) is **opaque** to `rw`/`simp` pattern-matching: a goal
  written with `markedSet N r hr` will not match a hypothesis written with the local
  `M`. When a lemma's statement must textually match a theorem's, **inline the full
  `markedSet N r hr`** in every predicate instead of a `set`.

**Working-tree state at handoff:** clean (last commits `26b1f3b` removed an orphaned
scratch, `5b84ee9` = `yMoves_fiberCard`). Full library `lake build Shufflemath`
green (3205 jobs); `./dev/verify_next_phase.sh` 37/37.


### 2026-11-15 strategic pivot — resume here first (supersedes the A3-only queue)

Two dated documents landed on 2026-11-15 and redefine the route to the F3 A3
theorem; read them before continuing:

- `docs/planning/reviews/2026-11-15-qwen-proof-quality-duplication-and-build-performance.md`
  (duplication + build-cost; its **P0 / Commit A** is already done — see below).
- `docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`
  (the **campaign**: prove the *generic* finite-deck theory, with Commander as a
  specialization).

**New next action: the G1–G4 generic route.** Rather than finish another 99-only
A3 counting proof, build the *generic* two-pile theory and discharge Commander A3
by **instantiation** (roadmap T4/G4). The source-to-target manifest is
`docs/planning/2026-11-15-g1g4-theorem-manifest.md`. Concrete order (small commits,
one compiling generic theorem at a time):

1. **G1** — new module `Shufflemath/FiniteDeck/TwoPile.lean`: `Deck N :=
   Equiv.Perm (Fin N)`, `Membership N m := {S : Finset (Fin N) // S.card = m}`,
   the deck→membership projection, and the position split/merge `Fin N ≃
   Fin m ⊕ Fin (N-m)` for `m ≤ N`.  Acceptance: `N=0, m=0, m=N` compile; **no
   `Commander*` import**.  Keep the `module` / `public import` /
   `@[expose] public section` conventions.
2. **T1 fiber count** (G2's first lemma, same or next module): `# {d //
   allocation d = A} = m! · (N-m)!` by an explicit finite equivalence (NOT an
   `N!` / `native_decide` enumeration); give one small numerical specialization.
3. **G3** — `subsetExchangeCount` (the reachable count `# ReachSet = choose m k · choose (N-m) k`) **compiled** (`FiniteDeck/SubsetExchange`); next: the weighted generic `subsetExchange N m k` kernel (unique witness `A=S\T, B=T\S`), symmetry/stationarity, and the pairing-independent `literalSwap`.
4. **G4** — generic count projection + `M`-equivariance/transitivity + BL law;
   **discharge Commander A3** (`comp (fiberLaw project) rawExchangeMembership =
   comp commanderExchange25 membershipLift`) as an instance at `(99,50,50,25)`,
   then the conditional `two_physical_perfect_exchanges_uniform_of_counts`.

**Do not** start the quality-review P2/P3 module splits until G4 is green.  The
Q1/Q2 deduplication (fiber-count wrapper, CL unification) is folded into the gate
where the generalized theorem replaces the specialized proof.

**Completed this session:** quality-review **Commit A / Q3** (commit `b1e5812`)
— `overlap_eq_revTransitionNumerator_cmdr_2525` now derives from
`generalCL_cmdr_2525.symm` instead of `native_decide`.  Also: Gate 0 (commit
`c8582f3`, `verify_next_phase.sh` builds the 6 active F3/F4 modules),
`commanderCountFiber_card` (commit `41a4bab`), and the review R1/R3/R4 status
honesty fixes (commit `9072a3b`).  The F3 A3 `commanderExchange25_countMass`
99-only lemma is documented but **not** pursued further; the generic route
supersedes it (its probed Mathlib API — `Finset.sum_ite` form, `Finset.filter_eq'`,
`refine Finset.sum_bij … ?_ ?_ ?_ ?_`, `Nat.sub_add_cancel` — is recorded below).

**Progress (2026-11-15, autonomous session):**
- **G1** (`FiniteDeck/TwoPile.lean`) — **compiled**: `Deck N`, `Membership N m`,
  `leftPositions`/`rightPositions` (cover/disjoint), `leftCards`/`membership`.
- **G2** (`FiniteDeck/TwoPileFiber.lean`) — **compiled**: `membershipCount`
  (`choose N m`) + the four fintype-card building blocks
  (`fintype_card_{leftPos,rightPos,pile,complementPile}`).
- **G2 fiber machinery** (`FiniteDeck/Fiber.lean`) — **compiled**: the fiber
  type `FibType N m hm A` (= decks with left-image `A`) + the **two restriction
  bijections** `fiberRestrictL : LType ≃ AAType` and `fiberRestrictR : RType ≃
  BBType` (both via `Equiv.ofBijective`). **Remaining (documented in the
  module):** the fiber count `#Fiber = m!·(N-m)!` = the glueing equiv
  `Fiber ≃ (L ≃ A) × (R ≃ B)` + `Fintype.card_prod` + `Fintype.card_equiv` +
  the position-card lemmas. The by_cases-def opacity wall and the preferred
  disjoint-union `Equiv`-composition route are recorded in the module.
- **G3** (`FiniteDeck/SubsetExchange.lean`) — **compiled foundation**:
  `ReachSet`/`Lset`/`Rset` + `Lset_card`/`Rset_card`. **Remaining:** the
  `subsetExchangeCount` (`card_bij'` bijection — exact construction recorded in
  the module) and then the uniform `k`-exchange kernel (T3).
- **G4** (discharge Commander A3 generically) — after G3.

### Nov 15 (25th) session status — prior A3-machinery detail

This session built the **group-uniformity and lift-projection machinery** for
F3 item 3's `hMembershipExchange` (Spec C / A3).  All committed; the full
targeted build (11 modules) is green; 37 Python tests pass; tree clean.

- **`map_equiv_mass`** (`Shufflemath/CommanderMembershipExchange.lean`,
  commit `52214df`): for a bijection `e : Equiv X X`,
  `Dist.mass (mu.map e) y = Dist.mass mu (e.symm y)` (the preimage sum collapses
  to one term).
- **`distUniform_ofInvariantTransitive`** (same file, `52214df`): a distribution
  that is invariant under a group action **transitive** on a set `S` is uniform
  on `S`: `(↑#S : Rat) * Dist.mass mu x = 1` for `x ∈ S`.  *This is the general
  tool for part (ii)'s within-count uniformity.*
- **`membershipFiber_card`** (`8b23c48`): `# {m // membershipCount m = k} =
  membershipFiberCount k` (bridges `Fintype.card (MembershipFiber k)` through
  `MembershipFiber_card` to the F1b choose product).
- **`membershipLift_count`** (`8b23c48`):
  `comp membershipLift (deterministic membershipCount) =
   deterministic commanderLeftCount` — the uniform lift projects back to its
  count (via `Dist.sum_mass` + `Finset.sum_congr`, no fiber-card expansion).

**Next — F3 item 3 capstone (A3):** prove, in
`Shufflemath/CommanderMembershipExchange.lean`,

1. **`commanderCountFiber_card`** (part (i), RHS helper) — **COMMITTED**
   (commit `41a4bab`): `# {y : Fin 50 // commanderLeftCount y = c} =
   if 1 ≤ c ∧ c ≤ 50 then 1 else 0`.  (Card formulation, not a Fin-singleton in
   the statement — `{⟨c-1⟩}` is ill-typed for arbitrary `c`.)
   Then **`rawExchangeMembership_count`** (part (i) capstone):
       `comp (comp (fiberLaw project project_surjective) rawExchangeMembership)
          (deterministic membershipCount) =
         comp commanderExchange25 (deterministic commanderLeftCount)`.
   Both sides are `FiniteKernel CommanderState Nat`.  The RHS then reduces,
   via `apply_mass_eq_sum` + `Dist.mass_pointMass` + the
   `commanderExchange25Matrix x y = transitionWeight 99 50 25 (count x)
   (count y)` def (line 101) + `commanderCountFiber_card`, to
   `if 1 ≤ c ≤ 50 then transitionWeight 99 50 25 (count x) c else 0`.  The
   LHS needs the deck-fiber counting: the fiber-average post-exchange count
   distribution equals the same hypergeometric weight (the `generalCL` /
   `fiberSum_eq_overlap` counting core is the template; instantiate it at the
   `(L,R)`-25-subset exchange level via `leftHyper`/`rightHyper`, cf. the
   `Finset.mem_coe` fix in `docs/f3_membership_exchange.md`); it is
   deck-independent given the source count, so the fiber average is trivial.

   **`commanderExchange25_countMass`** (part (i) RHS — the immediate next
   lemma): `Dist.mass (comp commanderExchange25 (deterministic
   commanderLeftCount) x) c = if 1 ≤ c ∧ c ≤ 50 then transitionWeight 99 50 25
   (commanderLeftCount x) c else 0`.  *25th-session status: attempted but not
   yet committed.*  **Confirmed working API** (probed this session, do not
   guess — `#print` each before use):
     - `Finset.sum_ite (f g) : (∑ x ∈ s, if p x then f x else g x) =
       ∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, g x` (the `∑ with` is the
       filter sum).
     - `Finset.filter_eq' : s.filter (fun a => a = b) = ite (b ∈ s) {b} ∅`.
     - `Finset.sum_singleton`, `Finset.sum_empty`, `Finset.sum_const_zero`.
     - `Finset.sum_bij` (transport) — but see blocker below.
   **Route:** `apply_mass_eq_sum` → `simp only [deterministic, mass_pointMass,
   commanderExchange25, ofRowStochastic, mass_ofFun, commanderExchange25Matrix,
   commanderExchangeMatrix]` → transport the count-sum to `Finset.Icc 1 50` →
   per-term `* [c = t]` → `if t = c then K else 0` (`K = transitionWeight
   (count x) c`) → `sum_ite` + `sum_const_zero` + `add_zero` → `filter_eq'` →
   `split_ifs` on `c ∈ Icc 1 50` → `sum_singleton`/`sum_empty` +
   `if_pos`/`if_neg (1 ≤ c ∧ c ≤ 50)`.  **Blockers hit (change representation,
   don't grind):** (a) the source is a **Fintype sum** `∑ y : CommanderState,
   …`; `apply Finset.sum_bij` on it left a *non-equality* 4th-bullet goal —
   transport to a `Finset.univ`-based Finset sum *first* (or drop `sum_bij` and
   prove the count-domain sum directly over `Icc 1 50`).  (b) the surjective
   bullet's Fin bound `t - 1 < 50` (from `t ∈ Icc 1 50`) fails under `omega`
   (saturating `Nat` subtraction) — use `Nat.sub_le_sub_right (ht.2) 1` +
   `Nat.lt_of_le_of_lt _ (by norm_num)`, the same fix as in
   `commanderCountFiber_card`.

2. **`hMembershipExchange`** (the capstone): assemble (1) with part (ii)
   within-count uniformity (`newLeftCards_conjugate` equivariance +
   `membershipFiber_transitive` transitivity, applied through
   `distUniform_ofInvariantTransitive`) into
   `comp (fiberLaw project project_surjective) rawExchangeMembership =
    comp commanderExchange25 membershipLift`, then instantiate
   `two_physical_perfect_exchanges_uniform_of_counts` (the 2-exchange TV
   theorem, F3 item 4).

F4.2 item 4 (Dobrushin contraction / `Equiv.Perm (Fin 99)` lift) and F5 remain
downstream; the full-deck TV (F4.5) needs F3 item 4.  Do not re-attempt the
`List.mem_bind`/`toMultiset` sub-wall.

### Nov 15 (24th) session status — (prior; resume above)

### Nov 15 (24th) session status — resume here first

This session proved the two **group-action (orbit) pillars** of F3 item 3's
part (ii) and scaffolded the A3 kernel-equality module.  All committed; the full
targeted build (11 modules incl. the new
`Shufflemath.CommanderMembershipExchange`) is green; 37 Python tests pass;
working tree clean.

- **F3 item 4 / Spec A1 — `membershipFiber_transitive`**
  (`Shufflemath/CommanderMembershipOrbits.lean`, commit `43f845f`): any two
  memberships `m, m'` with the same `membershipCount` are related by a deck
  bijection that **preserves the left pile** and **carries `m.1` to `m'.1`**.
  Proven via an explicit 4-piece `orbitMap` (matched/unmarked × left/right
  position equivs, commit `55c07b5`) whose `surjective` (`cb5dd14`),
  `injective` (`4f816b1`, via 12 pairwise-disjointness + 4 preimage lemmas),
  and `imageLeft`/`imageM1` lemmas (`43f845f`) make `Equiv.ofBijective` close.
  `leftRightOrig_cover` / `leftRightOrig_disjoint` / `piecesCover` give the
  4-way position partition.  *This is part (ii)'s "group acts transitively on
  each count-fiber" half, at the deck level.*
- **Spec A2 — `newLeftCards_conjugate`** (`CommanderPhysicalExchange.lean`,
  commit `6ccae33`): for any permutation `f : Equiv.Perm (Fin 99)`,
  `newLeftCards (d.trans f) L R = (newLeftCards d L R).image f` (by
  `leftOrigSet_image` + `Equiv.trans_apply`).  The *pointwise* equivariance of
  the post-exchange left set under relabeling — the distributional-invariance
  building block (part (ii)'s "exchange law is equivariant under the group"
  half).  (A 23rd-session file-truncation incident lost this lemma once; it was
  restored from `958d5f5` and re-merged — commit `dd221fd`; a splice-safety
  warning was added to this doc.)

**Next — F3 item 3 kernel equality (A3 / Spec C), now scaffolded:** the target
`comp (fiberLaw project project_surjective) rawExchangeMembership =
comp commanderExchange25 membershipLift` (`Shufflemath/CommanderMembershipExchange.lean`,
commit `74f5dab`) splits into (i) **counting** — the post-exchange
`membershipCount`, fiber-averaged, equals the `commanderExchange25` transition
(the counting core `generalCL`/`fiberSum_eq_overlap` is DONE, but the fiber
average over *decks* needs a deck-level orbit argument) — and (ii)
**within-count uniformity** — given the count, the membership is uniform over
its fiber, which follows from **`newLeftCards_conjugate`** (equivariance) +
**`membershipFiber_transitive`** (transitivity).  *Concrete next step:* prove
the count-projection part (i) — reduce the `project`-fiber average of
`newLeftOriginalCount_eq` to the hypergeometric `transitionWeight` — likely via
a deck-level transitivity lemma (the `Equiv.Perm`-level analog of
`membershipFiber_transitive`) making the fiber-average depend only on the
source count, then compute it for a canonical deck.  F4.2 item 4 (Dobrushin
contraction / `Equiv.Perm (Fin 99)` lift) and F5 (full theorem) remain
downstream/blocked; do not re-attempt the `List.mem_bind`/`toMultiset` sub-wall.

**Splice-safety (23rd session):** a Python `s[:start] + ... + s[end:]` splice
with `end = s.rfind("-/")` (or any `find` returning `-1`) **silently truncated**
`CommanderPhysicalExchange.lean` to its last character (lost 267 lines of
committed code, including `newLeftCards_conjugate`).  *Always `assert end != -1
and start != -1` before a splice* (or use `s.split(anchor)` with a length
check).  The file was restored from `958d5f5` + the new lemma re-merged
(`dd221fd`).  Also: `∘` coerces `Equiv`/`Deck` to plain `Function.comp` (losing
the type) — use explicit `.trans`; and `f '' s` (Set image) breaks `Finset.ext`
— use `(s).image f`.

### Nov 14 (6th) session status — resume here first

This session completed the **F4.3 Fintype-free TV subadditivity** — the
last blocker in the `distProductFinsupp` route the 5th session documented —
**and the S1-side of the F3 item 3 general CL** (the `s1_bij`/`fiberA_card`
5th-session walls are broken). All committed; 37 tests pass; tree clean.

- **F4.3 core — GSR two-pile product mass from Finsupp weights**
  (`CommanderLocalGSR.lean`, `472efa8`): `gsrMapDelta_mass` (the one-coordinate
  `StdSimplex.map` image of a fixed first coordinate contributes the second
  law's mass exactly when the coordinates match), `gsrProductKernel_mass`
  (`(gsrProductKernel nL nR a b _ _ (L,R)).weights (L',R') =
  (idealShuffle nL _ _ L).weights L' * (idealShuffle nR _ _ R).weights R'`,
  via the `map`/`join` `AddMonoidHom` structure, not `apply_mass_dom`), and
  `gsrProductKernel_pointMass` (the same when the input is a point mass).
- **F4.3 Fintype-free product — `Finite.distProductFinsupp`** (`d3e010f`):
  `distProductFinsupp p q = (p.map (fun a => q.map (fun b => (a,b)))).join`,
  built from `StdSimplex.map`/`join` (no `Fintype`), with the simp-lemma
  `distProductFinsupp_mass : (distProductFinsupp μ ν).weights (a,b) =
  μ a · ν b`. This is the exact construction `gsrProductKernel` uses, so the
  two are structurally identical.
- **F4.3 Fintype-free TV — `TotalVariation`** (`1de7d21`, `a0444a9`):
  `tvFinsupp p q = (1/2) * (p.support ∪ q.support).sum |p-q|` (Fintype-free TV,
  coincides with `Dist.tv` on Fintype spaces); `suppDistProductFinsupp`
  (product support = Cartesian product of supports); `twoTv_eq_unionSum`;
  `not_mem_support_zero`; `sumOverEnlarged_eq_one` (mass 1 over any
  support-enlarging set); `productMassBound` (the scalar
  `|ab-a'b'| ≤ |a-a'| b + a' |b-b'|`); and the capstone
  **`distProductFinsupp_tv_subadditive :
  tv (prod μ ν) (prod μ' ν') ≤ tv μ μ' + tv ν ν'`** — the Fintype-free analog
  of `distProduct_tv_subadditive`, proved by moving the `L1` sum to
  `(supp μ ∪ supp μ') × (supp ν ∪ supp ν')`, pointwise `productMassBound`,
  and factoring both pile-sums to mass 1.

**F4.3 is COMPLETE.** Both payoff steps are done and committed:
  (a) `gsrProductKernel_eq_distProductFinsupp` (definitional bridge, `6a9eb6f`)
  and (b) `gsrProductKernel_rowTV_bound` (`6a9eb6f`) — for any two-pile product
  reference, the two-pile GSR kernel's TV is at most the sum of the per-pile
  GSR-vs-reference errors. (Note: `idealShuffle n a _ x` is NOT uniform for
  finite `a`; the "reference" in the row bound is a *parameter* `perfectL`/
  `perfectR`, not a fixed uniform — that generality is what makes it usable.)

### Nov 13 (11th) session status — resume here first

**F3 item 3 — all four summand matches and the summand-level assembly are
PROVEN; the general CL is the final (sum-reindexing) step.** This session
completed the remaining factor matches and the summand assembly:

- **`F4match`** (commit `2f93a91`): the 4th-factor bridge
  `chooseSigned (N-r-(m-y)) ((m-x)-((m-k)-(y-a))) = Nat.choose (N-m-r+y)
  (k-(x-(y-a)))`, via `intSub_eqCast` (new: `(a-b:Int) = ↑(a-b)` for `b≤a`)
  + `intSubSubAdd_eqCast` (new: `(N-m-r+y:Int) = ↑(N-m-r+y)` under
  `m+r≤N`). Together with the 9th/10th-session `F1match`/`F2match`/`F3match`,
  **all four factor matches are now proven.**
- **`tterm_eq_oterm`** (commit `135968c`): the *summand assembly* — in the
  admissible regime, `tterm (N m r k) x y a = oterm (N m r k) x y (y-a)`.
  The two 4-factor products differ only by the order of the middle (m/r)
  factors (`ring`) and the 4th-factor base `(N-m)-(r-y) = N-m-r+y`
  (`omega` under the regime). The two guards collapse via
  `rw [if_pos h1g, if_pos h2g]` (NOT `split_ifs`, which is a parse error).
- **`transitionNumerator_eq_sum_tterm`** (commit `b95f389`): the `a`-term of
  `transitionNumerator (N m r k) y x` (source `y`, target `x`) is
  definitionally `tterm (N m r k) x y a`, so the transition is the sum of the
  `tterm` summands over `a ∈ [0,k]` (by `rfl`).

With `overlap_eq_sum_oterm` (overlap = sum of `oterm` over `t ∈ [0, m-k]`),
`transitionNumerator_eq_sum_tterm`, and `tterm_eq_oterm`, the general CL
`transitionNumerator N m r k y x = overlap_count N m r k x y` is reduced to
the **final step: the `t = y - a` sum reindexing** between the `a`-sum
(`∑_{a∈[0,k]}`) and the `t`-sum (`∑_{t∈[0,m-k]}`).  The reindexing aligns the
supports: `oterm t = 0` outside `[max (0, y-k), min y (m-k)]` (from the
`(m-y, m-k-t)` factor), so both sums equal the sum over that common support.
Plan: (i) pointwise `tterm a = oterm (y-a)` for *all* `a` (generalize
`tterm_eq_oterm` to the guard-fail cases, both sides 0); (ii) `Finset.sum_bij`/
`sum_image` on the `a ↦ y-a` map; (iii) clip both `Finset.range` sums to the
common support using the `oterm = 0`-outside lemma.  Then F3 item 4
(2-exchange TV) follows from the CL + `fiberSum_eq`.  **No** `Finset`-API
2-bin products are involved.

11th-session gotchas (for the reindexing and future `Int`/`choose` work):
  - The CL is `overlap_count (N m r k) x y = transitionNumerator (N m r k) y
    x` — the **4th/5th arguments are swapped** (transition source `y`, target
    `x`); `tterm` uses `y` as its "source" (matching the overlap's `y`), so the
    reindexing is `t = y - a`.
  - `transitionNumerator`/`tterm` take **six flat args** (`N m r k x y a`), not
    a grouped `(N m r k)` triple — `transitionNumerator (N m r k) y x` is a
    parse error ("Function expected").
  - `Int.toNat_natCast (n : Nat) : (n : Int).toNat = n` is the correct
    `(↑n).toNat = n` lemma (NOT `Int.toNat_of_nonneg`, which gives an `Int`
    equality, not `Nat` equality).
  - `let`-bound variables inside a `def` (e.g. `nI`/`mI` in `oterm`) are NOT
    accessible in the proof — mirror them with explicit `let` in the proof, and
    make the key `have` (e.g. `hR : ↑(k-b) = …`) the *first* statement before
    any `dsimp` of `e`/`base`, or downstream `rw` pattern-matching fails.
  - `rw [if_pos h1g, if_pos h2g]` selects the nonzero branch of nested
    `ite`s; `split_ifs with h, h2` is a parse error in Lean 4.34.
  - `ring_nf` reorders/normalizes a product of atoms but reports "made no
    progress" when the only remaining difference is a `Nat`-subtraction base
    identity (e.g. `(N-m)-(r-y) = N-m-r+y`); prove that base identity
    separately (`omega` handles it in the regime) and `rw` it in, then a
    single `ring_nf` closes.

*Resume order:* **F3 item 3 (the general CL) is now COMPLETE** — `generalCL`
proves `transitionNumerator N m r k y x = overlap_count N m r k x y` (see the
12th-session note below).  The next deep step is **F3 item 4** (the unconditional
physical-perfect-local 2-exchange TV theorem), which follows from the CL +
`fiberSum_eq`/`fiberSum_swap`; then **F5 full/optimizer**.  **F4.5 full-deck
decay** (contractive) remains blocked on finiteness (the non-finite pile-list
space admits the non-expansive bound but not the Dobrushin contraction); defer.

### 12th-session status — F3 item 3 COMPLETE

**The general CL is proven symbolically** (three commits this session:
`tterm_eq_oterm_all`, `oterm_sum_clip_eq`/`finsetSum_zero_on`/zero-ness lemmas,
and `generalCL` — all in `ExchangeOverlap.lean`, all committed).

The proof closes the last step the 11th session had identified as stuck:
  1. `tterm_eq_oterm_all` — the **pointwise all-`a`** equality
     `tterm (N m r k) x y a = oterm (N m r k) x y (y-a)`.  Three cases: both
     guards hold (the 11th-session `tterm_eq_oterm`); the F4 guard fails
     (h1g holds, h2g fails) → `tterm = 0` and oterm's 4th factor has a negative
     index; the F2 guard fails (h1g fails) → `tterm = 0` and oterm's 2nd factor
     has a negative index.  The vanishing-factor closures use the **`let
     t := y-a` representation trick** (below) so `rw` locates the factor inside
     the 4-way product, then `chooseSigned_zero_neg` + `mul_zero`/`zero_mul`.
  2. `transition_eq_sum_oterm_ySuba` + `rangeImage_ySuba_eq_Icc` — reindex the
     transition `a`-sum over `[0,k]` to the `t`-sum over `[y-k,y]` via the
     injective map `a ↦ y-a` (a bijection for `k ≤ y`, by `Finset.sum_image`).
  3. `oterm_sum_clip_eq` — clip **both** the transition and the overlap `oterm`
     sums to the common range `[y-k, min (y, m-k)]`: `oterm t = 0` for `t < y-k`
     and `t > m-k` (F3 factor `choose (m-y) (m-k-t)` off-range) and for `t > y`
     (F1 factor `choose y t`), via `oterm_zero_below`/`above_mk`/`above_y` +
     `Finset.sum_sdiff` + `finsetSum_zero_on`.
  4. `generalCL` — assemble (1)–(3) + `overlap_eq_sum_oterm` +
     `Nat.range_succ_eq_Icc_zero` into
     `transitionNumerator N m r k y x = overlap_count N m r k x y` for the
     admissible regime (`k ≤ y ≤ m`, `y ≤ r`, `m+r ≤ N`, `r-y ≤ N-m`).

**The term-representation wall (11th session) is broken.**  The fix: inside the
guard-fail `have`, bind `let t := y-a` so the index is written as the **single
cast** `↑t` — exactly matching oterm's inlined `tI := t`.  Writing `(y-a : Int)`
fresh normalizes to the **difference of casts** `↑y - ↑a` (definitionally equal,
different AST), which is why `rw`/`simp`/`conv`/`change` all failed to locate the
factor inside the `dsimp`-ed 4-way product before.  `omega` proves the needed
`Int` cast inequalities (e.g. `(k:Int)+(t:Int) < (x:Int)`) directly from the
`Nat` guard hypotheses.

**m + r > N extension — RESOLVED this session.**  The 4th-factor base
subtlety (the left-saturated `N - m - r + y` = `y` vs the non-saturating
`(N-m) - (r-y)` = `y - 1` for the Commander) is fixed by using the
**non-saturating** base.  The chain `baseInt_eqNatCast` → `F4match_ns` →
`tterm_eq_oterm_ns` → `tterm_eq_oterm_all_ns` → `transition_eq_sum_oterm_ySuba_ns`
→ **`generalCL_ns`** proves the counting identity **without** `m + r ≤ N`, and
**`generalCL_cmdr_2525`** proves the 25-25 Commander transition **symbolically**
(no `native_decide`).  With `generalCL` (`m + r ≤ N`) the counting core
`transitionNumerator = overlap_count` now holds for **every valid deck**
(Commander 99 50 50 25 and 7442 included).

**Next (F3 item 3 core / item 4 — part (ii) only):** the counting (part (i)) is
done.  The remaining half of the kernel equality
`comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
membershipLift` is **part (ii): given the new count `m`, the new membership is
uniform over `{μ : membershipCount μ = m}`** — a member-level symmetry
(group-action) statement, distinct from the count-level CL.  Then the 2-exchange
TV (`run_tv_eq_macro_of_membership_exchange`, already a proven general theorem)
instantiates with this `hMembershipExchange`.  See `lean_plan.md` F3 item 4.
The guard-FAIL cases and the reindexing are regime-independent (reused verbatim
in the `_ns` chain); only the 4th-factor base changed.

### Nov 12 (8th) session status### Nov 12 (8th) session status (historical — superseded by the 12th-session note above)


**F3 item 3 general CL fully scoped (the last deep step).** This session
extracted the **parameter-free** module `Shufflemath.FinsetFiberCount`
(commit `6ae278f`) and reduced the general CL to a *sum* equality.
CRUCIAL correction (commit `0811eb6`): the pointwise identity
`g(a) = h(y-a)` is **false** for `a > y` (Nat-saturating `t := y-a` to `0`
makes `h(0)` potentially nonzero while `g(a)=0`). The correct target is
`transitionNumerator (N m r k) y x = overlap_count (N m r k) x y` as a
**finite-sum** identity. The `ExchangeOverlap.lean` section comment records
the exact factor structures and the support alignment:
  - transition summand `tg(a) = choose x a · choose (m-x)(k-a) · choose
    (r-x)(y-x+a) · choose (N-m-r+x)(k-y+x-a)`, summed over `a ∈ [0,k]`;
  - overlap summand `oh(t) = choose (r-y)(x-t) · choose (N-r-m+y)(k-x+t) ·
    choose r x · choose (N-m)(x-k)`, summed over `t ∈ [0, m-k]`.
This is a **generalized Vandermonde / hypergeometric convolution** between
the two 4-factor decompositions (NOT a simple 1-factor Vandermonde). On the
common support (after `t := y-a`, both reduce to `[max (0, y-k), min y
(m-k)]`) the factors match by `Nat.choose_symm`/`choose_sub`; off support
both sides vanish. Remaining difficulty: (i) the exact `Finset.sum_bij`/
`sum_image` reindex of the two `Finset.range` sums, and (ii) aligning the
*different* pulled-out constants (`choose (N-m)(x-k)·choose r x` on the
overlap side vs `choose (m-x)(k-a)·choose (N-m-r+x)(k-y+x-a)` structure on
the transition side). Small-deck versions (`…_cmdr_251`, `overlap_count_symmetry`)
already confirm the identity; the general proof is the final F3 item 3 step.

*Resume order:* The **F4.5 Fintype-free foundation is COMPLETE** (this
  session): `apply_mass_finsupp`, `kernel_apply_lipschitz` (the Fintype-free
  1-Lipschitz kernel contraction), `mixtureTV_le`, `gsrOneStep_terminalTV_bound`
  (the 49+50 two-pile 1-step terminal bound), `run_nonexpansive`, and
  `gsrRunNonexpansive` (multi-step non-expansiveness for GSR schedules).
  Next: (1) **F3 item 3 general CL — S1-side DONE this session** (`d55b69d`):
  `s1Fiber_biUnion` (S1 fiber = pairwise-disjoint biUnion of per-`A` fibers),
  `fiberA_card` (a single fiber's count = the outside part, via the *dependent*
  `Finset.card_bij (fun S1 _ => S1 \ T1)`), `s1Fiber_card` (the `card_biUnion`
  + sum-of-constant assembly), and **`s1Fiber_choose`** (closed form
  `|s1Fiber x t T1| = choose |T1| t * choose (|stars|-|T1|) (x-t)` for any
  `ExchangeAdmissible`).  The 5th-session wall is bypassed: **no 2-bin product
  finset** is built — we decompose by the intermediate `A = S1 ∩ T1` and use
  `Finset.card_bij` + `Finset.card_biUnion` + `Finset.card_powersetCard` instead
  (`Finset.product`/`×˘` never reduced under `rw [card_product]`/`mem_product`).
  6th-session gotchas recorded in `ExchangeOverlap.lean`: Finset membership is
  an opaque `Quot.lift` (only `rw [mem_inter|mem_sdiff|mem_union]` then `rcases`);
  the `∃ a ha, …` form needs `refine ⟨…, ?_, ?_⟩` (`use` fills only `a`);
  conjunctions nest as `((P ∧ Q) ∧ R)` (use `And.intro (And.intro …)`);
  the empty-set direction closes by `cases` on `List.Mem z []` (`mem_empty`
  does not exist); `Nat.sub_add_cancel` (not `add_sub_cancel_left`) for
  `t + (x - t) = x`.  A new **parameter-free** module `Shufflemath.FinsetFiberCount`
  (commit `6ae278f`) factors the S1/S2 fiber machinery out of
  `ExchangeOverlap.lean` (defs `sFiber`/`sFiberA` + theorems `sFiber_biUnion`,
  `sFiberA_card`, `sFiber_card`, `sFiber_choose`, requiring only `[DecidableEq α]`)
  so both the marked and plain sides instantiate the same general lemma.
  **(2) Next concrete step — the general CL, now sharply narrowed (commits
  `08a864b`, `19892fa`):** since `fiberSum_eq` and `fiberSum_swap` are both
  already proven, the full symbolic CL
  `fiberSum p x y = choose(p.r,y)*choose(p.N-p.r,(p.m-y))*overlap_count (…)`
  reduces, for a valid macro state, to the **single** pure-`Nat`/`choose`
  identity `transitionNumerator (N m r k) y x = overlap_count (N m r k) x y`
  (only `native_decide` small-deck versions exist).  The `ExchangeOverlap.lean`
  section comment records the full analysis: the reindexing `t = y - a` (marked
  overlap = source marked − marked moved out) makes the four transition factors
  match the four overlap factors (two by `Nat.choose` symmetry), and the only
  remaining difficulty is the **boundary** (the transition sum's `if`-guards /
  `Nat`-saturated `y - a` vs the overlap sum's `chooseSigned = 0` out of range).
  The proof is a pure `Nat`/`choose` reindexing with **no** `Finset` API.  OR go
  straight to (3) F3 item 4 (2-exchange TV, downstream of this CL).
  (4) F5 full/optimizer. (5) **F4.5 full-deck decay**
  (contractive, to uniform) — blocked on finiteness: the non-finite pile-list
  space admits the non-expansive bound but not the Dobrushin *contraction*; a
  decay result needs the F4.2 Deck-level GSR lift to `Equiv.Perm (Fin 99)`
  (the `List.mem_bind`/`toMultiset` sub-wall) or a new Finsupp Dobrushin
  coefficient (incompatible with the non-finite space). Defer.

### Nov 12 (3rd) session status — resume here first

**F4.1 is COMPLETE.** The capstone theorem is proved and committed
(`17ffab6`):

- **`productLabelShuffle_uniform_eq_ideal`** (`GSR.lean`):
  `productLabelShuffle a b (uniformLabels n a) (uniformLabels n b) =
  idealShuffle n (a*b)` for `0 < a`, `0 < b`. A two-stage uniform
  `a`- then `b`-label shuffle has exactly the law of a single uniform
  `(a*b)`-alphabet inverse riffle. Assembled from the joint-distribution
  bridge, the `labelReparam` pushforward, and the sorting-compatibility
  identity.
- **`apply_mass_dom`** (`Finite.lean`): the `apply`-row-mass formula with
  the (unused) codomain `Fintype`/`DecidableEq` instances dropped, so the
  bridge and `map_uniform_mass` apply at the deck level where the output is
  `List (Fin n)` (not `Fintype`).
- **Relaxed `map_uniform_mass` and the joint-distribution bridge** in
  `GSR.lean` (codomain needs only `DecidableEq`).

All 37 tests pass. **F4.1 is now a finished theorem in the library.**

### Nov 12 (4th) session status — resume here first

This session (post-F4.1) made two committed results and a precise
analysis of the two remaining hard walls:

- **F4.2 set-preservation — `stableBuckets_set`** (`GSR.lean`,
  `fa13f57`): `x ∈ stableBuckets a labels deck ↔ x ∈ deck`. A GSR stable
  sort of a pile keeps exactly the pile's cards (every card lands in the
  unique bucket matching its label), so the *set* — and hence the
  membership state — is preserved by a GSR step. Proved by expanding
  `List.flatMap`/`List.filter`/`List.range` and bridging `==` with
  `beq_iff_eq`.
- **F4.2 remaining (wall):** the *multiset* permutation
  (`stableBuckets` preserves the deck up to `Multiset`/`List.Perm`) is the
  linchpin for building the GSR product as a `Deck` (`Equiv.Perm`). In
  this Mathlib/Lean build the direct routes are blocked:
  `List.mem_bind`, `List.length_filter`, `List.toMultiset`, and
  `Multiset.count_ofList` do not exist; the `List.sum`→`Finset.sum`
  conversion and the `flatMap`-with-conditional-insert → `insertIdx`
  rewrite each resist repeated attempts. `stableBuckets_set` (above) is
  the essential *set* content; the multiset/permutation fact is the
  remaining sub-wall for the F4.2 GSR product.
- **F3 item 3 general identity — reduced to one counting lemma.** The
  identity `overlap_count (n m r k) x y = transitionNumerator (n m r k) y x`
  (small-deck + Commander `native_decide` checks in `ExchangeOverlap.lean`)
  no longer needs the raw hypergeometric convolution. It follows from the
  **fiber-counting lemma (CL)** —
  `fiberSum p x y = choose(r, y) * choose(N - r, m - y) *
  overlap_count (N m r k) x y` — plus the already-proved `fiberSum_swap`
  and `fiberSum_eq` (the stationary `choose` factors cancel; the plain
  factor is `N - r`, not `N - m`, which coincide only at `r = m`).
  **CL is verified on all three small decks**
  (`fiberCounting_{6321,7442,8431}`, `native_decide`). The **single
  remaining piece** is the general (symbolic) proof of CL: reindexing the
  7-way `fiberSum` sum into the `(S, T)` double count (the unique-exchange
  per target). This is the last blocker for F3 item 4 and F4.5.

**All 37 tests pass; working tree clean.**


### Nov 12 (5th) session status — resume here first

This session advanced **F4.2**, **F5**, and the **F3 item 3** reduction (all
committed; 37 tests pass; tree clean):

- **F4.2 GSR product — `gsrProductKernel` + `gsrLocal_preserves_pile`**
  (`CommanderLocalGSR.lean`, `4e1b76f`). `gsrProductKernel (nL nR a b) :
  FiniteKernel (List (Fin nL) × List (Fin nR)) (same)` applies the F4.1
  `GSR.idealShuffle` independently to each pile and joins the two outputs.
  `gsrLocal_preserves_pile` states the membership content: a within-pile GSR
  output holds exactly the pile's original cards (`stableBuckets_set`). The
  *distributional* multiset/permutation fact (that the output is a genuine
  `Multiset`-equal / `List.Perm`-equivalent rearrangement, not just set-equal)
  remains the F4.2 sub-wall (missing `List.mem_bind`/`length_filter`/
  `toMultiset` in this build); the set-preservation is the essential F4.2
  content for membership.
- **F4.3 row-wise TV machinery — `distProduct` + `distProduct_tv_subadditive`**
  (`87cc71f`, `104fd5e`). `Finite.distProduct μ ν : Dist (α × β)` is the
  independent (tensor) product of two finite distributions — a valid
  probability law (total mass factors to `(∑ μ)(∑ ν) = 1·1`, proved via
  univ-product reindex + `Finset.sum_product` + `mul_sum` factoring +
  `sum_mass`), with the simp-lemma `distProduct_mass : mass (distProduct μ ν)
  (a,b) = μ(a)·ν(b)`. `TotalVariation.distProduct_tv_subadditive`:
  `TV(μ⊗ν, μ'⊗ν') ≤ TV(μ,μ') + TV(ν,ν')` — the two-pile row-wise bound: a step
  that shuffles two piles independently is discrepant from a reference by at
  most the sum of the two per-pile discrepancies (triangle inequality +
  nonnegativity + Fubini). This is the general reusable core of F4.3.
  **Wall (documented):** instantiating it to the *actual* `gsrProductKernel`
  vs the perfect-local reference is blocked on a **Fintype** requirement, two
  ways over: (a) `Finite.distProduct` is defined via `Dist.ofFun`, which needs
  `[Fintype α] [Fintype β]`, so `distProduct (GSR.idealShuffle nL a _ L)
  (GSR.idealShuffle nR b _ R)` cannot even be *constructed* — `idealShuffle`
  is a `FiniteKernel (List (Fin n)) (List (Fin n))` and `List (Fin n)` has no
  `Fintype` instance; (b) the `gsrProductKernel` nested `map`/`join` mass
  reduction normally goes through `apply_mass_dom`, which also needs a
  `Fintype` domain. Both walls share the same root (non-Fintype `List (Fin n)`
  domain). **Route:** a *Fintype-free* product distribution — construct
  `StdSimplex (α × β)` directly with `weights = ∑_{a∈μ.support} ∑_{b∈ν.support}
  single (a,b) (μ a · ν b)` (a finite double Finsupp sum, no `Fintype`), prove
  its total mass `(∑ μ)(∑ ν) = 1` by summing over the finite Finsupp support,
  and the mass formula `weights (a,b) = μ a · ν b`; then `gsrProductKernel (L,R)`
  equals that product and `distProduct_tv_subadditive` (re-stated over Finsupp
  sums, not `Finset.univ`) gives the per-pile bound.
- **F5 — `costed_terminalTV_le` + `protocolCost_nonneg` + `ActionKind` +
  `costedProtocol_certificate`**
  (`e203310`, `ec68b71`, `4d08580`). `ProtocolCertificate.costed_terminalTV_le`: a costed
  schedule's terminal TV ≤ `errorBudget` of its step kernels + the
  ideal-reference TV (reuses `terminalTV_le_reference_add_budget`; no F4
  instance required, so it advances independently). `Cost.protocolCost_nonneg`
  (a schedule of nonnegative-cost actions has nonnegative total cost) and the
  `ActionKind` inductive (`localRiffle`/`exchange`/`splitRecombine`).
- **F3 item 3 — clean CL derivation recorded** (`ExchangeOverlap.lean`,
  `ef93f8d`): the general identity needs only the symbolic
  `fiberSum p x y = choose(r,y)·choose(N-r,m-y)·overlap_count (N m r k) x y`,
  because that plus `fiberSum_swap` and `fiberSum_eq (y x)` cancels the
  nonzero `choose` factor to `overlap_count (N m r k) x y =
  transitionNumerator (N m r k) y x`. Equivalently, reindex the 7-tuple fiber
  to the `(S,T)` pair (`A = S\T`, `B = T\S`, `|S∩T| = m-k`). The recorded
  TODO lists this build's Finset API walls (`Finset.card_le`,
  `not_mem_empty`, `product`-notation, and `mem_powersetCard`-at-h recursion
  all fail; use `sum_le_sum`, `card_bij` on `image` targets). `inter_sdiff_union`
  (the reconstruction identity) is proven.

**All 37 tests pass; working tree clean.**

*Resume order:* (1) F4.3 — the `gsrProductKernel = distProduct` point-mass
connection (wall above; prove from Finsupp weights, not `apply_mass_dom`), then
state the per-pile GSR-vs-uniform TV bound. (2) F3 item 3 general CL (symbolic
identity, Finset API wall). (3) F3 item 4, F4.5, F5 full/optimizer — all
downstream of (1)/(2).

### Nov 12 (2nd) session status — prior session (reference)

This session (after GPT-6.5's unblock doc `docs/qwen_unblock_nov12.md`) made
**three substantial committed wins** (all 37 tests pass; working tree clean):

- **F4.1 sorting-compatibility — the `Bool`/`==`/`&&` bridge is DONE.**
  The per-card filter predicate `combineVal_filter_eq` and the full
  `stableBuckets_combine_eq_lex` are committed in `GSR.lean`. The key
  correction from GPT's candidate: use **`beq_iff_eq`** (an `Iff`:
  `(a == b) = true ↔ a = b`) and **`Bool.and_eq_true_iff`** (an `Iff`:
  `(x && y) = true ↔ x = true ∧ y = true`), NOT `Nat.beq_eq` (an
  `=`-of-`Prop`, which does not compose with `Bool.eq_iff_iff`). The proof
  goes `Bool.eq_iff_iff.mpr` → `beq_iff_eq` → the `=`-world `combinedLabel_pred`
  → `Nat.div_add_mod`/`mod_lt`. **F4.1 kernel equality:** COMPLETED in the
  3rd session (`productLabelShuffle_uniform_eq_ideal`, `17ffab6`).
- **F4.2 local-shuffle — the bijection is DONE via `Equiv` construction.**
  `Shufflemath/CommanderLocalGSR.lean` now has `pileRelabelEquiv pl pr : Fin
  99 ≃ Fin 99` (built on GPT's **`finSumFinEquiv`** + `Equiv.sumCongr` +
  `Equiv.trans`, avoiding the manual `if p.val < 50` `Fin`-equality wall) and
  `reorderedDeck`/`reorderedDeck_leftCards`. `finSumFinEquiv` itself does not
  reduce under `simp` (it is defined by `Equiv.ofFun` with an explicit
  `isLt` proof), so the apply-lemmas are `finSumFinEquiv_apply_left/right`.
  **F4.2 remaining:** the *GSR product* — a `FiniteKernel Deck Deck` where
  the pile permutations are GSR-distributed (route in the unblock doc §3).
  The deterministic membership-preservation (`reorderedDeck_leftCards`) is done.
- **F3 item 3 — sub-lemma 1 and sub-lemma 3 done; 5-conjunct assembly still open.**
  `Shufflemath/FinsetCombinatorics.lean` has `isExchangePair`,
  `exchangePair_unique_B`, `exchangePair_unique_A`, `cardSdiffInter`,
  `cardSdiffInter2` (the 5-conjunct canonical-pair *cardinality* identity).
  **Sub-lemma 3 (overlap = reversed transition numerator) is now proved** in
  `Shufflemath/ExchangeOverlap.lean`: `chooseSigned` (Int-based, mirrors the
  Python reference `choose`) + `overlap_count` (four-bin count computed in
  `Int`), and `native_decide` proves `overlap_count (n m r k) x y =
  transitionNumerator (n m r k) y x` QUANTIFIED over the full valid
  marked-count range of three small decks `(6,3,2,1)/(7,4,4,2)/(8,4,3,1)`
  (exact `Fin` ranges, offset by `1` for the deck whose range starts at `1`)
  plus three Commander `(99,50,50,25)` spot checks (incl. `(10,40)`, which the
  `Nat`-saturated version got wrong). **Wall 1:** the *general* (non-numeric)
  overlap identity is still open — it is a genuine hypergeometric/Vandermonde
  convolution, not a reindexing (the LHS and RHS sums have different
  summands), so a structural/bijection proof is needed. **Wall 2:**
  `exchangePair_exists` (assemble the 5-conjunct `isExchangePair` in a
  `Fintype` context) hits `Finset`-quotient `rw`/`by simpa`-in-term-position
  quirks. See `docs/f3_membership_exchange.md`.

- **F3 item 3 — the four-bin `overlap_count` def is in place.**
  New file `Shufflemath/ExchangeOverlap.lean` (green, committed):
  `overlap_count (n m r k) x y` is the four-bin (marked/unmarked ×
  in/outside-T) `choose`-sum counting the `m`-subsets `S` with `x`
  marked cards and `|S ∩ T| = m - k` for a fixed `T` holding `y`
  marked identities.  This is the left-hand side of the F3 item 3
  identity `overlap_count (n m r k) x y =
  transitionNumerator (n m r k) y x` (reversed numerator; the Python
  test `tests/test_exchange_overlap_identity.py` verifies it by exact
  `int` arithmetic on three small decks + all 2,500 Commander pairs).
  *Wall:* the Lean proof of the identity (or the small-deck
  `norm_num` regression) is blocked because this Mathlib build's
  `norm_num` has no `Nat.choose` / `Finset.sum (Finset.range …)`
  extension (and `List.mem_bind`, `Fin.val_lt`, `List.toMultiset`
  are absent; use `Fin.isLt` / `.2` and avoid those).  The
  `Finset.sum_range_one`/`_succ` lemmas do exist for manual
  expansion, but `range 26` is not practical by hand.

**The GPT-6.5 unblock doc `docs/qwen_unblock_nov12.md` is the authoritative
guide** for the remaining F4.1-kernel, F4.2-GSR-product, and F3-item-3
routes. It contains the exact `Finsupp`/`Multiset`/`Equiv` routes and the
specific Mathlib lemmas (`Fin.sumFinEquiv`, `Equiv.sumCongr`,
`Multiset.ofFin`, `Finsupp.image_sum`, etc.).

### Nov 12 (1st) session status — prior to the GPT-6.5 unblock

**Build was green on all target modules; all committed.** The first Nov 12
session made the following committed progress (see `git log`):

- **F4.1 sorting-compatibility — the `List.range` wall is BROKEN.**
  `List.range_add` exists in this build (`List.range (m+n) = List.range m ++
  List.map (fun x => m + x) (List.range n)`), which gives the block
  decomposition the old notes said was missing. On top of it, **three new
  lemmas are committed in `GSR.lean`:** `div_block`/`mod_block` (for `x < a`,
  `(a*b' + x)/a = b'` and `(a*b' + x)%a = x`) and `rangeMap_divmod_eq_nested`
  (the `(div,mod)` sequence over `List.range (a*b)` equals the nested `(j,i)`
  sequence over `List.range b × List.range a` in lexicographic order — the
  *index-level* content of the sorting-compatibility, proved by induction on
  `b`). **Remaining F4.1:** the per-card filter predicate in the `Bool`/`==`/`&&`
  world (the `Nat.beq_eq` bridge handles a bare `==` comparison but not the
  `Bool`-equality goal left by `List.filter_congr`; the route is `split_ifs` on
  the `==` bools, using `combinedLabel_pred` + `Nat.div_add_mod` in the `=`
  world) plus the flatMap assembly via `rangeMap_divmod_eq_nested` +
  `List.flatMap_map`. Then the kernel equality
  `productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b) (a*b)`
  follows. **Do not re-attempt the `Int`-cast or `noCarryEq` routes** (the
  block decomposition is now available); also note the `decodeLabel` `Fin.val`
  unfolding causes a `simp` recursion loop, so prove the `combineVal` fact by
  `change`/`rfl`, not `simp`.
- **F4.2 local-shuffle — core done.** New file `Shufflemath/CommanderLocalGSR.lean`
  (green, committed): `pileRelabelFn pl pr` (left positions permuted by `pl`,
  right by `pr`, never crossing piles) + `pileRelabelFn_left`/`_right`, and
  `permutedLeftCards_eq` proving the left-card set of the permuted deck equals
  `leftCards d` (via `univImage_reindex`, a bijection leaves the image of
  `univ` unchanged). **This is the F4.2 core: a local shuffle cannot change the
  membership state.** *Remaining F4.2:* prove `pileRelabelFn` is a bijection
  (to make a valid `Deck`/`FiniteKernel`) and take the GSR product over the two
  piles.
- **F3 item 3 core — still open** (the hard hypergeometric counting identity);
  see `docs/f3_membership_exchange.md`. F3 item 4 (2-exchange TV) and F4.3–F4.5
  remain downstream of it.

**Recommended next action:** F4.1 is **substantially along** — the label-law
(`productLabels_pushforward_uniform`), the two-ruffle composition law
(`labelShuffle_comp`), and all the mechanism ingredients (`encodeLabel`/`decodeLabel`,
`combineLabels`/`splitLabels`, `labelReparam`, `mixedRadix_unique`,
`combineVal_pred_eq`, `rangeMap_divmod_eq_nested`, `div_block`/`mod_block`) are
proved and committed. The **F4.1 goal** is the kernel equality
`productLabelShuffle a b (uniform a) (uniform b) = idealShuffle n (a*b)`, which
*follows from* the list-level sorting-compatibility
`stableBuckets (a*b) (combineLabels …) = lexBuckets a b …` (the last step is the
`Bool`/`==`/`&&` filter bridge — see `docs/f41_sorting_compatibility.md`). So
F4.1 and its kernel equality remain open on that one bridge.

Priority order for the remaining items:
1. **F3 item 3 core** (`docs/f3_membership_exchange.md`) — the hard hypergeometric
   counting identity; the critical path for F3 item 4 (2-exchange TV) and F4.5.
2. **F4.2 bijection** (`docs/f42_local_gsr.md`) — `pileRelabelFn_leftVal`/`_rightVal`
   helpers are done; the `leftVal`/`rightVal` disjoint-range case analysis for
   injective/surjective is the remaining step, then the GSR product kernel.
3. **F4.3** (row-wise TV bound) and **F4.5** (full-deck terminal bound — needs F3
   item 4 and F4.3/F4.4), then **F5** (measured/parametric costs, bounded
   optimizer certificate).

Apply the stuck protocol (`-- TODO(proof)`, commit what builds, move on) after
~2 failed iterations on any single proof. Re-run `./dev/verify_next_phase.sh`
after each tranche.

**Walls hit this session (do not re-derive):**
- **`Finset ⊆` is `Set`/`Multiset`-based** (`Finset.subset_def`, `mem_coe`).
  Applying a subset hypothesis `hLs : L ⊆ s` to a membership `hxL : x ∈ L` to
  get `x ∈ s`: `exact hLs hxL` works when `x ∈ s` is the *direct goal*, but
  `have h : x ∈ s := hLs hxL` (and `:= by exact hLs hxL`) fail with "Type
  mismatch / assumption failed". A `rcases`-derived `hxL` behaves differently
  from a binder-derived one. Route through `Finset.mem_coe` or make `x ∈ s`
  the direct goal. (This blocked `sdiff_in_complement`; see
  `docs/f3_membership_exchange.md`.)
- **`pileRelabelFn`'s `if h : p.val < 50` has a fresh binder.** Reduce it with
  `dsimp only [pileRelabelFn]` + `simp [hlt]` (or `by_cases hlt` then
  `split_ifs`), not with the hypothesis directly. The `leftVal`/`rightVal`
  helpers use exactly this. The `Fin` proof-irrelevance of `⟨v, h1⟩` vs
  `⟨v, h2⟩` (same `val`, different `isLt`) means `⟨v, h1⟩ = ⟨v, h2⟩` needs
  `Fin.ext`/`rfl` on `v`, not definitional equality.
- **`Bool`/`==`/`&&` filter bridge** (`List.filter_congr` leaves a `Bool`-
  equality goal): `Nat.beq_eq` bridges a *bare* `==`↔`=` comparison and
  `(b1 && b2) = true ↔ (b1 = true) ∧ (b2 = true)` is simp-able, but the
  full `Bool`-equality goal resists `simp [Nat.beq_eq]` in this build. The
  `by_cases`/`split_ifs` route on the three `==` bools (using `combineVal_pred_eq`
  in the `=` world) is the identified path — not yet completed.
- **F4.2 injective proof**: the same-pile case reduces to
  `leftPosition (pl ⟨p⟩) = leftPosition (pl ⟨q⟩)` → `⟨p⟩ = ⟨q⟩` → `p.val =
  q.val` (via `leftPosition_injective` + `pl.injective` + `Fin.ext`); the
  cross-pile cases use `pileRelabelFn_leftVal`/`_rightVal` (disjoint ranges).
  The `if`-reduction + `Fin` proof-irrelevance are the fiddly parts.

### (Prior state, Nov 11 — reference)

**F1 is COMPLETE (commit `12e66df`). F2 is COMPLETE.** In
`Shufflemath/CommanderMembershipKernels` (green, committed):
* F2a: `Membership`, `membership`, `membershipCount`, `membershipFiber_iff`.
* F2b: `localLift` (perfect-local) + `localLift_preserves_membership`.
* F2c-i: `MembershipFiber` + `MembershipFiber_card` + `membershipFiberCount`.
* F2c-ii/iii: `membershipLift` (normalised to sum 1) + `apply_mass_eq_sum`.
* F2c-iv-a: `fiberSet_project_decomp` + `membershipFiber_disjoint`.

**F2 is COMPLETE (commit `19d417c`). F3 items 1, 2, and 3a are COMPLETE. F3 item 3 core is the current hard item.**

The F2c-iv-b capstone `membershipLift.comp localLift =
FiberDisintegration.fiberLaw project project_surjective` is **proved** (full
*kernel* form, not just point-mass). The earlier notes in this section and in
[`f2c_ivb_sum_collapse.md`](f2c_ivb_sum_collapse.md) describing a
normalisation / `ext` wall are **superseded**: the wall was the *default
`simp` set* (and `field_simp`, which uses it) unfolding `membership`/`leftCards`
(terms depending on `d : Equiv.Perm (Fin 99)`). Written with `simp only` over an
explicit lemma list, `ite_eq_left`/`ite_eq_right` `ite` reductions, and
`by_cases` on the `Membership`/`Nat` equalities, the proof never recurses, and
the kernel-level lift is just `StdSimplex.weights_inj` + `Finsupp.ext` (both
non-recursing over `Finsupp Deck`). **Do not re-attempt the `Finsupp.mapDomain`
or `DecidableEq (Equiv.Perm …)` pushforward routes** — they are obsolete.

**(Nov 11 reference) Next action: F3 item 3 core.** In
`Shufflemath/CommanderPhysicalExchange`, done: item 1 (`newLeftCards d L R`,
`newLeftOriginalCount_eq`), item 2 (`rawExchange : FiniteKernel Deck Deck` via
`rawExchangeMembership` + `localLift`, commit `b25d5f4`), item 3a
(`hMembershipExchange_lhs_reduces`, commit `958d5f5`). The **open core** is:
```
comp (FiberDisintegration.fiberLaw project project_surjective) rawExchangeMembership
  = comp BernoulliLaplace.commanderExchange25 membershipLift
```
Mass-at-`m` (from input `x`) is the exact counting identity
`|{(d,(L,R)) : project d = x, newLeftCards d L R = m}| / (|fiber project x| * choose 50 25 * choose 49 25)
= transitionWeight 99 50 25 (count x) (count m) / |{m' : count m' = count m}|`.
Two parts: (i) the new-count distribution equals the Bernoulli--Laplace
`transitionWeight` hypergeometric sum, (ii) *given* the new count the new
membership is *uniform* over that count's fiber (a symmetry/group-action
statement — the harder half). On the critical path for F3 item 4 (2-exchange TV)
and F4.5.

**Alternate if the F3 core stalls (stuck protocol): F4.1 (standalone GSR
product-alphabet) in `GSR.lean`** — the sorting-compatibility lemma
(`stableBuckets (a*b) (combineLabels …) deck = lexBuckets a b minor major deck`)
and the kernel equality `productLabelShuffle (uniform) = idealShuffle`. The
single-label core (encodeLabel/decodeLabel, combineLabels/splitLabels,
labelReparam, map_bijective_uniformDist, productLabels_pushforward_uniform) is
done. The sorting-compatibility prior attempts hit `List.range.loop` /
`Nat`-cancellation elaboration and were reverted; retry with the `Int`-cast
arithmetic or by proving `stableBuckets (a*b) (combineLabels …) deck =
stableBuckets b major (stableBuckets a minor deck)` and reusing the existing
`stableBuckets_comp` theorem (= `lexBuckets`).

After F3, run `./dev/verify_next_phase.sh`, then **F4** (the standalone GSR
product-alphabet in `GSR.lean` — sorting-compatibility / kernel equality — and
the local-GSR kernel / row-wise TV / telescope). The F1 API notes below remain
useful reference.

**F4.1 (standalone GSR product-alphabet) progress — independent of the
`Equiv.Perm` wall, in `GSR.lean` (all green, committed):** the single-label
lexicographic core is done: `encodeLabel`/`decodeLabel` split a `Fin (a*b)`
label into a `Fin b` major and `Fin a` minor (a bijection, with
`encodeLabel_decodeLabel`/`decodeLabel_encodeLabel`); `combineLabels`/
`splitLabels` lift this per-card to label arrays and assemble the
`labelReparam` `Equiv`; `map_bijective_uniformDist` (a bijection carries the
uniform law to the uniform law on the target, proved via the singleton-fiber
pushforward mass) plus `productUniformLabels` and
`productLabels_pushforward_uniform` show the `(a*b)`-alphabet GSR label law
equals the pushforward of the independent product of a `b`- and an
`a`-alphabet law. **Remaining F4.1:** the sorting-compatibility lemma
(`stableBuckets (a*b) (combineLabels …) deck = lexBuckets … deck`, via mixed-
radiex uniqueness of `major*a+minor` and the `range (a*b)` block decomposition)
and the kernel equality `productLabelShuffle (uniform) = idealShuffle` that
follows. *Note:* the first `noCarryEq`/`rangeProductBlocks` attempts hit
`List.range.loop` / `Nat`-cancellation elaboration issues and were reverted;
retry with the `Int`-cast or explicit `Nat.eq_of_mul_eq_mul_left`.

* `leftPile S := {x // x ∈ S}` and `rightPile S := {x // x ∈ (Finset.univ \ S)}`
  (abbrevs, so `Fintype.Subtype.fintype` synthesizes).
* `leftEquiv S d hd : Fin 50 ≃ leftPile S` — built via
  `Equiv.ofBijective (leftFun S d hd) ⟨inj, surj⟩`; `leftFun i = ⟨d
  (leftPosition i), leftCardInS⟩`. **Key:** build the equiv to the plain
  subtype (NOT to `(S : Set)`); the `⟨x, proof⟩` construction works once the
  target is `{x // x ∈ S}`. `leftEquiv_apply`, `leftEquiv_card = 50!`.
* `rightEquiv S d hd : Fin 49 ≃ rightPile S` — `rightFun j = ⟨d (rightPosition
  j), rightCardInS⟩`; `rightCardInS` reduces to `Finset.univ \ S` and closes
  with `simp only [Finset.mem_sdiff]` + `constructor` (membership in an sdiff
  is *not* an inductive type, so a bare `constructor` fails).
  `rightEquiv_apply`, `rightEquiv_card = 49!`.
* `deckFunSub S eL eR p` / `deckFunInvSub` — the position-wise (resp. value-wise)
  assembly, now over the subtype equivs; `left_invSub` (`deckFunSub ∘ deckFunInvSub
  = id`), `deckFunSub_left` / `deckFunSub_right`.
* `pasteDeckSub S eL eR : Deck` — `Equiv.ofBijective (deckFunSub …)`; surjectivity
  is `left_invSub`, injectivity is `Finite.injective_iff_surjective` (namespace
  **`Finite`**). `pasteDeckSub_leftCards` (left pile = `S`), `pasteDeckSub_self`
  (`pasteDeckSub (leftEquiv d) (rightEquiv d) = d`, by `apply Equiv.ext` +
  `change` + `split_ifs` — **`split_ifs` is the only tactic that splits a
  named-binder `if` inside a `def`**).
* `toLR / fromLR` and the inverse laws `fromLR_toLR`, `toLR_fromLR`; then
  `decksLR : decksWithLeft S ≃ (Fin 50 ≃ leftPile S) × (Fin 49 ≃ rightPile S)`
  via `Equiv.ofBijective (toLR S) ⟨inj, surj⟩`, where injectivity and
  surjectivity fall out of the two inverse laws (no `admit`/`sorry`).
* **`decksWithLeft_card : Fintype.card (decksWithLeft S) = 50! · 49!`** — the
  F1a deliverable: `rw [Fintype.card_congr (decksLR S), Fintype.card_prod]` +
  `simp [leftEquiv_card, rightEquiv_card]`. (`Fintype.card_congr` is the
  equiv-transport lemma; `Fintype.card_equiv` is for counting the equiv space
  itself and is *not* the right tool here.)

**F1b is COMPLETE and green.** `Shufflemath/CommanderFiberMembership.lean`
builds (`lake build Shufflemath.CommanderFiberMembership`, EXIT 0) and proves the
membership-set count. The fiber over `x` (where `k = x.val + 1` initially-left
cards remain) is determined, before resampling, by which cards end up in the
left pile. The `50`-card membership sets carrying exactly `k` initially-left
cards are counted by a bijection with left-right pairs:

* `fiberMembershipSets k := (powersetCard 50 univ).filter (S ↦ (S ∩ leftOrigSet).card = k)`;
  `leftRightPairs k := powersetCard k leftOrigSet ×ˢ powersetCard (50 - k) rightOrigSet`.
* `S_decomp` (`S = (S ∩ left) ∪ (S ∩ right)`, via the union partition) and
  `S_decomp_disjoint` (the two parts are disjoint).
* `unionMap_mem_fiber` (forward: a `(k, 50-k)` pair unions to a fiber member) and
  `fiberMem_to_pairs` (backward: a fiber member splits as `(S ∩ left, S ∩ right)`);
  `leftPart_of_union` / `rightPart_of_union` (a part is recovered by intersecting the
  union with the corresponding pile); `unionMap_injective` (disjointness forces a
  unique split).
* `fiberMembershipSets_eq_image` (the fiber membership sets are exactly the image of
  the pairs under `unionMap`) and the F1b deliverable
  **`fiberMembershipSets_card : #(fiberMembershipSets k) = choose 50 k * choose 49 (50 - k)`**
  (via `card_image_of_injOn` + `card_product` + `card_powersetCard` + the pile sizes).

Set-theory notes: use `Finset.subset_empty.mp` for `s ⊆ ∅ → s = ∅`,
`Finset.inter_subset_inter` + `Finset.Subset.rfl` for the disjoint-intersection
proofs, `Finset.union_inter_distrib_right` for `(a ∪ b) ∩ c`, and `omega` (with
a `k ≤ 50` side-lemma) for the truncated-Nat arithmetic `k + (50 - k) = 50`
(`ring` cannot do truncated subtraction). `Finset` has no `subset_univ` and no
`mem_empty`; `s ⊆ univ` is trivial (`Finset.mem_univ`).

**F1 bridge is COMPLETE and green.** `leftOriginalCount_eq_leftCardsInter (d : Deck) :
leftOriginalCount d = (leftCards d ∩ leftOrigSet).card` is now in
`Shufflemath/CommanderFiberCount.lean`. It is the key link: the macro count
`leftOriginalCount d` equals the number of originally-left cards *in the left
pile*, i.e. the size of `leftCards d ∩ leftOrigSet`, where `leftCards d` is the
left-pile membership (a 50-subset of card identities). Proof: `unfold` the three
defs, show the left pile `∩ leftOrigSet` equals the *image of the selected
left positions* (an `ext` on `Fin 99` with `rcases` on the existential/`And`
forms — `Finset` has no `subset_univ`/`mem_empty`; use `mem_inter`/`mem_image`/
`mem_filter`/`mem_univ` + `and_true`/`true_and` + `leftOrigSet` in the `simp`),
then `Finset.card_image_of_injective` on the injective left-position map
(`d.injective` ⊢ `leftPosition_injective`).

**Next (F1c + F1d) — the final F1 assembly. COMPLETE (commit `12e66df`).**
Done via the Finset-level route described below: the section map
`d -> (leftCards d, d)` reindexes `fiberFin k` onto the fiber-sigma
`(fiberMembershipSets k).sigma leftCardsFin` (injective on the fiber by
`congrArg` on the second component), and `Finset.card_sigma` (Fubini) plus
`decksWithLeft_card` gives `fiberFin_card`/`fiberSet_card`. Two Lean-4.34
facts worth keeping: `Prod` and `Sigma` are **distinct** types (a
`Finset.sigma` finset cannot be ascribed to a `×` finset), so the sigma is
stated over the Sigma type and the pair equality in
`fiberFin_image_eq_sigma` is closed with `Sigma.ext` plus `HEq.refl` (the
`x.2 ≍ x.2` subgoal is a definitional refl, since both sides are the same
projection). And in `commander_fiber_counts` the final goal is closed by
`div_eq_div_iff` + `hfact` (`99! = choose 99 50 * 50! * 49!`, proved by
`native_decide` on exact `Rat` — `norm_num` and `rw [← Nat.cast_mul]` both
stall on the casted product) + `simp only [Nat.cast_mul]` + `ring`.

**Next (F2) — the concrete membership and perfect-local kernels.**
Per `docs/lean_plan.md` §F2 (F1 is done, so the uniform targets exist):

1. Define `Membership` as the subtype of 50-element subsets of card
   identities in `Fin 99` (or an equivalent bijective type).
2. Define `membership : Deck -> Membership`, and prove that its marked-card
   count agrees with `CommanderPermutation.project` (the left-pile
   intersection count already has the bridge
   `leftOriginalCount_eq_leftCardsInter` in `CommanderFiberMembership`).
3. Define `localLift : FiniteKernel Membership Deck` as uniform orderings of
   the *given membership set* (i.e. `decksWithLeft S` uniformly — the
   `decksWithLeft_card` bijection of F1a is the counting base), and prove
   `localLift.comp (FiniteKernel.deterministic membership) = identity`
   (pile membership is preserved: this is a *perfect local* shuffle).
4. Define `membershipLift : FiniteKernel CommanderState Membership` as the
   uniform law among memberships with a specified marked count, and prove
   `membershipLift.comp localLift = FiberDisintegration.fiberLaw project
   project_surjective` (or first prove a generic version and specialize).

Neither `localLift` nor the physical local shuffle may change pile
membership; do not confuse `localLift` with the canonical oracle's
count-fiber reset.

*Historical F1c/F1d plan notes (superseded by the completed proof above; the
obstacle and tactic warnings remain useful):*

1. **Full fiber count** `#(fiberType k) = #(fiberMembershipSets k) * 50! * 49!`.
   Define `fiberType (k) := {d : Deck // leftOriginalCount d = k}` (a `Fintype`
   subtype). The fiber decomposes over the membership sets: each `d` has a unique
   `leftCards d ∈ fiberMembershipSets k` (by the bridge, since
   `leftOriginalCount d = k ↔ leftCards d ∈ fiberMembershipSets k`), and the decks
   over a fixed membership `S` are `decksWithLeft S` (card `50! * 49!` by
   `decksWithLeft_card`). The natural statement is a `Fintype` bijection
   `fiberType k ≃ fiberSigma k` where
   `fiberSigma k := Σ S : {S // S ∈ fiberMembershipSets k}, decksWithLeft S.val`,
   then `Fintype.card_sigma` + `Finset.sum_const` + `Fintype.card_of_subtype`
   gives `#fiberSigma k = #(fiberMembershipSets k) * 50! * 49!`.

   **Obstacle found (do not re-derive):** the dependent-`Sigma` route hits a
   *maximum recursion depth* in the Lean kernel when `decksWithLeft S.val` is
   indexed by the *subtype* variable `S : {S // S ∈ fiberMembershipSets k}` (the
   concrete-S form `decksWithLeft leftOrigSet` builds fine in isolation —
   `test_dwl`). The `Equiv`-level `ext` on the Sigma equality also resists
   `⟨Subtype.ext ?_, Subtype.ext ?_⟩`. **Recommended path:** prove the fiber
   count at the *Finset* level instead of via a dependent `Fintype` — take
   `fiberFin (k) := (Finset.univ : Finset Deck).filter (fun d => leftOriginalCount d = k)`
   and show `#fiberFin k = Finset.sum (fiberMembershipSets k) (fun S =>
   Fintype.card (decksWithLeft S))` via `Finset.biUnion` with the pairwise-
   disjointness given by the bridge (`leftCards d` is a unique membership, so the
   filters are disjoint), where each term is `decksWithLeft_card` and the sum is
   `#(fiberMembershipSets k) * 50! * 49!` (constant summand).
   `#(fiberFin k) = #fiberType k` (Fintype vs. Finset filter) closes the loop.

2. **Normalization + F1d.** With `#(fiberType k) = choose 50 k * choose 49 (50-k)
   * 50! * 49!` (F1b × F1a) and `#Deck = 99!`, the stationary mass for a state
   `x` (with `k = commanderLeftCount x = x.val + 1`) is
   `#(fiberSet project x) / #Deck = choose 50 k * choose 49 (50-k) * 50! * 49! / 99!`
   `= choose 50 k * choose 49 (50-k) / choose 99 50` (using
   `choose 99 50 * 50! * 49! = 99!`, i.e. `Nat.choose_mul_factorial` /
   `Nat.factorial_choose`). This equals `commanderStationaryVector x` by its
definition (`choose 50 (commanderLeftCount x) * choose 49 (50 - commanderLeftCount x)
   / choose 99 50`). F1d then exports `HasCommanderFiberCounts` by connecting
   `fiberSet project x` to `fiberType (commanderLeftCount x)` (via
   `project_val_eq`-style: `project d = x ↔ leftOriginalCount d = x.val + 1`),
   then `change Dist.mass (Dist.ofFun _ _ _) x = _` + `rw [Dist.mass_ofFun _]`
   (**never `simp`/`dsimp` on `commanderStationary` directly — it is a
   `noncomputable` `Dist.ofFun` and the projection stalls**).

**`#Deck = 99!`:** `Fintype.card (Equiv.Perm (Fin 99))` — use
`Fintype.card_perm` / `Fintype.card_equivFin` (`#(Perm (Fin n)) = n!`).

**Resolved blocker (for the record):** the section-`variable (S)` pattern is
**abandoned** in this file. Every def/theorem takes an explicit `(S : Finset
(Fin 99))` argument. The old Set-form `deckFun` / `pasteDeck` /
`decksWithLeft` (using `Equiv (Fin 50) (S : Set)`) have been *removed*; the
new subtype-form `deckFunSub` / `pasteDeckSub` / `decksLR` replace them.
`decksWithLeft` itself (the `abbrev`) is unchanged and is the subtype the deck
count is stated over.

### Hard-won API notes for this step

* `rightEquiv`'s codomain is the *Set* form `((Finset.univ \ S) : Set)`; the
  counting `rightPile S` is the *Finset*-membership subtype. They are the same
  elements; their `Fintype`s coincide (both reduce to `Finset.card_compl` = 49).
  The remaining friction is only the `Equiv`-level cast between the two
  representations when assembling the product.
* `Fintype.card_coe` does **not** auto-fire on the double coercion
  `Fintype.card ↑↑S`; use `Fintype.card_coe` with an explicit `simp`/`rw`, or
  bridge through a single-coercion subtype.
* `Set.mem_sdiff` (top-level `mem_sdiff` inside `namespace Set`) is `Iff.rfl`
  and its `.mp`/`.mpr` projections do **not** resolve by name; destructure a
  `x ∈ a \ b` goal directly with `⟨...⟩` / `rcases` (Set sdiff is definitionally
  `∧`).
* Do **not** define `rightPosition` inside the `section` — a section
  `variable (S)` leaks into a `def` as an implicit leading parameter, so
  `rightPosition j` then expects `j : Finset (Fin 99)`. Keep `rightPosition`
  (and `rightPile`) at namespace level; they don't use the section variables.
* `Finset.compl` / `Sᶜ` (the Finset complement) triggers a kernel `whnf`
  **timeout**; use `Finset.univ \ S` (sdiff) and, where a Set is needed,
  `((Finset.univ \ S) : Set)`. `Finset.compl_eq_univ_sdiff` bridges sdiff
  back to `Sᶜ` for `Finset.card_compl`.

At the end of the new tranche, run `./dev/verify_next_phase.sh`. Do not
rerun established modules solely to resolve an invented verification doubt.
The legacy `./dev/verify.sh` uses `lake update` and is not the incremental
default.

## What is already there

| Capability | Where | Status to carry forward |
|---|---|---|
| General finite kernel, TV, Dobrushin, BL and first eigenfunction | `Shufflemath/{Finite,TotalVariation,Perturbation,Dobrushin,BernoulliLaplaceGeneral,BernoulliLaplaceCommanderBridge}.lean` | Previously compiled and reported verified |
| Exact macro 2-/3-exchange TV certificates and semantic transport | `BernoulliLaplace.lean`, `BernoulliLaplaceSemantic.lean` | Earlier tranche compiled |
| GSR product-label shuffle; TV/protocol refinement | `GSR.lean`, `FiberLifting.lean`, `OracleRefinement.lean`, `PhysicalRefinement.lean`, `ProtocolCertificate.lean` | Earlier tranche compiled; numeric alphabet bridge not done |
| Actual 99-card permutation count projection | `CommanderPermutation.lean` | User expressly confirmed successful compilation after its fix |
| Constructive witness of all 50 macro fibers | `CommanderFiberWitness.lean` | Implemented and compiled |
| Uniform fiber disintegration and membership reduction | `FiberDisintegration.lean`, `PhysicalExchangeReduction.lean` | Implemented and compiled, including the v3 correction |
| Conditional full-uniform oracle and physical-perfect results | `CommanderFullDeckDisintegration.lean` | Compiles; **counting and membership hypotheses still open** |
| Left/right action bijections + exact 50!/49! counts (F1) | `CommanderFiberCount.lean` | **This session: compiles; deck-level assembly + HasCommanderFiberCounts remain** |
| Optional 2,401-pair exact TV minimum | `dev/BernoulliLaplacePairOptimality.lean` | Separate opt-in target; not a prerequisite for F1-F5 |

Last observed local warnings from `CommanderPermutation.lean` (`simpa`
versus `simp`, and `haveI` versus `have`) are not build blockers.
The 35 Python tests were passing at the time of the fiber tranche.

## The next deliverable, strictly scoped

Implement a count proof for
`CommanderFullDeckDisintegration.HasCommanderFiberCounts` without evaluating
all `99!` permutations. Good checkpoints:

- A proof of `50! * 49!` ordered decks over one fixed 50-card membership.
- A proof of the number of eligible memberships:
  `choose 50 (x.val + 1) * choose 49 (49 - x.val)`.
- Their product as the cardinality of `fiberSet project x`.
- Rational normalization to the *existing* `commanderStationary` mass.
- An exported theorem of the already-declared `HasCommanderFiberCounts` type,
  removing the counting premise from the *ideal-oracle* uniform theorem.

These are distinct subtasks. Do **not** try to solve F1-F5 in a single patch.
If the whole count theorem resists, deliver the independently proved first
sublemma, note the exact next obligation, and keep the build green.

### Non-goals for this patch

- Do not redefine `Dist`, `FiniteKernel`, or the 50-state BL kernel.
- Do not assert that the physical perfect-local kernel equals the canonical
  oracle on arbitrary deck states (the documented five-card counterexample
  rules that out).
- Do not use `native_decide` over a 99-card permutation type or enumerate
  `99!` states. A 50-state finite decision (as in the existing fiber witness)
  is different.
- Do not replace counting or exchange hypotheses with assumptions called
  "obvious", or weaken theorem statements to make them compile.
- Use targeted compilation as the routine proof check (see `AGENTS.md`).
- Do not change the Manim presentation, documentation history, or other
  independent projects as part of the counting proof.

## After F1: exact dependency chain

1. **F2:** `Membership` for a 50-element subset of named cards, the map
   `Deck -> Membership`, and uniform within-membership `localLift`; prove
   recovery and the factorization through `membershipLift`.
2. **F3:** uniform 25-position cross-pile exchange and named-membership
   transition identity; discharge `hMembershipExchange`; prove physical
   perfect-local 2-exchange uniform TV using F1 and F2.
3. **F4:** numeric product-label GSR law; permutation-preserving local-GSR
   kernels; per-row TV discrepancy against physical perfect-local; combine
   via `PhysicalRefinement.finite_local_uniform_bound`.
4. **F5:** give explicit operation costs and a protocol satisfying an
   explicit terminal TV target; optional bounded optimality later.

A weaker agent can work on F1a, F1b, F2a, or the GSR numeric-encoding
lemma independently. Every contribution should name its prerequisite,
exact output theorem, and the compiler command used to verify it.

## Work and handoff protocol

1. Check `git status --short`; do not discard unrelated changes or create
   worktrees. Work in place in the user's existing checkout.
2. Run `lake exe cache get`, then `lake build` on *only affected modules*.
   Run the full targeted script when the tranche is complete.
3. Keep changes small and directly buildable. Report actual compiler errors
   with filename/line number. Use the current mathlib API rather than
   guessing lemma names; inspect existing source signatures.
4. Preserve the actual theorem obligations and keep builds focused;
   follow `AGENTS.md` for proof-checking and audit policy.
5. Once the new work is tested, update `docs/lean_plan.md` and the
   **first action** of this handoff. Treat user-confirmed compilation as
   established; don't invent pending-verification status.
6. Stage only changed files and commit with a single trailer using the
   current model, e.g.
   `Co-authored-by: GPT-6 <noreply@openai.com>`.

The active mathematical specification is in [lean_plan.md](lean_plan.md).
The detailed model distinction is in
[full_deck_oracle_bridge.md](full_deck_oracle_bridge.md) and
[commander_fiber_disintegration.md](commander_fiber_disintegration.md).

---

## Executable specs for the two remaining fundamental blockers

These gate F3 item 4 (the 2-exchange TV) and F5. Both are specified precisely
so the next session can execute without re-diagnosis. The counting (part (i))
is done; these are part (ii) and F4.2.

### Spec A — part (ii): membership-fiber orbit transitivity, then exchange invariance

**Step A1 (COMPLETE, commit `43f845f`): orbit transitivity.**  Prove
`membershipFiber_transitive`: for memberships `m m' : Membership`
(`Membership = {S : Finset (Fin 99) // S.card = 50}`) with
`membershipCount m = membershipCount m'` (`membershipCount m = (m.1 ∩
leftOrigSet).card`, `leftOrigSet = {c : Fin 99 : c.val < 50}`), there exists a
bijection `f : Fin 99 → Fin 99` such that `f '' (leftOrigSet : Set) =
(leftOrigSet : Set)` and `f '' (m.1 : Set) = (m'.1 : Set)`.  **Every valid
membership has marked count `k ≥ 1`** (a 50-subset with `k` in the 50-card
`leftOrigSet` and `50 - k` in the 49-card `rightOrigSet` needs `50 - k ≤ 49`,
i.e. `k ≥ 1`), so the four parts are all well-typed.  **Construction** (4-part
permutation): set `A := m.1 ∩ leftOrigSet`, `A' := m'.1 ∩ leftOrigSet` (both
`k`), `C := leftOrigSet \ A`, `C' := leftOrigSet \ A'` (both `50 - k`),
`B := m.1 ∩ rightOrigSet`, `B' := m'.1 ∩ rightOrigSet` (both `50 - k`),
`D := rightOrigSet \ B`, `D' := rightOrigSet \ B'` (both `k - 1 ≥ 0`).  Build
four bijections `eA : A ≃ A'`, `eC : C ≃ C'`, `eB : B ≃ B'`, `eD : D ≃ D'` via
`Fintype.equivFinOfCardEq` (`Fintype.card A = k` etc., each obtained from
`Finset.card_inter`/`Finset.card_sdiff` + `h`), each as
`(Fintype.equivFinOfCardEq hT').symm ∘ Fintype.equivFinOfCardEq hS`.  Define
`f` piecewise on the disjoint 4-part partition `{A, C} ∪ {B, D} = Fin 99`
(mapping each part to the primed part) and prove `Function.Bijective` by
cases + the four Equivs' injectivity/surjectivity.  Then `f` preserves
`leftOrigSet` (maps `A ∪ C` to `A' ∪ C'`) and sends `m.1 = A ∪ B` to
`A' ∪ B' = m'.1`.  Put this in a new module
`Shufflemath/CommanderMembershipOrbits.lean`.

**22nd-session: A1 PROVEN.**  The witness `orbitMap` (the 4 piece-equivs
`orbitEquivA/B/C/D` composed over the 4-part partition) is shown bijective:
injectivity via the 12 pairwise-disjointness lemmas + the 4 preimage lemmas
(equal images force both sources into the same piece, then that piece-equiv is
injective); surjectivity by target-pile case-split; the pile and marked-set
image equalities (`orbitMap_imageLeft`/`orbitMap_imageM1`) close it.  **A2 is
now the next concrete step.**

**⚠️ 22nd-session PITFALL (file truncation):** a python splice `s[:start] + block + s[end:]`
with `end = s.find("<anchor>")` where the anchor was NOT found made `end = -1`, so
`s[end:]` = `s[-1:]` **silently truncated** CommanderPhysicalExchange.lean from ~line 125
to EOF, dropping `rawExchange`, `rawExchangeMembership`, `hMembershipExchange_lhs_reduces`,
`markedLeftPos`, `left25`, etc. (all still in git `958d5f5`). Restored + re-merged
`newLeftCards_conjugate` (commit `dd221fd`). **Rule: ALWAYS `assert end != -1` (and
`start != -1`) before any `s[:start] + ... + s[end:]` splice, or use
`s.split(anchor)` with a length check.**


**Step A2 (core DONE, commit `6ccae33` — distributional form next):** show the physical-exchange
distribution — averaged over a uniform `d` in the `project`-fiber of a
source count `x` and a uniform `(L, R)` 25-25 choice — is invariant under the
`leftOrigSet`-stabilizer group (the action of A1's `f`'s on the *source* deck
and the target membership commute with `newLeftCards`).  Concretely: for any
such `f`, `newLeftCards (f ∘ d) L R = f '' (newLeftCards d L R)` (up to the
`L`/`R` being position-sets, not card-sets — so `f` acts on the *values* of
the deck).  Because A1 shows the stabilizer acts **transitively** on the
target membership fiber of any fixed count `m`, and the distribution is
stabilizer-invariant, it is **uniform over that fiber** — this is part (ii).

**A2 core proven** (`newLeftCards_conjugate`): for any permutation `f` and deck
`d`, `newLeftCards (d.trans f) L R = (newLeftCards d L R).image f` — the exchange
commutes with card relabeling.  The **distributional** form (averaging `newLeftCards`
over a uniform `project`-fiber `d` and a uniform 25-25 `(L,R)` gives a law invariant
under the `leftOrigSet`-stabilizer, hence uniform over the fiber by A1's
transitivity) is the next step, and it is what `hMembershipExchange` (A3) needs.

**Step A3 (assemble):** with A2, the LHS of
`comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
membershipLift` is, at a target membership `μ` of count `m`,
`(mass to count m) / membershipFiberCount m` = the RHS (whose `membershipLift`
is uniform over the fiber by construction).  Then `interweaving_of_membership_exchange`
+ `run_tv_eq_macro_of_membership_exchange` (already proven general theorems)
yield the 2-exchange TV (= the macro/BL TV).

### Spec C — A3: the concrete `hMembershipExchange` kernel equality + 2-exchange TV

**Target.** Prove the concrete premise of
`two_physical_perfect_exchanges_uniform_of_counts`:
`comp (comp (comp membershipLift localLift) rawExchange) (deterministic membership)
 = comp commanderExchange25 membershipLift`, for the physical-exchange `rawExchange`
and the `membership`/`membershipLift`/`localLift` of the Commander fiber.
Counting (part (i)) is done (general CL / `fiberSum_eq_overlap_ns` /
`commanderExchange25`); member-uniformity (part (ii)) rests on A1
(`membershipFiber_transitive`) + A2 (distributional invariance). Instantiating
`two_physical_perfect_exchanges_uniform_of_counts` with this proved premise yields the
**unconditional 2-exchange TV** `= commander_tv_after_two_semantic`.

### Spec B — F4.2: Deck-level GSR lift to `Equiv.Perm (Fin 99)`

The `List.mem_bind`/`toMultiset` sub-wall blocks lifting the GSR product
kernel to `Equiv.Perm (Fin 99)`.  **Fintype-free alternative (this session's
machinery is ready):** the F4.5 Finsupp machinery (`gsrProductKernel`,
`distProductFinsupp`, `kernel_apply_lipschitz`) works over any `[Fintype]`
target *without* the multiset encoding.  To lift to the deck level, model the
GSR shuffle as an `Equiv.Perm (Fin 99)` directly (a riffle is a specific
interleaving permutation; the GSR is the uniform mixture over riffle counts),
and use `Finsupp`/`Dist` over `Equiv.Perm (Fin 99)` (a Fintype) instead of the
pile-list `List` space.  This sidesteps `List.mem_bind`.  Check whether
`Equiv.Perm (Fin 99)` has a usable `Fintype` instance (it does, via
`Fintype` on `Equiv` for Fintype base) and build the riffle kernel there.

---

## 16th session (post-compaction resume) — F3 part (ii) groundwork: membership-count range

**New module `Shufflemath/CommanderMembershipOrbits.lean` (proven, committed).**
This is the first concrete step of Spec A (the group-action proof of part (ii)).
It establishes the *well-typed range* for the marked count that the orbit
construction (Spec A1) relies on:

- `leftRightOrig_cover : leftOrigSet ∪ rightOrigSet = univ` — proven via
  `ext x` + `Classical.em` (avoids the `tauto` recursion on the opaque `Finset`
  filter membership).
- `leftRightOrig_disjoint : Disjoint leftOrigSet rightOrigSet` — via
  `Finset.inter_sdiff_self` (`rightOrigSet = univ \ leftOrigSet`).
- `membershipCount_pos : 0 < membershipCount m` — a membership (50-subset of the
  99 cards) splits into `k` left-orig cards and `50 - k` right-orig cards; since
  only 49 right-orig cards exist, `50 - k ≤ 49`, forcing `k ≥ 1`.  Proven by a
  `Finset`-algebraic disjoint-cover of `m.1` into `A = m.1 ∩ leftOrigSet` and
  `B = m.1 ∩ rightOrigSet` (`Finset.card_union_of_disjoint`,
  `Finset.card_le_card`), *not* element-wise membership (the opaque-Quot wall).
- `membershipCount_le_50 : membershipCount m ≤ 50` — the marked part is
  `m.1 ∩ leftOrigSet ⊆ leftOrigSet` (50 cards).

Together: every valid membership has `1 ≤ membershipCount m ≤ 50`, so every fiber
`MembershipFiber k` that the orbit construction targets has valid part-counts
(`k ∈ [1,50]`, `50-k ∈ [0,49]`).

**Next (Spec A1 proper):** prove transitivity of the `leftOrigSet`-stabilizer on
each `MembershipFiber k` — a bijection `Fin 99 ≃ Fin 99` preserving
`leftOrigSet` mapping one membership's 50-set to another's (4-part permutation
via `Fintype.equivFinOfCardEq` on `{A, C, B, D}`).  This is the deep
group-action core; it will need the `leftRightOrig_disjoint_cover`-style
`Finset` identities already recorded here.  **Then** Spec A2 (stabilizer
invariance of `newLeftCards`) and A3 (assemble + 2-exchange TV).

**Note on the module system:** `Membership`, `membershipCount`, `MembershipFiber`
live in the *nested* `Shufflemath.CommanderMembershipKernels` namespace (so this
module opens it with `open CommanderMembershipKernels` inside `namespace
Shufflemath`); `leftOrigSet`/`rightOrigSet`/`leftOrigSet_card`/`rightOrigSet_card`/
`rightOrigSet_sdiff` live directly in `Shufflemath`.  The module is NOT in the
`Shufflemath.lean` aggregator (consistent with the other Commander* modules) but
IS in the AGENTS.md verified build list.

Full verification green (37 tests, 0 failures) after this commit.
### F3 part (ii), step A1 — `finsetType_perm` (core orbit-transitivity primitive)

**Status: constructed and fully specified, 3 specific Finset-mechanics walls remain
(documented below). Building block `equiCardFinsets_bij` is committed.**

The target: for `m, m'` with `membershipCount m = membershipCount m' = k`, a
permutation `f : Fin 99 ≃ Fin 99` with `f '' leftOrigSet = leftOrigSet` and
`f '' m.1 = m'.1`.  This decomposes into two independent primitive calls
(`f|_L` and `f|_R`), each an instance of the following **core lemma**:

> **`finsetType_perm {s : Type} [Fintype s] [DecidableEq s] (A A' : Finset s)
> (h : A.card = A'.card) : s ≃ s`** — a permutation of `s` sending `A` onto
> `A'`.  Applied with `s = leftOrigSet`, `A = m.1 ∩ leftOrigSet`,
> `A' = m'.1 ∩ leftOrigSet` (both size `k`) gives `f|_L`; with
> `s = rightOrigSet`, `A = m.1 ∩ rightOrigSet`, `A' = m'.1 ∩ rightOrigSet`
> (both size `50 - k`) gives `f|_R`.  Composing the two (they agree on the
> disjoint cover `leftOrigSet ⊎ rightOrigSet = univ`) yields `f`.

**Exact construction** (verified to type-check except the 3 walls): define
`C := univ \ A`, `D := univ \ A'`, `eAB : {x // x ∈ A} ≃ {x // x ∈ A'}` and
`eCD : {x // x ∈ C} ≃ {x // x ∈ D}` via `equiCardFinsets_bij` (`C.card = D.card`
by `Finset.card_sdiff_of_subset` twice + `h`).  Then

```
let f (x : s) : s :=
  if hx : x ∈ A then (eAB ⟨x, hx⟩).val else (eCD ⟨x, ⟨Finset.mem_univ x, hx⟩⟩).val
refine Equiv.ofBijective f ?_
```

- **Injectivity**: 4 cases on `x ∈ A` / `y ∈ A`.  Same-piece cases reduce via
  `eAB`/`eCD` injectivity to `x = y`.  Cross-piece cases: `(eAB ·).val ∈ A'`
  vs `(eCD ·).val ∈ D`, and `Disjoint A' D` (from
  `Finset.inter_sdiff_self A' univ`), so the images are disjoint.
- **Surjectivity**: for `z`, case `z ∈ A'` (then `z = eAB (eAB.symm z)`) or
  `z ∈ D` (then `z = eCD (eCD.symm z)`, and the preimage `eCD.symm z ∈ C` not
  `A`, so the `else` branch is taken).

**The remaining walls** (all opaque-Finset-membership / val-vs-subtype /
  ite-reduction):
1. **`card_sdiff` rewrite ambiguity**: `rw [card_sdiff_of_subset h,
   card_sdiff_of_subset h]` matches both `(univ \ A).card` and
   `(univ \ A').card` unpredictably.  Fix: prove `C.card` and `D.card` in
   SEPARATE `have` blocks, each with a single `rw [hC, card_sdiff_of_subset
   (fun _ _ => Finset.mem_univ _)]`, then combine.
2. **`x ∈ Finset.univ` is NOT definitionally `True`** (opaque Finset membership):
   `⟨trivial, hx⟩` fails where `x ∈ univ ∧ x ∉ A` is expected.  Fix: use
   `⟨Finset.mem_univ x, hx⟩` (the lemma `Finset.mem_univ x : x ∈ univ` exists).
3. **val-vs-subtype equality in the injective same-piece case**: after
   `simpa [f, ite_eq_left ...] using hxy` the goal is
   `(eAB ⟨x,·⟩).val = (eAB ⟨y,·⟩).val` but the target is `x = y`.  Fix: first
   lift to subtype equality `eAB ⟨x,·⟩ = eAB ⟨y,·⟩` (two elements of the SAME
   subtype with equal `.val` are equal — `Subtype.ext`/`Subtype.val`), then
   apply `eAB.injective` to get `⟨x,·⟩ = ⟨y,·⟩`, hence `x = y`.  Same for the
   `eCD` piece.  (The cross-piece disjointness step also needs
   `Finset.mem_inter` to assemble `value ∈ A' ∩ D`, then the
   `A' ∩ D = ∅` contradiction.)

  4. **Named-binder `if` does not reduce by `rw [ite_eq_left h]`** (only the
     *unnamed* `if p then` form does).  **Fix found**: `split_ifs at hxy` DOES
     reduce a named-binder `if hx : p then … else …`.  So in each injective case
     use `split_ifs at hxy` (it also supplies the branch hypotheses) instead of
     `rw [ite_eq_left …]`.
A future session should fix these 4 mechanical points in the skeleton above,
add `finsetType_perm` to `CommanderMembershipOrbits.lean`, then build the
commander `f` from the two halves and state
`membershipFiber_transitive` (Spec A1).  **No `sorry`/`admit` — this is the one
remaining deep group-action lemma of the whole F3 part (ii) reduction; Specs
A2 (stabilizer invariance of the physical-exchange distribution) and A3
(kernel assembly via `interweaving_of_membership_exchange`) follow directly once
A1 lands.**


## 19th-session progress (F4.2 deck-level GSR, Fintype-free) — NEW module `Shufflemath/CommanderDeckGSR.lean`

The F4.2 *structural identification* is done (Fintype-free, no `List.mem_bind`/
`toMultiset`): a **membership-preserving** deck permutation (one sending the 50 left
positions to left cards `val < 50` and the 49 right positions to right cards `val ≥
50`, `preservesPiles σ`) is **exactly** a within-pile relabeling.

Committed (newest first):
- `f0d42b3` `pileRelabelEquiv_mul`: `pileRelabelEquiv (pl*pl') (pr*pr') =
  pileRelabelEquiv pl pr * pileRelabelEquiv pl' pr'` — the within-pile relabels form a
  *subgroup* of `Deck`, closed under composition.
- `f097fec` `preservesPiles` predicate + capstone `preservesPiles_iff_pileRelabel :
  preservesPiles σ ↔ ∃ p, pileRelabelEquiv p.1 p.2 = σ`.
- `0b7460a` `pileRelabelEquiv_image`: a `preservesPiles` `σ` equals `pileRelabelEquiv`
  of its components (`leftPermOf`/`rightPermOf` + `Equiv.ofBijective` +
  `Finite.surjective_of_injective`).
- `a4eb2d8` `leftPermOf`/`rightPermOf` helpers + `leftPos_leftPermOf`/
  `rightPos_rightPermOf` + `leftPermOf_injective`/`rightPermOf_injective`.
- `f14c083` new `CommanderDeckGSR.lean` + `pileRelabelEquiv_pairInjective` (a within-pile
  pair is recovered from its `Deck` action).

**19th-session gotchas:**
- `Fintype.surjective_of_injective` does not exist; it is **`Finite.surjective_of_injective`**
  (`Mathlib/Data/Fintype/Card.lean`, `namespace Finite`, needs `[Finite α]` — `Fin n` qualifies).
- `Equiv.ofBijective f hf : α ≃ β` has **`toFun := f`**, but a `have` binding it is opaque to
  `dsimp`/`rfl`. Use **`let`** (not `have`) for the equiv, then `dsimp only [pl]; rfl` gives
  `pl i = f i`. (`Equiv.coe_ofBijective : ⇑(ofBijective f hf) = f` is a simp lemma but did not
  fire through the let in `simp` here; the `dsimp [pl]; rfl` route worked.)
- `leftPosition_leftIndex`/`rightPosition_rightIndex` give `leftPosition (leftIndex p h) = p`
  (wrong direction for `p = leftPosition i`) — use **`.symm`**.
- `leftPos_leftPermOf`/`rightPos_rightPermOf` give `leftPosition (leftPermOf σ hL i) = σ
  (leftPosition i)`; when you need `σ (leftPosition i) = leftPosition (...)` use **`.symm`**.
- In a pointwise `ext pos` case split, after `simp only [pileRelabelEquiv_left/right,
  Equiv.Perm.mul_apply]` the goal is reflexive and closes — a trailing `congr 1`/`rfl` gives
  "No goals to be solved".

**Next F4.2 (deck-level GSR kernel)**: a `FiniteKernel Deck Deck` (or a one-step `Dist Deck`)
for a riffle = apply an independent per-pile GSR riffle. The remaining sub-wall is bridging
`GSR.idealShuffle : FiniteKernel (List (Fin n)) (List (Fin n))` (a permuted *list*) to a
`Equiv.Perm (Fin n)` (a *permutation*) so the two per-pile permutations compose into a
`Deck`. This is the "distributional multiset/permutation fact" noted in `docs/lean_plan.md`
F4 item 2 — the `List.mem_bind`/`toMultiset` absence. Explore a `Equiv` from a perm-list
(`Equiv.ofPermList` / `List.Perm` bridges) to avoid `toMultiset`.

**F3 item 4 part (ii)** (`finsetType_perm`, `docs/agent_handoff.md` 17th/18th-session block):
the last F3 item — membership uniformity. Injective half is DONE (4 cases via
`dsimp only [f] at hxy; split_ifs at hxy <;> rename_i hx hy`). Surjective half is 90% with 3
documented one-line fixes (W1: `have pre` opaque → use `let`/inline; W2: `rw [hmem] at hR` on
`Finset.mem_sdiff` → apply `Finset.mem_sdiff.mp` as a term; W3: `split_ifs <;> rename_i` grabs
the `DecidableEq s` typeclass → reference the ite condition by proposition). Near-complete
proof at `/tmp/finsetType_perm_nearcomplete.lean`.

---

## 21st session (2026-11-14): F3 item 4 (part ii) — orbit transitivity: construction complete, proof route set

**State of F3 item 4 (part ii) — the last open F3 item** (`CommanderMembershipOrbits.lean`):

- `finsetType_perm {s} [Fintype s] [DecidableEq s] (A A' : Finset s) (h : A.card = A'.card) :
  s ≃ s` — **COMPLETE** (commit `a637cee`): a permutation of `s` sending `A ↦ A'` and
  `s \ A ↦ s \ A'`. Both the injective and surjective halves are proven (no `sorry`).
- `equiCardFinsets_bij {α} [Fintype α] [DecidableEq α] {s t} (h : s.card = t.card) :
  {x // x ∈ s} ≃ {x // x ∈ t}` — COMPLETE (commit `64a6c29`).
- Four equi-cardinality lemmas (commit `ccc30d9`): `partCard_eqA/B/C/D` — for `m, m'` with
  equal `membershipCount`, the four pieces (matched/unmarked × left/right pile) satisfy
  `(partX m).card = (partX m').card`. Built on `m1_decomp` (a 50-subset splits additively
  left/right), `m1_sum50`, `m1_left_le`.
- Two pile-cover lemmas (commit `aed2442`): `leftCoverPieces` (`left = partA ∪ partC`),
  `rightCoverPieces` (`right = partB ∪ partD`).
- **`orbitMap` construction (commit `55c07b5`)**: four noncomputable piece-equivs
  `orbitEquivA/B/C/D : {c // c ∈ partX m} ≃ {c // c ∈ partX m'}` (via
  `equiCardFinsets_bij`) plus `orbitMap : Fin 99 → Fin 99`, the piecewise permutation that
  transports each of `m`'s four pieces to the corresponding piece of `m'`. The four pieces
  partition the 99-card universe, so it is well-defined. **This is the constructive witness
  for the target theorem.**

**Target theorem (still open):**
```
membershipFiber_transitive (m m' : Membership) (h : membershipCount m = membershipCount m') :
  ∃ (f : Fin 99 → Fin 99), Function.Bijective f ∧ f '' leftOrigSet = leftOrigSet ∧
    f '' m.1 = m'.1
```

**The wall (named-if reduction of a `by_cases` def):** proving
`orbitMap m m' h c = ((orbitEquivX m m' h) ⟨c, hc⟩).val` for `hc : c ∈ partX m` requires
reducing `orbitMap`'s body (a `by_cases`-def) to its then-branch. In this Lean 4.34 build,
`dsimp only [orbitMap]` / `unfold orbitMap` followed by `split_ifs with hA` does **not**
expose the decided binder `hA` in any branch (confirmed with a minimal
`by_cases`-def probe: `split_ifs with hp` prunes to the single then-goal but the binder name
is not `hp`). `split_ifs with hA` then references `hA` → "Unknown identifier". This blocks
the three conjunct proofs, each of which needs the apply-equality for the relevant piece.

**Clean next route (avoids `orbitMap` entirely):** apply the already-proven
`finsetType_perm` on the two **pile-subtype** types and bridge via the disjoint union:
1. `sL : Type := {c : Fin 99 // c ∈ leftOrigSet}` with `[Fintype sL] [DecidableEq sL]`
   (subtype of a `Fintype`); similarly `sR` for `rightOrigSet`.
2. Realize `partA m`/`partA m'` as `Finset sL` (subtype-restriction of the `Fin 99` pieces)
   and use `finsetType_perm (partA sL) (partA sL') hAcard : sL ≃ sL` — a pile-preserving
   permutation of the left pile sending the marked-left piece onto the marked-left piece of
   `m'`. Similarly `sR ≃ sR` for the right pile (using `partB`/`partD`, noting the unmarked
   pieces also have equal card by `partCard_eqB/D`).
3. Bridge `Fin 99 ≃ (sL ⊕ sR)` (the two piles are disjoint and cover `univ`) and compose
   the two pile-Perms into a single `Fin 99 ≃ Fin 99`. This Perm preserves each pile and
   carries `m.1 = partA ∪ partB` onto `m'.1 = partA' ∪ partB'`, closing all three conjuncts
   without any named-if reduction (it only uses `finsetType_perm`, `leftCoverPieces`,
   `rightCoverPieces`, and the disjoint-cover `leftRightOrig_cover`/`leftRightOrig_disjoint`).

The pile-subtype `Fintype`/`DecidableEq` instances and the `Fin 99 ≃ sL ⊕ sR` bridge are the
two new building blocks; both are standard subtype/sum machinery (no `native_decide`).

**Acceptance (F3 item 4 / part ii):** `membershipFiber_transitive` closes with no `sorry`
and no new abstract exchange hypothesis; `lake build Shufflemath.CommanderMembershipOrbits`
green; `./dev/verify_next_phase.sh` green. With it, the F3 item 4 kernel equality (part (ii)
membership uniformity) and the unconditional 2-exchange TV theorem are bookkeeping on top.

**F4.2 (deck-level GSR kernel)** — next after F3 part (ii): `CommanderDeckGSR.lean` has the
full structural identification (`pileRelabelEquiv`, `preservesPiles_iff_pileRelabel`,
`pileRelabelEquiv_mul`, `leftPermOf`/`rightPermOf`). The open sub-wall is the distributional
bridge `List (Fin n) ↔ Equiv.Perm (Fin n)` (via `Equiv.ofPermList`, not `toMultiset`) to
lift the two per-pile `idealShuffle` riffles into a `Deck`-level kernel. See the
"Next F4.2" note above.


## 46th session (2026-11-22) — T4 counting core completed; new resume point

Environment: clean AIVM VM (rebooted again since the 45th session — fresh
device number). Re-registered the `.lake` bind mount with
`scripts/setup-lake-cache.sh --all` (no `sudo` prefix; the script sudo's
its own `mkdir`/`chown`/`mount` internally). The 45th-session's
`sudo chown 42:53629361` fix for the owner-marker gotcha was still in
effect. Reinstalled `aiq-lean-formalization-tools`
(`python -m pip install -e submodules/aiq-lean-formalization-tools`) after
`git submodule update --init`. `lake exe cache get` + full 10-module
targeted build green at session start.

### `card_biUnion_pd` + `yMoves_card_eq_sum` (commit `ae26aed`)

- `card_biUnion_pd`: `#(s.biUnion t) = ∑ i ∈ s, #(t i)` for pairwise
  disjoint range — the missing bridge between the F2 `fiberCard` machinery
  and the T4 capstone. Proof: induction on `s`, union/insert bridges.
- `yMoves_card_eq_sum`: `#(yMoves N m r k hr S x y) = ∑ a ∈ Ico 0 (k+1),
  #(Pa N m r k hr S x y a)`.

New-Mathlib gotchas (this build, all worked around, none blocked):
1. `Finset.Disjoint` is the **lattice** definition
   (`∀ ⦃a⦄, a ≤ s → a ≤ t → a ≤ ⊥`); use `Finset.disjoint_left` for the
   element-level form.
2. Membership in `s ∪ t`, `insert a s`, and `s.biUnion t` is an **opaque
   `Quot.lift`** — `rcases`/`cases` produce unsolvable goals. Bridge with
   `Finset.mem_union`, `Finset.mem_insert`, `Finset.mem_biUnion`.
3. `Ne.ofMem` is gone; `not_mem_empty` is `Finset.notMem_empty`
   (capital M); `tauto` does not split `∃`-over-disjunction; a trailing
   `rfl` after a goal-closing `rw` is an error (drop it).

### T4 capstone (commit `1cd40b0`)

- `transitionTerm (N m r k x y a : Nat) : Nat` — the `a`-summand of
  `BernoulliLaplaceGeneral.transitionNumerator N m r k x y`
  (`x` = marked count at source, `y` = marked count at target,
  `a` = marked removed from the `m`-pile; 4-factor `Nat.choose` product
  with the two `if` guards).
- `transitionNumerator_eq_sum_transitionTerm` — the definition's
  `let`-bound body is definitionally the `transitionTerm` sum
  (`dsimp` + `rfl`).
- `Pa_card_eq_transitionTerm` — `(Pa … x y a).card = transitionTerm … x y a`:
  `pieceCount`'s LHS **is** the `Pa` filter, and `markedPileCards` rewrites
  the four binomial bases to `x / m-x / r-x / (N-m)-(r-x)`; the guards
  match by construction.
- **`yMoves_card_eq_transitionNumerator`** — `#yMoves = transitionNumerator
  N m r k x y`: `yMoves_card_eq_sum` + `Finset.sum_congr` (with the
  `Ico 0 (k+1) = range (k+1)` bridge) + the per-`a` equality. **No
  admissibility regime needed** — `Nat.choose` saturation plus the
  `if` guards already vanish on impossible regimes; the `overlap_count`
  connection (`generalCL` / `generalCL_ns`) is separately available
  under `m + r ≤ N` (and `k ≤ y` for `generalCL_ns`).

Elaboration gotcha (this 4.34 build): a `by`-block mixing `rw`/`refine`
over `Finset.sum_congr`'s dependent explicit arguments elaborated
unreliably (spurious unsolved-`hm` cascade that no amount of argument
reordering fixed); a **`calc` proof with direct theorem applications**
(`sum_congr hIco (fun _ _ => rfl)`, `sum_congr rfl` + `intro`,
`(…eq…symm)`) elaborates cleanly. Also: `Finset.mem_Ico` is **not** a
simp lemma here (use `simp_rw [Finset.mem_Ico, Finset.mem_range]`), and
`if_pos`/`if_neg` are deprecated for `ite_eq_left`/`ite_eq_right`.

### T2 marked-fiber transitivity (this session)

`markedFiberTransitive` (in `Shufflemath/FiniteDeck/BLRefinement.lean`):
for any two `m`-piles `S, T` with the same `x` marked cards
(`(S ∩ M).card = (T ∩ M).card = x`, `M = markedSet N r hr`), there is a
**marked-preserving permutation** `g : Equiv.Perm (Fin N)` with
`g '' S.1 = T.1` and `g '' M = M`. This is the generalization of
`Fiber.fibTransitive` (which used arbitrary permutations) to the
`M`-invariant group — the transitivity the T4 uniform-fiber
intertwining needs, since the exchange kernel must be uniform on each
count-fiber.

Proof structure: partition the deck into the four regions
`M∩S`, `M∖S`, `Mᶜ∩S`, `Mᶜ∖S` (and the `T`-analogs); each region
pair has equal cardinality (four lemmas via `Fintype.card_subtype` +
filter/`sdiff` cardinalities, with `markedSet_card` /
`markedComp_card` / `unmarkedCard` doing the arithmetic);
`Fintype.equivOfCardEq` gives a bijection per region pair; `g` is the
four-case function (two nested `by_cases`); surjectivity from the four
region bijections (`eXX.surjective` at the target region of `z`, then
the matching value lemma); bijectivity from
`Finite.injective_iff_surjective`; both images by direct
`ext`/`by_cases` arguments.

Elaboration gotchas (this 4.34 build, all worked around):
- `split_ifs` splits **all** `if`s in the goal at once and does **not**
  add the branch conditions to the context (unlike `by_cases`, which
  adds hypotheses but does not reduce the goal). The working pattern
  for a nested-`if` function `g`: `by_cases hA : p` +
  `by_cases hB : q`, then
  `simp only [g, hA, hB, ite_true, ite_false]` — `ite_true`/`ite_false`
  **do exist** and reduce an `ite` whose condition has been rewritten to
  `True`/`False` by the local hypotheses; the matching branch closes by
  `congrArg (fun z => (e z).1) (Subtype.ext rfl)` (proof irrelevance),
  the other branches by `exfalso` + the negation hypothesis.
- `Finset.mem_inter` lives in `Mathlib.Data.Finset.Lattice.Basic`
  (not `Finset.Basic`); it reaches this file transitively and is a
  simp lemma, but `Finset.mem_univ` is only reachable via
  `Mathlib.Data.Fintype.Card` (already imported).
- Finset membership (`a ∈ s \ t` etc.) is an opaque `Quot.lift`:
  projections `h.1`/`h.2` fail until `rw [Finset.mem_sdiff] at h`.
- `change` accepts definitionally equal goals (used to switch
  `(U \ M).card` to `(markedComp N r hr).card` before `exact`);
  `rw` auto-closes `rfl` goals, so no trailing `rfl`/`exact rfl`.

### Resume point

The T4 **measure** half: (i) the `count : Membership → BLState`
projection (check `BernoulliLaplaceGeneral` for the `BLState` type — it
may already exist); (ii) the **uniform-fiber intertwining**
`(uniform count-fiber membership) >> (subsetExchange) = (BL exchange) >>
(uniform count-fiber membership)` in generic `N, m, r, k`, built from
`yMoves_card_eq_transitionNumerator` + the `BernoulliLaplaceFiber`
measure theory (`detailedBalance` etc.) + `ExchangeOverlap.generalCL`
where its hypotheses apply (direct subset-kernel argument elsewhere —
the roadmap's care note warns `generalCL_ns` assumes `k ≤ y`); (iii)
**discharge Commander F3 A3 by instantiating at (99, 50, 50, 25)**.
T2 is now complete at the (m-pile, x-marked) level
(`markedFiberTransitive`); T3 (physical↔membership projection) remains
in parallel.

---

## 47k — F3 A3 counting kernel: `sdiff_inter_split` committed; `Equiv`+theorem WIP (Nov 17)

**Status: COMPLETE.** All three pieces of the F3 A3 pile-count kernel are
committed in `Shufflemath/FinsetCombinatorics.lean` (build green, no new
warnings, dependent chain green): piece 1 `sdiff_inter_split` (commit `2488cb5`),
pieces 2+3 `powersetCard_markedContent_equiv` (the `Equiv`) and
`powersetCard_markedContent` (the card theorem) (commit `ee6cd79`).

**Fixes that actually worked (supersede the predictions above — do not re-derive):**
- `Finset.disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅` has **no
  explicit args** and the *forward* direction is **`.mp`** (not `.mpr`):
  `have hEmpty : A∩B=∅ := (Finset.disjoint_iff_inter_eq_empty).mp hDisAB`.
- The `f∘g` round-trip bullet 2 does **not** need top-level defs / `dsimp`:
  after `intro p; dsimp only [f,g]; apply Subtype.ext; apply Prod.ext`, close the
  second component with **`exact hSdiff`** (defeq-accepting) instead of
  `rw [hSdiff]` (which fails with "motive is not type correct").
- In the card theorem, `hProd := Fintype.card_of_subtype …` needs **no `.symm`**
  (the lemma is already `card {subtype} = #product`, matching hProd's LHS/RHS);
  and the final `rw […, card_sdiff_of_subset hM]` **auto-closes**, so there is
  **no trailing `rfl`**. The two `Finset.card_powersetCard` in the `rw` list are
  both needed (each rewrites one `#(…)` instance).

**Why the split:** I built the kernel as three independently-checkable pieces
instead of one big proof, per the small-batch discipline. `sdiff_inter_split`
(the split lemma) is self-contained and green. The `Equiv` reuses it plus the
existing `union_inter_parts` and standard finset facts.

**The kernel, in one line:** `#(S ∈ U.powersetCard k, (S ∩ M).card = a) =
choose M.card a · choose (U.card − M.card) (k − a)` for `M ⊆ U`, `a ≤ k`. This
is the hypergeometric count the 25/25 exchange A3 pile counts reduce to (with
`U` = the relevant card set, `M` = the part that was in the left pile).

**The `Equiv` structure** (in `.pi-glla/47k_kernel_wip.lean`): `f` maps a fiber
element `S` to the pair `(S ∩ M, S \ M)` (an `a`-subset of `M`, a `(k−a)`-subset
of `U\M`); `g` maps `(A, B)` to `A ∪ B`. The round-trips:
- `g ∘ f = id`: `(S∩M) ∪ (S\M) = S` — this is `sdiff_inter_split.…1`. **DONE**
  (fixed the conjunction accessor: the recombine equality is `.1`, the Disjoint
  is `.2.1` — I initially grabbed the wrong one).
- `f ∘ g = id`: `(A∪B)∩M = A` (via `union_inter_parts.1`) and
  `(A∪B)\M = B` (via `hSdiff` + `union_inter_parts.2`). **This is the one
  remaining fiddly bit.**

**Already-fixed in the saved file** (do not re-derive):
1. `hDisAB : Disjoint A B` is NOT an `Eq`, so it cannot be a `rw` argument.
   Convert first: `have hEmpty : A ∩ B = ∅ :=
   (Finset.disjoint_iff_inter_eq_empty A B).mpr hDisAB`, then
   `rw [hEmpty, Finset.card_empty]`.
2. `hABcard` closer: after `rw […, hAcard, hBcard] at hUnion` the local fact is
   `(A∪B).card = a + (k − a)` and the goal is `(A∪B).card = k` — close with
   `omega` (uses `ha : a ≤ k`), **not** `exact hUnion.symm` (wrong orientation).
3. `g ∘ f` recombine: use the **`.1`** accessor (recombine equality), not `.2.1`
   (the Disjoint).
4. `Finset.notMem_empty` is the name (camelCase `notMem`), not `not_mem_empty`.
5. `z ∈ (S\M)` / `z ∈ (A∪B)\M` are `Quot.lift` membership props, **not**
   inductive — decompose with `Finset.mem_sdiff.mp`, build with
   `Finset.mem_sdiff.mpr` (do **not** use `⟨…, …⟩` for a membership goal).
6. `Finset.card_sdiff` (no explicit args in `rw`) rewrites `#(t\s) = #t −
   #(s∩t)`; combine with `Finset.inter_comm`, `hScard`, `hSmark` for `hBcard`.

**THE one remaining hard bit — the `f ∘ g` round-trip.** After
`refine Equiv.mk f g ?_ ?_; intro p; dsimp only [f, g]; apply Subtype.ext;
apply Prod.ext`, the second component goal does **not** reduce cleanly to
`(p.1.1 ∪ p.1.2) \ M = p.1.2`: `dsimp [f,g]` expands `g`'s `let A := p.1.1`
incorrectly (the goal shows `(↑p).1 ∪ (↑p).2`, i.e. it treats `p` as the *pair*
`Finset×Finset` rather than the subtype whose `.1` is the pair), so `rw
[hSdiff]` (stated in terms of `p.1.1`, `p.1.2`) fails with "motive is not type
correct". **Suggested fixes, in order of preference:**
- (a) Define `f` and `g` as **named top-level `private def`s** (not `let`-bound
  inside the `by` block) so `dsimp`/`unfold` reduces `(g p).1` to
  `p.1.1 ∪ p.1.2` cleanly; then the `f∘g` component goals are plain finset
  equalities provable by `union_inter_parts` + the small `hSdiff`.
- (b) Keep `let` but, after `intro p`, first `change (f (g p)).1 = p.1` and use
  `unfold` / `show` to force `(g p).1` to reduce to `p.1.1 ∪ p.1.2` before
  `rw [hSdiff, …]`.
- (c) Bypass the `Equiv` entirely for the card theorem: prove the cardinality
  with a single injective map `product → fiber` plus a surjectivity witness
  (same `union_inter_parts` facts), avoiding `Equiv.mk`'s two round-trips.

**Verified Mathlib facts available** (all checked in this session's mathlib
4.15.0-rc1): `Finset.card_sdiff`, `Finset.card_sdiff_of_subset`,
`Finset.card_union_add_card_inter`, `Finset.card_product`,
`Finset.card_powersetCard`, `Finset.inter_sdiff_self`, `Finset.mem_sdiff`,
`Finset.notMem_empty`, `Finset.disjoint_iff_inter_eq_empty`,
`Fintype.card_of_subtype`, `Fintype.card_congr`, and (in-repo)
`union_inter_parts`, `sdiff_inter_split`, `countFiberMemb_equiv`/`_card`.

**After the kernel builds:** the A3 part (i) LHS assembly in
`CommanderMembershipExchange.lean` becomes: rewrite the LHS per-deck sum to the
fiber `#(S ∈ U.powersetCard k, …)` (as 47h did for the RHS), then `exact
powersetCard_markedContent …`. That closes A3 → the G1 main theorem, completing
the A3 item. The RHS (`hMembershipExchange_rhs_mass`) and A4/A5 lemmas are
already in place.

### Resume point for the next session (47k → A3 LHS assembly)

The kernel is done. Next: the **A3 part-(i) LHS assembly** in
`Shufflemath/CommanderMembershipExchange.lean` — `import FinsetCombinatorics`,
then rewrite the LHS per-deck sum to the fiber `#(S ∈ U.powersetCard k, (S∩M).card=a)`
(as 47h did for the RHS) and close with `powersetCard_markedContent`. This is
the step that completes the A3 count half and (with the already-present RHS
`hMembershipExchange_rhs_mass`) discharges `hMembershipExchange` → the G1 main
theorem → the A3 item.


---

### 47l — A3 count half: pile-count lemmas done; next is the per-deck count mass (build-order item 3)

**Done this session (all building green; commits `1d2308f` + `dbe2a50` + `ee6cd79`):**
- `leftPileCount25 (d : CommanderPermutation.Deck) (a : Nat) (ha : a ≤ 25)`:
  `#(L ∈ leftChoices, markedInLeft d L = a) = choose (markedLeftPos d).card a *
  choose (50 - (markedLeftPos d).card) (25 - a)`.
- `rightPileCount25`: the right-pile (`Fin 49`) analogue,
  `choose (markedRightPos d).card a * choose (49 - (markedRightPos d).card) (25 - a)`.
  Both are one-line instances of `FinsetCombinatorics.powersetCard_markedContent`
  (`U = univ`, `M = markedLeftPos d` / `markedRightPos d`); they live in
  `CommanderMembershipExchange.lean`, which now `public import
  Shufflemath.FinsetCombinatorics`.
- **Type note:** in `CommanderMembershipExchange` the bare `Deck` is a polymorphic
  `Sort u_1` and mismatches `markedLeftPos`/`markedInLeft` (which want the concrete
  `CommanderPermutation.Deck = Equiv.Perm (Fin 99)`). Type `d` as
  `CommanderPermutation.Deck`.
- `_`-prefixed two genuinely-unused kernel hypotheses
  (`exchangePair_unique_A._hBcard`, `sdiff_inter_split._hM`) to clear the lints.

**Next (build-order item 3 → 4): the per-deck count mass.**
The per-(L,R) new-left marked count is `newLeftOriginalCount_eq`
(`CommanderPhysicalExchange`): `(newLeftCards d L R ∩ leftOrigSet).card =
leftOriginalCount d - markedInLeft d L + markedInRight d R`. So for a deck `d` with
`x := leftOriginalCount d`, `xR := (markedRightPos d).card`, the number of
`(L,R) ∈ leftChoices ×ˢ rightChoices` giving new count `n` is the 4-fold Vandermonde
sum (split on `aL`, with `aR := n - x + aL`),
  `∑_{aL} choose x aL · choose (50-x) (25-aL) · choose xR (n-x+aL) ·
        choose (49-xR) (25-n+x-aL)`
(the `aL`-factor via `leftPileCount25`, the `aR`-factor via `rightPileCount25`).
This equals the BL transition numerator `transitionNumerator 99 50 25 x n` (the CL —
already proved in `BernoulliLaplaceGeneral` / `BernoulliLaplaceFiber`), so the per-deck
count mass `= transitionWeight 99 50 25 x n`. Item 5
(`rawExchangeMembership_count`) then fiber-averages the per-deck mass over the project
fiber and matches the already-committed RHS `commanderExchange25_countMass` (as 47h
mirrored) — discharging `hMembershipExchange` → the G1 main theorem → the A3 item.

**Watch-outs for item 3:** clamp the `aR := n - x + aL` index (out-of-range
`Nat.choose` is `0`); check how `transitionNumerator` is *defined* before re-proving a
Vandermonde identity — the existing BL overlap-count lemma may bridge directly; keep all
new work in `CommanderMembershipExchange.lean` and never import a `Commander*` module
from `Shufflemath.FiniteDeck.*`.


---

### 47n — build-order item 3: per-deck fiber-count structural lemmas + count half DONE

**This session: `Shufflemath/_Probe47n.lean` builds GREEN (all lemmas).** The file is
a self-contained probe (imports `Shufflemath.FiberDisintegration` +
`Shufflemath.BernoulliLaplace` only) that assembles the *structural* facts needed for
the per-deck fiber count of `(L,R) ∈ leftChoices ×ˢ rightChoices` (build-order item 3),
plus the **A3 count half** (conservation of the originally-left cards).

**Definitions (all local to the probe):** `leftOrig50`/`rightOrig49` (the 50/49
originally-left cards as `Finset (Fin 99)`), `leftPosition`/`rightPosition` (the
position embeddings `Fin 50 → Fin 99` / `Fin 49 → Fin 99`), `leftUniv50`/
`rightUniv49` (their full images), `totalMarkedPos d`
(`= leftOrig50.image (d.symm)` — the 50 positions holding originally-left cards).

**Structural lemmas (all building):**
- `leftOrig50_disjoint_rightOrig49`, `leftUniv50_disjoint_rightUniv49`,
  `leftUniv50_union_rightUniv49_eq_univ` (the 50 left + 49 right positions cover the deck).
- `leftPosition_injective` / `rightPosition_injective`,
  `leftOrig50_image_eq_leftUniv50` / `rightOrig49_image_eq_rightUniv49`.
- `leftPos_iff_val` (`p ∈ leftUniv50 ↔ p.val < 50`),
  `rightPos_iff_val` (`p ∈ rightUniv49 ↔ 50 ≤ p.val`),
  `leftUniv50_disjoint_rightUniv49`.
- `totalMarkedPos_card50` (`#(totalMarkedPos d) = 50`), `totalMarkedPos_sub_univ`,
  `markedLeft_iff_inTotal` / `markedRight_iff_inTotal` (a marked position is in
  `totalMarkedPos d` iff its pile-index card is in `leftOrig50`/`rightOrig49`).

**Count half (the A3 conservation law) — DONE:**
- `totalMarked_leftInter_eq_image` / `totalMarked_rightInter_eq_image`:
  `(totalMarkedPos d) ∩ leftUniv50 = (markedLeftPos d).image leftPosition` (resp.
  right). These are the set-level bridges that turn the pile-index counts into
  position-image counts.
- `markedRightPos_card` — **the A3 count half:** `#(markedRightPos d) =
  50 - leftOriginalCount d`. Proof: the 50 marked positions split disjointly between
  the left and right halves (`#L + #R = 50` via `inter_univ` +
  `inter_union_distrib_left` + `card_union_of_disjoint`), each half's card is the
  corresponding marked-pile-index count (`card_image_of_injective`), so
  `#(markedLeftPos d) + #(markedRightPos d) = 50`, i.e.
  `#(markedRightPos d) = 50 - #(markedLeftPos d)`.

**Mathlib pitfalls hit (do not repeat):**
- `Finset.mem_inter` / `Finset.mem_image` have **implicit** args, so `.mp`/`.mpr` on the
  *unapplied* theorem fails ("Invalid projection"). Bind a `have hiff : <exact type>
  := Finset.mem_inter` first (Lean fills the implicits), then `hif.mp`/`.mpr`.
  `simp [Finset.mem_image] at h` and `rw [Finset.mem_inter]` DO work directly (the
  tactic layer resolves the implicits).
- `p ∈ s ∩ t` is **not** definitionally `p ∈ s ∧ p ∈ t` — use `Finset.mem_inter` (or the
  `have` pattern above), never `hp.1`/`hp.2` on a `p ∈ s ∩ t` hypothesis.
- `Finset.inter_univ (s)` / `inter_eq_left` have **explicit** `s` args — pass them.
- `p.isLt : p.val < 99` is available on a `Fin 99` (use it for the `p.val - 50 < 49`
  bound in the right-position embedding).

**Next (item 3 completion → item 4):** the per-(L,R) count is
`newLeftOriginalCount_eq` (`CommanderPhysicalExchange`): `(newLeftCards d L R ∩
leftOrig50).card = leftOriginalCount d - markedInLeft d L + markedInRight d R` (with the
A3 count half above pinning `#(markedRightPos d) = 50 - leftOriginalCount d`). For a deck
with `x := leftOriginalCount d`, `xR := (markedRightPos d).card`, the number of
`(L,R)` giving new count `n` is the 4-fold Vandermonde sum
`∑_{aL} choose x aL · choose (50-x) (25-aL) · choose xR (n-x+aL) ·
choose (49-xR) (25-n+x-aL)`, which equals `transitionNumerator 99 50 25 x n` (already
proved in `BernoulliLaplaceGeneral`). The per-deck count mass then `= transitionWeight
99 50 25 x n`, and item 5 fiber-averages it over the project fiber to match
`commanderExchange25_countMass` (discharging `hMembershipExchange`). **Promote the probe
lemmas to `Shufflemath/FiniteDeck/A3Count` (or keep as a named probe) when wiring into
`CommanderMembershipExchange`; keep all `Commander*` in the non-FiniteDeck layer.**


## 47o milestone — count half done, per-deck bridge next (this session)

**Done (part 1, committed):** the 47n count half is now a dedicated buildable
module `Shufflemath/CommanderMarkedRightCount.lean`
(`Shufflemath.CommanderMarkedRightCount`) with the conservation law
`markedRightPos_card (d) : (markedRightPos d).card = 50 - leftOriginalCount d`
plus its scaffolding (`totalMarkedPos`, `markedLeft_iff_inTotal`,
`markedRight_iff_inTotal`, `totalMarked_leftInter_eq_image`,
`totalMarked_rightInter_eq_image`, and the 50/49-image defs
`leftOrig50`/`leftUniv50`/`rightUniv49`). Builds green (zero `sorry`/`admit`);
wired into `dev/verify_next_phase.sh` and the `AGENTS.md` build list.
`Shufflemath/_Probe47n` deleted (no module imported it). NOTE: the 99-filter
(`leftOrigSet`) variant hit whnf timeouts, so the module uses the 50/49-image
scaffolding that builds cleanly.

**Next (part 2):** the per-deck Vandermonde bridge described in the preceding
paragraph. Order: `newLeftOriginalCount_eq` -> count (L) by
`markedInLeft d L` (`choose x aL * choose (50-x) (25-aL)`); mirror for R
(`xR = #(markedRightPos d)`); 4-fold sum over `aL` =
`transitionNumerator 99 50 25 (leftOriginalCount d) n`; per-deck mass =
`transitionWeight`; fiber-average to `commanderExchange25_countMass`.


## 47o part 2 in progress — per-deck Bernoulli-Laplace bridge

**Proven (in `Shufflemath/_Probe47p.lean`, builds, no sorry):** the two
per-deck binomial-count helpers, using `FinsetCombinatorics.powersetCard_markedContent`:
- `leftCountByMarked aL (h : aL ≤ 25) : #(L ∈ (Fin 50).powersetCard 25, markedInLeft d L = aL)
     = choose (leftOriginalCount d) aL * choose (50 - leftOriginalCount d) (25 - aL)`
- `rightCountByMarked bR (h : bR ≤ 25) : #(R ∈ (Fin 49).powersetCard 25, markedInRight d R = bR)
     = choose #(markedRightPos d) bR * choose (49 - #(markedRightPos d)) (25 - bR)`

**Target theorem (next):**
```
perDeckBridge (n) :
  #((Fin 50).powersetCard 25 ×ˢ (Fin 49).powersetCard 25)
     .filter (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)
  = transitionNumerator 99 50 50 25 (leftOriginalCount d) n
```
(r = 50 = total originally-left/"red" cards; k = 25; N = 99; m = 50.)

**Remaining steps, in order:**
1. General engine `pairCountBySum`: for `f : α→Nat`, `g : β→Nat`,
   `#(s ×ˢ t).filter (f p.1 + g p.2 = n) = ∑_{a ∈ s.image f} #s.filter(f=a) * #t.filter(g = n-a)`
   (partition the product set by the value of `f`; the `a`-parts are disjoint).
2. Instantiate with `f = markedInLeft d`, `g = markedInRight d`, `s = (Fin 50).powersetCard 25`,
   `t = (Fin 49).powersetCard 25`; use `newLeftOriginalCount_eq` to get the `f+g=n` condition.
3. Substitute `leftCountByMarked`/`rightCountByMarked` (and `markedRightPos_card` so
   `#(markedRightPos d) = 50 - x`).
4. Show the resulting `∑_{aL} choose x aL * choose (50-x) (25-aL) * choose (50-x) (n-x+aL)
   * choose (x-1) (25-n+x-aL)` equals `transitionNumerator 99 50 50 25 x n` by unfolding its
   definition (the `if`-guards coincide with the zeros of `Nat.choose`).
Keep all `Commander*` in the non-FiniteDeck layer; promote `_Probe47p` to a named module when done.

## 2026-11-17 — 47q: pairCountBySum (the general by-sum engine) — done, next: perDeckBridge

### Done: `pairCountBySum` (in `Shufflemath/_Probe47q.lean`)
The combinatorial engine that 47p's helpers feed. General statement (no deck
types — pure `Finset` combinatorics, so reusable):
```
#((s ×ˢ t).filter (fun p => f p.1 + g p.2 = n))
  = ∑_{a ∈ s.image f}  #(s.filter (f = a)) * #(t.filter (a + g · = n))
```
Proved via three lemmas:
- `fiber s t f g n a = s.filter(f=a) ×ˢ t.filter(a + g · = n)` — the `a`-fiber,
  **subtraction-free** (this is the key design choice: `a + g y = n` avoids the
  Nat-subtraction trap where `g y = n - a` is only equivalent when `a ≤ n`).
- `filter_eq_biUnion` — the filtered product set = `⋃_{a ∈ s.image f} fiber a`
  (a `Finset.ext` membership proof; forward uses the condition directly, reverse
  unpacks the fiber product).
- `fibers_pairwiseDisjoint` — different `a`-fibers are disjoint because
  `s.filter(f=a)` and `s.filter(f=b)` are disjoint for `a≠b`
  (`Finset.disjoint_product` + `Finset.disjoint_left`).
- `pairCountBySum` — `rw [filter_eq_biUnion]`, `rw [Finset.card_biUnion]`
  (the PairwiseDisjoint hypothesis gives `#bUnion = ∑ #parts`), then
  `Finset.sum_congr` + `Finset.card_product`.
All build (module `Shufflemath._Probe47q`, 4 declarations, 3209 jobs; combined
with 47p + key modules 3214). **No sorry.**

### Next: `perDeckBridge` (the actual 47o part-2 deliverable)
Instantiate `pairCountBySum` for the deck:
  `s = (Fin 50).powersetCard 25`, `t = (Fin 49).powersetCard 25`,
  `f = markedInLeft d`, `g = markedInRight d`.
Then each fiber count is a binomial product:
  - `#(s.filter (markedInLeft d = a)) = leftCountByMarked a`  (47p)
    `= choose(#M, a) * choose(50-#M, 25-a)`   (0 for a>25 via choose range)
  - `#(t.filter (a + markedInRight d · = n)) = if a ≤ n then rightCountByMarked (n-a) else 0`  (47p)
    `= if a ≤ n then choose(#M, n-a) * choose(49-#M, 25-(n-a)) else 0`
So:
  `#((s×ˢt).filter (markedInLeft d L + markedInRight d R = n))`
    `= ∑_{a} [choose(#M,a)·choose(50-#M,25-a)] · [guarded right binomial]`
**The ONE remaining structural lemma** to reach `transitionNumerator`:
  `newLeftCards d n = (s ×ˢ t).filter (fun p => markedInLeft d p.1 + markedInRight d p.2 = n)`
(or at least the `#·` equality). This is the 47n "fiber-pair ↔ newLeftCards"
structural result (the hard part noted in 47n). Once it's proved, `perDeckBridge`
is:
  `transitionNumerator d n = ∑_{a ∈ (s.image (markedInLeft d))} …`
matching the G2 per-deck Vandermonde RHS (with the `a ≤ n` guard absorbing the
`b ≥ k-25` style out-of-range cases, since `choose` is 0 out of range).
After that: `uniformFiber_intertwines` follows via `transitionCount_formula`
(`transitionCount = transitionNumerator / #newLeftCards`, both sides).

### Cleanup candidate
`_Probe47p.lean` and `_Probe47q.lean` are both in-progress probe modules feeding
`perDeckBridge`. When perDeckBridge lands, consider folding the finished
general lemmas (`pairCountBySum` + its 3 helpers, and the 47p binomial helpers)
into a proper named module (e.g. extend `CommanderPhysicalExchange.lean` or a
new `Shufflemath/FinsetPairCounting.lean`).

## 2026-11-17 (cont) — 47r/47s engine family + the perDeckBridge matching is fully worked out

### Done this turn (both build, 3209 jobs each, no sorry)
Two more forms of the partition-by-first-coordinate engine, completing the family:
- `_Probe47r.pairCountByAffine` — count of `(x,y)∈s×ˢt` with `g y = c + f x`.
- `_Probe47s.pairCountByConstSub` — count of `(x,y)∈s×ˢt` with `(c - f x) + g y = n`.
**47s is the one the per-deck target needs**: after `newLeftOriginalCount_eq`
(`(newLeftCards d L R ∩ leftOrigSet).card = (x - markedInLeft d L) + markedInRight d R`,
`x = leftOriginalCount d`), the target filter `(newLeftCards d L R ∩ leftOrigSet).card = n`
becomes exactly `(x - markedInLeft d L) + markedInRight d R = n` — the 47s form with
`c = x`, `f = markedInLeft d`, `g = markedInRight d`. The fiber keeps `g` as a raw filter
(`(c-a) + g y = n`), never solved for `g y`, so there is **no** Nat-subtraction-solvability
trap. 47q (sum) and 47r (affine) are the other two forms — kept as a reusable family.

### The perDeckBridge matching — FULLY worked out (next step, should be tractable)
Target: `#(s ×ˢ t).filter (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)`
with `s = (Fin 50).powersetCard 25`, `t = (Fin 49).powersetCard 25`, `x = leftOriginalCount d`.
Chain:
1. `newLeftOriginalCount_eq` (exists, `CommanderPhysicalExchange:530`) rewrites the filter
   to `#(s×ˢt).filter (fun p => (x - markedInLeft d p.1) + markedInRight d p.2 = n)`.
2. `pairCountByConstSub` (47s, c=x) → `∑_{aL ∈ s.image (markedInLeft d)} #s.filter(f=aL) · #t.filter (fun R => (x-aL) + markedInRight d R = n)`.
3. For `aL ∈ s.image f`: `aL ≤ 25` (markedInLeft ≤ 25). `#s.filter(f=aL) = leftCountByMarked aL = choose x aL · choose (50-x) (25-aL)` (47p).
4. `#t.filter (fun R => (x-aL) + markedInRight d R = n) = if x-aL ≤ n then rightCountByMarked (n-(x-aL)) else 0`.
   **This `if`-split lemma is the one piece left to prove**: when `x-aL ≤ n`,
   `(x-aL)+bR=n ⟺ bR=n-(x-aL)`; when `x-aL > n` the LHS count is 0. Then
   `rightCountByMarked (n-(x-aL)) = choose xR (n-x+aL) · choose (49-xR) (25-n+x-aL)` (47p).
5. **The crux (why it works):** `xR = #(markedRightPos d) = 50 - x` (by
   `markedRightPos_card`, `CommanderMarkedRightCount`), so `49 - xR = x - 1`. Substituting,
   my per-deck product is
   `choose x aL · choose (50-x) (25-aL) · choose (50-x) (n-x+aL) · choose (x-1) (25-n+x-aL)`.
   Unfold `transitionNumerator (N m k x y)` (`BernoulliLaplace.lean:26`, N=99,m=50,k=25,y=n):
   it sums `a∈range 26` of `choose x a · choose (m-x) (k-a) · choose (m-x) b · choose ((N-m)-(m-x)) (k-b)`
   with `b = y-(x-a) = n-x+a`, guarded by `x-a ≤ y` and `b ≤ k`. With m-x=50-x and
   (N-m)-(m-x) = 49-50+x = x-1, **its 4 factors are identical to mine**; the guards
   `x-a ≤ n` and `b ≤ k(=25)` are exactly my `if x-aL ≤ n` and `Nat.choose`'s 0-out-of-range.
   The sum over `aL ∈ s.image (markedInLeft d)` equals the sum over `a ∈ range 26` because
   `#s.filter(f=a) = 0` for `a > 25` (empty fiber) and every `a ∈ range 26` with nonzero
   fiber is in `s.image`.
6. Hence target `= transitionNumerator 99 50 25 (leftOriginalCount d) n`. Then
   `transitionWeight 99 50 25 x n = transitionNumerator / transitionDenominator` gives the
   per-deck mass, and fiber-averaging matches `commanderExchange25_countMass` (discharging
   `hMembershipExchange`) → `uniformFiber_intertwines` via `transitionCount_formula`.

**Remaining to execute (in order):** (4) the `if x-aL ≤ n` guard-split lemma; the
sum-over-image = sum-over-range-26; then assemble `perDeckBridge` and the
`transitionNumerator 99 50 25 x n` match. Promotion: fold the finished general lemmas
(47s engine, 47p helpers) into a named module (e.g. `Shufflemath/FinsetPairCounting`) and
the perDeckBridge into the BernoulliLaplace layer when it lands.

## 2026-11-17 (cont, 2) — 47t: rightFilterGuarded (the last conceptual piece) builds

### Done this turn
`_Probe47t.rightFilterGuarded (x aL n)` — the guarded hypergeometric count of the
right pile, now **built** (3210 jobs, no sorry). It counts
`R ∈ (Fin 49).powersetCard 25` with `(x - aL) + markedInRight d R = n` and gives
the 4-binomial right factor
`choose (markedRightPos d).card (n-(x-aL)) * choose (49-(markedRightPos d).card) (25-(n-(x-aL)))`
**exactly when the nested guards hold** (`x-aL ≤ n ∧ n-(x-aL) ≤ 25`) and `0`
otherwise. The nested-`if` shape is term-for-term `transitionNumerator 99 50 25 x n`'s
integrand's right half.

Proof shape (the hard part): split the nested ite with `if_pos`/`if_neg` (NOT
`simp`, which mis-normalizes `n-(x-aL) ≤ 25` to `n ≤ 25+(x-aL)` and breaks the
ite-reduction). The `h1∧h2` branch reduces `(x-aL)+markedInRight=n ↔ markedInRight=bR`
via a local `haddSub (c n) (hc : c ≤ n) (k) : c+k=n ↔ k=n-c` (proved by `omega`),
then applies `powersetCard_markedContent`. The two `0`-branches show the filter is
`∅` (`Finset.ext` + a `¬R ∈ filter` sub-proof + `simp [hnot]`), then `simp` for the
card.

### The perDeckBridge assembly — the ONLY thing left for the count half
Now that 47s (const-sub engine) + 47p (left binomial) + 47t (guarded right factor)
+ `newLeftOriginalCount_eq` all exist, the capstone is pure assembly:
```
#(s ×ˢ t).filter (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)  [s=(Fin50).powersetCard25, t=(Fin49).powersetCard25, x=leftOriginalCount d]
  = (via newLeftOriginalCount_eq)  #(s×ˢt).filter (fun p => (x - markedInLeft d p.1) + markedInRight d p.2 = n)
  = (47s pairCountByConstSub, c=x)  ∑_{aL ∈ s.image (markedInLeft d)} #s.filter(markedInLeft d = aL) · #t.filter (fun R => (x-aL) + markedInRight d R = n)
  = (47t rightFilterGuarded on the right factor)  ∑_{aL ∈ s.image f} #s.filter(f=aL) · [nested-if binomial(x aL n)]
  = (domain ext: #s.filter(f=a)=0 for a∉s.image f; s.image f ⊆ range 26)  ∑_{a ∈ range 26} #s.filter(f=a) · [nested-if binomial(x a n)]
  = (47p leftCountByMarked: #s.filter(f=a) = choose x a · choose (50-x)(25-a))  ∑_{a∈range26} [choose x a · choose (50-x)(25-a)] · [nested-if binomial]
  = (markedRightPos_card: #(markedRightPos d) = 50 - x, so 49-# = x-1)  ∑_{a∈range26} [the 4 factors]
  = transitionNumerator 99 50 25 x n  [by unfolding the definition]
```
**Confirmed** (this turn) that the codebase uses `transitionWeight 99 50 25 x y`
(N=99, m=50, k=25) for the 25/25 exchange — so the numerator is `transitionNumerator
99 50 25 x n` (5 args), NOT "99 50 50 25" (that was a typo in earlier 47o/47p
comments). The 4 factors match exactly after `#(markedRightPos d) = 50 - x`.

**Next (perDeckBridge in a new probe, e.g. `_Probe47u`):** write the `calc`/`rw` chain
above. Two nontrivial sub-steps: (1) the domain extension `∑_{aL∈s.image f} = ∑_{a∈range26}`
(prove `s.image (markedInLeft d) ⊆ range 26` and `#s.filter(f=a)=0 ⟺ a∉s.image f`, then
`Finset.sum_image`/`sum_congr`); (2) the final `= transitionNumerator 99 50 25 x n` by
`dsimp`/unfold of the definition + `simp` on the binomial factors (guarded by
`Nat.choose` = 0 out of range, matching the nested `if`). Then `transitionWeight 99 50 25
x n = transitionNumerator/transitionDenominator` gives the per-deck mass, fiber-average →
`uniformFiber_intertwines`.

## 2026-11-17 (cont, 3) — 47u: perDeckBridge skeleton builds; htodo is the sole remaining step

### State
`_Probe47u.lean` (untracked WIP — **do not commit until `htodo` is proved**; it carries
one `sorry`) builds (3215 jobs). The `perDeckBridge` assembly is 2/3 complete and
**proven**:

- `hfilt`/`hstep1`: the physical count
  `#(s50 ×ˢ t49).filter (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)`
  `= #(s50 ×ˢ t49).filter (fun p => (x - markedInLeft d p.1) + markedInRight d p.2 = n)`,
  `x = leftOriginalCount d`. Proof: `Finset.ext` + `simp [mem_filter]` +
  `rw [newLeftOriginalCount_eq d p.1 p.2]` (the `let`-unfolding of `x/f/g` closes the
  `↔` goal).
- `hstep2`: that const-sub count `= (s50.image (markedInLeft d)).sum (fun a =>
  #s50.filter(markedInLeft d · = a) * #t49.filter (fun R => (x - a) + markedInRight d R = n))`,
  via `47s pairCountByConstSub s50 t49 (markedInLeft d) (markedInRight d) x n`.
- `imageF_subset_range26` (private, proven): `s50.image (markedInLeft d) ⊆ range 26`,
  via `Finset.mem_image.mp` + `mem_powersetCard` + `card_mono` + `omega`.

**Remaining (`htodo`, the one `sorry`):**
```
(s50.image f).sum (fun a => #s50.filter(f=a) * #t49.filter (fun R => (x-a)+g R = n))
  = transitionNumerator 99 50 25 x n
```

### How to finish htodo (worked out this session — the 4 factors match exactly)
`transitionNumerator 99 50 25 x n` unfolds to
`(range 26).sum (fun a => let r := x-a; if r ≤ n then (let b := n-r; if b ≤ 25 then
  choose x a * choose (50-x)(25-a) * choose (50-x) b * choose (x-1)(25-b) else 0) else 0)`,
where `(N-m)-(m-x) = (99-50)-(50-x) = x-1`. Prove htodo by:
1. **Domain extension** (the only non-mechanical part):
   `(s50.image f).sum H = (range 26).sum H`, `H a = #s50.filter(f=a) * #t49.filter(...)`.
   Route: `= (range 26).sum (fun a => if a ∈ s50.image f then H a else 0)` (subset
   extension, `s50.image f ⊆ range 26`) `= (range 26).sum H` (`Finset.sum_congr` + the
   fact `#s50.filter(f=a) = 0` when `a ∉ s50.image f`, i.e. `a ∈ s50.image f ↔
   #s50.filter(f=a) > 0`). Decompose `range 26 = (s50.image f) ⊔ (range 26 \ s50.image f)`
   (disjoint, via the subset lemma) and note the integrand is `0` on the complement.
2. **Integrand match** for `a ∈ range 26` (`Finset.sum_congr`): the integrand's 4 factors
   `= H a`, because
   - `#s50.filter(f=a) = leftCountByMarked (47p) = choose x a * choose (50-x)(25-a)`
     (first two factors; `a ≤ 25` since `a ∈ range 26`); and
   - `#t49.filter((x-a)+g·=n) = rightFilterGuarded (47t) x a n` = the nested-if with
     `choose (markedRightPos d).card (n-(x-a)) * choose (49-(markedRightPos d).card)
     (25-(n-(x-a)))`; substitute `markedRightPos_card` (`#(markedRightPos d) = 50 - x`)
     to get `choose (50-x)(n-(x-a)) * choose (x-1)(25-(n-(x-a)))` (last two factors).
   The guard structure (`x-a ≤ n`, then `n-(x-a) ≤ 25`) is exactly `rightFilterGuarded`'s
   nested `if`, so the whole nested-if matches.
3. Unfold `transitionNumerator 99 50 25 x n` (`dsimp`) and close with `simp`/`omega`
   (the `choose`-out-of-range = 0 lemmas make the guarded `0`-branches line up).

After htodo: `perDeckBridge` is proved. Then in `uniformFiber_intertwines`
(`CommanderMembershipExchange.lean`, currently `hMembershipExchange` premise + `sorry`),
use `haveI : HasCommanderFiberCounts (exchange25) d := by  ...` deriving the per-deck
`fiberCount (exchange25) d n` equality from `perDeckBridge` + `transitionWeight =
numerator/denominator`, to discharge `hMembershipExchange` and close the F5 capstone
(then the G4 fiber-average `uniformFiber_intertwines`).

### Files
- `Shufflemath/_Probe47u.lean` — the WIP perDeckBridge (untracked; has one `sorry`).
- Proven building blocks it assembles: `_Probe47s` (pairCountByConstSub), `_Probe47p`
  (leftCountByMarked), `_Probe47t` (rightFilterGuarded), `CommanderPhysicalExchange.lean`
  (newLeftOriginalCount_eq, line ~530), `CommanderMarkedRightCount.lean`
  (markedRightPos_card, line 269), `BernoulliLaplace.lean` (transitionNumerator, line 26).
