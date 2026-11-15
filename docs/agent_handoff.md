# Agent handoff: next Shufflemath task

**Updated:** 2026-11-12 (5th session). **F4.1 COMPLETE** (`17ffab6`) and
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

1. **Do not stop, ask, or end the session before Wed Nov 18 23:59:59 EST 2026.**
   (Deadline extended from the original Thu Nov 12 22:27:06 EST at the
   user's request on the Nov 12 session.) This is a long autonomous build.
   You **will be compacted multiple times**; compaction is normal and is not
   a stopping signal.
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
  `t + (x - t) = x`.  **(2) Next concrete step:** assemble the full symbolic CL
  `fiberSum p x y = choose(r,y) * choose(N-r, m-y) * overlap_count (N m r k) x y`
  from the S1-side (this session) + the mirrored S2/plain-side count +
  `fiberSum_swap`/`fiberSum_eq`; OR go straight to (3) F3 item 4 (2-exchange TV).
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
