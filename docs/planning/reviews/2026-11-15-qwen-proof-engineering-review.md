# Shufflemath proof-engineering review - 2026-11-15

**Review date:** 2026-11-15 (America/New_York)  
**Reviewed source snapshot:** `shufflemath-source-2026-11-15T200601-5-6ec82508fa1b.tar.gz`  
**Git revision:** `6ec82508fa1bce8b15e2c37dd1a73bdcb22d38f8`  
**Purpose:** Dated, retained feedback to the Qwen formalization agent. This is a historical review, **not** a replacement for the active task queue.  
**Active sources of truth in this snapshot:** `AGENTS.md`, `docs/lean_plan.md`, `docs/agent_handoff.md`.

> **Repository layout note:** `docs/planning/` did **not** exist at this revision. This review is intentionally placed in `docs/planning/reviews/` for the requested permanent planning-review history. Do not infer that the active plan has moved: `docs/lean_plan.md` remains authoritative until an explicit migration is agreed and committed. Before claiming to have completed "all of docs/planning," first reconcile this path discrepancy and enumerate the actual planning obligations.

## 1. Review method and evidence limits

This review inspected the above source snapshot, the active F1-F5 roadmap, agent handoff, recent Git log, verification script, and source declarations in the relevant Lean modules. `python3 -m unittest discover -s tests -q` returned **37 tests, OK**. The checkout was clean at the archived revision. Neither `lake` nor `lean` was present in this review environment, so no new Lean compilation, tactic experiment, axiom-dependency inspection, or proof certification was performed here. Prior successful Lean builds are *reported by the repository's handoff*, not independently reconfirmed by this reviewer.

Evidence convention used below:

- **Source-level established:** the named theorem or construction occurs in committed `.lean` text. This does not by itself constitute an independent build verification.
- **Reported green:** the agent handoff claims a successful project build at its revision.
- **Open:** the required declaration, closed instance, or end-to-end theorem is absent from this snapshot, even if its ingredients are present.
- **Proposed:** a proof strategy or mathematical estimate requiring Lean formalization and verification.

The review does not recommend revisiting the proved F1/F2 foundations without specific contrary evidence, enumerating `99!` decks, introducing axioms, or running bulk axiom-reporting instrumentation during ordinary development.

## 2. Executive assessment

Qwen's mathematical progress is significant. The symbolic Bernoulli-Laplace/overlap identity has been extended to the Commander `(99,50,50,25)` regime; the deck-membership orbit/transitivity machinery and an equivariant card-set lemma are committed; F4 has concrete product-kernel and Fintype-free TV infrastructure; and F5 has a sound abstract cost/TV-certificate interface.

**The immediate problem is now integration and precision of semantics, not lack of preliminary lemmas.** The highest-value next result is the complete *concrete* membership-exchange kernel equality (A3), followed by an unconditional physical-perfect-local Commander corollary. Several files describe preparatory work as if that capstone had already landed. Do not treat an assembly sketch, a count projection, or an abstract theorem taking `hMembershipExchange` as an argument as completion of the concrete result.

The second major issue is the gap between a membership-correct exchange *model* and an actual finite-state kernel implementing a specified swap of positions. Keep this distinction visible in names, theorem statements, and claims about real physical shuffling.

## 3. Snapshot status against the real roadmap

| Workstream | Evidence at this revision | Status and completion gap |
| --- | --- | --- |
| F1: Commander fiber counts | `CommanderFiberCount`, `CommanderFiberMembership`, `CommanderFullDeckDisintegration.commander_fiber_counts` | **Complete in source / reported green.** Do not reopen without a counterexample or build failure. |
| F2: membership and perfect-local disintegration | `CommanderMembershipKernels.membershipLift_localLift_eq_fiberLaw` | **Complete in source / reported green.** This is the two-layer lift, not physical exchange. |
| F3: combinatorial counting | `ExchangeOverlap.generalCL_cmdr_2525` and related overlap/fiber-count results; `CommanderMembershipOrbits.membershipFiber_transitive` | **Critical ingredients complete**, including symbolic counting and orbit transitivity. These are not yet the whole A3 kernel law. |
| F3: concrete A3 and full physical-perfect theorem | `CommanderMembershipExchange` has `map_equiv_mass`, `distUniform_ofInvariantTransitive`, `membershipFiber_card`, `membershipLift_count`; `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_of_counts` still *takes* `hMembershipExchange` | **Open.** Missing `rawExchangeMembership_count`, full within-count invariance/assembly, and concrete theorem discharging `hMembershipExchange`. |
| F4.1: product-label GSR algebra | `GSR.productLabelShuffle_uniform_eq_ideal` | **Complete in source / reported green.** |
| F4.2: local-GSR semantics | `CommanderLocalGSR.gsrProductKernel`, `gsrLocal_preserves_pile`; `CommanderDeckGSR.preservesPiles_iff_pileRelabel`, `pileRelabelEquiv_pairInjective` | **Partial.** A product law on pile lists and a structural subgroup identification exist; a deck-to-deck *random finite-GSR kernel* for arbitrary `Deck` inputs has not been defined and certified. |
| F4.3-F4.4: distributional TV tools | `CommanderLocalGSR.gsrProductKernel_eq_distProductFinsupp`, `gsrProductKernel_rowTV_bound`, `gsrOneStep_terminalTV_bound`, `gsrRunNonexpansive`; generic weighted telescope | **Useful general tools complete.** The end-to-end *numerical* GSR-vs-perfect-local deck bound and its concrete schedule are missing. The roadmap text that still calls the product bridge blocked is stale. |
| F4.5: actual full-deck terminal guarantee | `PhysicalRefinement.finite_local_uniform_bound`, `ProtocolCertificate.terminalTV_le_reference_add_budget` | **Open** at a concrete finite-GSR Commander protocol and explicit initial/target laws. |
| F5: cost and bounded optimization | `Cost.ActionKind`, `protocolCost_nonneg`, `ProtocolCertificate.costedProtocol_certificate` | **Abstract interface present; concrete instance/finite-class optimizer open.** Nonnegative cost or a sufficient upper bound alone is not optimality. |

The optional 2,401-pair certificate, presentation work, and extended numerical experiments are **not release blockers for the F1-F5 theorem ladder** unless their logical dependencies are explicitly made part of a new acceptance target.

## 4. Findings requiring correction

### R1 - Critical: missing concrete F3 capstone is obscured by optimistic status wording

**Evidence:** `Shufflemath/CommanderMembershipExchange.lean` announces in its module-level comment that it "proves" the physical-exchange law, but contains only supporting lemmas and a proposed `rawExchangeMembership_count` / `hMembershipExchange` assembly plan. `docs/f3_membership_exchange.md` and the most recent section of `docs/agent_handoff.md` correctly list A3 as outstanding. Other passages of `docs/lean_plan.md` say "F3 item 3 is now COMPLETE in both halves" when referring to the combinatorial/orbit ingredients rather than the concrete kernel equality.

**Action:** Record two separate gates: `(F3-a) combinatorial/orbit ingredients` (complete) and `(F3-b) concrete membership-kernel equality and physical corollary` (open). Modify the misleading docstring and stale roadmap statements **only when updating the current handoff**. In the dated review, preserve the original evidence rather than silently rewriting history. The acceptance theorem must instantiate the actual `rawExchange`, `membershipLift`, `localLift`, and `commanderExchange25` without retaining the unproved exchange-law premise.

### R2 - High: `rawExchange` is not a literal fixed-pair position swap

**Evidence:** `CommanderPhysicalExchange.rawExchange` is defined by

```lean
FiniteKernel.comp rawExchangeMembership localLift
```

It samples the *post-exchange membership* and then resamples a uniform ordering in that membership fiber. The `rawExchangeMembership` component correctly models the distribution of the left-card set under uniform selected-position subsets, but there is no deck-level deterministic bijection pairing the selected positions. Subsequent `exchangeThenLocalReset` therefore applies another local reset to a kernel that has already reset order.

**Action:** Distinguish three operations in prose and, ideally, declarations:

1. A physical **swap kernel** built from a fixed explicit bijective pairing of the selected 25 left and 25 right positions, acting on a `Deck`.
2. A **membership exchange kernel**, obtained by observing only the post-exchange left set.
3. A **swap-then-perfect-local kernel**, which may equivalently use `rawExchangeMembership.comp localLift` *after its relationship to (1) has been proved*.

First prove that observing the physical swap's membership agrees with `rawExchangeMembership`; then use composition with `localLift`. If constructing (1) is deferred, label the existing construction as an **abstract perfect-local implementation**, not as an already formalized fixed-pair physical swap. This distinction must not be hidden by the fact that the observed membership law is correct.

### R3 - High: the standard verification path misses active proof targets

**Evidence:** `dev/verify_next_phase.sh` explicitly builds F1/F2 and `CommanderPhysicalExchange`, but not `Shufflemath.CommanderMembershipExchange`, `Shufflemath.CommanderMembershipOrbits`, `Shufflemath.CommanderDeckGSR`, `Shufflemath.CommanderLocalGSR`, `Shufflemath.ExchangeOverlap`, or `Shufflemath.FinsetCombinatorics`. The last two are standalone proof modules not imported by the default target graph. `Shufflemath.lean` omits these modules as well. Successful builds of other targets do not certify these active modules.

**Action:** Add those six modules as **direct** Lake targets in `dev/verify_next_phase.sh`; add any other new workstream entry point as it is created. Do not replace the existing targeted strategy with an expensive wildcard or optional all-pair certificate. A targeted build of each newly edited module is still the fast development loop; the amended script is the tranche handoff gate. The full script can continue to run the 37 Python tests; each type of evidence should be reported separately.

### R4 - High: compaction handoff contains contradictory starting instructions

**Evidence:** `AGENTS.md` still tells a fresh agent to resume the F2c-iv-b capstone, although F2 is complete. `docs/lean_plan.md` has an 11-Nov status date and repeats the obsolete F2 entry point. `docs/agent_handoff.md` opens with a 12-Nov fifth-session summary but now contains a 15-Nov 25th-session entry; multiple historical sections are marked "resume here first." At roughly 1,500 lines, rereading the entire handoff after every compaction costs substantial context and makes stale instructions more likely to be followed.

**Action:** After stabilizing the next A3 tranche, keep the current operational header to approximately one screen: revision, green targets, completed milestones, current theorem, exact blockers, next command, and owner. Preserve older entries in dated historical notes rather than deleting them. Fix active pointers in `AGENTS.md` and `docs/lean_plan.md`. **Do not overwrite or discard historical data**; the current document must be concise, the history append-only.

### R5 - Medium: large bespoke proofs deserve a reuse/maintenance pass, not immediate demolition

**Evidence:** `CommanderMembershipOrbits.lean` is about 900 lines, including a four-part partition, twelve cross-part disjointness lemmas, and separate image/preimage/injectivity arguments. The technique is legitimate and the handoff reports it compiles, but it imposes a substantial maintenance cost. The handoff also records a destructive source-text splice that truncated `CommanderPhysicalExchange.lean` and later had to be restored.

**Action:** **Keep the completed orbit theorem** for A3; do not divert into a speculative refactor first. After a physical corollary compiles, consider a generic disjoint-piece equivalence construction (or existing `Equiv.sumCongr`, `Equiv.Perm`, finite-type/subtype equivalences) and a small theorem naming the group action. Require a concrete deletion of duplication and preserved theorem statements before accepting a refactor. For automated file edits, assert that each anchor occurs exactly once, stage a patch diff, and fail closed if anchors are absent. Never do an unchecked `s[:start] + ... + s[end:]` splice.

### R6 - Medium: the initial-law and optimization claims need sharper scopes

**Evidence:** `two_physical_perfect_exchanges_uniform_of_counts` starts from a **uniform lift of the segregated macro state**, not an explicitly ordered deterministic segregated `Deck`. `Cost` currently has an action alphabet and additive nonnegative costs but no imposed cost calibration, bounded protocol class, or proven minimum-cost theorem.

**Action:** State the initial law visibly in any advertised physical guarantee. If a deterministic initial deck is desired, prove a first-step special case or include the necessary initial local shuffle and its cost. Keep three distinct claims apart: (i) a concrete schedule meets an error threshold; (ii) it minimizes a *conservative certified upper-bound objective* over a finite class; (iii) it minimizes **actual TV** or physical cost over a specified class. Claim (iii) only with exact performance values or lower bounds for competitors.

## 5. Proof-engineering strategy: close the statements, not just their scaffolding

The agent has good small-lemma discipline, but more attention should go to *the shape of the next exported theorem*. For each tranche:

1. Write the final declaration and its exact assumptions as a comment or temporary scratch theorem. Identify which of those assumptions are not yet proved.
2. Draw a five-node-or-smaller dependency chain from existing declarations to that theorem. Choose one missing edge, not a broad new support library.
3. Prove a **transport or equivalence lemma before expanding probability mass**. Pushforward/reindexing/finite support lemmas should eliminate large sums before arithmetic begins.
4. Isolate one representative point-mass computation in a small scratch file if elaboration stalls. Test the *exact target toolchain/API*; do not infer a Mathlib lemma name from memory. Promote only a compiler-checked proof.
5. Use `simp only` with named lemmas, explicit `change`, `rw` and `calc` chains around `StdSimplex`, `Finsupp`, `Finset` and `Equiv`. Avoid unconstrained `simp`/`aesop` or normalization over `Equiv.Perm (Fin 99)`.
6. At a `Nat` subtraction boundary, carry side conditions or move the algebra into `Int`, with a proved cast bridge. Do not rely on saturated subtraction identities outside their valid range. Retain the successful non-saturating approach from `ExchangeOverlap`.
7. When repeated case splits arise, look for a generic equivalence, a partition with tagged summands, or a finite-group invariance lemma. Never hand-prove injectivity and surjectivity if a usable `Equiv` can be constructed directly.
8. After two genuinely failed attempts with the same goal shape, record the **type of failed expression**, relevant error, and an alternative formulation; change representation before trying another tactic variation. A theorem that compiles but does not discharge the advertised interface is not a finished tranche.
9. Prefer small high-value regression examples and direct Lake builds to blanket test proliferation. Python is useful for discovering wrong combinatorics but cannot close a Lean obligation.
10. Check the statement's interpretation once more at completion. A model-level equality may hold while a stronger physical or optimality statement does not.

### F3 implementation option A: factor through membership first (preferred if it compiles cleanly)

Currently `rawExchangeMembership` takes `Deck`, although the resulting membership distribution depends only on the old left-card set, not on order within either pile. Factor out that dependence:

- Define a kernel `exchangeMembershipKernel : FiniteKernel Membership Membership` whose support is the valid 50-element target sets `T` with `|(S \ T)| = 25` (equivalently `|(T \ S)| = 25`). For equal-size memberships, the two differences have equal cardinality.
- Prove a bijection between position-choice pairs `(L,R) : exchangeChoice` and target memberships `T` adjacent to `S = membership d`: `S \ T` determines precisely the 25 outgoing named cards, `T \ S` the incoming ones, and the deck's left/right position maps uniquely recover the corresponding chosen positions. The exchange pairing is irrelevant for **membership**, not for ordered-deck results.
- Prove the kernel factorization

```lean
rawExchangeMembership =
  FiniteKernel.comp (FiniteKernel.deterministic membership)
    exchangeMembershipKernel
```

  (spelling and namespaces to be compiler-checked). This should be a transport of the uniform choice law across a finite equivalence, not a bespoke `Finsupp.mapDomain` sum over deck permutations.
- The A3 target becomes a purely membership-level intertwining:

```lean
FiniteKernel.comp membershipLift exchangeMembershipKernel =
  FiniteKernel.comp BernoulliLaplace.commanderExchange25 membershipLift
```

  Import `Shufflemath.ExchangeOverlap` explicitly where needed, then combine F1b fiber cardinalities, `ExchangeOverlap.generalCL_cmdr_2525`, and symmetry/detailed balance **at the membership level**. `membershipFiber_transitive` and the existing group-uniformity lemma can prove within-count uniformity.

The proposed one-to-one adjacency characterization must be proved, not assumed. It is a good first checkpoint: if it cannot be proved with a small bijection, fall back to option B rather than growing an unbounded abstraction layer.

### F3 implementation option B: finish the existing A3 architecture

If option A creates an avoidable API detour, use the present `CommanderMembershipExchange` design without rewriting it:

1. Establish the left and right subset-count lemmas on a *single deck* using the existing `markedLeftPos`, `markedRightPos`, `FinsetCombinatorics` and choose-product interfaces. The number of 25-subsets containing `i` marked cards depends only on `leftOriginalCount d`.
2. Sum independent choices to obtain the count-level `rawExchangeMembership_count` equality. Prove the per-deck formula first; only then average over the project fiber. Use the already-proved Commander-specific symbolic numerator law rather than a 50-case `native_decide` or a fresh four-bin algebra campaign.
3. For the target-membership law, define the action of a marked/unmarked-preserving deck relabeling on `Membership` as an **equivalence**. Show it preserves membership counts; prove the project-fiber input law is invariant under corresponding right relabelings; lift `newLeftCards_conjugate` to an equality of output distributions (not merely a pointwise image).
4. Apply `distUniform_ofInvariantTransitive` to the pushed-forward result, using `membershipFiber_transitive` to supply transitivity. Verify the support is in the target count fiber. Combine constancy with the count projection and `membershipFiber_card`; finally use kernel extensionality.
5. State and prove `hMembershipExchange` and then a concrete physical-perfect-local corollary applying `two_physical_perfect_exchanges_uniform_of_counts` with `commander_fiber_counts` and the F2 recovery/factorization lemmas. No abstract membership-exchange hypothesis may remain in the exported corollary.

**Suggested independent acceptance checkpoints:** (a) factorization or per-deck count law, (b) count-projection equality, (c) invariance under a typed membership action, (d) complete A3, (e) unconditional two-exchange theorem. Keep these in separate small, green commits.

## 6. F4 strategy: choose a finite representation that matches the final deck theorem

The F4.2 work so far has established a useful structural fact: pile-preserving deck permutations are within-pile relabelings, via `pileRelabelEquiv`. Use that to transport distributions instead of trying to prove a generic list-to-permutation conversion by expanding `List.mem_bind` and `List.toMultiset` across a non-`Fintype` list type.

Proposed development ladder:

1. Choose the canonical ordered list of the 50 left **positions** and 49 right positions. Show an `a`-label stable sort induces a permutation of those indices; preserve length/nodup and total coverage structurally. If possible, define the induced position equivalence directly instead of converting arbitrary lists of card identities.
2. Take two independent per-pile index-shuffle laws, transport them through `pileRelabelEquiv` and `reorderedDeck` to a `FiniteKernel Deck Deck`. Prove membership preservation and that the deck-level kernel agrees with the specified physical within-pile inverse-GSR operation. The law should work for **any** current deck, not only the canonical initial deck.
3. Transport the already-proved `gsrProductKernel_eq_distProductFinsupp` and `gsrProductKernel_rowTV_bound` into that finite deck space. State the reference kernel as **uniform order conditional on the current membership**, not a globally uniform deck refresh.
4. Derive a quantitative local error. The first certificate can be loose but explicit; do not wait for the exact Bayer-Diaconis permutation formula.
5. Plug the per-step discrepancy and the F3 physical-perfect reference into `PhysicalRefinement.finite_local_uniform_bound` or the existing weighted-telescope infrastructure. Name the initial law, target `uniformDist Deck`, schedule, and constants.

### Concrete candidate for the first quantitative GSR bound

For an inverse `a`-shuffle defined by assigning independent uniform labels and stable-sorting `n` **distinct** cards, condition on all labels being different. By exchangeability of the labels, the relative order on this event is uniform over the `n!` possible orders. Therefore the shuffle distribution is a mixture of the uniform law and a collision-event law, implying

```
TV(inverse_a_shuffle(n), uniform_n) <= P(any label collision)
                                       <= choose(n, 2) / a.
```

The second inequality is the elementary pairwise union bound. This is a **proposed proof route**, not a proved project theorem. It requires a formal conditioning/mixing argument, including the zero-probability case when `a < n`. The bound is allowed to exceed 1 (still valid, but not useful) and can be capped at 1. For the 50-card and 49-card piles it gives a row-error budget at most

```
choose(50,2)/a + choose(49,2)/b = 1225/a + 1176/b.
```

For equal alphabets `a=b=A`, the simple upper bound is `2401/A`. When interpreting `A = 2^r` as `r` successive 2-way riffles, the cost model must charge **r riffles per pile**, not one magical `A`-way operation. The quantified statement also needs to be uniform in the source *ordered* pile, not merely proved for one list.

This supplies a realistic first path to a fully explicit, if conservative, F4 theorem. Improve the rate after one complete end-to-end certificate exists.

## 7. F5 strategy: certify feasibility first, optimize only a precisely declared objective

A final F5 theorem should explicitly contain: the initial deck distribution (possibly a lifted segregated macro state), target uniform distribution, finite physical action schedule, the exact finite-GSR deck kernels and exchanges, a rational terminal TV bound, additive action cost, cost units, and any assumptions used to interpret the model as physical operations.

Implement in two milestones:

**F5-A (feasibility/cost):** choose concrete integer riffle rounds, exchange count, and any initial reset; build an explicit finite list of `CostedKernel Deck`. Prove its semantics equal the schedule in F4, derive `TV <= epsilon` (for a named rational `epsilon`) and `protocolCost = C`. The abstract certificate already exists: instantiate it, do not rebuild perturbation calculus.

**F5-B (bounded optimization):** define an explicit finite admissible class and an objective. If the objective is the **certified upper bound**, a finite search/`argmin` proof can establish minimal cost among protocols passing that *sufficient bound*. If the claim is optimal actual TV or globally fastest physical shuffle, prove the required competitor lower bounds/exact values first. A computed optimum of an upper-bound surrogate is not an optimum of physical reality. State finiteness, cost calibration and completeness of the admissible class in the theorem, rather than in prose alone.

Prefer a modest, honest certified class and a complete proof over an unconstrained global-optimum aspiration. Keep any measurements as explicit parameters or separately documented empirical estimates; do not smuggle them into pure mathematics as universal facts.

## 8. Recommended sequence and acceptance gates

These are **ordered proof deliverables**, not time estimates and not instructions to keep producing documentation instead of theorems.

| Gate | Next commits / result | Done only when |
| --- | --- | --- |
| 0. Make verification truthful | Add direct builds for `CommanderMembershipExchange`, `CommanderMembershipOrbits`, `CommanderDeckGSR`, `CommanderLocalGSR`, `ExchangeOverlap`, and `FinsetCombinatorics`; fix the most misleading active status pointers | `./dev/verify_next_phase.sh` runs on the working machine, all listed modules build, Python tests pass; retain the prior dated notes |
| 1. F3 count law | Membership factorization **or** `rawExchangeMembership_count` as a closed Lean theorem | The type is the intended complete count-kernel equation, not a separate cardinality observation |
| 2. F3 uniform target law | Equivariant action on membership laws and invariance proof | Invariance, support, and transitivity are all explicit and the uniform-fiber conclusion compiles |
| 3. F3 final assembly | Concrete `hMembershipExchange` and unconditional two-exchange physical-perfect theorem | No unproved `hMembershipExchange` or `HasCommanderFiberCounts` parameter survives in the exported Commander result; initial law is explicit |
| 4. Model correctness | Fixed-pair position-swap kernel or honest renaming/statement of the model boundary | The claimed physical swap has an actual deck-level semantics and a proved membership pushforward, or claims are explicitly weakened |
| 5. F4 deck kernel | GSR shuffles realized as membership-preserving `Deck` kernels | Correct support/order preservation, equivalence to the pile GSR law, and row-TV transport are Lean-checked |
| 6. F4 quantitative terminal bound | Collision-based or better per-pile bound plus concrete reference schedule | One explicit 99-card finite-GSR protocol has a Lean-checked symbolic or rational TV upper bound against uniform |
| 7. F5 feasibility | Concrete `CostedKernel Deck` schedule and threshold | Named schedule, `TV <= epsilon`, and exact cost all appear in the theorem |
| 8. F5 optimization | Bounded finite protocol class and precise minimum-cost claim | The objective is unambiguous (actual TV vs bound surrogate) and the minimization quantifier is discharged by a proof |
| 9. Historical/documentation closeout | Reconcile `docs/planning/` vs `docs/lean_plan.md`; update active pointers and status | Every F1-F5 acceptance in the active roadmap maps to a compiled named theorem or is visibly recorded open; do not declare an absent planning tree complete |

## 9. Small-batch instructions for Qwen's next session

**Read the most recent section of `docs/agent_handoff.md`, then this review, then the active F3 portion of `docs/lean_plan.md`.** Do not restart F2. Before building new abstractions, check the exact declaration targeted by the next gate and the source-level prerequisites. Perform Gate 0's missing verification-target update in a small standalone commit, then start F3 Gate 1.

Suggested first proof trial: write a local, source-order-independent membership-exchange equivalence for a fixed `Deck`. Prove that each valid 25-out/25-in target membership has exactly one `(L,R)` preimage. If this closes compactly, use it to factor `rawExchangeMembership` through `membership`; otherwise complete the existing per-deck `leftHyper`/`rightHyper` route and do not block F3 on the new abstraction. Either way, the next meaningful outcome is a **compiled count-projection theorem**, not another speculative roadmap entry.

Every completed batch should record: theorem name and exact statement; new and reused lemmas; build target and result; whether the exported theorem is still conditional; and the next one missing edge. Do not claim a theorem completed because all its ingredients exist. Keep the current worktree and refrain from creating worktrees. Preserve the history of unsuccessful proof attempts as **short, dated, informative summaries**, not repeated multi-page compaction instructions.

## 10. Retrospective assessment criteria

For later analysis of whether this review helped, compare subsequent commits against the following falsifiable outcomes:

1. Did the concrete A3 membership-kernel equality get proved, and at what revision?
2. Was the physical-vs-membership/reset model boundary formalized or honestly labeled?
3. Did the default verification script begin building the active modules directly?
4. Was the handoff's single current task unambiguous after compaction?
5. Was the final F4 deck-level GSR theorem quantitative and tied to a concrete protocol?
6. Did F5 distinguish certified feasibility, bound-surrogate optimization, and actual-TV optimality?
7. Did new work decrease dependency depth and duplicate argument volume rather than merely increasing theorem count?

The desired end state is **a small collection of strong, interpretable end-to-end theorems with clear physical assumptions**, not the largest possible inventory of helper lemmas.
