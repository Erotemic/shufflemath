# Lean formalization roadmap (current)

Status date: **2026-10-21**. This is the **single active mathematical task list**.
For a new agent, begin with [agent_handoff.md](agent_handoff.md). Historical
phase notes are linked at the end; they do not override this plan. Read
`AGENTS.md` before modifying code.

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
| Inverse GSR | `GSR` | Stable label buckets and product-*label* composition; not yet numeric `Fin (a*b)` uniform-law identification |
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

**Start with F1a below.** The preceding fiber/disintegration tranche is
complete and compiles. For new Lean work, run `lake exe cache get` followed
by the affected module's `lake build`; run `./dev/verify_next_phase.sh` when
finishing a tranche. This is a regression workflow, not an extra gate on
the existing results.

## Work queue in dependency order

### F1. Prove the exact Commander fiber count -- FIRST mathematical task

**Goal:** discharge
`CommanderFullDeckDisintegration.HasCommanderFiberCounts`, already defined
in `Shufflemath/CommanderFullDeckDisintegration.lean`:

```lean
forall x : BernoulliLaplace.CommanderState,
  Dist.mass BernoulliLaplace.commanderStationary x =
    ((FiberDisintegration.fiberSet CommanderPermutation.project x).card : Rat) /
      (Fintype.card CommanderPermutation.Deck : Rat)
```

This is **not proved** by `CommanderPermutation.project_surjective`: an
inhabited fiber need not have the right *cardinality*. Build a structural
counting proof, without evaluating a type containing `99!` permutations.

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

### F2. Define the concrete membership and perfect-local kernels

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

### F3. Prove the 25-position physical-exchange membership law

**Dependency:** F2.

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
2. Define a permutation-preserving local-GSR kernel for the ordered cards in
   each *fixed* pile. Prove it cannot change the membership state.
3. Establish the row-wise bound against *physical perfect-local* shuffling:
   for each deck, the TV discrepancy is no greater than the sum of the two
   local GSR-versus-uniform errors (49-card and 50-card working sets).
4. Use the existing `PhysicalRefinement.finite_local_uniform_bound` and
   `ProtocolCertificate` weighted telescope to compose these errors over a
   schedule. Use a named initial law and an explicit 99-card uniform target.

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
