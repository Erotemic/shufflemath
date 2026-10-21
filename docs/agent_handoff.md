# Agent handoff: next Shufflemath task

**Updated:** 2026-10-21. **Source basis:** the October 21 source snapshot
(`9257fa35bb1b`), the October 21 fiber/disintegration overlay and its three
successive compilation fixes, plus the user's reported local build output.
This is an *operational handoff*. `lean_plan.md` is the authority for overall
scope and priority; `AGENTS.md` governs repository behavior.

## Exactly where to resume

**First action: verify the latest `FiberDisintegration.lean` v3 fix.** The
user's last displayed build failed because an `omit ... in` directive
intervened between a doc comment and the `fiber_card_pos` theorem. A v3
replacement removed that directive; the conversation does not yet include
its successful local build result. Do not repeat this as a current failure
without running the build, and do not question earlier user-confirmed
successful Lean builds.

```bash
cd ~/code/shufflemath
lake exe cache get
lake build \
  Shufflemath.FiberDisintegration \
  Shufflemath.PhysicalExchangeReduction \
  Shufflemath.CommanderFullDeckDisintegration
./dev/verify_next_phase.sh
```

If the build passes, **start F1a in `docs/lean_plan.md`**: count complete
permutations with a fixed left-pile membership subset. Work in one small
lemma-sized batch. If it fails, read the *first* actual error and fix the
affected module; rerun only that target before the full gate. The legacy
`./dev/verify.sh` uses `lake update` and is not a good default for this task.

## What is already there

| Capability | Where | Status to carry forward |
|---|---|---|
| General finite kernel, TV, Dobrushin, BL and first eigenfunction | `Shufflemath/{Finite,TotalVariation,Perturbation,Dobrushin,BernoulliLaplaceGeneral,BernoulliLaplaceCommanderBridge}.lean` | Previously compiled and reported verified |
| Exact macro 2-/3-exchange TV certificates and semantic transport | `BernoulliLaplace.lean`, `BernoulliLaplaceSemantic.lean` | Earlier tranche compiled |
| GSR product-label shuffle; TV/protocol refinement | `GSR.lean`, `FiberLifting.lean`, `OracleRefinement.lean`, `PhysicalRefinement.lean`, `ProtocolCertificate.lean` | Earlier tranche compiled; numeric alphabet bridge not done |
| Actual 99-card permutation count projection | `CommanderPermutation.lean` | User expressly confirmed successful compilation after its fix |
| Constructive witness of all 50 macro fibers | `CommanderFiberWitness.lean` | Authored; included in most recent targeted verification script |
| Uniform fiber disintegration and membership reduction | `FiberDisintegration.lean`, `PhysicalExchangeReduction.lean` | Authored; latest full local build not yet confirmed after v3 fix |
| Conditional full-uniform oracle and physical-perfect results | `CommanderFullDeckDisintegration.lean` | Authored; downstream of disintegration build; **counting and membership hypotheses still open** |
| Optional 2,401-pair exact TV minimum | `dev/BernoulliLaplacePairOptimality.lean` | Source provided; no confirmed `--pair` verification result |

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
- Do not run axiom-printing checks for routine verification.
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
4. Avoid `sorry`, `admit`, axioms, broad heartbeat disablement, and redundant
   proof-authority APIs. Avoid `#print axioms` spam; a final comparator-style
   audit is a separate task, not a standard build check.
5. Once tested, update `docs/lean_plan.md` status and the **first action** of
   this handoff, with the successful command and date. Do not mark a theorem
   unverified just because the packaging environment cannot run Lean when
   the user has already verified it locally.
6. Stage only changed files and commit with a single trailer using the
   current model, e.g.
   `Co-authored-by: GPT-6 <noreply@openai.com>`.

The active mathematical specification is in [lean_plan.md](lean_plan.md).
The detailed model distinction is in
[full_deck_oracle_bridge.md](full_deck_oracle_bridge.md) and
[commander_fiber_disintegration.md](commander_fiber_disintegration.md).
