# Qwen proof-quality, consolidation, and rebuild-cost review

**Date:** 2026-11-15  
**Repository:** `shufflemath`  
**Reviewed snapshot:** `shufflemath-source-2026-11-15T200601-5-6ec82508fa1b.tar.gz` (source snapshot labeled `6ec8250`)  
**Document status:** historical, additive review; do not overwrite or revise `2026-11-15-qwen-proof-engineering-review.md`  
**Audience:** Qwen, the next Lean proof contributor, and future maintainers comparing proof-engineering progress.

## 1. Verdict and scope

The earlier November 15 review was principally about finishing the missing F3-F5 theorems. **This separate review is about the quality and maintainability of the existing proofs, duplicate mathematics, and the cost of recompilation.** It is a diagnosis and a prescriptive refactoring plan, not a claim that measured performance regressions have already been demonstrated.

The code contains *real* duplication, not merely long proof scripts. The strongest examples are (a) two independently proved subset-fiber-counting chains, (b) two independent schedule-intertwining inductions, and (c) an older restricted overlap-identity proof chain followed by a more general one. One numerical `native_decide` certificate can already be replaced by a later symbolic theorem. There are also large upstream modules whose internal organization makes rebuilds coarser than necessary.

**Evidence limit.** This assessment inspects source declarations, line ranges, import relationships, and the repository verification script. It did not compile Lean, obtain elaborated dependency graphs, or time fresh/warm builds; no claim below that a refactor "saves X seconds" is established. The pinned Lean version is 4.34.0. All code sketches below are candidate *proof shapes*, not certified drop-in patches; use the project's `module` / `public import` / `@[expose] public section` conventions and compile each step locally.

### Snapshot-level data

- 33 `Shufflemath/*.lean` modules. The three largest relevant files are `BernoulliLaplaceGeneral.lean` (2,340 lines), `ExchangeOverlap.lean` (1,224), and `CommanderMembershipOrbits.lean` (903); `TotalVariation.lean` has 1,085 lines. Size is a triage signal, **not** a runtime measurement.
- A source-level reverse-import walk finds 12 downstream modules for `BernoulliLaplaceGeneral`, 26 for `TotalVariation`, 27 for `Matrix`, and 30 for `Finite`. By contrast, `ExchangeOverlap` and `FinsetFiberCount` have **zero** downstream `Shufflemath` imports in this snapshot. The last two can be made cleaner, but their cleanup alone will not accelerate the rest of the library's incremental builds.
- `Shufflemath.lean` imports neither most Commander modules nor `ExchangeOverlap`; `dev/verify_next_phase.sh` omits `CommanderMembershipExchange`, `CommanderMembershipOrbits`, `CommanderDeckGSR`, `ExchangeOverlap`, and `FinsetFiberCount`. Consequently, the default verification path is not a complete test of the active tranche.

## 2. Prioritized work table

| ID | Finding | Proof-quality value | Likely incremental-build value | Priority |
|---|---|---|---|---|
| Q1 | Two subset-fiber counting constructions (`ExchangeOverlap` vs. `FinsetFiberCount`) | High: actual duplicated mathematics | Low until imported; may improve this target itself | **P1: safe first consolidation** |
| Q2 | Restricted `generalCL` chain repeated by stronger `generalCL_ns` chain | High: duplicated arithmetic and boundary cases | Moderate for the optional `ExchangeOverlap` target | **P1: preserve theorem API, remove redundant proofs** |
| Q3 | `native_decide` Commander center certificate duplicates a proved symbolic identity | High: removes redundant certificate | Potentially high for `ExchangeOverlap`; must measure | **P0: quick win** |
| Q4 | Two schedule inductions and transport lemmas (`OracleRefinement`, `PhysicalRefinement`) | High: same abstract argument twice | Moderate, depending on module placement | **P1: share an abstract theorem** |
| Q5 | General BL first-mode proofs live in central `BernoulliLaplaceGeneral` | High: better separation of domains | **High potential**: 12 downstream modules | **P2: measured module split** |
| Q6 | Product/mixture TV machinery shares the central `TotalVariation` module | Medium: responsibilities mixed | **High potential**: 26 downstream modules | **P2: measured split, only after Q5** |
| Q7 | Matrix and kernel Dobrushin APIs have parallel definitions | Medium: clarify canonical representation | Uncertain | P3: consolidate *proofs*, retain useful views |
| Q8 | Four-piece orbit equivalence in `CommanderMembershipOrbits` | Medium: long specialized construction | Low: one downstream importer | P3: **defer** while F3 is open |
| Q9 | Wide imports and duplicate import declarations | Medium: dependency clarity | Varies; especially `FinsetFiberCount`'s `import Mathlib` | P1: surgical import diet |

**Ordering rule:** a missing mathematical theorem (the F3 membership-kernel equality) is still more important than cosmetic cleanup. Do P0 and small P1 changes in isolated commits; do not start broad P2/P3 migrations until the active F3 capstone has a green build or the split removes an observed development bottleneck.

## 3. Q1: remove the duplicated subset-fiber proof chain

**Concrete evidence.** `Shufflemath/ExchangeOverlap.lean:332-522` defines `s1Fiber`, `fiberA` and proves `s1Fiber_biUnion`, `fiberA_card`, `s1Fiber_card`, `s1Fiber_choose`. `Shufflemath/FinsetFiberCount.lean:20-185` independently defines `sFiber`, `sFiberA` and proves their generic counterparts, `sFiber_biUnion`, `sFiberA_card`, `sFiber_card`, `sFiber_choose`. The generic definitions use an arbitrary `Finset` universe `U` and arbitrary `T1`; the specialized definitions are exactly the same constructions for `U := starsUniv p`.

The extraction succeeded conceptually but was **not integrated back**: `ExchangeOverlap` does not import `FinsetFiberCount` in this snapshot. Both long bijection/cardinality arguments remain present.

**Actionable replacement recipe for Qwen:**

1. First compile `Shufflemath.FinsetFiberCount` unchanged, and separately compile `Shufflemath.ExchangeOverlap`; record baseline elapsed time and memory. This is especially important because `FinsetFiberCount.lean:3` has a broad `import Mathlib`.
2. Import `Shufflemath.FinsetFiberCount` from `ExchangeOverlap`. Keep the existing names and statements initially as compatibility wrappers. Do not rename users or delete code before the wrappers compile.
3. Show the definitional bridge (`s1Fiber p x t T1` is `sFiber (starsUniv p) T1 x t`; similarly `fiberA` is `sFiberA`). The intended proof for `s1Fiber_choose` can then have this shape (check elaboration in the current module system):

```lean
-- Candidate body replacing the existing long specialized proof.
  change (sFiber (starsUniv p) T1 x t).card =
    Nat.choose T1.card t *
      Nat.choose ((starsUniv p).card - T1.card) (x - t)
  exact sFiber_choose (starsUniv p) T1 x t htx hT1
```

4. Likewise make `s1Fiber_biUnion`, `fiberA_card`, and `s1Fiber_card` thin corollaries of the generic corresponding theorem, *not* separate `Finset.card_bij` / `Finset.card_biUnion` developments. If `change` fails, first establish a small definitional equality with `rfl`, and rewrite using it; **do not open every finite-set definition with blanket `simp`.**
5. Search all callers by name and verify them; only then remove unused specialized proofs. Keep the public theorem names as wrappers if callers or historical documentation rely on them.
6. Recompile the two targets and their importers, if any. Record what disappeared (number of duplicate non-wrapper proofs and source lines), not just how many lines were edited.

**Acceptance:** one cardinality-bijection proof family, one generic interface, specialized results established in a handful of lines. The same theorem statements remain available. No changes to the physical meaning of `Membership`, exchange, or BL parameters.

## 4. Q2/Q3: prefer the strongest overlap identity; remove redundant computational certification

**Concrete evidence.** In `ExchangeOverlap.lean`, `F4match` (line 722), `tterm_eq_oterm` (766), `tterm_eq_oterm_all` (809), and `transition_eq_sum_oterm_ySuba` (876) support the restricted `generalCL` (1019), which assumes `m + r <= N`. Later, `baseInt_eqNatCast` (1079), `F4match_ns` (1092), `tterm_eq_oterm_ns` (1125), `tterm_eq_oterm_all_ns` (1138), and `transition_eq_sum_oterm_ySuba_ns` (1180) establish `generalCL_ns` (1208), without that restriction. The non-saturating chain already reuses much of the common earlier factor algebra.

**Concrete refactor:** make `generalCL_ns` the canonical mathematical result. Keep `generalCL` with its original statement and name, but prove it as a corollary: its `hN : m + r <= N` implies the needed `m <= N`; the other prerequisites are already present. This requires **declaration reordering**: Lean cannot refer to a theorem declared later in the same source file. Move the canonical theorem (and its prerequisites) before the small `generalCL` wrapper, or move the wrapper and `fiberSum_eq_overlap` below `generalCL_ns`.

Once the wrapper compiles, check whether the old restricted `F4match`, `tterm_eq_oterm`, `tterm_eq_oterm_all`, and `transition_eq_sum_oterm_ySuba` have external users. The snapshot shows only internal links through the old chain. Remove the unused restricted proof chain; retain helpers shared by both, such as `F1match`, `F2match`, `F3match`, the signed-choose lemmas, and the support-clipping argument. This replaces duplicated proof reasoning with one stronger route.

**Specific immediate replacement.** `overlap_eq_revTransitionNumerator_cmdr_2525` (line 114) uses `native_decide` on the center case. `generalCL_cmdr_2525` (line 1222) already proves exactly the reversed equality symbolically. Move the former theorem **after** `generalCL_cmdr_2525`, preserving its public name and statement, and replace the proof with:

```lean
  exact generalCL_cmdr_2525.symm
```

The *position* matters: simply editing the early proof fails because the general theorem is declared later. Inspect prior uses before relocating (a source-name search shows no callers beyond comments in this snapshot). This is an especially good Qwen-sized change: one theorem, one build, one commit.

**Boundary warning.** Do **not** delete `overlap_eq_revTransitionNumerator_cmdr_251` (the `(x,y)=(25,1)` case) on the same rationale. `generalCL_ns` assumes `k <= y`, which fails at `k=25, y=1`. Likewise, do not claim the stronger identity has been proved for all 2,500 Commander pairs without handling the `y < 25` range separately. A smaller theorem with the wrong domain is not an improvement.

**Acceptance:** (i) center certificate now follows from a theorem; (ii) restricted CL derives from the stronger CL; (iii) no lost boundary cases; (iv) optional `ExchangeOverlap` builds without extended heartbeats or `native_decide` on 99-permutation data. Keep small-deck computations where they provide genuinely independent regression evidence.

## 5. Q4: one generic schedule-intertwining induction, not two

`OracleRefinement.lean:82-136` proves the schedule kernel equality and distribution transport by list induction; `PhysicalRefinement.lean:31-76` proves essentially the same induction with a general per-step `List.Forall₂` premise. Their conclusions are the same kind of composition/transport statement, and the physical version is *more general*.

**Refactor route that avoids an import cycle:**

1. Extract the generic `PhysicalRefinement.schedule_intertwining` and its associated distribution transport lemma to a small `Shufflemath.ScheduleIntertwining` (name is suggestive) module, importing the existing `compList` definition from `Perturbation` and only the finite-kernel prerequisites. Preserve `List.Forall₂` as the general interface.
2. Both `OracleRefinement` and `PhysicalRefinement` import this shared module. Keep their existing named theorems, but make them short applications of the generic results.
3. In `OracleRefinement`, derive a `List.Forall₂` witness between `schedule` and `oracleSchedule project lift schedule` by induction over `schedule`; each cons step uses the existing `oracle_intertwining` theorem. Then apply the generic schedule theorem.
4. In `PhysicalRefinement`, pass its existing `hsteps` directly to the generic theorem. The `schedule_apply` wrappers likewise become single applications.
5. Recompile all consumers of both wrappers. Inspect the import graph again; the new generic module must **not** import either refinement module.

**Do not** import `PhysicalRefinement` from `OracleRefinement` as a shortcut: today `PhysicalRefinement` already imports `OracleRefinement`, so that would introduce a cycle. The extraction is warranted because both arguments are true at the same abstraction level, not just superficially similar syntax.

**Acceptance:** exactly one nontrivial list induction proving schedule intertwining; the oracle and physical public APIs are preserved; zero circular imports; no additional hypotheses on physical oracles.

## 6. Q5: extract the entire first-mode block from `BernoulliLaplaceGeneral`

This is the **clearest build-granularity experiment**, not a command to reprove the 385-line `blConditionalMean` by brute force.

- `BernoulliLaplaceGeneral.lean:1263-2340` is the first-mode/eigenfunction development, beginning with `section firstMode` and `blFirstModeFactor` (line 1279). It contains `innerYToB_w`, `chooseSum_weighted`, `blConditionalMean` (1781-2165, 385 lines), `blFirstModeFunc`, and its nonzero companion.
- The earlier core includes exchange definitions, normalization, row-stochasticity, and stationary law. These are used by the fiber, counting, and Commander modules that have no reason to import the full eigenfunction proof.
- The main external consumer of the first-mode declarations is `BernoulliLaplaceCommanderBridge.lean:129-216`. The source-level reverse import count of the whole current general module is 12.

**Concrete module split:** create `Shufflemath/BernoulliLaplaceFirstMode.lean`, importing `Shufflemath.BernoulliLaplaceGeneral`. Move the complete `section firstMode` from about line 1270 to the end into it. Keep `namespace Shufflemath; namespace BernoulliLaplaceGeneral` and the *same declaration names and statements* in the new file. Adjust the existing section/namespace closures without altering the theorem types. Change `BernoulliLaplaceCommanderBridge` to import the new module in addition to its other necessary inputs. Add the new module to the relevant explicitly built target list.

Do **not** move `innerYToB` (lines 384-629) or `innerYToB_b` (630-874) on the first pass: `blRowStochastic` in the general core depends on the unweighted earlier argument. Moving those too would change the dependency architecture and risk introducing a cycle. The first pass should be a mechanical move, **not** a rewrite of any 385-line proof.

**Why this may help:** editing `blConditionalMean` no longer changes the central BL macro-model source file; modules that only need the core would not import the first-mode module. It can also reduce the cost of recompiling the core itself. **Why it may not help:** Lean elaboration, object generation, and transitive imports can dominate; the moved proof may simply cost the same amount elsewhere. This is why timing is mandatory before claiming a speedup.

**Acceptance:** fully-qualified names and theorem statements unchanged, no cycle, macro-kernel consumers no longer import the eigenfunction module, explicit targeted builds green, and cold/warm numbers recorded for at least two edit scenarios: a first-mode proof edit and a core transition-kernel edit. Abandon or revert if measured results worsen meaningfully.

## 7. Q6/Q7: defer broad TV and Dobrushin surgery until there is measured evidence

`TotalVariation.lean` is 1,085 lines and is upstream of 26 modules. The first half develops basic TV and matrix-row compatibility (`MatrixTV.*` around lines 439-485); later sections contain product-TV bounds (`distProduct_tv_subadditive`, `distProductFinsupp_tv_subadditive`), kernel Lipschitz results, and mixture bounds (`mixtureTV_le` near line 963). These are different layers of abstraction. A *future* `TotalVariationProducts` or `TotalVariationAdvanced` companion module could isolate product/mixture arguments if downstream proofs do not require all of them.

But **do not split at an arbitrary line number**. `Dobrushin` imports `TotalVariation` and uses its TV core, and other results may cross the proposed boundary. Before moving anything, ask `leanq` for elaborated declaration dependencies after building, or identify every use of candidate declarations by source search and compiler probes. Move one independent theorem cluster at a time, preserving names and noncyclic imports. Verify the rebuild fan-out actually falls.

`MatrixTV.dobrushinCoeff` (`TotalVariation.lean:459`) and `Dobrushin.dobrushinCoeff` (`Dobrushin.lean:72`) are *not* accidental duplicate names: one accepts matrices, the other kernels, and the existing bridge `dobrushinCoeff_matrix_link` proves their equality in the applicable case. Retain both user-facing interfaces if clients need them. Look for duplicated proofs that can be derived through the bridge; do not erase one representation merely to reduce declaration count.

## 8. Q8/Q9: orbit construction and import hygiene

**Orbit proof.** `CommanderMembershipOrbits.lean` builds a four-part card-bijection and proves its injectivity/surjectivity by detailed case splitting (`finsetType_perm`, `piecesCover`, `orbitMap_injective`, etc.). This is a plausible candidate for a reusable equivalence between matched finite partitions, but it has only one downstream importer, `CommanderMembershipExchange`. Rewriting the 903-line module during an unfinished F3 capstone increases proof risk for little demonstrated rebuild benefit. **Defer.** After F3 closes, prototype a generic partition-bijection lemma in an isolated module, prove it, and replace the concrete orbit proof *without changing* its external theorem; delete the old cases only when the replacement compiles.

**Imports.** `FinsetFiberCount.lean:3` uses the umbrella `import Mathlib` even though the file also explicitly declares many narrower `public import Mathlib.*` modules and `public meta import Lean.Meta.DiscrTree`. Try deleting the umbrella import in a controlled branch after confirming the generic fiber proofs compile, then add only specific imports required by resulting error messages. This module is presently a leaf, but it will become an upstream dependency if Q1 is integrated. Avoid blanket `public import Mathlib` merely to quiet missing-lemma errors.

`BernoulliLaplace.lean` repeats `public import Shufflemath.TotalVariation`; `CommanderFiberWitness.lean` repeats `CommanderPermutation`; and `ExchangeOverlap.lean` repeats `BernoulliLaplaceGeneral` and `BernoulliLaplaceFiber` as **ordinary public imports**, while also using `public meta import` for the `native_decide` path. Eliminate only identical redundant import declarations. **Do not** delete a needed `public meta import` just because a `public import` of the same module exists: they serve different roles under the repository's Lean 4.34 module conventions.

`FinsetCombinatorics.lean` is also currently unimported by other project modules. It may become useful during F3, but do not mistake an unconsumed helper module for completed integration. Decide later whether to consume its uniqueness lemmas or preserve it as an experimental leaf. Deleting it does not materially change the common import graph today.

## 9. A proof-writing protocol designed for Qwen

The following rules would improve quality more than more general advice to "simplify the proof".

1. **Prove one mathematical invariant at a time.** For each new result write, in three lines: the intended theorem type, the already-proved theorem it should derive from, and the single missing bridge. If the new statement can be obtained by specialization or `Equiv` transport, do not build a second counting induction.
2. **Search before proving.** Search project declarations by the *mathematical expression* as well as by name: subset fiber size, pushforward, schedule intertwining, kernel composition, stationary measure. Then inspect Mathlib for a generic equivalence, cardinality theorem, or transport lemma. The best new lemma may be a two-line adapter.
3. **Control unfolding.** Prefer `simp only [known_lemma_1, known_lemma_2]`, `change`, `show`, `rw`, and `calc` to an unbounded `simp [membership, leftCards, Deck, ...]`. The F2 handoff documents a real failure mode: the default simplifier unfolded `Equiv.Perm (Fin 99)` constructions and exhausted elaborator resources. Package a point-mass identity before using `StdSimplex.weights_inj` / `Finsupp.ext` to lift to kernels.
4. **Keep theorem statements exact.** Before moving or replacing a proof, write down all explicit hypotheses and the full conclusion; preserve them in compatibility wrappers. Beware `Nat` saturating subtraction: a `Nat.choose` expression may silently represent a different count when an `Int` bin size is negative. Handle support and boundary cases explicitly.
5. **Eliminate proof chains, not merely duplicate names.** If lemma `A` is superseded by `B`, first prove `A` from `B`; compile; inspect callers; then delete the old internal chain. Lean checks declarations in source order, so declaration moves may be necessary.
6. **Separate mathematical reuse from physical-model equality.** Oracle resampling, membership-level exchange, fixed-position physical swaps, and finite local GSR have different semantics. A shorter proof obtained by silently identifying them is not valid.
7. **Use a small compile-feedback loop.** Change one theorem or one module boundary; run `lake build Shufflemath.Target`; preserve the first meaningful Lean error; do not make five speculative tactic rewrites before rebuilding. On a hard wall, write a minimal reproducible goal in an isolated scratch module and return to the canonical theorem only after the tactic or representation is understood.
8. **Do not suppress the environment.** Do not globally increase `maxHeartbeats`, install project-wide aggressive `simp` lemmas, add axioms, or replace a symbolic proof with 99! evaluation. A local resource limit change is diagnostic evidence, not proof quality.
9. **Preserve theorem names and attribution.** Avoid renaming public facts just to shorten code. In this project `module` visibility and `@[expose] public section` are part of the API, so compilation must check both the theorem producer and an importing consumer.
10. **Work in one shared directory, no worktrees.** Stage only intended files. Keep commits small, keep active status in `docs/lean_plan.md` / `docs/agent_handoff.md`, and do not rewrite this historical review after committing it.

## 10. Measurements and acceptance gates: prove a speedup rather than assume one

For a single clean baseline and each candidate refactor, record **what changed** and **what actually recompiled**. Use the pinned toolchain and a fixed host. Warm the Mathlib cache *before* the timed region, rather than timing a download.

Suggested local commands:

```bash
cd ~/code/shufflemath
lake exe cache get

# For baseline or candidate edits, use the same target and warmed cache.
/usr/bin/time -f '%e sec elapsed; %M KB max RSS' \
  lake build Shufflemath.ExchangeOverlap
/usr/bin/time -f '%e sec elapsed; %M KB max RSS' \
  lake build Shufflemath.BernoulliLaplaceGeneral
/usr/bin/time -f '%e sec elapsed; %M KB max RSS' \
  lake build Shufflemath.CommanderMembershipExchange

# Also exercise a real downstream importer after a changed upstream source.
/usr/bin/time -f '%e sec elapsed; %M KB max RSS' \
  lake build Shufflemath.CommanderFiberCount
```

**Interpretation:** sequential no-op runs are cache checks, not compilation measurements. For a meaningful edit-cost comparison, rebuild after the same representative source change (or in a dedicated baseline/candidate comparison), record actual rebuilt modules from verbose Lake output, and distinguish first-run/cold dependency work from warm incremental work. Never compare one run that downloads Mathlib with another that uses a warm cache. Do not run `lake clean` indiscriminately or delete shared caches. The provided `lake-build-report` utility can supplement timing with build diagnostics; use its installed help for the exact flags, not guessed commands.

For each refactor, add a terse ledger entry to the active handoff (not to this immutable review):

| Field | Required evidence |
|---|---|
| Module or theorem moved | Exact old/new file, old/new declaration name |
| Semantic preservation | Named theorem(s) with identical hypotheses and conclusion, importing consumer builds |
| Proof duplication removed | Which independent proof chains became wrappers / were deleted |
| Before vs. after | Timed target and hardware, cache state, rebuilt modules, elapsed time, max RSS |
| Scope of build check | `lake build` targets including optional leaf modules; Python suite as secondary check |
| Next risk | Open boundary case, importing module, or theorem still needing migration |

**Review acceptance:** a refactor is successful if it preserves statements, makes the mathematical dependency clearer, and either removes actual duplicate work or measurably improves build behavior without increasing downstream coupling. "Fewer lines" or "more clever tactics" is not sufficient.

## 11. Exact recommended execution order (small commits)

**Commit A - one safe theorem replacement.** In `ExchangeOverlap`, relocate the `(25,25)` numerical theorem after its symbolic counterpart and replace the `native_decide` with `.symm`. Compile only `Shufflemath.ExchangeOverlap`. Do not touch the `(25,1)` case. Record elapsed time if feasible.

**Commit B - integrate generic fiber counting.** Compile the generic module, import it into `ExchangeOverlap`, replace `s1Fiber_choose` and then the supporting specialized cardinality lemmas with wrappers, run both targeted builds, and delete only verified redundant proofs. Tackle the `import Mathlib` diet in a separate micro-commit if it introduces new errors.

**Commit C - unify restricted and non-saturating CL.** Make `generalCL` a short corollary of `generalCL_ns` after resolving source order. Remove old restricted-only lemmas once unused. Recheck all Commander and small-deck boundary certificates. The scope of `generalCL_ns` is not all valid Commander `(x,y)` pairs; add a separate boundary argument before making that claim.

**Commit D - share schedule algebra.** Extract the generic `List.Forall₂` schedule theorem; keep Oracle and Physical wrappers, each built with its previous clients. Confirm no import cycle and compare dependency graph size.

**Commit E - perform one measured split.** Split `BernoulliLaplaceFirstMode` from the BL core with no proof edits. Compile BL general, first mode, Commander bridge, fiber count, and the affected aggregate target. Compare edit-to-build time and recompile fan-out; keep only if useful.

**After the F3 capstone closes:** consider extracting advanced TV lemmas and refactoring the Commander orbit construction. Do not make these prerequisites for F3-F5. Complete the roadmap's missing mathematical results using the improved infrastructure, rather than spending all available time on housekeeping.

## 12. What *not* to claim from this review

- The largest Lean file is not necessarily the slowest to elaborate. No per-declaration profiler data was available.
- A generic proof is not automatically faster: abstractions can increase typeclass inference, rewrite search, or import costs.
- The matrix/kernel Dobrushin definitions and the two BL state-space interfaces are useful distinct representations until the bridges are shown redundant.
- The BL `generalCL_ns` proof does not automatically cover low-`y` Commander boundary cases.
- Removing an unimported leaf proof will not change hot-path recompiles of other modules.
- This historical document is **not** a claim that Qwen's active F3-F5 tasks are complete, or that the suggested Lean snippets have been compiled.

**Bottom line:** keep a single generic fiber-counting proof, a single general overlap-identity chain, and a single generic schedule-intertwining induction; move the first-mode development out of the hot BL core *after measuring*; preserve explicit semantics and public theorem signatures. The goal is fewer independent proofs to maintain and smaller edit-to-build impact, not a cosmetic reduction in file count.
