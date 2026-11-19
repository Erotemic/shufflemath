# Qwen reviews — open-recommendations follow-up check-off

**Date:** 2026-11-24
**Status:** audit snapshot of the two 2026-11-15 qwen reviews' recommendations,
re-checked against the current tree (verification contract item 6). This is a
*check-off*, not a rewrite of the historical reviews (which remain immutable).
Legend: **DONE** = completed in the tree; **PARTIAL** = the honest labeling /
partial deliverable is in place but the full item is not; **OPEN** = not
started; **DEFERRED** = the review itself recommended deferral.

## Duplication / build-performance review (Q1–Q9)
`2026-11-15-qwen-proof-quality-duplication-and-build-performance.md`

| ID | Recommendation | Status | Current evidence |
|----|----------------|--------|------------------|
| Q1 | Integrate generic fiber counting: `ExchangeOverlap` → `FinsetFiberCount` (one cardinality-bijection family, specialized as wrappers) | **OPEN** | `Shufflemath/ExchangeOverlap.lean` has no `import … FinsetFiberCount`; both `s1Fiber*` and `sFiber*` chains still present. |
| Q2 | Make `generalCL` a corollary of `generalCL_ns` (reorder so the non-saturating chain comes first; drop the redundant restricted chain) | **OPEN** | `generalCL` (`ExchangeOverlap.lean:1015`) is declared *before* `generalCL_ns` (`:1204`) and is still an independent proof; the reordering has not been done. |
| Q3 | Replace the `(25,25)` center `native_decide` certificate with `generalCL_cmdr_2525.symm` | **DONE** | `overlap_eq_revTransitionNumerator_cmdr_2525` (`ExchangeOverlap.lean:1225`) is now `exact generalCL_cmdr_2525.symm`; the `native_decide` proof is superseded. |
| Q4 | Extract a shared `ScheduleIntertwining` module (one generic `List.Forall₂` induction for Oracle + Physical) | **OPEN** | No `Shufflemath/ScheduleIntertwining.lean`; `OracleRefinement` and `PhysicalRefinement` each still carry their own schedule induction. |
| Q5 | Split `BernoulliLaplaceFirstMode` out of the BL core (measured, no proof edits) | **OPEN** | No `Shufflemath/BernoulliLaplaceFirstMode.lean`; the `section firstMode` block still lives in `BernoulliLaplaceGeneral.lean`. |
| Q6/Q7 | Defer broad `TotalVariation` / Dobrushin surgery until measured | **DEFERRED** | Review explicitly recommends deferral pending measured evidence; no split attempted. |
| Q8 | Defer the `CommanderMembershipOrbits` refactor until after F3 closes, then prototype a generic partition-bijection | **DEFERRED** | F3 is now closed, but the 903-line orbit module is still the concrete four-part construction; no generic replacement. Low priority (one downstream importer). |
| Q9 | Import hygiene: drop the umbrella `import Mathlib` from `FinsetFiberCount`; dedup repeated imports | **OPEN** | `Shufflemath/FinsetFiberCount.lean:3` still has the umbrella `import Mathlib`. |

## Proof-engineering review (R1–R6)
`2026-11-15-qwen-proof-engineering-review.md`

| ID | Finding / action | Status | Current evidence |
|----|------------------|--------|------------------|
| R1 | Record the F3 gap honestly (F3-a ingredients vs F3-b concrete kernel law) and correct optimistic wording | **DONE** | The concrete A3 kernel law `hMembershipExchange_kernel` is proved and the `agent_handoff.md` / `lean_plan.md` status now reflects completion; the misleading "proves A3" docstring wording is resolved. |
| R2 | Distinguish the fixed-pair physical swap (1), the membership-exchange kernel (2), and swap-then-reset (3); label the current model honestly | **PARTIAL** | `CommanderPhysicalExchange.lean`'s module docstring explicitly frames the exchange as the **membership-level** transition and separates the (fixed) pairing from the membership. The literal deck-level fixed-pair swap kernel (1) is **not** constructed; `rawExchange = rawExchangeMembership ∘ localLift` is the (3) construction. |
| R3 | Add the active modules as direct `verify_next_phase.sh` targets | **DONE** | `dev/verify_next_phase.sh` builds `CommanderMembershipExchange`, `CommanderMembershipOrbits`, `CommanderDeckGSR`, `CommanderLocalGSR`, `ExchangeOverlap`, `FinsetCombinatorics` (all six). |
| R4 | Keep the operational header ~one screen; move history to dated notes; fix active pointers | **OPEN** | `docs/agent_handoff.md` is now 3512 lines (grew from ~1500 at review time); the operational banner is at the top but the historical append-only body has accumulated. A periodic reorganization is the remaining work. |
| R5 | Keep the orbit theorem; add safe-splice discipline for automated edits | **DEFERRED** | Orbit refactor deferred (see Q8); the splice-safety guidance is process advice, observed in practice (the destructive splice was a one-off, since guarded). |
| R6 | Keep three optimization claims apart (feasibility / bound-surrogate / actual-TV); state the initial law visibly | **DONE** | The F5-B section of `CommanderCostedCertificate.lean` states claims (i)/(ii)/(iii) separately with proof sources and status; the F5 certificates state the initial law (lifted segregated macro state) in their statements. |

## Ordered gates (Gates 0–9)

| Gate | Deliverable | Status |
|------|-------------|--------|
| 0 | Truthful verification script | **DONE** (R3) |
| 1 | F3 count law (`rawExchangeMembership_count`) | **DONE** |
| 2 | F3 uniform target law (`distUniform_ofInvariantTransitive`, invariance, transitivity) | **DONE** |
| 3 | F3 final assembly (`hMembershipExchange_kernel` + `two_physical_perfect_exchanges_uniform_unconditional`) | **DONE** |
| 4 | Model correctness (fixed-pair deck swap, or honest labeling) | **PARTIAL** (honest membership-level labeling in place; literal deck-level fixed-pair swap kernel not built — R2) |
| 5 | F4 deck-level GSR kernel (`Deck = Equiv.Perm (Fin 99)`) | **OPEN** (F4.2 sub-wall: the `List (Fin n)` point-mass → permutation transport, `gsrProductKernel_eq_distProductFinsupp`) |
| 6 | F4 quantitative full-deck terminal TV bound (concrete protocol, explicit initial/target) | **OPEN** (needs Gate 5; the `errorBudget`/Dobrushin recursion over the 99! univ is the same sub-wall) |
| 7 | F5 feasibility (concrete `CostedKernel` schedule, `TV ≤ ε`, exact cost) | **DONE** (`f5FullDeck_certificate`, `macroCountExchange_costedCertificate`, non-degenerate certificates) |
| 8 | F5 bounded optimization (finite class + precise min claim) | **STATED, not proved** (F5-B section: objective `f5OptCost` named; (ii) bound-surrogate and (iii) actual-TV claims stated with proof sources, not proved) |
| 9 | Documentation closeout (reconcile planning paths; active pointers; every F1–F5 acceptance maps to a named theorem or is visibly open) | **IN PROGRESS** (this audit: G1–G4 manifest → done + named declarations; this check-off; `lean_plan`/`handoff` → final state) |

## Summary

- **Closed by later work:** Q3, R1, R3, R6, Gates 0–3, 7.
- **Genuinely open (mathematical):** Gate 5 / Gate 6 (the F4.2 `List (Fin n) →
  Equiv.Perm (Fin 99)` point-mash transport, blocking the non-degenerate
  full-deck bound) and Gate 8's proofs (F5 optimization, needs competitor
  lower bounds).
- **Open (engineering / housekeeping, no math):** Q1, Q2, Q4, Q5, Q9, R4,
  and the Gate-4 literal deck-level swap kernel (R2).
- **Deliberately deferred by the reviews:** Q6/Q7, Q8, R5.

These open items are the roadmap for future sessions; none is a prerequisite
for the already-closed F1–F3 (A3) capstone or for the F5 feasibility
certificate (Gate 7).
