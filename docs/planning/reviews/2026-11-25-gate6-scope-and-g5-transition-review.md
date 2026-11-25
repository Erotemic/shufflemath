# 2026-11-25 — Gate 6 scope and G5 transition

Basis: archive `shufflemath-source-2026-11-25T002852-5-3dc079aa7d92.tar.gz`, HEAD
`3dc079aa7d926078c42070db9192195914f2f3e7` (clean working tree). The previous evening's
external handoff was not applied. This document supersedes its action list, not any
checked-in historical review. Use the companion **2026-11-25-gate6-and-multipile-executable-handoff.md**.

## What changed since 682228f

- `3dd1ae5` promoted the three-round theorem and K1 algebra into
  `Shufflemath/FiniteDeck/Gate6ThreeRound.lean`, imported by `Shufflemath.lean`
  and `dev/verify_next_phase.sh`. Six obsolete probes were deleted. The handoff
  reports a successful 9010-job build. Do not reimplement that theorem.
- `3dc079a` created `FiniteDeck/Piles.lean` and added a targeted verification
  entry. It defines `realizesAllocation`, `MultiFiber`, `twoPilePos`,
  `twoPileCard`, and four projection lemmas. It does not yet prove partition
  validity, the two-pile fiber equivalence, the product-factorial theorem, or
  histograms. It is not yet imported by `Shufflemath.lean`.
- The batch-5b investigation established more supporting lemmas but hit another
  large Finset/Fintype wall. The exact ideal-orbit law already exists as
  `k1_bridgeA` and `paK_rho99Ideal_eq_localLift`. The batch-5b side result can
  be obtained by evaluating the latter at the identity. Do not resume `_Probe5b`
  subset membership or `Finset.univ` normalization.
- The most recent commit has a GPT-5.6 co-author trailer. The source establishes
  what the agent campaign did, not which model performed every step. The source
  notes also contain later calendar labels (e.g. session 84 dated Dec 30);
  identify results by commit and declaration, not those labels.

## What Gate 6 actually guarantees

`g6_threeRound_headline` is a real theorem about three state-dependent,
correct-order rounds from `g6ThreeRoundStart`. That start is
`apply (pointMass commanderSegregatedState) (fiberLaw project project_surjective)`.
It is uniform within a segregated macro fiber, not a deterministic deck.
The theorem's bound is < 1/1000. The 41-exchange Dobrushin theorem does not
repair the deterministic-start gap, since it likewise assumes a fiber-uniform
start. `g6ThreeRoundFiniteKernel` is misleadingly named: its definition is the
**ideal** exchange/local-reset kernel, whereas `g6ThreeRoundFiniteRound` is the
finite rank-law round. Avoid mixing these up. Comments calling the q3 result
finite are misleading; the theorem statements are the authoritative evidence.

A second independent issue is the GSR direction. `GSRPermutationLaw.lean`
constructs `gsrPermutationLaw` by pushing labels through `rankEquiv` (old
position -> new position). Its proved `idealShuffle_canonical_eq_permLaw`
uses `σ.symm` to read the resulting list. `FiniteDeck.act p d = p.trans d`
reads `d (p i)`; it requires new position -> old position. `GSRDeckRound.rhoRoundFinite`
still embeds rank permutations without inversion. The current theorem is valid
for that law, but it has not yet certified the stated stable-sort inverse-GSR
protocol. Inversion preserves the uniform law and the TV bound. No new
collision analysis is needed. Also make the binary-riffle interpretation an
explicit theorem, not a comment equating 2^23 labels with 23 operations.

## Recommended next work

1. Close the deterministic-start bridge by membership-row independence and
   reset absorption, using small generic statements, followed by relabeling.
   Do not demand equality of all finite-riffle rows within a fiber; it is false.
2. Certify pullback-oriented GSR. Preserve the existing rank-law theorem as
   a valid intermediate result; add a corrected theorem rather than silently
   rename it. Apply the already-proved one-round perturbation with a new law.
3. Finish G5 using a single generic partition/Sigma gluing equivalence. Do not
   generalize the 700-line two-pile orbit construction line by line. Extend the
   same theorem to slot counts and histogram lumping. Empty piles/categories
   must be allowed; only operations that choose positive numbers of cards
   require nonempty sources and capacity hypotheses.
4. G7 and G8 should follow the actionable roadmap. G9 remains optional research.

The active `.pi-glla/goals/20261120183004-9jlt8s.md` still points to the November
20 hints. `AGENTS.md` and the append-only handoff also retain stale resume
instructions. Do not edit live loop state through this overlay. The human
should replace the active goal; the companion has a paste-ready replacement.

Validation here: the 37 existing Python tests passed. Lean/Lake are not
available in this environment; all new Lean seeds are uncompiled candidates.
The reported green build is from repository history, not independent Lean
verification. The overlay adds documents and isolated candidates only.
