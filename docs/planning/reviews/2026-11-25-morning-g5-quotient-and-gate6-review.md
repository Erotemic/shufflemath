# 2026-11-25 morning — G5 quotient mathematics and Gate 6 scope review

**Reviewed base:** `91284abc9ec2` (archive captured 2026-11-25 08:55 EST).
**Purpose:** feedback for the autonomous Qwen3.8:27B agent; historical record,
not a replacement for the roadmap. The companion implementation guide is
`docs/planning/proof-strategies/2026-11-25-morning-g5-quotient-and-counting-handoff.md`.

## 1. What worked since midnight

The last operator overlay was actually delivered this time. `25fc7ab` adds it;
`10d9bef` integrates the two candidate files into `FiniteDeck/Partition.lean`
and `Gate6K1Bridges.lean`. The commit reports green targeted and aggregator
builds. The following are substantive accomplishments, not merely plans:

| Commit | Evidence / mathematical content |
| --- | --- |
| `10d9bef` | `partitionSigmaEquiv`, `sigmaBlockEquiv`, `glueBlocks`, `glueBlocks_apply_member`; generic `uniform_same_image`, `range_iff_mem_of_card_eq`, `reset_absorption`, `equal_after_first_run`, `action_comp_eq_conv`, `action_run_tv_noise`, `perm_inverse_uniform`, `perm_inverse_tv`, `ideal_batch5b` |
| `06e52d3`, `fe4a9a5` | `Histograms.lump`, `lump_pileTotal`, `lump_categoryTotal` (namespace `Shufflemath.FiniteDeck`) |
| `e8ab9e1`, `37e5221` | `multiPile_equivFiber`, `multiPile_card`: arbitrary finite partition fiber equivalence and factorial count |
| `f3446cd`, `c0faf73` | Six-card/three-pile example; `glueBlocks_imagePile`, `glueBlocks_preservesEveryPile` |
| `1aa68fd`, `7790c57`, `6210f39` | `exchangePair_injOn`, `pairwiseExchangeCount`, `exchangePair_involution`, `exchangeTargets_symmetric` |
| `7feaa2f`, `9641cf8`, `051b839` | `histAllocSum_choose`, `allocCard_choose`, `allocPi_card` |
| `de37159` | `twoPileExchangeTotal`, `twoPileTransitionStochastic` |

The multi-pile count theorem really does have arbitrary `N` and arbitrary
number of piles. This is an important success: the partition construction
replaced an ad hoc case-by-case generalization of the two-pile proof. The
remaining histogram counting and transition law are separate obligations.

## 2. Correct the target before doing further algebra

`MultiPileExchange.twoPileTransitionStochastic` (in the `FiniteDeck`
namespace) proves a rational scalar identity, the product of two list-based
Vandermonde sums divided by the common denominator. It does NOT yet define a
`FiniteKernel` on allocations or histograms, prove the formula for any
individual target histogram, or establish that the histogram law agrees with
an actual exchange of named cards. `allocPi_card` counts a family of synthetic
category selections; its link to subsets of an actual pile is open.

`exchangeTargets_symmetric` is a good microscopic combinatorial result. Use
it to prove symmetry of the allocation kernel after constructing that kernel
and showing its denominator is fixed. Do NOT demand symmetry of the quotient.
The last section of `2026-12-31-g5-multipile-state-and-walls.md` correctly
notes that the quotient measure is not uniform, but its proposed column-sum /
symmetry direction is ambiguous and risks pursuing a false property.

Counterexample: N=4, two piles of size 2, two colors with 2 cards each, exchange
1. Let x denote red cards in pile 0. Then P(0,1)=1, P(1,0)=1/4, and
pi=(1,4,1)/6. P is not symmetric, and its column sums are (1/4,5/2,1/4), not
all one. Weighted detailed balance holds: pi(0)*P(0,1)=pi(1)*P(1,0)=1/6.
This is not a Lean performance problem; the wrong claim is false.

Instead, construct the microscopic kernel by a uniform choice pushforward,
prove color-relabeling equivariance and histogram-fiber transitivity, and
apply one generic theorem about strongly lumpable reversible kernels. This
will give actual stochasticity, weighted detailed balance, and the
uniform-fiber intertwining. The exact hypergeometric formula can follow as
a counting characterization, rather than as a prerequisite for stationarity.

## 3. The reusable theorem hiding in the new code

The newly integrated `glueBlocks` accepts an arbitrary index type. Use
`Fin p × Fin c` as that index: each cell is `C i` filtered by color `j`.
Two allocations with equal histograms have equal-size corresponding cells.
Glue local bijections between cells to get a **single color-preserving
permutation** carrying one allocation to the other. This gives every
histogram-fiber transitivity theorem at once. It also gives a stabilizer
count for the histogram fiber by reusing `multiPile_card` twice (category
blocks, then cell blocks). No new bespoke orbit proof is necessary.

This construction should precede further algebra on the product of binomial
coefficients. It is independent of exchange size and works for empty cells.

## 4. Gate 6: do not confuse compiled building blocks with the final theorem

`FiniteDeck/Gate6ThreeRound.lean:g6_threeRound_headline` remains a useful,
compiled restricted-start theorem. `g6ThreeRoundStart` is a distribution
uniform in the segregated macro fiber. `Gate6K1Bridges.lean:ideal_batch5b`
now proves the local-reset identity, so do not reopen batch 5b's support proof.
The new generic helpers are integrated, but no new theorem in the snapshot
closes all deterministic starts. `rhoRoundFinite` in `GSRDeckRound.lean`
still embeds `gsrPermutationLaw` directly. `GSRPermutationLaw.lean` proves
that the sorted deck uses the inverse of that rank permutation. The old
bound is still valid for the old law; it is not automatically a certificate
for the intended stable-sort/inverse-GSR protocol. A theorem establishing
23 independent binary steps equal the 2^23-label pullback law is also needed.

The companion guide gives a narrower remaining route: (1) row independence
for rawExchangeMembership by the equal-cardinality reach-set lemma; (2) equal
segregated fibers, using a generic same-fiber-law theorem rather than a new
mass calculation; (3) reset absorption; (4) all-start ideal mixing via the
already-compiled action/relabel theorem; (5) finite perturbation from each
point mass, using the corrected inverse-GSR law. The finite proof need not
be transported from the old fiber-uniform finite headline.

## 5. Proof and build quality

The earlier partition proof strategy has clearly paid off. Qwen's changes
also document a real resolution of the `∀`/subtype Fintype issue: `open
Classical`, named finite instances, and separate `Fintype.card_congr` and
`Fintype.card_pi` rewrites. Do not treat that wall as a reason to replace
all dependent types with list calculations. Use the generic algebra first;
only require finite carriers at the theorem boundary where a cardinality or
finite sum is needed. The supplied candidate modules deliberately separate
the Fintype-free and Fintype-dependent results.

The verification script now includes `Gate6ThreeRound`, `Partition`,
`Histograms`, and `MultiPileExchange`. `MultiPileFiber` and `PileFiber` are
reachable via dependencies of the aggregator, but are not explicit targets
of the targeted script; add the final G5 capstone (and its actual dependency
chain) to the standard verification path. `ThreePileTwoColor` is not directly
imported by the aggregator at the reviewed base; compile/wire it as a small
worked example if the roadmap requires that regression. Check that all
production imports are explicit, not dependent on accidentally imported
private probes. Do not turn this into a general cleanup exercise mid-proof.

The active goal file `.pi-glla/goals/20261120183004-9jlt8s.md` still refers to
November 20. The user must replace the actual goal; a new checked-in document
alone does not update loop state. Several agent-authored notes have December
2026 dates although the captured commits are November 25; select guidance by
commit/dependency status, not the apparent latest date in a filename.

## 6. Next acceptance gates (short)

1. Compile the two generic quotient/cell-relabel seeds; migrate only checked
   declarations. `Gate6AssemblySeeds` is an independent closure thread.
2. Implement an actual allocation kernel and histogram observation with a
   finite valid carrier. Prove exchange preserves partition and capacities,
   then row equivariance and strong lumpability. Test k=0, zero-size inactive
   piles, and 3 piles/2 colors, without assuming all histograms equally likely.
3. Prove quotient stationarity and weighted balance by the generic theorem.
   Prove the histogram fiber count using the category-permutation stabilizer,
   and connect the product-of-choose formula to the actual kernel. Prove
   uniform-fiber intertwining, not merely a scalar normalization.
4. Close the stronger Gate 6 scope and pullback composition. Independently
   continue G7/G8; use existing validated generic results rather than copying
   the two-pile proof development.

## 7. Evidence and limits

The review is based on the supplied Git snapshot and its recorded build
reports. The reviewer reran all 37 Python tests successfully. Lean/Lake are
not installed in the review environment, so the new Lean seed files are
uncompiled candidates, not green proofs. The guide identifies alternatives
if syntax or exact Mathlib lemma names differ. Existing production files and
previous review documents are unchanged by the overlay.
