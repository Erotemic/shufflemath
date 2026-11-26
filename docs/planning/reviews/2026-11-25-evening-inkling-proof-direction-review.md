# Proof direction review: Inkling2 handoff, 2026-11-25 evening

**Reviewed revision:** `3d25fc8e4114dbbdb0897d6ee95f199e6220f83c` (archive timestamp 2026-11-25 23:36:53 EST). This is a dated historical record, not a new set of independent project goals. Read the companion `../proof-strategies/2026-11-25-evening-allocation-first-histogram-and-mixing-hints.md` for the current execution plan.

## 1. Assessment and scope

The change from Qwen3.8:27B to Inkling2 does not change the mathematical objective. Increased token throughput and access to the preceding work confound any inference about intrinsic model strength. The useful observation is the choice of proofs, not a model ranking. This review is based on the reconstructed source and commit history; it is not a fresh Lean compilation or a performance benchmark. Proposed new Lean files are isolated candidates, not compiled results.

Inkling made useful progress: `HistogramFiber.lean` proves two-color subset-fiber counts, the size-constrained marginal law, a reachable histogram carrier, `sizeNFiberLaw`, `deckFiber_prob_eq_blStationary`, and `validHistPi_mass`. It correctly records that `histogramTransition` is only a scalar formula with no row-sum or stationary-law proof yet. The reachable-carrier approach avoids the need for a universal realizability theorem just to define a fiber kernel. Its integer-first factorial argument in `deckFiber_prob` is a useful proof pattern to preserve.

The strongest architecture inherited from Qwen is `MultiExchange.Allocation` (the namespace is `Shufflemath.FiniteDeck`), an owner-function subtype with exact capacities; `UniformExchange.swapKernel`, a genuine `Dist` obtained by sampling two independent card identities; `swapPiles_involution`, `swapKernel_symmetric`, and `swapKernel_uniformStationary`; and the generic partition/Sigma gluing and product factorial `multiPile_card` results. Those should be the foundation of the next general proof, not a second bespoke histogram construction.

## 2. Findings at the source level

| Source | What is proved/defined | What to do |
|---|---|---|
| `FiniteDeck/MultiExchange.lean` | `Allocation N p n`, `relabel`, `relabel_commute_owner`, `swapPiles` | Use as the sole fixed-capacity microscopic allocation carrier. Add accessor for its pile/category cells. |
| `FiniteDeck/UniformExchange.lean` | `swapKernel hN` selects ordered pairs from `Fin N × Fin N`, including equal cards; normalization automatic, symmetric, uniform stationary | Finish actual input/output equivariance (the existing `swapKernel_equivariant` proves the mass of the already-pushed output; it does not compare with `swapKernel hN (relabel σ A)`). More importantly, derive histogram lumpability by the direct cell-pair factorization in the hints. |
| `FiniteDeck/Histograms.lean` | `lump`, row/column sums, `lumpedNum`, scalar selection weights | Reuse the counting ideas but construct actual laws by pushforward. |
| `FiniteDeck/MultiPileExchange.lean` | `exchangePair`, cardinality/injectivity/reversal, scalar profile counts | `lumpedTransition_rowSum` is a normalization of the recursive selection count, not yet the row sum over destination histograms. `lumpedTransition_swap` merely swaps the two input profile factors; it is not reversibility in the new state. Do not build on that misinterpretation. |
| `FiniteDeck/HistogramFiber.lean` (848 lines) | Two-color specializations; `validHistPi_mass`; `histogramTransition` at the end | Preserve the useful specialized results, but close the two-color chain by an equivalence to `BernoulliLaplaceGeneral.BLState`, not another direct stationarity proof. Use the same generic histogram carrier for further development. |
| `FiniteDeck/ThreePileTwoColor.lean` | Concrete partition/cardinality/row and column total examples | Extend this with an actual histogram exchange row, a stochasticity theorem and a nontrivial stationary/transition calculation; it is not yet the full G5 acceptance test. |
| `FiniteDeck/Partition.lean`, `MultiPileFiber.lean` | Arbitrary-index `partitionSigmaEquiv`, `sigmaBlockEquiv`, `glueBlocks`; fiber equivalence and `multiPile_card` | Use the labeled-slots counting proof in the hints to get histogram counts and realizability together, without a large group quotient implementation. |
| `FiniteDeck/Gate6ThreeRound.lean` | Imported `g6_threeRound_headline` from `g6ThreeRoundStart` | Still restricted to fiber-uniform segregated starts. `g6ThreeRoundFiniteKernel` is actually the IDEAL kernel in the q3 proof; avoid reading the name as semantics. |
| `GSRDeckRound.lean` | `rhoRoundFinite` uses `PermutationLaw.gsrPermutationLaw` directly | Still check rank vs pullback; for physical stable-sort inverse GSR use the inverse law, then prove repeated binary-riffle interpretation. Do not declare G6 fully done from the existing headline. |

The two-pile histogram specialization is not wasted: it is an independent cross-check and an opportunity to connect the two representations. But it should not grow into a second Bernoulli–Laplace library. The goal is a single general result specialized in multiple ways.

### Important semantic distinctions

* **Unrestricted transposition:** `swapKernel` chooses any two cards from the whole deck, with replacement. It can act within a pile (no change). Its histogram kernel is not the fixed-size pairwise k-subset exchange kernel. In two piles it is a mixture of the k=1 exchange and identity, with cross-pile probability `2*m*(N-m)/N^2`. For arbitrary piles it is the corresponding mixture over unordered pile pairs. Prove these bridges rather than silently substituting one chain for another.
* **A histogram of a reachable allocation** is not a free array of Nat values. Use a bounded finite type and range subtype first; prove the margin characterization when counting slots. Row-normalized probability kernels must live on valid states. An invalid selection with saturated subtraction must be killed by its zero binomial factor before arithmetic on the state is used.
* **Microscopic symmetry** is not histogram symmetry. For N=4, two piles of size 2 and two colors of size 2, fixed k=1 has count kernel rows `(0,1,0)`, `(1/4,1/2,1/4)`, `(0,1,0)`, with stationary masses `(1/6,2/3,1/6)`. Weighted detailed balance is the right goal. The unrestricted-transposition kernel instead has an additional holding probability of 1/2 in this example.

## 3. Proof-quality feedback (not a performance claim)

1. Favor representations that encode normalization (`Dist.map`), reachability (`Set.range` subtype) and validity (owner capacities) over separate large scalar proofs. A scalar identity is valuable as an explicit mass formula for a kernel, not a substitute for the kernel.
2. Prove finite-sum interfaces at abstract `X`, `Y` first. Then instantiate them using `exact`/small congruences. Avoid unfolding `Allocation`/large permutation `Fintype` universes. The earlier Gate 6 experience shows that a correct term can still be expensive to elaborate. No reason to raise limits on the same representation repeatedly.
3. Reuse `dev/qwen-hints/2026-11-25-morning/QuotientSeeds.lean`, `CellRelabelSeeds.lean`, `Gate6AssemblySeeds.lean`. They are in this snapshot but not imported into the library. Compile and integrate the ones actually needed; do not clone their generic lemmas. The new hints supply a simpler alternative to cell-orbit transitivity for transposition lumpability and complement (not replace) the old seed files.
4. Use theorem statements to compare scope. `swapKernel_uniformStationary` is pointwise mass equality, so convert it once into `Stationary`. `validHistPi_mass` only sums scalar weights. `histogramTransition` is unnormalized in the Lean sense until a theorem connects it to a normalized law or proves normalization. Keep notes honest.
5. `AGENTS.md` still names G1–G4 and old F2 resume points; `.pi-glla/goals/20261120183004-9jlt8s.md` still points to November 20. Have the operator replace the active goal, and update active handoff/manifest in the next relevant commit. Do not edit historical reviews or live loop state from this overlay.
6. `dev/verify_next_phase.sh` includes `HistogramFiber` and Gate6ThreeRound but does not explicitly target `MultiExchange`, `BlockPartition`, `UniformExchange`, `MultiPileFiber`, or `ThreePileTwoColor`. Several are imported by `Shufflemath.lean`, but add explicit verification targets for new canonical modules so the focused verification path really covers the milestones. Do not add broad axiom/placeholder scans contrary to `AGENTS.md`.

## 4. Recommended milestones

* **I0:** quick BL representation bridge (or skip after two bounded failures and finish the generic kernel first). Show transition and stationary mass formulas on the two actual valid carriers. This closes the work Inkling is already doing.
* **I1:** generic normalized histogram quotient of `swapKernel` for arbitrary piles/categories; explicit cell-pair law; derive stationary pushforward and weighted detailed balance. Do not wait for the closed-form histogram counts.
* **I2:** labeled-slots equivalence, reachable = valid margins, division-free count identity and stationary formula. No orbit-stabilizer dependency. Give arbitrary fixed-pile pairwise k-selection kernels the same distribution-first treatment, including a real equality with the existing k-subset formula and the BL special case.
* **I3:** finish remaining Gate 6 scope and rank/pullback bridges using earlier supplied candidates; extend the local permutation action and comparison inequality to arbitrary finite piles.
* **I4:** G7 draws/deals/discards via variable-capacity selection; G8 quantified mixing (the new adjacent-transposition coupling is a useful first bound), cost certificates, and precise distinction between a sufficient-bound optimizer and true optimality.

The new guide gives exact mathematical proofs, proposed helper signatures, and an execution sequence. The strongest new results are proposed, not claims of already compiled theorems. Core gates are G0–G8; optional G9 spectral research does not prevent core completion.
