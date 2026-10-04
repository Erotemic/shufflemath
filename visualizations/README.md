# shufflemath visualizations

This directory is a long-form Manim / `manim-slides` **study course** for the
mathematics behind `shufflemath`.  It is deliberately not optimized for a
20-minute conference talk.  The primary goal is to make the probability,
combinatorics, Markov-chain theory, and formalization interfaces understandable
well enough that we can later state the Lean theorems without cargo-culting the
literature.

The presentation architecture still follows the Davis--Kahan visualization
project:

- semantic colors are stable across every chapter;
- motion is used when the process itself is the explanation;
- animation-first scenes may opt out of the static handout;
- exact finite numbers are recomputed by checked Python models rather than
  entered as arbitrary plot coordinates;
- parts render independently and can be studied one at a time;
- live HTML, PDF/PPTX exports, and static-summary handouts are all supported.

## Pedagogical contract

The study deck follows stricter rules than an ordinary slide deck.

1. **Define before use.** New symbols and technical terms get a definition or a
   reminder before they carry an argument.
2. **Concrete before abstract.** Important models begin with a small finite
   example that can be followed by hand.
3. **Derive before quote.** Formulas such as the GSR permutation probability,
   the Bernoulli--Laplace transition law, the first eigenvalue, and the
   perturbation telescope are derived from the random experiment.
4. **Repeat definitions after long gaps.** A reader should not need to remember
   what `d_TV`, `lambda`, `Delta`, or `delta` meant 50 scenes earlier.
5. **Separate theorem from intuition.** Schematic teaching models and heuristics
   are labeled as such; published results are not silently strengthened.
6. **End chapters with checkpoints.** Each major chapter has a glossary and a
   statement of what the learner should now be able to derive unaided.
7. **Connect mathematics to Lean.** The final chapter names the symbolic theorem
   interfaces we intend to formalize and distinguishes them from external
   search/computation.

## Decks

The current study course has **155 scenes** across six parts.

### Part 0 — mathematical foundations (18 scenes)

Finite state spaces, distributions, permutation conventions, random variables,
projection versus exact lumping, Markov kernels, row-vector composition,
stationarity, detailed balance, total variation, event witnesses, contraction,
eigenfunctions, mixing time, cutoff, and a foundations glossary.

### Part 1 — classical ideal riffles (39 scenes)

The physical GSR riffle, inverse stable-sort labels, descents and rising
sequences, stars-and-bars, Eulerian numbers and their recurrence, exact
Bayer--Diaconis permutation probabilities, exact TV aggregation, likelihood
ratios, the optimal rising-sequence witness, the 52-card seven-riffle table,
and the `3/2 log_2(n)` cutoff scale.

The physical mechanics are genuinely animated: the title scene splits a deck
into two opposed packets, brings the inner corners together, releases an
interleaving, forms an exaggerated bridge, and collapses back to a squared
packet.  Additional labs animate inverse stable sorting, the discovery of
rising sequences, and composition of repeated inverse riffles into multi-bit
addresses.

### Part 2 — large decks and Bernoulli--Laplace (35 scenes)

The Nestoridi--White perfect-local oracle, the membership projection,
hypergeometric sampling, the stationary law, the exact transition kernel,
row-stochasticity, reversibility, a complete 8-card worked chain, conditional
expectation, the first centered eigenfunction, the Commander 50/49
specialization, the projection/full-deck caveat, coupling, path coupling,
self-adjoint spectral theory, subset symmetry, Gelfand-pair intuition,
dual-Hahn polynomials, second-moment lower bounds, unequal urns, and `S_k`
block dynamics.

### Part 3 — realistic local riffles (23 scenes)

Biased cuts, inverse biased labels, general `p`-shuffles, the tensor/product
composition law, collision probability, strong stationary times, Fulman's
finite collision bound, TV versus separation versus relative `L^infinity`,
quasisymmetric functions, a worked example showing why biased shuffles depend
on **descent positions** rather than only the number of descents, extremal
identity/reversal permutations, clumpy/dealer correlation, a pedagogical
Markov source, run lengths, nonexchangeability, Jonasson--Morris, general cut
laws, and the finite interface needed by the protocol layer.

### Part 4 — compositional error and optimal protocols (20 scenes)

Actual versus oracle kernels, worst-row kernel error, its convexity proof,
ordinary TV contraction, the hybrid/telescoping replacement theorem, Dobrushin
coefficients, quantitative contraction, an **exact weighted telescope and its
proof**, total error budgeting, physical costs, constrained optimization,
Pareto dominance, external search versus Lean certificates, robust parameter
sets, and the intended end-to-end operational theorem.

### Part 5 — formalization roadmap (20 scenes)

The dependency graph, the math-to-Lean dictionary, symbolic Bernoulli--Laplace
and GSR targets, composition targets, realism targets, the boundary between
proof and computation, what *not* to formalize first, a study checklist, and a
master glossary.

## Focused decks

Besides the six parts:

- `riffle-hero` — one scene, solely for iterating on the physical title riffle;
- `shufflemath-short` — the complete classical seven-riffle derivation;
- `shufflemath-study` — all 155 study scenes in pedagogical order;
- `shufflemath-glossary` — six chapter glossary/checkpoint scenes;
- `shufflemath-advanced-math` — 18 advanced proof-tool scenes (coupling,
  spectral/symmetry machinery, strong stationary times, quasisymmetric
  functions, and Dobrushin refinement);
- `shufflemath-full` — compatibility alias for the complete six-part course.

## Semantic colors

| color role | meaning |
|---|---|
| blue | finite local shuffle / mash |
| amber | cross-working-set exchange |
| green | uniform target / certified success |
| pink | residual nonuniformity / TV error |
| violet | physical cost / optimization |
| cyan | perfect-local oracle used in prior idealized models |
| vermilion | empirical / human-behavior parameter |

Set `SHUFFLEVIZ_THEME=light` (or `make ... THEME=light`) for a printable light
variant. Theme outputs get a `-light` suffix and do not overwrite the dark deck.

## Setup

```bash
cd visualizations
uv sync --extra slides --extra test
```

Manim also needs the usual Cairo/Pango/FFmpeg/LaTeX host packages.

## Recommended study/build workflow

First validate the source and exact finite models:

```bash
make test
make lint
```

Then render the small reference/foundations decks before committing to the full
155-scene build:

```bash
make glossary QUALITY=l PDF=0 JOBS=1
make part0 QUALITY=l PDF=0 JOBS=2
make advanced QUALITY=l PDF=0 JOBS=2
```

Study individual mathematical chapters:

```bash
make short QUALITY=l PDF=0 JOBS=2   # classical GSR / seven-riffle chapter
make part2 QUALITY=l PDF=0 JOBS=2   # Bernoulli--Laplace deep dive
make part3 QUALITY=l PDF=0 JOBS=2   # biased / correlated riffles
make part4 QUALITY=l PDF=0 JOBS=2   # perturbation + optimization mathematics
```

Build the complete course:

```bash
make study QUALITY=l PDF=0 JOBS=4
```

Then use normal/high quality once the draft is visually clean:

```bash
make study JOBS=4
make study THEME=light JOBS=4
```

Other useful targets:

```bash
make hero QUALITY=l PDF=0 JOBS=1
make mechanics QUALITY=l JOBS=1
make handout
make standalone
make final
```

Present a built deck:

```bash
make present-study
make present-part2
make present-advanced
```

## Static handouts

Live/HTML presentation is the primary medium for process-heavy scenes. Scenes
with `handout = False` are intentionally animation-first and are omitted from
`*.handout.pdf`; adjacent theorem/summary scenes carry the printable result.
The deep study content itself remains handout-friendly wherever the mathematics
can be represented clearly in a final frame.

## Numerical status

`shuffleviz/model.py` independently recomputes the finite numbers used by the
visuals. In addition to the original GSR and Commander calculations it now
contains a general exact two-urn Bernoulli--Laplace transition model,
hypergeometric stationary law, conditional mean, and centered first-mode
factor. Tests pin the 8-card toy example, detailed balance, Commander support,
and the `k=25` first eigenvalue.

These computations are pedagogical/evidence infrastructure. They do not replace
the symbolic Lean proofs identified in the roadmap.
