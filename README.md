# shufflemath

`shufflemath` studies how to randomize cards when the available physical
shuffle operations are constrained. The motivating case is a 99-card Magic:
The Gathering Commander deck: two piles of 50 and 49 cards are practical to
riffle individually, but recombining and repartitioning them has a cost.
Human cuts and riffles may also be biased or clumpy.

The research objective is to find a finite protocol with a **certified
full-deck total-variation bound** and an **explicit physical cost**, and
ultimately to optimize cost within a stated protocol class. We combine
literature, exact rational computation, and Lean 4 formalization.

## Where work stands (October 21, 2026)

**Start new formalization work at [docs/agent_handoff.md](docs/agent_handoff.md),
then use [docs/lean_plan.md](docs/lean_plan.md) as the active roadmap.**
Those are the only current planning authorities. Older tranche and
October 4-12 autonomous-session notes are historical references.

The earlier Lean development establishes:

- `StdSimplex Rat` finite distributions and `FiniteKernel`, stochastic-matrix
  views, exact rational TV, Dobrushin contraction, and weighted perturbation;
- general hypergeometric Bernoulli--Laplace normalization, stationarity,
  detailed balance, and a proved centered first eigenfunction;
- the exact 99-card 50/49, 25-position-exchange specialization, with
  2- and 3-exchange macrostate TV certificates;
- the semantic array-to-kernel bridge, stable inverse-GSR product-label
  composition, generic recoverable-fiber TV lifting, canonical oracle
  intertwining, and physical-refinement/cost interfaces;
- an actual `Equiv.Perm (Fin 99)` deck type and a correct macrostate count
  projection, whose compilation the user confirmed.

The October 21 follow-on adds explicit witnesses for every 99-card count
fiber, a generic exact uniform-fiber disintegration theorem, and the
membership-level physical refinement reduction. The source also contains
conditional exact oracle/full-uniform TV theorems. **The complete
fiber/disintegration tranche compiles, as confirmed by the user's workflow
when moving to the documentation handoff.** The remaining work is to
prove the stated counting and membership hypotheses, not to revalidate
already-completed source.

**Still open:** proving the exact 99-card fiber-cardinality identity
(`HasCommanderFiberCounts`), constructing named-card membership and
physical-perfect-local exchange kernels with the required intertwining,
and bounding finite-GSR versus perfect-local error. A theorem about the
50-state chain, or even the canonical oracle, is **not** a theorem about
an arbitrary physical human shuffle.

### Mathematical models (keep separate)

| Model | What one step preserves | Status |
|---|---|---|
| 50-state Bernoulli--Laplace chain | Only the original-left count | Exact macrostate results |
| Canonical full-deck oracle | Count transition; globally resamples its permutation fiber | Generic transfer theorems; uniform-target identification awaits fiber counts |
| Physical perfect-local shuffle | Named-card membership after selecting exchange positions, then perfect order randomization *within* each pile | Conditional membership-level theorem; concrete exchange proof open |
| Physical finite-GSR shuffle | Membership after raw exchange; imperfect pile order randomization | Exact small-deck Python model; general Lean discrepancy bound open |

## Build and verification

This repository pins Lean 4.34.0 and mathlib in `lean-toolchain` and
`lake-manifest.json`. For the current development, use the cache before
building the explicit optional/full-deck targets:

```bash
cd ~/code/shufflemath
lake exe cache get
lake build \
  Shufflemath.CommanderFiberWitness \
  Shufflemath.FiberDisintegration \
  Shufflemath.PhysicalExchangeReduction \
  Shufflemath.CommanderFullDeckDisintegration
./dev/verify_next_phase.sh
```

`./dev/verify_next_phase.sh` builds the complete targeted next-phase list
and runs the Python regression suite. For the expensive, separately
scoped 2,401-candidate pair certificate, use:

```bash
./dev/verify_next_phase.sh --pair
```

A plain `lake build` uses `Shufflemath.lean` and does not compile all
optional modules. Do not habitually run `lake update` in a pinned checkout:
the legacy `dev/verify.sh` invokes it, so use the targeted script instead.
Independent exact references and tests:

```bash
python3 -m unittest discover -s tests -v
python3 experiments/commander_pair_search.py
python3 experiments/gsr_inverse.py
python3 experiments/oracle_gsr_budget.py --target 1/100
```

Python experiments support theorem development; they are not substitutes
for Lean proofs.

## Reusable numerical benchmark

The 50-state chain records `X`, the number of originally-left cards
currently in the 50-card left pile. `CommanderState = Fin 50` encodes
`X=1,...,50` as `x.val+1`. From complete segregation, two ideal
25-position exchanges have macrostate TV approximately `0.00248417758708`;
three have approximately `0.0000257596683780`. The exact rational values
are in [docs/findings.md](docs/findings.md). These numbers are not
unconditional full-deck or human-shuffle guarantees.

## Documentation map

- **[docs/agent_handoff.md](docs/agent_handoff.md):** exact restart task,
  first pending proof task, and acceptance rules for a new/less experienced
  agent.
- **[docs/lean_plan.md](docs/lean_plan.md):** sole active theorem roadmap,
  dependencies F1-F5, optional tasks, and exit criteria.
- [docs/commander_fiber_disintegration.md](docs/commander_fiber_disintegration.md):
  technical reference for the fiber/disintegration/membership layer.
- [docs/full_deck_oracle_bridge.md](docs/full_deck_oracle_bridge.md):
  definitions and differences among canonical and physical kernels.
- [docs/formalization_next_phase.md](docs/formalization_next_phase.md):
  historical October 20 GSR/semantic-bridge design record.
- [docs/formalization_dependency_audit.md](docs/formalization_dependency_audit.md),
  [docs/autonomous_lean_build.md](docs/autonomous_lean_build.md), and
  [docs/lean_build_history.md](docs/lean_build_history.md): historical
  research and build-session context, **not active plans**.
- [docs/problem.md](docs/problem.md), [docs/literature.md](docs/literature.md),
  [docs/measurement.md](docs/measurement.md): problem statement, external
  literature, and empirical model-fitting policy.
- `Shufflemath/`: Lean library; `dev/`: verification scripts and optional
  expensive pair theorem; `experiments/` and `tests/`: independent exact
  rational reference implementations and regression tests.
- `visualizations/`: separately built Manim mathematics course, not a
  prerequisite for formalization. See its own README and Makefile.

## Research principles

- Keep a single authority for each mathematical object: `StdSimplex` is
  the semantic distribution; matrices are a proved computational view.
- Separate **Lean theorems**, **conditional Lean theorems**, **exact Python
  checks**, and **hypotheses**. Never silently collapse those categories.
- Preserve named-card membership when modeling a local pile shuffle; never
  substitute a count-fiber reset for a physical operation.
- Model cut bias, clumping, untouched tails, working-set sizes and operation
  costs as distinct parameters. Do not summarize them with a single vague
  "shuffle efficiency" parameter.
- Optimize **cost subject to a randomness criterion**, not raw shuffle
  count. Keep any player-facing recommendation conditional on its model.
