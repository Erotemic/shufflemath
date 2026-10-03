# shufflemath

`shufflemath` studies how to randomize cards when the physical shuffle operation is constrained.

The motivating case is a 99-card Magic: The Gathering Commander deck that is too large for a player to comfortably mash/riffle as one packet. A player may be able to shuffle 49--50 cards quickly, while recombining and repartitioning the deck is slower. Real human shuffles are also imperfect: cuts may be biased, cards may fall in clumps, and an end packet may fail to participate.

The central optimization problem is:

> Given a model of the available physical operations, their costs, and a target distance from the uniform distribution, what finite sequence of operations minimizes expected physical time?

This repository has three parallel tracks:

1. **Literature and problem formulation** -- establish precisely which parts are known and which combined problem appears open.
2. **Exact finite computation** -- use rational arithmetic to generate candidate protocols and numerical/conjectural targets for formalization.
3. **Lean formalization** -- build finite probability/Markov-chain machinery and prove certified statements about shuffle protocols.

## Current scope

The first formal model intentionally starts simpler than a full human shuffle:

- finite decks and finite-state probability weights;
- Markov kernels and deterministic rearrangements;
- explicit operation costs;
- the Bernoulli--Laplace first-mode contraction factor for two working piles;
- the 99-card / 50+49 arithmetic showing why an exchange of 25 cards is the natural first candidate.

The next milestone is an exact finite transition kernel for the 50/49 Bernoulli--Laplace projection, followed by a local GSR riffle kernel. Once that baseline is proved, the local kernel can be replaced by biased and clumpy human-shuffle models.

## Repository map

- `docs/literature.md` -- literature review and novelty boundary.
- `docs/problem.md` -- mathematical optimization problem.
- `docs/lean_plan.md` -- theorem ladder for Lean.
- `docs/popular_communication.md` -- plan for a Magic-player-facing explanation/tool.
- `docs/measurement.md` -- how to measure a real person's shuffle without pretending the model is universal.
- `references.bib` -- seed bibliography.
- `experiments/bernoulli_laplace.py` -- exact-rational finite computation for the two-pile exchange chain.
- `Shufflemath/Finite.lean` -- finite weights, kernels, total variation, deterministic kernels.
- `Shufflemath/Cost.lean` -- costed operations and protocol costs.
- `Shufflemath/BernoulliLaplace.lean` -- first-mode factor and Commander-specific arithmetic targets.

## Build

The project is pinned to Lean 4 / mathlib `v4.19.0` as a conservative reproducible starting point.

```bash
lake update
lake build
```

The exact-rational Python experiment has no third-party dependencies:

```bash
python experiments/bernoulli_laplace.py
python -m unittest discover -s tests -v
```

## Research principles

- Separate **proved facts**, **finite exact computations**, **simulation evidence**, and **heuristics**.
- Do not use a single scalar such as "70% shuffle efficiency" unless it is explicitly introduced as an approximation.
- Treat cut bias, clumping, untouched tails, working-set size, and operation time as distinct parameters.
- Optimize **physical cost subject to a randomness criterion**, rather than optimizing a raw shuffle count.
- Keep the human-facing recommendation conditional on the model and measured ergonomics.

## Status

This is an initial research scaffold. The Bernoulli--Laplace exchange computation is executable; the Lean files establish the definitions and first arithmetic facts but the current environment used to create this repository did not contain Lean, so `lake build` still needs to be run in a Lean-enabled environment before treating the formal layer as verified.
