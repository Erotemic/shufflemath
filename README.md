# shufflemath

`shufflemath` studies how to randomize cards when the physical shuffle operation is constrained.

The motivating case is a 99-card Magic: The Gathering Commander deck that is too large for a player to comfortably mash/riffle as one packet. A player may be able to shuffle 49--50 cards quickly, while recombining and repartitioning the deck is slower. Real human shuffles are also imperfect: cuts may be biased, cards may fall in clumps, and an end packet may fail to participate.

The central optimization problem is:

> Given a model of the available physical operations, their costs, and a target distance from the uniform distribution, what finite sequence of operations minimizes expected physical time?

The repository has three parallel tracks:

1. **Literature and problem formulation** -- establish precisely which parts are known and which combined problem appears open.
2. **Exact finite computation** -- use rational arithmetic to generate candidate protocols and exact targets for formalization.
3. **Lean formalization** -- prove finite probability, Markov-chain, and shuffle-protocol statements.

## Formal architecture

The finite Lean layer now uses modern mathlib abstractions rather than maintaining a parallel probability API:

- `Dist alpha := Convexity.StdSimplex Rat alpha` is the semantic exact finite distribution type.
- `FiniteKernel alpha beta := alpha -> Dist beta` is the semantic finite Markov-kernel type.
- rational matrices are the computational view used for exact finite certificates;
- `FiniteKernel.toMatrix` and `FiniteKernel.ofRowStochastic` form the bridge;
- total variation and Dobrushin coefficients are exact rational quantities;
- the Commander Bernoulli--Laplace kernel is defined once as an exact matrix and lifted to a semantic kernel after row-stochasticity is proved.

This keeps probability normalization in the type while retaining computable rational certificates.

## Current formal results

The first Commander model tracks

```
X = number of originally-left cards currently in the 50-card left pile.
```

For a 99-card deck split 50/49, `CommanderState = Fin 50` represents the feasible values 1 through 50.

The Lean sources now contain:

- the exact hypergeometric Bernoulli--Laplace transition formula;
- the exact 25-card exchange transition matrix;
- a finite certificate that every matrix row is a probability distribution;
- the exact hypergeometric stationary distribution and a finite stationarity certificate;
- the exact first-mode factor and the finite theorem that exchange size 25 minimizes its absolute value over sizes 1..49;
- exact rational TV-distance certificates after two and three 25-card exchanges.

The Python reference implementation remains independent and is used to cross-check the exact numbers and generate conjectures.

## Repository map

- `docs/literature.md` -- literature review and novelty boundary.
- `docs/problem.md` -- mathematical optimization problem.
- `docs/lean_plan.md` -- theorem ladder for Lean.
- `docs/formalization_dependency_audit.md` -- mathlib / MCMC / TauCeti abstraction audit.
- `docs/popular_communication.md` -- plan for a Magic-player-facing explanation/tool.
- `docs/measurement.md` -- measuring a real person's shuffle.
- `references.bib` -- seed bibliography.
- `experiments/bernoulli_laplace.py` -- exact-rational reference computation.
- `Shufflemath/Finite.lean` -- `StdSimplex` distributions and semantic finite kernels.
- `Shufflemath/Matrix.lean` -- stochastic-matrix bridge.
- `Shufflemath/TotalVariation.lean` -- exact rational TV and Dobrushin quantities.
- `Shufflemath/Cost.lean` -- costed operations and protocol costs.
- `Shufflemath/BernoulliLaplace.lean` -- exact Bernoulli--Laplace model and Commander certificates.

## Build

The project is pinned to Lean 4 / mathlib `v4.34.0`.

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
- Keep one authority for each mathematical object: semantic distributions/kernels are `StdSimplex` based; matrices are a proved computational view, not a second probability definition.

## Near-term theorem ladder

1. prove the general Bernoulli--Laplace row-normalization identity symbolically, replacing the Commander-only finite certificate;
2. prove reversibility and the first eigenfunction/eigenvalue theorem;
3. formalize ideal GSR inverse riffles and the `a`-shuffle composition law;
4. prove TV contraction / perturbation bounds for heterogeneous finite kernels;
5. introduce costed schedule search and certificates;
6. add biased/clumpy local shuffle models.
