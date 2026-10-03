# Formalization dependency audit

Status: first pass, 2026-10-03.

This audit compares the initial `shufflemath` finite formalization with modern
Mathlib, TauCeti, and `or4nge19/MCMC`.  The goal is to avoid creating a second
probability / finite-Markov-chain API unless the project genuinely needs one.

## Executive decision

For the near-term finite shuffling theory:

1. **Use Mathlib as the only library dependency.**
2. **Upgrade from Lean/Mathlib 4.19.0 to at least 4.34.0 before expanding the
   finite probability API.**  Mathlib 4.34.0 contains both
   `Convexity.StdSimplex` and `Matrix.rowStochastic`.
3. **Do not add TauCeti yet.**  Its useful Markov-chain additions are primarily
   general measure/path-law machinery; they do not currently supply the finite
   TV / Dobrushin / mixing layer that `shufflemath` needs first, and TauCeti
   tracks Mathlib master with a newer Lean toolchain.
4. **Do not add `or4nge19/MCMC` as a dependency yet.**  Treat it as prior Lean
   formalization and a source of proofs/API ideas.  Its finite layer defines a
   second stochastic-matrix predicate instead of modern Mathlib's
   `Matrix.rowStochastic`, and its TV/Dobrushin development is specialized to
   `ℝ`, while `shufflemath` benefits from exact `ℚ` calculations.
5. **Retain project-specific shuffle and cost theory.**  Mathlib does not
   contain riffle/GSR shuffles, Eulerian-number/rising-sequence shuffle theory,
   Bernoulli--Laplace transition kernels, or cost-optimal protocol scheduling.

## Current duplicate authorities

### `Weight` / `Weight.IsProbability`

Current code:

```lean
abbrev Weight (α : Type*) := α → ℚ

def Weight.IsProbability [Fintype α] (μ : Weight α) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ Weight.total μ = 1
```

Modern Mathlib has `Convexity.StdSimplex R X`, a finitely supported collection
of nonnegative weights summing to one.  For `R = ℚ`, this is an exact rational
probability distribution and already provides:

- `StdSimplex.single` (point mass),
- `StdSimplex.map`,
- `StdSimplex.join`,
- normalization and nonnegativity as structure fields,
- finite-sum lemmas when the state type is a `Fintype`.

**Recommendation:** replace `Weight` plus `IsProbability` with an alias such as

```lean
abbrev Dist (α : Type*) := Convexity.StdSimplex ℚ α
```

The central invariant then becomes intrinsic to the type rather than a theorem
parameter carried through every operation.

### `Kernel` / `Kernel.IsMarkov`

Current code:

```lean
abbrev Kernel (α β : Type*) := α → β → ℚ

def Kernel.IsMarkov [Fintype β] (K : Kernel α β) : Prop :=
  ∀ x, Weight.IsProbability (K x)
```

This duplicates the normalization invariant and makes invalid kernels easy to
construct.

**Recommendation:** use a finite exact kernel whose fibres are distributions:

```lean
abbrev FiniteKernel (α β : Type*) := α → Dist β
```

Then define:

```lean
def FiniteKernel.deterministic (f : α → β) : FiniteKernel α β :=
  fun x => .single (f x)

def FiniteKernel.apply (μ : Dist α) (K : FiniteKernel α β) : Dist β :=
  (μ.map K).join

def FiniteKernel.comp (K : FiniteKernel α β) (L : FiniteKernel β γ) :
    FiniteKernel α γ :=
  fun x => ((K x).map L).join
```

The exact spelling should be compiler-checked after the toolchain bump, but this
is the desired abstraction boundary.

### Matrix representation

Modern Mathlib has `Matrix.rowStochastic R n`, with closure under matrix
multiplication and basic row-stochastic API.

A stochastic matrix should therefore be a **derived representation** of a
`FiniteKernel`, not a second primary model.

Add bridges of the form:

```lean
def FiniteKernel.toMatrix [Fintype β] (K : FiniteKernel α β) :
    Matrix α β ℚ := ...
```

and, for square finite kernels, prove that `toMatrix K` is row-stochastic.
Use the matrix representation for eigenvectors/eigenvalues, Bernoulli--Laplace
spectral calculations, and linear algebra.  Use the fibre-distribution
representation for composition and probability semantics.

This gives one authority with two views rather than two independent models.

## Total variation and finite mixing

Mathlib currently does not expose the finite-chain TV/Dobrushin layer we need.
`or4nge19/MCMC` does have:

- finite `tvDist`,
- Dobrushin coefficient,
- TV contraction,
- submultiplicativity,
- primitive-chain convergence machinery.

However its implementation is specialized to `ℝ` and defines its own
`IsStochastic` rather than using modern Mathlib's `Matrix.rowStochastic`.

**Recommendation:** adapt the small reusable part into `shufflemath` rather
than depending on the whole package.  Prefer a coefficient-generic finite TV
API where practical:

```lean
def Dist.tv [Fintype α] (μ ν : Convexity.StdSimplex R α) : R :=
  (1 / 2) * ∑ x, |μ.weights x - ν.weights x|
```

for an appropriate ordered field `R`.  The project can instantiate this at
`ℚ` for exact certificates and cast to `ℝ` only when analysis requires it.

For the Dobrushin coefficient, prefer a finite maximum over pairs of states over
an `sSup` formulation.  This keeps exact rational values available and avoids
introducing completeness merely because the state space is finite.

Potential upstream candidates after the API stabilizes:

- total variation on `StdSimplex` over finite types,
- the finite Dobrushin contraction theorem stated using
  `Matrix.rowStochastic`.

## Stationarity and general Markov kernels

Mathlib already has the measure-theoretic
`ProbabilityTheory.Kernel.Invariant`.  TauCeti adds useful path-law and
randomization results on top of Mathlib kernels, including a homogeneous
Markov-chain path law.

Those are not needed for the first exact finite results.  Define finite
stationarity in terms of the finite distribution action, then add a bridge to
Mathlib's measure-kernel notion only when a theorem actually needs it.

This avoids pulling ENNReal, measurable-space, and standard-Borel obligations
into elementary finite combinatorics.

TauCeti becomes worth reconsidering when the project needs one of:

- general path-space Markov-chain laws,
- conditional distributions/disintegration,
- measure-theoretic sampling statements,
- infinite/general-state versions of the shuffle process.

## Perron--Frobenius / spectral machinery

Mathlib has irreducible/primitive matrix definitions but does not currently
contain a complete Perron--Frobenius development matching the one in
`or4nge19/MCMC`.

`MCMC` therefore remains potentially useful later for general finite-chain
spectral convergence.  It is not needed for the first Bernoulli--Laplace
results, because we can prove the relevant eigenfunction/eigenvalue directly
and compute exact finite powers/TV distances without a general PF theorem.

Re-evaluate this dependency when we need a theorem of the form
"primitive stochastic matrix converges geometrically to its unique stationary
law" as a reusable black box rather than a shuffle-specific result.

## Domain-specific gaps we must formalize

These were not found in Mathlib, TauCeti, or the inspected MCMC library and are
therefore legitimate `shufflemath` content.

### Bernoulli--Laplace

Mathlib supplies `Nat.choose` and extensive binomial/Vandermonde identities,
but not a packaged hypergeometric probability distribution or
Bernoulli--Laplace chain.

We should define the transition law in exact rational arithmetic from binomial
coefficients and prove its normalization using existing choose identities.

### GSR / a-shuffles

No riffle-shuffle formalization was found.  In particular, the inspected
libraries do not provide:

- Gilbert--Shannon--Reeds riffles,
- inverse riffles via random labels,
- the a-shuffle composition law,
- rising-sequence statistics,
- Eulerian-number shuffle formulas,
- Bayer--Diaconis total-variation formulas.

A clean first formal model should use the inverse-shuffle label construction.
It exposes the randomness directly and should make the composition theorem
(`a`-shuffle followed by `b`-shuffle is an `ab`-shuffle) simpler than starting
from the rising-sequence probability formula.

Eulerian/rising-sequence machinery can then be introduced only when needed for
closed-form TV calculations.

### Imperfect/clumpy human shuffles

No existing Lean formalization was found for the Jonasson--Morris clumpy riffle
model or the more recent general imperfect-riffle models.  This is downstream
work after the exact GSR layer is stable.

### Cost-optimal schedules

The cost model and optimization over heterogeneous shuffle operations are
project-specific.  `CostedKernel` should remain, although its representation can
be simplified after the kernel refactor.

Consider using a bundled nonnegative cost type (e.g. nonnegative rationals) or
parameterizing the cost semiring once the intended optimization theorems are
clear.  Do not generalize this prematurely.

## File-by-file verdict on the initial repository

### `Shufflemath/Finite.lean`

**Refactor before adding more theorems.**

Keep the project-facing concepts (`Dist`, finite stochastic kernel, TV), but
rebase them on `StdSimplex` and `Matrix.rowStochastic`.  Do not keep
`Weight.IsProbability` or `Kernel.IsMarkov` as competing normalization APIs.

### `Shufflemath/Cost.lean`

**Keep the concept.**

Change `step` to the new finite-kernel type.  The additive protocol-cost lemmas
are project-specific and appropriate.

### `Shufflemath/BernoulliLaplace.lean`

**Keep.**

`firstModeFactor` and the Commander specializations are domain content, not a
library duplicate.

Eventually replace the finite `native_decide` optimality check with a general
mathematical theorem characterizing the integer `k` nearest

```text
m * (N - m) / N
```

as minimizing the absolute first-mode factor (within the legal exchange range).
The concrete 99-card theorem should then be a corollary.

## Proposed module layout after the refactor

```text
Shufflemath/
  Finite/
    Distribution.lean     -- StdSimplex-facing aliases/helpers + exact TV
    Kernel.lean           -- α → Dist β, apply, comp, deterministic
    Matrix.lean           -- to/from matrix views, rowStochastic bridge
    Dobrushin.lean        -- finite exact contraction theory
  Shuffle/
    GSR.lean              -- inverse riffle / a-shuffle construction
    RiffleStats.lean      -- rising sequences / Eulerian material if needed
  BernoulliLaplace/
    Kernel.lean           -- exact hypergeometric transition kernel
    Spectral.lean         -- first mode and later eigenmodes
    Commander99.lean      -- exact finite certificates for 50/49
  Protocol/
    Cost.lean
    Schedule.lean
    Optimize.lean
```

Do not split into all of these files immediately; this is a target boundary,
not a request for indirection.  Start with `Finite.lean` until its definitions
stabilize, then split when files become independently meaningful.

## Immediate implementation sequence

1. Upgrade Lean/Mathlib from 4.19.0 to 4.34.0 and get the current three Lean
   files green without semantic changes.
2. Refactor `Weight`/`Kernel` onto `StdSimplex` while preserving the public
   theorem intent.
3. Add the matrix bridge and prove row-stochasticity.
4. Port/adapt finite TV contraction ideas from `or4nge19/MCMC`, generalized so
   exact `ℚ` remains usable.
5. Implement the exact Bernoulli--Laplace transition kernel and stationary law.
6. Prove the first-mode eigenvalue formula; derive the 25-card result from a
   general minimization theorem.
7. Only then begin the GSR local-shuffle layer.

## Dependency decision table

| Capability | Mathlib 4.34 | MCMC | TauCeti | shufflemath action |
|---|---|---|---|---|
| Exact rational finite distribution | `StdSimplex ℚ` | no special gain | no special gain | use Mathlib |
| Stochastic matrices | `Matrix.rowStochastic` | duplicates it | measure kernels instead | use Mathlib |
| PMFs / uniform finite sampling | yes | no special gain | higher-level sampling | use Mathlib where appropriate |
| Finite TV | no integrated API | yes, `ℝ` | not found | adapt locally, generic/exact |
| Dobrushin contraction | not found | yes, `ℝ` | not found | adapt locally |
| General Markov path law | base kernel machinery | partial/WIP | yes | defer; TauCeti later if needed |
| Perron--Frobenius convergence | incomplete for our needs | substantial | not relevant | defer dependency decision |
| Bernoulli--Laplace | no | no | no | implement here |
| GSR / riffle shuffles | no | no | no | implement here |
| Eulerian/rising-sequence shuffle theory | no | no | no | implement only as needed |
| Human clumpy riffles | no | no | no | implement later |
| Cost-optimal protocol scheduling | no | no | no | implement here |

