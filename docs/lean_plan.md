# Lean formalization plan

The guiding rule is to formalize finite exact statements first. Asymptotic probability theory can come later.

## L0: finite exact infrastructure -- implemented

The project now uses mathlib's probability-simplex abstraction directly:

- `Dist alpha := Convexity.StdSimplex Rat alpha`;
- `FiniteKernel alpha beta := alpha -> Dist beta`;
- deterministic kernels, composition, application, and repeated execution;
- rational stochastic-matrix bridge;
- exact rational total variation and finite Dobrushin coefficient;
- additive costed kernels.

The old `Weight + IsProbability` and `Kernel + IsMarkov` duplicate authorities have been removed.

## L1: Bernoulli--Laplace -- Commander certificates and general theory implemented

The 50-state statistic is

```
X = number of originally-left cards currently in the 50-card left pile.
```

The current source defines the exact hypergeometric transition formula and specializes it to `N=99`, `m=50`, `k=25`.

Implemented finite certificates:

1. the 25-card exchange matrix is row stochastic;
2. the hypergeometric stationary vector normalizes;
3. that vector is a fixed point of the 25-card exchange matrix;
4. `k=25` minimizes the absolute first-mode factor over exchanges 1..49;
5. exact TV values after two and three 25-card exchanges from complete
   segregation;
6. the general `N`/`m`/`r` exchange theory (`BernoulliLaplaceGeneral.lean`
   and `BernoulliLaplaceFiber.lean`): symbolic row normalization, the
   stationary distribution, detailed balance by fiber counting, and the
   `BLState 99 50 50` `↔` `Fin 50` bridge proving agreement with the
   Commander instance (`BernoulliLaplaceCommanderBridge.lean`).

Remaining symbolic targets (1--3 done):

1. [done] row normalization for general admissible `N,m,k` using
   Vandermonde identities;
2. [done] the hypergeometric stationary distribution symbolically;
3. [done] reversibility;
4. the first nonconstant eigenfunction and factor (in progress);
5. connect the exact matrix TV certificates to the semantic
   `Dist`/`FiniteKernel` view;
6. certify the finite `(25,25)` optimality search rather than only its
   first-mode surrogate.

## L2: ideal GSR local riffle

Formalize one inverse GSR shuffle via independent binary labels. Repeated riffles can then be represented via larger labels (`a = 2^r`).

Targets:

- equivalence between repeated 2-shuffles and an `a`-shuffle;
- exact finite probability of a permutation in terms of rising sequences / descents;
- exact or certified TV distances for working-set sizes 49 and 50;
- a local-shuffle kernel embedded in the 99-card state space.

## L3: compositional error theorem -- implemented (`Shufflemath/Perturbation.lean`)

Prove exact finite total-variation contraction and a telescoping perturbation theorem.

Desired statement shape:

```
TV(K0*K1*...*Kn, L0*L1*...*Ln)
  <= sum_i sup_x TV(Ki x, Li x).
```

The local finite Dobrushin definition is already in place. The proof strategy should reuse the structure of the existing `or4nge19/MCMC` formalization while using mathlib's stochastic-matrix authority and rational coefficients where possible.

## L4: costed protocol certificates

Represent an action alphabet such as:

```
local-left
local-right
exchange k
```

or symmetric paired local operations if that is the protocol class under study.

A search program can produce a candidate protocol and a compact certificate. Lean verifies:

- its cost;
- its terminal error bound;
- and, for a bounded finite action space, that no cheaper candidate satisfies the same target.

The search itself need not initially be formalized.

## L5: biased/clumpy local models

After the GSR baseline is stable:

- biased-cut inverse riffle;
- Jonasson--Morris Markovian binary-label process;
- untouched-tail variants;
- optional robust parameter intervals.

Do not jump directly to a fitted empirical model before the finite GSR infrastructure is validated.

## L6: public theorem statements

Aim for statements with an operational interpretation, e.g.:

> Under model M with cost ratio rho in interval I and TV target epsilon, protocol P has certified cost C and every protocol in action class A with lower cost fails the target.

These are suitable both for formal verification and popular communication.
