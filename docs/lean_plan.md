# Lean formalization plan

The guiding rule is to formalize finite exact statements first. Asymptotic probability theory can come later.

## Phase L0: finite algebraic infrastructure

- finite signed/probability weights over a `Fintype`;
- normalization predicate;
- finite Markov kernels as rational matrices/functions;
- application and composition;
- deterministic kernels;
- total-variation distance;
- protocol cost as a sum over actions.

Initial files:

- `Shufflemath/Finite.lean`
- `Shufflemath/Cost.lean`

The choice of rational weights is deliberate: the finite Commander calculations are exact and can eventually be checked by kernel reduction rather than trusted floating-point numerics.

## Phase L1: Commander Bernoulli--Laplace projection

Formalize the 50-state statistic

```
X = number of originally-left cards currently in the 50-card left pile.
```

For left pile size `m`, right pile size `N-m`, and exchange size `k`, derive the exact hypergeometric transition probability

```
P(x -> y).
```

Targets:

1. prove each row is a probability distribution;
2. prove the hypergeometric stationary distribution;
3. prove reversibility;
4. prove/lift the first nonconstant eigenfunction and factor;
5. specialize to `N=99`, `m=50`;
6. prove `k=25` minimizes `|lambda_1|` over allowed integer `k`;
7. certify exact TV bounds after selected sequences, especially `(25,25)`.

The current `BernoulliLaplace.lean` starts only with the arithmetic factor; the spectral interpretation is intentionally marked as future work.

## Phase L2: ideal GSR local riffle

Formalize one inverse GSR shuffle via independent binary labels. Repeated riffles can then be represented via larger labels (`a=2^r`).

Targets:

- equivalence between repeated 2-shuffles and an `a`-shuffle;
- exact finite probability of a permutation in terms of rising sequences / descents;
- exact or certified TV distances for working-set sizes 49 and 50;
- a local-shuffle kernel embedded in the 99-card state space.

## Phase L3: compositional error theorem

Prove a generic total-variation contraction theorem for finite Markov kernels and a telescoping perturbation theorem.

Desired statement shape:

```
TV(K0*K1*...*Kn, L0*L1*...*Ln)
  <= sum_i sup_x TV(Ki x, Li x).
```

This is a key abstraction boundary: known/tractable local-shuffle error can be combined with known/tractable cross-pile mixing.

## Phase L4: costed protocol certificates

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

## Phase L5: biased/clumpy local models

After the GSR baseline is stable:

- biased-cut inverse riffle;
- Jonasson--Morris Markovian binary-label process;
- optional robust parameter intervals.

Do not jump directly to a fitted empirical model before the finite GSR infrastructure is validated.

## Phase L6: public theorem statements

Aim for statements with an operational interpretation, e.g.:

> Under model M with cost ratio rho in interval I and TV target epsilon, protocol P has certified cost C and every protocol in action class A with lower cost fails the target.

These are suitable both for formal verification and popular communication.
