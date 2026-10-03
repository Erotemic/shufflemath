# Initial findings

This file records results already reproduced by code in this repository and distinguishes them from theorem targets that are not yet formalized.

## 99 cards split 50/49: first Bernoulli--Laplace mode

For the unequal two-urn exchange model, the first nonconstant mode has the standard factor

```
lambda_1(N,m,k) = 1 - N*k / (m*(N-m)).
```

For `N=99`, `m=50`, the real zero is

```
50*49/99 = 24.747474...
```

The nearest integer exchange is therefore 25. Exact values around the optimum are

```
k=24: lambda_1 =  37/1225 ~=  0.03020408
k=25: lambda_1 =  -1/98   ~= -0.01020408
k=26: lambda_1 = -62/1225 ~= -0.05061224
```

`Shufflemath/BernoulliLaplace.lean` includes a finite arithmetic theorem stating that `k=25` minimizes the absolute value of this expression over exchange sizes 1 through 49. The spectral theorem connecting this expression to the transition kernel is still a formalization target.

## Exact finite 50-state exchange computation

`experiments/bernoulli_laplace.py` tracks

```
X = number of originally-left cards currently in the 50-card left pile.
```

It constructs the exact hypergeometric transition probabilities using `fractions.Fraction` and compares the resulting distribution with the exact hypergeometric stationary law.

Starting from perfectly segregated 50/49 piles and repeatedly exchanging `k=25` cards from each side gives:

| exchanges | total-variation distance of the pile-membership statistic |
|---:|---:|
| 1 | 0.841615338839 |
| 2 | 0.00248417758708 |
| 3 | 0.0000257596683780 |
| 4 | 0.000000262719118303 |

These are exact-rational computations; the table prints decimal renderings.

The experiment also searches all `49^2` two-exchange schedules in floating point to generate a candidate and then reevaluates the winning candidate exactly. It finds

```
(25, 25)
```

with TV distance `0.00248417758708` for this projected chain.

**Status:** this exhaustive search is a conjecture generator, not yet a formal optimality proof. One of the near-term Lean goals is to certify the finite search result.

## What these numbers do not yet mean

They do **not** say that two physical cuts are sufficient to randomize a Commander deck. The 50-state projection assumes that each local pile has already been perfectly randomized internally. It measures only residual memory of which original half a card came from.

The project exists precisely to remove that oracle-perfect-local-shuffle assumption and account for the cost and imperfection of the local physical shuffles.
