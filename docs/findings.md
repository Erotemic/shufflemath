# Current findings

This file distinguishes exact finite results already reproduced by the repository from theorem targets that remain symbolic/formalization work.

## 99 cards split 50/49: first Bernoulli--Laplace mode

For the unequal two-urn exchange model, the first nonconstant mode has factor

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

`Shufflemath/BernoulliLaplace.lean` contains a finite exact theorem stating that `k=25` minimizes the absolute value of this expression over exchange sizes 1 through 49. The symbolic target — proving that this expression is the first nonconstant eigenvalue of the exact transition matrix, rather than merely importing the known formula as the definition of `firstModeFactor` — is in progress: the general Bernoulli–Laplace exchange theory (`BernoulliLaplaceGeneral.lean`, with the fiber-counting companion `BernoulliLaplaceFiber.lean`) is built, and the first-mode machinery in its `firstMode` section (the weighted Vandermonde and reindexing lemmas) is the current work item; see the "Next action" section of `docs/autonomous_lean_build.md`.

## Exact finite 50-state exchange model

The macrostate is

```
X = number of originally-left cards currently in the 50-card left pile.
```

For the 99-card / 50+49 case, the feasible values are 1 through 50, represented in Lean by `Fin 50` with decoded value `x.val + 1`.

Both the Python reference implementation and the Lean source use the same hypergeometric counting formula:

- choose `a` original-left cards among the `k` cards leaving the left pile;
- choose the remainder from original-right cards in the left pile;
- choose `b` original-left cards among the `k` cards entering from the right pile;
- require `x - a + b = y`;
- divide by `choose(50,k) * choose(49,k)`.

For `k=25`, the Lean source defines the exact rational 50x50 transition matrix and contains finite certificates that:

1. every entry is nonnegative and every row sums to one;
2. the hypergeometric stationary vector normalizes;
3. applying the transition matrix to that stationary vector returns the same vector.

These certificates use `native_decide` over a finite exact-rational computation. The symbolic proofs using binomial identities now exist in the general theory (`BernoulliLaplaceGeneral.lean`: `blRowStochastic` and the stationary distribution, with the detailed-balance fiber counting in `BernoulliLaplaceFiber.lean`), and `BernoulliLaplaceCommanderBridge.lean` proves the general and concrete theories agree at the Commander parameters.

## Exact TV distances from complete segregation

Starting with all 50 original-left cards in the left pile and repeatedly exchanging 25 cards from each side gives:

| exchanges | total-variation distance of the pile-membership statistic |
|---:|---:|
| 1 | 0.841615338839 |
| 2 | 0.00248417758708 |
| 3 | 0.0000257596683780 |
| 4 | 0.000000262719118303 |

The exact values currently certified in Lean are:

```
steps=2:
12255318415559330995522631403472464258192877
------------------------------------------------
4933350368865509640837610315994582805439728012

steps=3:
172379525755689183991816396516567920780192827919620440221147749
--------------------------------------------------------------------
6691837923759692633601708022649918108038775216019298375918637677488
```

The Python test suite also checks the exact four-step rational value, row normalization, stationarity, and the two-exchange search result.

## Two-exchange search

The exact-rational Python model searches all `49^2` two-exchange schedules using floating point only to rank candidates, then reevaluates the winner exactly. It finds

```
(25, 25)
```

with TV distance `0.00248417758708` for the projected chain.

**Status:** the search result is not yet a Lean optimality theorem. The current Lean theorem proves only that 25 minimizes the absolute first-mode factor. A near-term finite certificate should prove directly that no other `(k1,k2)` pair has lower terminal TV for this projected chain.

## What these numbers do not yet mean

They do **not** say that two physical cuts randomize a Commander deck. The 50-state projection describes only pile-membership memory. Nestoridi--White's idealized reduction assumes the local piles are perfectly randomized internally.

The main research problem remains to replace that oracle local randomization with repeated finite-cost local riffle/mash kernels, combine their error with cross-pile exchange, and optimize the physical-time cost of the whole schedule.
