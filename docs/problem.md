# Mathematical problem

## 1. State space

For a labeled `N`-card deck, the full state space is the symmetric group

```
Omega_N = S_N.
```

The target distribution `U_N` is uniform on `S_N`.

The initial state may be:

- a known deterministic deck ordering;
- a worst-case ordering;
- or a prior distribution representing an already partly mixed deck.

We should keep these cases distinct.

## 2. Physical operations

We distinguish at least two classes of operations.

### Local shuffle

`R_(m, theta)` acts only on a manageable working set of at most `m` cards.

Candidate models, in increasing realism:

1. ideal GSR riffle;
2. biased-cut riffle;
3. clumpy/dealer riffle;
4. measured human model with cut bias, run-length/clump behavior, and untouched-tail probability.

One physical local shuffle has cost `c_R(m, theta)`.

### Cross-working-set operation

`X_k` changes which cards share a local working set. For the two-pile large-deck model this can be represented by recombining, rotating/cutting `k` cards, and splitting again.

It has cost `c_X(k)`.

Unlike a local stochastic shuffle, a deterministic `X_k` injects no entropy. Its purpose is to move randomness already generated locally across the global deck.

## 3. Protocol

A protocol is a finite sequence such as

```
R^(r0) X_(k1) R^(r1) X_(k2) ... X_(kq) R^(rq).
```

The corresponding Markov kernel is the composition of the action kernels in execution order.

For constant local cost `s` and cross-operation cost `x(k)`, the cost is

```
C(sigma) = s * sum_i r_i + sum_j x(k_j).
```

An important dimensionless parameter is the cost ratio

```
rho = c_X / c_R.
```

For each randomness target, optimal protocols should form regions in `rho`-space. This suggests a phase diagram rather than one universal prescription.

## 4. Randomness criteria

Primary mathematical criterion:

```
d_TV(mu, U) = 1/2 * sum_x |mu(x) - U(x)|.
```

But public communication may also benefit from feature-specific diagnostics:

- probability adjacent cards from the initial deck remain adjacent;
- run-length statistics;
- card-position marginals;
- original-pile membership correlation;
- probability a fixed set remains together.

These are not substitutes for total variation, but they can diagnose specific physical defects.

## 5. Optimization problems

### Fixed model, fixed start

```
min_sigma C(sigma)
subject to d_TV(delta_start K_sigma, U) <= epsilon.
```

### Worst-case start

```
min_sigma C(sigma)
subject to sup_mu d_TV(mu K_sigma, U) <= epsilon.
```

### Robust human model

If shuffle parameters `theta` are only known to lie in a set `Theta`, require

```
sup_(theta in Theta) d_TV(delta_start K_(sigma, theta), U) <= epsilon.
```

This may be a better basis for recommendations than fitting one precise parameter value from limited measurements.

## 6. Commander reference problem

The motivating finite instance is:

```
N = 99
working piles = 50 and 49
```

For a perfect-local-shuffle Bernoulli--Laplace abstraction, exchanging `k` cards between the two piles has first nonconstant mode factor

```
lambda_1 = 1 - N*k / (m*(N-m)).
```

For `N=99`, `m=50`, the real-valued zero occurs at

```
k = 50*49/99 ~= 24.747...
```

so `k=25` is the natural integer candidate. In this repository we treat the formula and its interpretation separately: Lean initially verifies the exact arithmetic; proving the spectral statement itself is a later theorem target.

## 7. Perturbation decomposition

A useful proof strategy is to compare each finite local shuffle phase `L_r` with an oracle local randomizer `L_inf`.

If

```
epsilon_r = sup_mu d_TV(mu L_r, mu L_inf),
```

then Markov-kernel contraction and a telescoping argument should yield a bound of the form

```
d_TV(actual protocol, idealized protocol)
  <= sum_i epsilon_(r_i).
```

Combining that with a Bernoulli--Laplace bound separates the problem into:

- within-working-set error;
- cross-working-set mixing error.

This bound may be conservative but is attractive because it is compositional and formalizable.

## 8. Optimization strategy

We should solve increasingly rich finite action spaces.

1. Perfect local randomization + optimize exchange sizes. (Regression against known theory.)
2. GSR local shuffles + constant local/cross costs.
3. GSR + size-dependent costs.
4. Biased cut.
5. Clumpy/dealer riffle.
6. Measured/robust human model.

For each stage, compute a Pareto frontier over

```
(total physical cost, certified distance bound).
```

Then prove selected frontier points in Lean rather than trying to formalize a large numerical optimizer immediately.
