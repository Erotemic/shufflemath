# Visualization / study-course roadmap

The Manim material under `visualizations/` is not a literature-overview talk.
It is a **mathematical study course** whose purpose is to make the relevant
shuffle theory, Markov-chain theory, and finite-control mathematics intuitive
before the Lean development expands.

The course currently contains 155 scenes split into six parts. A separate
18-scene advanced-math deck collects the proof tools that are most likely to
need repeated study.

## Course-wide pedagogy

Every chapter should obey the following rules.

### 1. No undefined notation

A new symbol must be accompanied by its state space / type and plain-language
meaning. If a symbol returns after a long gap, use a reminder box. In
particular, distinguish:

- a sampled state from a distribution on states;
- a random variable from its law;
- a projection from an exact Markov lumping;
- `Delta(K,L)` (approximation error between two kernels) from `delta(K)`
  (Dobrushin contraction coefficient of one kernel);
- total variation from separation and relative `L^infinity`.

### 2. Concrete finite examples before general formulas

The recurring teaching pattern is:

1. state the random experiment;
2. work a small instance by hand;
3. write the finite formula;
4. prove/check normalization or consistency;
5. only then quote the literature theorem or asymptotic scaling.

### 3. Motion should explain processes

Manim is not used merely to fade static bullet lists. Physical riffles,
stable sorts, descent discovery, repeated label composition, distribution
motion, and protocol replacements should be animated when motion exposes the
mechanism. Animation-only scenes can opt out of the static handout.

### 4. Hard mathematics gets a sequence, not a name-drop

A paper's advanced tool is introduced as:

- definition;
- why it is relevant to this chain;
- one worked derivation / proof skeleton;
- what the published theorem obtains;
- which fragment, if any, we actually intend to formalize.

This is particularly important for coupling, path coupling, strong stationary
times, reversible spectral theory, Gelfand-pair/spherical-function symmetry,
dual Hahn polynomials, quasisymmetric functions, second-moment lower bounds,
and Dobrushin contraction.

## Part 0 — mathematical foundations

The foundations chapter exists so later sections never have to hide behind
notation.

### Definitions

- finite state space `Omega`;
- distribution / law `mu`, point mass `delta_x`, uniform law `U`;
- forward permutation versus inverse permutation;
- random variable `X : Omega -> Xspace` and induced law;
- projection and exact strong lumping;
- Markov kernel `K(x,y)` and row stochasticity;
- row-vector update `(mu K)(y)` and composition convention;
- stationary law `pi`;
- detailed balance / reversibility;
- total variation in `L1` and event forms;
- Markov operator on observables;
- eigenfunction/eigenvalue;
- mixing time and cutoff.

### Proofs / derivations

- law-of-total-probability kernel update;
- detailed balance implies stationarity;
- TV contraction under a common kernel;
- why an eigenfunction evolves by `lambda^t` in expectation.

### Formalization connection

These are the generic interfaces on which all shuffle-specific theorems depend.
They should eventually live below the Bernoulli--Laplace and GSR layers rather
than being re-proved ad hoc.

## Part 1 — earn the classical seven-riffle result

The chapter should make the Bayer--Diaconis result feel discoverable.

1. **Physical shuffle first.** Show a genuine split/interleave/bridge riffle.
2. **Entropy false start.** Uniform 52-card order needs about 225.6 bits; 52
   source bits per inverse riffle only proves at least five, motivating more
   structure.
3. **GSR mechanics.** Binomial cut plus uniform order-preserving interleaving;
   show the cancellation making each source word probability `2^-n`.
4. **Invert.** Explain why inversion preserves the uniform target and TV.
5. **Independent labels.** One inverse riffle = independent fair bits + stable
   sort.
6. **Repeated riffles.** Successive stable sorts concatenate into a uniform
   `a=2^k` address.
7. **Descents / rising sequences.** Define maximal consecutive increasing runs,
   not arbitrary increasing subsequences.
8. **Compatible labels.** Weak inequalities, with strict steps exactly at
   descents.
9. **Stars-and-bars.** Remove forced strict steps and derive the compatible-label
   count.
10. **Exact probability.** Derive
    `Q_a(pi)=a^-n binom(a+n-r(pi),n)`.
11. **Eulerian numbers.** Define them and derive the insertion recurrence.
12. **Exact TV aggregation.** Collapse `n!` states into `n` run-count classes.
13. **Uniform run moments.** Derive mean and variance from descent indicators.
14. **Likelihood ratio.** Define it before use; prove it is monotone in run
    count.
15. **Optimal event.** Identify `R<=25` at seven 52-card riffles and recover TV
    about 0.334.
16. **Cutoff scale.** Motivate `a ~ n^(3/2)` and `k ~ (3/2)log_2 n`, then state
    the sharp theorem separately from the finite 52-card calculation.

The full classical chapter ends with a glossary/checkpoint.

## Part 2 — Nestoridi--White and Bernoulli--Laplace in depth

The source model is the two-pile `k`-cut procedure with **perfect** independent
local randomization of the piles. That oracle assumption is stated prominently
because our project later removes it.

### Build the finite chain

1. Define the perfect-local oracle.
2. Explain the microstate/macrostate symmetry reduction.
3. Define `N,m,r,k,X` and feasible values of `X`.
4. Review hypergeometric sampling without replacement.
5. Count the stationary hypergeometric law.
6. Define red cards leaving/entering as `A,B` and derive `X'=X-A+B`.
7. Derive the exact transition sum from two independent hypergeometric draws.
8. Work the entire `N=8,m=4,r=4,k=1,X=3` row:
   `(0,0,9/16,6/16,1/16)`.
9. Explain row stochasticity as a partition of sample outcomes.
10. Check detailed balance numerically on the toy chain, then give the
    microstate-reversal proof.

### Derive the first mode

From hypergeometric sample means derive

`E[X'|X=x] = x - k x/m + k(r-x)/(N-m)`.

Center at `mu=mr/N` to obtain

`E[X'-mu|X=x] = lambda_1 (x-mu)`,

`lambda_1 = 1 - Nk/[m(N-m)]`.

For Commander `N=99,m=50,r=50`, the real zero is
`k=2450/99 ~= 24.747`, explaining why `k=25` nearly annihilates the first mode
(`lambda_1=-1/98`) before any exhaustive finite TV calculation is shown.

### Projection caveat

Membership-count TV is the full answer only when the conditional microstate law
has the symmetry supplied by the perfect-local oracle (or another proven exact
lumping argument). With finite local riffles it is not automatically full-deck
TV.

### Advanced proof tools

The advanced slides then teach rather than merely list:

- coupling and the coupling inequality;
- path coupling;
- reversibility as self-adjointness in the `pi`-weighted inner product;
- the microstate space as an `m`-subset walk under the `S_N` action;
- the working definition of the Gelfand pair
  `(S_N, S_m x S_{N-m})`;
- why a commutative radial algebra yields a shared eigenbasis;
- why dual-Hahn-type orthogonal polynomials appear;
- second-moment TV lower bounds;
- unequal-urn theory and the `S_k` perfect-block dynamics.

The current formalization plan needs the finite kernel, stationary law,
reversibility, first eigenfunction, and finite certificates first. Full
representation-theoretic machinery remains optional until a concrete theorem
requires it.

## Part 3 — biased and correlated riffles as distinct models

### Independent biased labels

Teach Fulman's `p`-shuffle as independent categorical labels followed by a
stable sort. Derive:

- biased two-shuffle / binomial packet size;
- general probability vector `p=(p_1,...,p_a)`;
- composition via product labels `p tensor q`;
- collision probability `sum_i p_i^2`;
- strong stationary time from distinct combined addresses;
- finite bound
  `TV <= binom(n,2) (sum_i p_i^2)^k`.

### Distance metrics

Define TV, separation, and relative `L^infinity` side by side before quoting a
cutoff theorem. Assaf--Diaconis--Soundararajan's sharp biased-cut results are
primarily stated in separation and relative `L^infinity`; the deck should not
silently relabel them as TV results.

### Quasisymmetric deep dive

Do not leave “quasisymmetric functions” as a literature buzzword.

1. contrast symmetric and quasisymmetric polynomials;
2. define inverse descent set;
3. define the fundamental weighted sum over weak label sequences with strict
   inequalities at inverse descents;
4. state `P_p(w)=Q_iDes(w)(p)`;
5. work the 3-card/two-label example:
   - strict at position 1 gives weight `p(1-p)^2`;
   - strict at position 2 gives weight `p^2(1-p)`;
6. conclude that fair GSR depends only on descent *count*, while biased labels
   can depend on descent *positions*;
7. explain identity/reversal extremality for separation / relative pointwise
   error.

### Correlated source words

Separate cut bias from clumping. Use a clearly labeled pedagogical two-state
Markov source to build intuition for same-hand persistence, geometric run
lengths, and loss of exchangeability. Then state the Jonasson--Morris
`O(log^4 n)` result under their model assumptions and explain why that asymptotic
bound is not yet a finite 49/50-card certificate.

## Part 4 — compositional error and costed control

This is the synthesis chapter.

### Kernel perturbation

Define

`Delta(K,L)=max_x TV(K(x,.),L(x,.))`

and prove `TV(mu K,mu L)<=Delta(K,L)` by convexity. Combine with ordinary TV
contraction to derive the hybrid telescope

`TV(mu K_1...K_T, mu L_1...L_T) <= sum_i Delta(K_i,L_i)`.

### Dobrushin refinement

Define

`delta(K)=max_{x,x'} TV(K(x,.),K(x',.))`

and prove

`TV(mu K,nu K) <= delta(K) TV(mu,nu)`.

With hybrids

`H_i=L_1...L_i K_{i+1}...K_T`,

the exact weighted telescope becomes

`TV(mu K_1...K_T, mu L_1...L_T)
 <= sum_i Delta(K_i,L_i) prod_{j=i+1}^T delta(K_j)`.

The deck includes a separate proof slide so this is not left as an informal
“future kernels wash out error” slogan.

### Optimization

Define the physical cost function, feasibility tolerance, Pareto dominance,
robust parameter set, and the exact meaning of “optimal within a declared
finite search space.” Search proposes schedules; Lean checks the compact exact
certificate.

## Part 5 — theorem-by-theorem Lean roadmap

The final chapter turns the study course into implementation dependencies.

1. finite exact distributions and kernels;
2. symbolic Bernoulli--Laplace normalization, stationarity, reversibility, and
   first mode;
3. GSR inverse-label semantics, composition, rising-sequence probability, and
   exact finite TV;
4. TV/Dobrushin contraction and weighted telescoping perturbation bounds;
5. costed protocol semantics and finite optimality certificates;
6. biased/correlated local-kernel interfaces;
7. robust parameter sets;
8. eventual operational theorem for a concrete human protocol.

## Core literature represented in the course

- Bayer & Diaconis, *Trailing the Dovetail Shuffle to its Lair* (1992).
- Fulman, *The combinatorics of biased riffle shuffles* (1998).
- Assaf, Diaconis & Soundararajan, *Riffle shuffles with biased cuts*
  (arXiv:1112.2650).
- Jonasson & Morris, *Rapid mixing of dealer shuffles and clumpy shuffles*
  (2015).
- Nestoridi & White, *Shuffling large decks of cards and the Bernoulli--Laplace
  urn model* (arXiv:1606.01437; journal version 2019).
- Griffin et al., *Cutoff in the Bernoulli-Laplace Model With Unequal Colors and
  Urn Sizes* (arXiv:2308.08676).
- Nestoridi, Priestley & Schmid, *The S_k shuffle block dynamics*
  (arXiv:2304.02588).
- Sellke, Shi & Wang, *Universality of Cutoff for Riffle Shuffling*
  (arXiv:2510.22783).

The deck deliberately labels recent/general results as prior art rather than as
our novelty. The project contribution is the synthesis: finite imperfect local
randomization, explicit working-set changes, heterogeneous physical cost, and
certified finite protocol optimization.
