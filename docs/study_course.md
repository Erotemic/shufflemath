# Shufflemath mathematical study course

This document describes the intended learning path for the Manim course in
`visualizations/`. The course is deliberately much more detailed than the
formalization plan: its purpose is to make the mathematics familiar enough that
formal theorem statements are motivated rather than copied from papers.

## Learning standard

A chapter is not complete merely because it states the relevant theorem. After
studying a chapter, the learner should be able to:

1. define every state space and random operation in ordinary language;
2. reconstruct the important formulas from the underlying random experiment;
3. explain which symmetry or sufficient statistic permits a state-space
   reduction;
4. name the probability metric used by each theorem;
5. distinguish exact finite statements from asymptotic intuition;
6. identify the theorem interface that the eventual Lean development needs.

## Part 0: foundations

Prerequisites are intentionally made explicit.

- finite state space `Omega`;
- distributions, point masses, and uniform law;
- permutation order versus inverse permutation;
- random variables and induced laws;
- projection versus exact Markov lumping;
- Markov kernels and row-stochastic matrices;
- row-vector kernel composition (`KL` = first `K`, then `L`);
- stationary distributions and detailed balance;
- total variation in sum form and event form;
- contraction under common post-processing;
- Markov operators on observables and eigenfunctions;
- mixing time and cutoff.

The key conceptual goal is to be able to move fluently between three views:
random states, distributions on states, and kernels that transform those
distributions.

## Part 1: classical GSR riffles

The chapter earns the seven-riffle result rather than citing it.

1. Watch an actual split/interleave/bridge riffle.
2. Define the GSR binomial cut and uniform order-preserving interleave.
3. Invert the permutation and discover the independent fair-bit stable sort.
4. Compose inverse shuffles into `a=2^k` addresses.
5. Define descents and maximal consecutive rising sequences.
6. Convert a target permutation into weak label inequalities with strict steps
   at descents.
7. Use stars-and-bars to count compatible labels.
8. Derive the exact `a`-shuffle probability.
9. Define Eulerian numbers and derive their insertion recurrence.
10. Aggregate the exact total-variation sum by rising-sequence class.
11. Derive the mean/variance of rising-sequence count under uniformity.
12. Define the likelihood ratio and prove it is monotone in the run count.
13. Identify the optimal TV witness event for seven 52-card riffles.
14. Read the exact finite TV table.
15. Motivate the `3/2 log_2(n)` cutoff scale.

## Part 2: Bernoulli--Laplace and large decks

The chapter begins from the physical large-deck procedure and derives the urn
chain.

1. State exactly what the perfect-local oracle does.
2. Explain when membership projection is exact and when it is merely a
   diagnostic.
3. Define the membership count `X` and its feasible support.
4. Review the hypergeometric law as sampling without replacement.
5. Count the hypergeometric stationary distribution.
6. Write one exchange as `X' = X - A + B`.
7. Derive the exact transition kernel from two hypergeometric draws.
8. Work an `N=8,m=4,r=4,k=1` row entirely by hand.
9. Prove row normalization probabilistically.
10. Define and check detailed balance, then derive stationarity.
11. Derive `E[X'|X=x]` and center at `mu=mr/N`.
12. Obtain the first eigenfunction and
    `lambda_1 = 1 - Nk/[m(N-m)]`.
13. Substitute `N=99,m=50,r=50` and explain `k=25` before looking at an exact
    TV calculation.
14. Separate membership mixing from full-deck mixing.
15. Study coupling, path coupling, reversible self-adjointness, subset symmetry,
    the Gelfand-pair/spherical-function viewpoint, dual Hahn polynomials, and
    second-moment lower bounds.
16. Compare unequal-urn theory and `S_k` block dynamics.

The advanced symmetry slides are included so that “dual Hahn polynomials” and
“spherical functions” do not remain unexplained names in a literature survey.
They are not a commitment to formalize the entire representation-theoretic
machinery.

## Part 3: biased and correlated riffles

The chapter separates physically distinct departures from GSR.

- biased packet-size / independent-label models;
- general `p`-shuffles and their product-label composition law;
- label collision probability `sum p_i^2`;
- strong stationary times and Fulman's finite collision bound;
- TV versus separation versus relative `L^infinity`;
- quasisymmetric functions and inverse descent sets;
- a three-card worked example showing that bias makes **descent position**
  matter, not merely descent count;
- clumpy/dealer same-hand correlation;
- a pedagogical two-state Markov source and its run-length distribution;
- why correlation destroys exchangeability at fixed cut size;
- Jonasson--Morris asymptotic rapid mixing;
- more general cut-size laws;
- finite model interfaces for measurement and robust certification.

## Part 4: compositional error and control

This chapter builds the theorem that lets the previous pieces coexist.

1. Define actual and oracle protocol kernels.
2. Define worst-row kernel error `Delta(K,L)`.
3. Prove `TV(mu K, mu L) <= Delta(K,L)` by convexity.
4. Revisit common-suffix TV contraction.
5. Build the three-step hybrid telescope, then the general one.
6. Define the Dobrushin coefficient `delta(K)`.
7. Prove quantitative Dobrushin contraction.
8. Fix a hybrid convention and derive the exact weighted telescope

   `TV(mu K_1...K_T, mu L_1...L_T)
      <= sum_i Delta(K_i,L_i) prod_{j>i} delta(K_j)`.

9. Split terminal error into actual-vs-oracle and oracle-vs-uniform terms.
10. Define physical cost, feasible protocols, Pareto dominance, and robust
    parameter sets.
11. Keep external search untrusted; make Lean verify the compact finite
    certificate.

## Part 5: formalization roadmap

The last chapter translates the mathematics into Lean-sized interfaces.

- finite exact distributions and kernels over rationals;
- symbolic Bernoulli--Laplace normalization/stationarity/reversibility/first
  eigenmode;
- GSR inverse labels, composition, rising-sequence formula, and exact finite TV;
- TV contraction and weighted telescoping perturbation bounds;
- costed protocol semantics and finite optimality certificates;
- biased and correlated local-kernel interfaces;
- robust parameter sets and an eventual operational theorem.

## How to use the deck while formalizing

Do not watch all 155 scenes every time. Use the chapter and focused builds:

```bash
cd visualizations
make glossary QUALITY=l PDF=0 JOBS=1
make part0 QUALITY=l PDF=0 JOBS=2
make short QUALITY=l PDF=0 JOBS=2
make part2 QUALITY=l PDF=0 JOBS=2
make advanced QUALITY=l PDF=0 JOBS=2
make part3 QUALITY=l PDF=0 JOBS=2
make part4 QUALITY=l PDF=0 JOBS=2
make part5 QUALITY=l PDF=0 JOBS=2
```

The glossary deck is the quick notation reference. The advanced deck is the
compact path through the proof tools that are easiest to forget between
formalization sessions.
