# Literature review and novelty boundary

## Executive summary

The broad question "how can a human shuffle a deck too large to hold?" is **not novel**. Nestoridi and White study precisely that motivation by splitting a large deck into manageable piles, perfectly randomizing each pile, recombining the piles, applying a deterministic operation such as a cut, and repeating.

Several other ingredients are also established research topics:

- ideal Gilbert--Shannon--Reeds (GSR) riffles and exact finite mixing;
- biased riffles and unequal cuts;
- clumpy/dealer riffles intended to better approximate human shuffling;
- Bernoulli--Laplace exchange processes;
- shuffle block dynamics where only a subdeck is randomized;
- optimization and scan-order questions for heterogeneous Markov kernels in general MCMC.

The apparent gap is the **combined finite control problem**:

> A deck is larger than the player's comfortable working set. A local shuffle is itself imperfect and takes finite time. Recombining/repartitioning the deck also has a distinct cost. Choose the finite sequence of local shuffles and cross-working-set operations that minimizes physical cost subject to a quantitative distance-to-uniform target.

A novelty claim should remain narrow until a broader bibliographic search (including theses and casino-industry literature) is complete.

## Closest prior work

### Bayer and Diaconis: GSR riffle shuffles

Dave Bayer and Persi Diaconis, *Trailing the Dovetail Shuffle to its Lair*, Annals of Applied Probability 2(2), 1992, 294--313. DOI: 10.1214/aoap/1177005705.

Canonical source for the GSR model, exact formulas after repeated riffles, and the cutoff scale near `(3/2) log_2 n`.

- Stanford record: https://statistics.stanford.edu/technical-reports/trailing-dovetail-shuffle-its-lair
- DOI: https://doi.org/10.1214/aoap/1177005705

Relevance: this should be our first local-shuffle kernel because it is exact, finite, and compositional. It is not yet a realistic human model.

### Nestoridi and White: large decks / Bernoulli--Laplace

Evita Nestoridi and Graham White, *Shuffling Large Decks of Cards and the Bernoulli--Laplace Urn Model*, Journal of Theoretical Probability 32(1), 2019, 417--446. DOI: 10.1007/s10959-018-0807-3. Preprint arXiv:1606.01437.

- arXiv: https://arxiv.org/abs/1606.01437
- Journal metadata: https://doi.org/10.1007/s10959-018-0807-3

This is the nearest ancestor of the project. Their motivating procedure is to:

1. split a large deck into manageable piles;
2. shuffle each pile thoroughly;
3. recombine the piles;
4. apply a simple deterministic operation such as a cut;
5. repeat.

The decisive difference is that the local piles are treated as **perfectly shuffled**. That collapses the state to pile membership and makes a second local shuffle immediately redundant. Therefore their model cannot express our central tradeoff: "perform another cheap local shuffle or pay for an expensive repartition now?"

### Jonasson and Morris: clumpy/dealer human riffles

Johan Jonasson and Benjamin Morris, *Rapid mixing of dealer shuffles and clumpy shuffles*, Electronic Communications in Probability 20 (2015), paper 20. DOI: 10.1214/ECP.v20-3682.

- DOI: https://doi.org/10.1214/ECP.v20-3682
- Chalmers record: https://research.chalmers.se/en/publication/215159

They study variants designed to model human shuffling more realistically. In an inverse description, successive binary labels are correlated, so cards tend to remain with the same hand (clumpy) or alternate hands more strongly (dealer). They prove an `O(log^4 n)` mixing upper bound for fixed parameters.

Relevance: a strong candidate for the second local-shuffle model after GSR. It directly represents clumping instead of compressing "shuffle quality" into one ad hoc efficiency number.

### Biased cuts

Jason Fulman, *The combinatorics of biased riffle shuffles*, 1998; arXiv:math/9712240.

- https://arxiv.org/abs/math/9712240

Sami Assaf, Persi Diaconis, and Kannan Soundararajan, *Riffle shuffles with biased cuts*, DMTCS Proceedings, 2012; arXiv:1112.2650.

- https://arxiv.org/abs/1112.2650
- https://doi.org/10.46298/dmtcs.3053

These show that persistent cut bias is already a mathematically developed problem. We should not claim novelty for "humans do not cut exactly 50/50."

### General cut-size distributions

Mark Sellke, Jialu Shi, and Jiamin Wang, *Universality of Cutoff for Riffle Shuffling*, arXiv:2510.22783 (2025).

- https://arxiv.org/abs/2510.22783

This extends cutoff analysis to broad pile-size distributions and deterministic/random sequences of pile sizes, still under a uniform interleaving model. It makes it especially important to keep **cut imbalance** distinct from **clumping / untouched chunks**.

### Block shuffle dynamics

Evita Nestoridi, Amanda Priestley, and Dominik Schmid, *The S_k Shuffle Block Dynamics*, ALEA 21 (2024), 1547--1566; arXiv:2304.02588.

- https://arxiv.org/abs/2304.02588
- https://doi.org/10.30757/ALEA.v21-58

At each step, a contiguous block of `k` cards is chosen and perfectly uniformly shuffled. This is a close neighbor of a working-set constraint, but it again treats local randomization as an oracle operation and uses a different block-selection protocol.

### Unequal Bernoulli--Laplace urns

Thomas Griffin, Bailey Hall, Jackson Hebner, David Herzog, Denis Selyuzhitsky, Kevin Wong, and John Wright, *Cutoff in the Bernoulli-Laplace Model With Unequal Colors and Urn Sizes*, arXiv:2308.08676.

- https://arxiv.org/abs/2308.08676

This is relevant to the 50/49 Commander split. It treats two unequal urn sizes and exchange of `k` uniformly sampled elements from each urn, including spectral analysis used by our first-mode calculation.

### Book-length overview

Persi Diaconis and Jason Fulman, *The Mathematics of Shuffling Cards*, AMS, 2023.

- https://doi.org/10.1090/mbk/146

This should be treated as a general map of established shuffle models and terminology.

## What appears to remain open / at least not directly treated

The project should avoid a broad "first cost-aware shuffle" claim. Cost-aware kernel selection and scan-order optimization exist in general Markov-chain / MCMC literature.

The narrower problem is:

- finite deck size `N`;
- physical working-set bound `m < N`;
- local shuffle kernel `R_theta` that is not an oracle uniform permutation;
- cross-working-set operations `X_k` that change which cards can interact;
- heterogeneous physical costs `c_R` and `c_X(k)`;
- finite protocol `sigma` selected to minimize total cost;
- quantitative terminal requirement such as total-variation distance at most `epsilon`.

Symbolically,

```
sigma = R^(r0) X_(k1) R^(r1) X_(k2) ... X_(kq) R^(rq)
```

and we seek

```
min_sigma cost(sigma)
subject to distance(delta_start K_sigma, Uniform) <= epsilon.
```

The GSR working-set version is the clean first target. The clumpy-human version is the more realistic follow-on.

## Novelty language to use carefully

Reasonable provisional wording:

> We study shuffling under a physical working-set constraint, where local randomization is achieved by repeated finite-cost riffle shuffles rather than by an oracle uniform shuffle. We assign distinct costs to local shuffles and operations that transfer cards between working sets, and optimize finite protocols for minimum cost at a prescribed distance from uniformity.

Do **not** currently claim:

- first mathematics of shuffling large decks;
- first imperfect-riffle model;
- first biased-cut model;
- first partial/block-deck shuffle;
- first cost-aware Markov-chain optimization;
- first varying-transfer-size Bernoulli--Laplace process.

## Search gaps still worth checking before publication

- dissertations/theses citing Nestoridi--White;
- casino shuffle-procedure optimization (riffle/strip/riffle and automatic shufflers);
- patents or operations-research work on large-deck manual shuffling;
- control of finite Markov chains with action-dependent costs under a terminal mixing constraint;
- exact finite rather than asymptotic work for block-update permutations.
