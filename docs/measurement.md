# Measuring a human shuffle

This document describes a minimal measurement protocol for fitting or bounding a local shuffle model.

## What to measure separately

### Cut ratio

Record the sizes of the two packets just before interleaving.

Do not infer clumping from cut imbalance. They are distinct mechanisms in the literature.

### Source run lengths

Label cards by which hand/packet they originated from and record the left/right source sequence after interleaving.

Useful summaries:

- mean run length;
- run-length histogram;
- probability the next card comes from the same source as the previous card;
- dependence on position in the shuffle.

The Jonasson--Morris `p`-riffle gives a natural first one-parameter model for this correlation.

### Untouched top/bottom tails

Record whether cards at either end repeatedly avoid the active interleave and how many.

Persistent untouched tails are qualitatively different from moderate cut imbalance because the same cards may fail to receive randomness across successive operations.

### Operation time

Measure separately:

- one local riffle/mash of a given packet size;
- recombine/cut/resplit;
- other candidate cross-working-set manipulations.

The optimization objective is elapsed physical cost, so these measurements are not incidental metadata.

## Model-fitting policy

Start with robust intervals rather than overfitting a small sample.

Example:

```
working size: 45--50
same-source transition probability: 0.55--0.65
untouched tail: 0--4 cards with high probability
local shuffle time: 0.9--1.2 s
repartition time: 3.5--4.5 s
```

Then optimize against the worst parameter value in the interval. A later version can use a Bayesian/empirical distribution if enough data exist.

## Data ethics / public tool

If measurements are ever collected from players:

- make upload opt-in;
- store shuffle observations, not identifying information, unless explicitly needed;
- publish the measurement protocol so results can be reproduced independently;
- distinguish sleeve/deck configuration because it changes physical behavior.
