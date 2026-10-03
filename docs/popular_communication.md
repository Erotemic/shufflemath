# Popular communication plan

## Core message

"Seven shuffles" is not a universal magic number. It is a result for a particular idealized riffle model and a standard 52-card deck. For real card games, the best protocol depends on:

- deck size;
- how many cards you can comfortably manipulate at once;
- whether your cards fall in clumps;
- whether an end packet tends not to participate;
- how long local shuffles take;
- how long recombining and repartitioning takes.

The goal is not to label someone a good or bad shuffler. The goal is to identify what their physical operation actually does and prescribe a protocol that compensates for it.

## 30-second Magic-player version

1. If you can comfortably mash the whole deck, use the whole deck; do not repeatedly shuffle two fixed halves.
2. If Commander is too large to hold, cards must migrate between your working packets.
3. For a 50/49 split, moving about 25 cards between working sets is mathematically motivated by Bernoulli--Laplace mixing.
4. If rebuilding the deck is slow, it can be efficient to do several local mashes before changing working sets.
5. The exact counts should come from a model/measurement rather than copying the 52-card "seven" rule.

## Candidate interactive tool

Inputs:

- deck size (40, 60, 99, custom);
- comfortable working-set size;
- time for one local mash;
- time for a repartition/recombine operation;
- optional measured cut/clump/tail diagnostics;
- desired randomness threshold.

Output:

- exact sequence of physical actions;
- estimated/certified model distance from uniform;
- total expected time;
- comparison with a few common alternatives;
- caveat describing the shuffle model used.

## Demonstration experiment

Use two visibly distinct groups of sleeved/proxy cards.

For a manageable test packet:

1. place colors/types in known blocks;
2. perform one normal mash;
3. record the resulting source-label sequence;
4. repeat 10--20 times;
5. summarize cut ratio, run lengths, and untouched ends.

A sequence such as

```
A B A B B A A B ...
```

contains information about interleaving quality. A sequence with long runs such as

```
A A A A B B B A A A ...
```

reveals clumping that a cut-ratio measurement alone misses.

## Communication rules

- Never say that pile shuffling by itself randomizes a deck.
- Separate tournament legality from mathematical randomization.
- Avoid presenting a model-specific number as universal.
- State whether a number is exact, simulated, asymptotic, or heuristic.
- Make accessibility a first-class case: smaller working sets should be supported directly rather than treated as a failure mode.
