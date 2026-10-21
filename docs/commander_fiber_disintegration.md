# The next 99-card proof tranche: explicit fibers, disintegration, and physical membership

Baseline: source snapshot `9257fa35bb1b`, October 21, 2026. The source
contains verified previous Lean modules, including the compiled
`CommanderPermutation`, `OracleRefinement`, and `PhysicalRefinement` code.
This tranche introduces additional Lean modules; the pinned local build is
required to check their elaboration.

## 1. Every macro fiber is inhabited (new: constructive proof)

`Shufflemath/CommanderFiberWitness.lean` constructs a *permutation of all
99 card identities* for each `x : Fin 50`. Start with deck identities in
ascending order and rotate by `49 - x`. The first 50 positions then contain
exactly `x+1` identities from `0..49`. The source proves the rotation is
an equivalence and checks the 50 projection equalities with `native_decide`.
The check does not enumerate the `99!` permutations or prove existence by
an abstract classical choice.

The theorem `project_surjective` closes the missing premise in the previous
`CommanderPermutation.uniformFiber` definition. Consequently exact
rational 2-step and 3-step oracle TV certificates now have no externally
supplied fiber-existence premise. Their target is the stationary *lifted*
full-deck law, which still needs identification with the uniform law.

## 2. Finite uniform disintegration (new: general theorem)

`Shufflemath/FiberDisintegration.lean` is independent of shuffle-specific
arithmetic. For a surjective observation `observe : beta -> alpha`, it
constructs:

- `fiberSet observe x`: the complete microstate fiber;
- `marginalLaw observe`: probability `|fiber x| / |beta|`;
- `fiberLaw observe hsurj`: mass `1/|fiber x|` at microstates in the
  fiber, zero elsewhere.

The theorem `marginal_comp_fiber_eq_uniform` proves symbolically that
mixing these uniform conditional fibers by their relative cardinalities
gives a **uniform distribution on all beta microstates**. This is a
non-enumerating sum rearrangement and works for unequal fiber sizes.
`fiberLaw_recovers` also proves that deterministic observation recovers the
macrostate, so the earlier isometric lifting theorems apply.

## 3. Exactly one 99-card counting obligation remains

`Shufflemath/CommanderFullDeckDisintegration.lean` packages this as:

```
HasCommanderFiberCounts := for every x : Fin 50,
  mass commanderStationary x =
    |{ full 99-card permutations with project deck = x }| / 99!
```

The generic disintegration theorem proves that this identity suffices for
`commanderStationary ; fiberLaw = uniform(Deck)`. It then derives the exact
2-step and 3-step full-deck uniform TV identities, conditional explicitly
on that one counting theorem. No `sorry`, axiom, or fabricated full-deck
uniform claim is used.

The intended next proof supplies the precise combinatorial count

```
|fiber x| = choose(50, x+1) * choose(49, 49-x) * 50! * 49!
```

and simplifies the fraction by `99!` to the already defined hypergeometric
stationary probability. The exact Python reference checks the formula for
all 50 states but does **not** replace the Lean counting proof.

## 4. Physical exchanges need a three-level refinement

The earlier `PhysicalRefinement` API correctly required *intertwining*;
its premise was still formulated as an abstract full-deck identity.
`Shufflemath/PhysicalExchangeReduction.lean` now decomposes the states as:

```
macro count --membershipLift--> named-card pile membership
            --localLift--> complete ordered deck
```

A perfect local shuffle changes the order *within* each pile, but not the
membership set. It is **not** the oracle that resamples an arbitrary full
deck conditional only on the macro count. (The existing five-card counter-
example distinguishes those two kernels pointwise.)

A raw position exchange followed by true perfect-local resampling
intertwines the macro chain whenever the raw exchange, applied to an input
that is uniform in its macro fiber, produces the correct law on **named-
card membership**. The new theorem proves this implication using exact
finite-kernel associativity. The specialization additionally requires that
`membershipLift ; localLift` equals the normalized full-deck fiber law.

This isolates the next physical combinatorial obligation without assuming
it: prove uniformity of post-exchange membership conditional on the new
count. `experiments/commander_fiber_witness.py` checks that property
exhaustively on decks up to six cards, including every input macrostate.

## Verification and subsequent work

```bash
cd ~/code/shufflemath
lake exe cache get
lake build \
  Shufflemath.CommanderFiberWitness \
  Shufflemath.FiberDisintegration \
  Shufflemath.PhysicalExchangeReduction \
  Shufflemath.CommanderFullDeckDisintegration
./dev/verify_next_phase.sh
```

The Python tests validate the 50 canonical witnesses, exact uniform-mixture
identity on 4--6-card decks, and membership-exchange intertwining on all
small-deck macro-count fibers. They cannot establish a 99-card Lean theorem.

Next most valuable Lean work: discharge `HasCommanderFiberCounts` with a
structural fiber cardinality equivalence; then implement membership and
local uniform laws for `Deck`, prove their factorization, and connect a
specified uniformly selected 25-position exchange to the membership law.
After those are compiled, prove one-step finite-GSR-vs-perfect-local TV
bounds and attach physical-time costs.
