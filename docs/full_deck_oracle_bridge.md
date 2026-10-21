# Full-deck oracle and physical-exchange models (reference)

**Technical reference updated October 21, 2026.** The active implementation
queue is [lean_plan.md](lean_plan.md), and the next single agent action is in
[agent_handoff.md](agent_handoff.md). This document describes the models
and proof boundaries; it is **not a second roadmap**.

## State space and projection

`CommanderPermutation.Deck` is `Equiv.Perm (Fin 99)`, an ordering of 99
individually named cards. The first 50 positions are the left pile. The
macro observation is the number of original-left card identities among
those positions, represented by `CommanderState = Fin 50`: a value `x`
represents the count `x.val + 1`.

`CommanderPermutation.project_surjective` constructs a real permutation
for every one of the 50 macro values. This solves **existence** of each
fiber, not its size. `FiberDisintegration.fiberLaw` samples uniformly
within a given fiber and recovers the macro observation.

## Three operations that must not be conflated

**Canonical oracle.** `OracleRefinement.oracleStep`: first observe the
current macro count, then take a BL exchange step on counts, then resample
a complete deck from the new count's fiber law. Given a recoverable lift,
`oracle_intertwining`, `schedule_intertwining`, and `run_tv_eq_macro`
follow from kernel algebra. They transport exact macrostate TV values to
TV against the *lifted stationary law*, whether or not that law is yet
identified with uniform on all 99! permutations.

**Physical exchange plus perfect-local shuffle.** Choose a subset of
positions of a fixed size from each pile (uniformly, without replacement),
exchange the selected cards under an explicit pairing, then independently
uniformly reorder **the same cards within each pile**. This retains named
pile membership after the exchange; it does not globally resample the
entire macrostate fiber. The exact Python specification is
`experiments/full_deck_oracle.py`.

A five-card example, initial deck `(0,1,3,2,4)`, gives TV `13/36` between
the one-step physical-perfect and canonical oracle output laws.
**Pointwise kernel equality is false.** Exhaustive 4-, 5-, and 6-card
reference checks instead support the *intertwining from a fiber-uniform
input*: this is the appropriate next Lean theorem.

**Physical exchange plus finite-GSR shuffle.** Replace each perfect local
uniform reordering with an independent finite-label GSR riffle. The proper
one-step TV comparison is with the **physical perfect-local** operation,
not the canonical oracle from an arbitrary ordered input. Its discrepancy
is bounded by the sum of the two local GSR-versus-uniform errors in exact
small-deck reference calculations. The general Lean row-error theorem
remains to be proved.

## Exact cardinalities and stationary law

For `N` named cards, `m` left positions, and `r` originally-left marked
cards, a fiber with `j` marked cards on the left has size

```
choose(r,j) * choose(N-r,m-j) * m! * (N-m)!
```

Reason: choose which cards belong to the left pile, then order the left
and right piles independently. The uniform permutation's projected
probability is this cardinality divided by `N!`, equivalently
`choose(r,j)*choose(N-r,m-j)/choose(N,m)`.

For Commander, `N=99`, `m=r=50`, and `j=x.val+1`. Thus the exact
counting target is

```
|fiber x| = choose(50,x.val+1) * choose(49,49-x.val) * 50! * 49!
```

The remaining Commander-specific Lean premise is declared as
`CommanderFullDeckDisintegration.HasCommanderFiberCounts`:

```
Dist.mass commanderStationary x =
  |fiber x| / |Equiv.Perm (Fin 99)|
```

`FiberDisintegration.stationary_disintegrates_of_mass` proves that **once
this identity holds**, lifting `commanderStationary` by the normalized
fiber law is the uniform complete-deck law, even though fibers have
different sizes. The Python code checks the 99-card integer identities
exactly, but no such check replaces this missing Lean counting proof.

## What exact 2-/3-exchange results currently mean

`CommanderFullDeckDisintegration.two_oracle_exchanges_uniform_of_counts`
and `.three_oracle_exchanges_uniform_of_counts` contain exact rational TV
targets, but explicitly accept `hcounts : HasCommanderFiberCounts`.
The unconditional earlier oracle certificates instead use the **lifted
stationary distribution** as their target. Once F1 discharges the fiber
count, these specializations become unconditional **ideal oracle**
full-deck uniform TV theorems.

Two ideal 25-position exchanges:

```
12255318415559330995522631403472464258192877
------------------------------------------------
4933350368865509640837610315994582805439728012
```

Three ideal 25-position exchanges:

```
172379525755689183991816396516567920780192827919620440221147749
--------------------------------------------------------------------
6691837923759692633601708022649918108038775216019298375918637677488
```

A physical perfect-local theorem needs **more than F1**. The existing
`PhysicalExchangeReduction` and
`CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_of_counts`
reduce it to the membership factorization and the named-membership
exchange law. F2 and F3 in the active plan specify those obligations.

## Verification boundaries

The user confirmed the earlier bridge modules through `CommanderPermutation`
compile. The October 21 fiber/disintegration extension, including its final
v3 correction, is also compiled under the user's established completion
workflow. Its 35 Python tests passed. The counting and physical-exchange
hypotheses remain mathematically open.

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

For current mathematical priorities, follow
[lean_plan.md](lean_plan.md), not older checklists embedded in previous
tranche notes.
