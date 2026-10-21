# Commander fibers, disintegration, and membership reduction

**Technical design reference, October 21, 2026.** This describes the
implemented Lean interfaces and the hypotheses still required. For the
**active order of work** use [lean_plan.md](lean_plan.md), starting at
[agent_handoff.md](agent_handoff.md).

## 1. Every macro fiber has a concrete deck witness

`Shufflemath/CommanderFiberWitness.lean` constructs a real permutation of
all 99 card identities for each `x : Fin 50`: rotate the identity deck by
`49 - x.val`. The first 50 positions then contain exactly `x.val + 1`
original-left identities. `deckForCount_projects_all` checks 50 concrete
instances with `native_decide`, **not** all 99! permutations.

`CommanderPermutation.project_surjective` removes the prior requirement
that callers supply an inhabitation proof. It enables recovery of the
macrostate from a normalized full-deck fiber law. It does **not** prove
that the 50 fibers have the hypergeometric relative sizes.

## 2. Generic finite uniform disintegration

`Shufflemath/FiberDisintegration.lean` provides, for any surjective
observation `observe : beta -> alpha` between suitable finite types:

- `fiberSet observe x`: the microscopic states with observation `x`;
- `marginalLaw observe`: exact mass `|fiber x| / |beta|`;
- `fiberLaw observe hsurj`: exact mass `1/|fiber x|` within that fiber,
  zero outside;
- `fiberLaw_recovers`: the conditional law followed by deterministic
  observation is the identity macro kernel;
- `marginal_comp_fiber_eq_uniform`: the cardinality-weighted mixture of
  these conditional laws is exactly uniform on all microscopic states;
- `stationary_disintegrates_of_mass`: an arbitrary macro law with these
  masses also lifts to uniform.

Unequal fiber sizes are allowed. The proofs use finite sum algebra rather
than complete-permutation enumeration.

## 3. Unproved Commander counting premise

`Shufflemath/CommanderFullDeckDisintegration.lean` defines
`HasCommanderFiberCounts` with the precise required condition:

```
for every x : CommanderState,
  mass commanderStationary x =
    |{ decks with project deck = x }| / 99!
```

To discharge it, count the eligible named-card memberships and the
within-pile orderings separately:

```
|fiber x| = choose(50,x.val+1) * choose(49,49-x.val) * 50! * 49!
```

Then divide by `99!` and identify the resulting rational expression with
`commanderStationary`. The independent Python reference checks this exact
formula for all 50 states, but that does **not** prove it in Lean.

After the count is proved, the existing conditional
`commander_uniform_disintegration`,
`two_oracle_exchanges_uniform_of_counts` and
`three_oracle_exchanges_uniform_of_counts` can be specialized without
`hcounts`. That closes the **ideal oracle** uniform-TV target only; it does
not close the physical-exchange theorem.

## 4. Physical exchange requires an intermediate named-membership state

`Shufflemath/PhysicalExchangeReduction.lean` uses three levels:

```
macro count --membershipLift--> named-card pile membership
            --localLift--> complete ordered deck
```

The second lift produces random within-pile orderings while holding
membership fixed. A real local pile shuffle cannot replace that map by
an arbitrary fresh deck with the same *count*: doing so changes which
specific card identities are in which pile.

The generic reduction proves that a raw position exchange plus perfect
local resampling intertwines with the BL macro chain **if**:

1. `localLift` recovers its membership (`hLocalRecovers`);
2. `membershipLift ; localLift` equals the macro count-fiber lift
   (`hfactor`);
3. the raw exchange started from a uniform count fiber produces the
   prescribed membership-level transition (`hMembershipExchange`).

These are *premises*, not silently discharged lemmas. The Commander
physical-perfect 2-step theorem also requires `HasCommanderFiberCounts`.
The exact small-deck reference exhaustively checks membership
intertwining on 4-, 5-, and 6-card cases. It is not a proof for 99 cards.

## 5. Recommended decomposition for the next agent

1. **V0:** verify the latest `FiberDisintegration` v3 one-line parser fix
   with the targeted build below; a successful build has not yet been
   reported after that correction.
2. **F1:** prove the exact Commander count, using a fixed-membership
   `50! * 49!` bijection and independent combinatorial membership count.
3. **F2:** give a concrete `Membership`, `membershipLift`, and `localLift`
   with factorization and recovery proofs.
4. **F3:** define the uniform 25-position raw exchange and prove the
   membership transition to discharge `hMembershipExchange`.
5. **F4:** compare finite-GSR local shuffles with the physical
   perfect-local reference; combine using weighted TV telescope.

Full acceptance criteria and dependency notes are maintained **only** in
[lean_plan.md](lean_plan.md). Do not start new proofs from this reference's
short list alone.

## Verification

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

At overlay creation, 35 Python tests passed, including 50 deck-witness
checks, exact small-deck uniform mixtures, and membership exchange
checks. Prior to the final v3 source correction, the latest Lean build
failed on a parser error in `FiberDisintegration.lean`. Do not infer the
v3 compilation result from that earlier log.
