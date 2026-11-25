# T5 — column-sum / reversibility & multivariate-hypergeometric stationary law (WIP, 2026-07-07)

**Status:** the two-pile exchange kernel is **well-defined on the state space**
(`exchangePairFiberMP`), **symmetric** (`exchangeTargets_symmetric`), and
**row-stochastic** (`twoPileTransitionStochastic`) — all landed in
`Shufflemath/FiniteDeck/MultiPileExchange.lean`.  This note captures the two
remaining T5 steps and the exact wall the next session should attack.

## What is done (committed)

- `FiberMP (N m n)` — the allocation-level state space: disjoint `(m,n)`-pairs of
  piles in an `N`-card deck.
- `exchangePairFiberMP` — a `k`-exchange of two disjoint `(m,n)`-piles lands
  again on a disjoint `(m,n)`-pair (size-preserving + disjointness-preserving),
  i.e. the exchange kernel is a **self-map of the state space**.
- `exchangeTargets_symmetric` — the number of `k`-exchanges `(A,B) → (A',B')`
  equals the number `(A',B') → (A,B)` (swap of the leaving sets is a bijection;
  `swapLands` + `exchangePair_involution`).
- `twoPileExchangeTotal` / `twoPileTransitionStochastic` — the normalized
  transition has **row-sum 1** (numerator `= choose (∑X) k · choose (∑Y) k`).

## Remaining step 1: column-sum (reversibility)

**Goal:** the kernel is column-stochastic / reversible, i.e. for a target
`(A',B')` of sizes `(m,n)`,

```
∑_{p ∈ valid(m,n)-pairs} #(exchangeTargets p → (A',B'))  =  choose m k · choose n k.
```

**Route (established, not yet landed):**
1. By `exchangeTargets_symmetric`, this equals
   `∑_p #(exchangeTargets (A',B') → p)` — a sum of **fiber sizes** of the map
   `g : D → stateSpace`, `D = powersetCard k A' ×ˢ powersetCard k B'`,
   `g q = exchangePair (A',B') q.1 q.2`, over `p`.
2. The fibers `D.filter (g q = p)` are pairwise disjoint (a `q` maps to one `p`)
   and their union is `D` (every `q ∈ D` maps to some valid `p`, by
   `exchangePairFiberMP`).  Hence the sum of fiber sizes `= #D` by
   `Finset.card_biUnion` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`).
3. `#D = choose m k · choose n k` by `Finset.card_powersetCard` (needs
   `k ≤ m`, `k ≤ n`, which follow from `D` being nonempty-relevant / the
   `choose` convention; guard with the `hKm`, `hKn` subset→card facts).

**The wall (Fintype context-dependence):** the fiber sum must be indexed over the
valid `(m,n)`-pairs.  `Fintype (FiberMP N m n)` synthesizes when `N m n` are
`variable`s but **fails when they are explicit `theorem` parameters** (observed:
`#check @Fintype (FiberMP N m n)` OK with `variable {N m n}`, `unsolved` inside
the theorem).  The robust workaround: **index the biUnion over the base type**
`Finset (Fin N) × Finset (Fin N)` (its `Fintype` synthesizes for general `N`
— verified) **filtered to the valid predicate**, and show the invalid entries
contribute 0 (their fiber is empty, since `g q` is always a valid pair by
`exchangePairFiberMP`).  Two further Lean subtleties hit on the way:
- `dsimp`/`rw` do **not** unfold local `let` bindings; use `change` (definitional
  equality) to expand `let D`/`let g` to the explicit `powersetCard ×ˢ …` term.
- The product eta: write the fiber predicate as `g q = (p.1, p.2)` (matches
  `exchangeTargets` definitionally) rather than `g q = p`.

## Remaining step 2: multivariate-hypergeometric stationary law

Show the uniform distribution on `FiberMP N m n` is invariant under the
exchange kernel (reversibility + row-stochasticity give this: a symmetric
row-stochastic kernel preserves the uniform).  Package as
`uniformExchangeInvariant` / `stationaryUniform`.  Depends on step 1.

**Suggested next session:** start a probe
`Shufflemath/_ProbeT5col.lean` with the base-type-filtered biUnion (step 1),
using `change` for the let-expansion and `Finset.card_biUnion` for the
pairwise-disjoint-fiber = total-card step.
