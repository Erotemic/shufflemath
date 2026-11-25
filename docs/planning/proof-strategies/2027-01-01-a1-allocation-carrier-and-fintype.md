# G5 / T5 — A1 allocation carrier: landed, and the Fintype solution

Date: 2027-01-01 (G5 continuation). Status: **A1.1 DONE** (committed `1728342`);
A1.3 (the actual exchange operation) is the next increment.

## What landed: `Shufflemath/FiniteDeck/MultiExchange.lean`

A new module defining the A1 allocation carrier, general `N`, arbitrary number
`p` of piles, fixed capacities `n : Fin p → Nat`:

- `pAlloc n o` — pile `i` of owner function `o : Fin N → Fin p` holds exactly
  `n i` cards.
- `Allocation (N p n) = { owner : Fin N → Fin p // pAlloc n owner }` — the
  carrier, in the **owner-function** representation.
- `Fintype (Allocation N p n)` — **explicit** instance (see below).
- `Allocation.pileCard` — trivial capacity lemma.
- `pileOwner P hP x` / `pileOwner_iff` — a card's unique pile in a partition.
- `Allocation.ofPartition` / `nonemptyOfPartition` — **inhabitation by a
  positional partition**: any `IsPartition P` yields an allocation with
  capacities `(P i).card`.

Added to the aggregator `Shufflemath.lean`. `lake build` + the full
`./dev/verify_next_phase.sh` pass (37 tests OK); the new module is warning-free.

## THE KEY INSIGHT: the carrier's Fintype, and why the product route died

**Dead end (confirmed by probe):** a dependent product of `Finset` carriers,
`∀ i, {S // S.card = n i ∧ ...}`, has **no `Fintype` instance** in Mathlib.
`Fintype.pi` (Pi.lean:307) is scoped to `[Fintype (f i)]` — and no such
instance exists for `Subtype (Finset (Fin N))`. So `card` of the allocation
space is not even stated.

**The fix (what actually works):** use the **owner-function** representation,
whose ambient type `Fin N → Fin p` carries the *ordinary* finite-product
`Fintype` (Pi.lean:141, `Fintype.prod`/`fintypeEquivFun`). The allocation is a
**subtype** of that finite type, and `Fintype.subtype` (Defs.lean:270) gives
the `Fintype` of the subtype from a `Finset` witness of its predicate:

```lean
noncomputable instance : Fintype (Allocation N p n) :=
  Fintype.subtype (Finset.univ.filter (pAlloc n))
    (fun o => by simp [Finset.mem_univ])
```

No `native_decide`, no enumeration, no axiom. This is the clean, reusable
solution to the "Finset-family Fintype wall" that has blocked every multi-pile
counting attempt since 2026-08-20 (see `g5-multipile-state-and-walls.md`).

## A1.3 (next): the actual exchange operation

Define, over `Allocation N p n`:
- `exchangeChoice (A A' : Allocation N p n)` — the choices taking `A` to `A'`
  (which named cards move between which piles), a `Fintype`.
- `update (A) (c : exchangeChoice A A') : Allocation N p n` — the deterministic
  move (must satisfy `update A c = A'` on valid choices).
- `exchangeKernel : FiniteKernel (Allocation N p n) (Allocation N p n)` — the
  **stochastic** map (a `Dist (Allocation …)` per state), built by averaging
  over the choices (e.g. uniform over `exchangeChoice`, or the fixed exchange
  law). Show it is **stochastic** (sums to 1).
- **A1.4** then: the kernel is **invariant under relabeling** (a `Perm (Fin N)`
  acting on owners preserves the kernel), and uniform `⊗` invariant is
  **stationary** via `symmetric_stationary` (Finite.lean:1836).

A **concrete example** (a small `N`, `p = 2`, capacities `(1, 1)`) must be
included as a sanity witness (handoff §0 item 3, §2 "Do not accept a claim").

## Constraints (repeated from the handoff)
- Do not weaken, bypass, or weaken the proof.
- General `N`; arbitrary `p`; fixed `n`.
- Do not use the dependent product of `Finset` allocations as the carrier.
- Do not duplicate the already-proved two-pile kernel machinery — reuse
  `TwoPile.exchangeKernel` / `MultiPileExchange` where applicable.
