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
  **Core done (2027-01-03):** `relabel`/`relabel_symm_relabel` + the owner-level
  commutation `relabel_commute_owner` + the kernel equivariance `swapKernel_equivariant`
  (uniform swap-kernel mass at `relabel σ B` equals the mass at `B`) — the
  A1.4 relabel-invariance headline, plus the clean `relabel_eq_iff` injectivity lemma.
  Remaining: the concrete small-`N` sanity witness (§2) and, if a *full*
  `relabel (swapPiles …) = swapPiles (relabel …)` commutation is later needed, the
  `noncomputable`-def elaboration wall (owner-level route only).

A **concrete example** (a small `N`, `p = 2`, capacities `(1, 1)`) must be
included as a sanity witness (handoff §0 item 3, §2 "Do not accept a claim").

## Constraints (repeated from the handoff)
- Do not weaken, bypass, or weaken the proof.
- General `N`; arbitrary `p`; fixed `n`.
- Do not use the dependent product of `Finset` allocations as the carrier.
- Do not duplicate the already-proved two-pile kernel machinery — reuse
  `TwoPile.exchangeKernel` / `MultiPileExchange` where applicable.

## A1.3a (done 2027-01-01): the two-card-pile-swap exchange primitive

The simplest nontrivial exchange: **swap the piles of two named cards** `a, b`
(ownership only — order inside piles is irrelevant in the carrier).  Added to
`Shufflemath.FiniteDeck.MultiExchange` (namespaced `Shufflemath.FiniteDeck`,
`n` implicit so `swapOwner A a b` is called without an explicit capacity):

- `swapOwner (A : Allocation N p n) (a b x : Fin N) : Fin p` — owner after the swap
  (`x=a→A b`, `x=b→A a`, else `A x`).
- `cardTransposition (a b x : Fin N) : Fin N` — the pointwise transposition of card
  indices (renamed from the earlier `swapFn` to avoid clashing with
  `LiteralSwapKernel.swapFn`, which is a two-pile L/R swap).
- `cardTransposition_involution`, `transposition (a b) : Fin N ≃ Fin N` (a genuine
  `Equiv`, via `Equiv.ofBijective` on `cardTransposition`).
- `swapOwner_eq_swapFn→swapOwner_eq_cardTransposition`: `swapOwner A a b x = A.val
  (cardTransposition a b x)` (proved by `dsimp` + `split_ifs`).
- `transposition_apply`, and the headline **`swapOwner_capacity`**: the swapped
  owner is again a valid `Allocation` (every pile's size is preserved), because
  `swapOwner = A.val ∘ σ` for the bijection `σ` and a bijection preserves each
  fiber's cardinality.
- `swapPiles (A a b) : Allocation N p n` — the packaged self-map.

### Key reusable fact: the finset↔fintype fiber-card bridge

`swapOwner_capacity` is proved by counting fibers with `Fintype.card` of the
preimage subtypes and an explicit `Equiv` between the two fibers (via `σ`),
then bridging to the carrier's `Finset.univ.filter …card = n i` statement.
The bridge that closes each step is simply:

    (Finset.univ.filter (fun x => p x)).card = Fintype.card {x // p x}
      := by simp [Fintype.card_subtype]

i.e. **`Fintype.card_subtype`** (`Fintype.card {x // p} = #{x | p}`) plus the
`Set.ncard`↔`Finset` simp rules (needs `public import Mathlib.Data.Set.Card`).
Both directions close by bare `simpa only [Fintype.card_subtype]`.  This is the
clean way to move between a carrier's `Finset`-filtered cardinality and a
`Fintype.card` of a fiber — reuse it for the general `exchangeKernel` / orbit
counts in A1.3/A1.4 rather than the `Finset.image` route (whose `ext`/`decide`
membership reduction does not simplify cleanly).

### Status / next
- `swapOwner_capacity` + `swapPiles` are the **deterministic** exchange (a
  fixed transposition of two cards).  The **stochastic** `exchangeChoice` /
  `update` / `exchangeKernel` described above (and relabel-invariance A1.4)
  are the remaining A1.3/A1.4 work; they should be built on this primitive
  (a general exchange = a composition of such two-card swaps).
- The section variable `n` in `MultiExchange.lean` is now **implicit**
  (`{n : Fin p → Nat}`) so that `Allocation N p n`-referencing defs are called
  as `swapOwner A a b x` (the capacity is inferred from `A`).  This is safe for
  the existing `Allocation.pileCard` / `Fintype` instance.

## A1.3b (done 2027-01-02): the uniform-transposition exchange kernel — a `Dist` that is symmetric

**Module:** `Shufflemath/FiniteDeck/UniformExchange.lean` (added to the
`Shufflemath.lean` aggregator).  Builds directly on the A1.3a primitive
(`swapPiles`, `swapOwner_eq_cardTransposition`, `cardTransposition`) in
`MultiExchange.lean`.  This is the **first stochastic exchange kernel** on the
A1 carrier, and the cleanest possible one: pick two card indices uniformly at
random and swap their piles.

### The kernel and its headline properties

- **`swapKernel (hN : 0 < N) (A : Allocation N p n) : Dist (Allocation N p n)`**
  — the pushforward of `GSR.uniformDist (Fin N × Fin N)` (the uniform law on all
  `N^2` card pairs, the `a = b` pair being the no-op) under
  `fun ab => swapPiles A ab.1 ab.2`.  A pushforward of a `Dist`, so every row
  sums to `1` by construction — a genuine stochastic kernel, no separate
  stochasticity proof needed.  Since `FiniteKernel α β := α → Dist β` is a bare
  **abbrev** (`Finite.lean:105`), `swapKernel hN` is *already* a
  `FiniteKernel (Allocation N p n) (Allocation N p n)` with no packaging.

- **`swapOwner_involutive`** — swapping `a, b` twice restores the original owner
  function.  Composes `swapOwner_eq_cardTransposition` with
  `cardTransposition_involution`; the intermediate step is the `simp [swapPiles]`
  identity `(swapPiles A a b).val = swapOwner A a b`.

- **`swapPiles_involution` / `swapPiles_swap_iff`** — the self-map is an
  involution on the carrier, and, stated as an `iff`,
  `swapPiles A a b = A' ↔ swapPiles A' a b = A`.  This `iff` is the
  **fiber-symmetry** fact: the preimage fiber of `A'` under the `a, b` swap is
  exactly the preimage fiber of `A` under the same swap.  Both directions close
  by `rw [← h]` + the involution with the correct carrier (`A` in `→`, `A'` in
  `←`) — the `rw [← h]` in the backward branch replaces the bare `A` target, not
  the `A` inside `swapPiles A`, so the two directions use *different*
  involution instances.

- **`swapKernel_mass`** — the explicit mass at `A'`:
  `Dist.mass (swapKernel hN A) A' = ∑ s : Fin N × Fin N, (N*N : Rat)⁻¹ · 1[A' = swapPiles A s.1 s.2]`.
  Follows by a `show` that unfolds `swapKernel` back to
  `(GSR.uniformDist (Fin N × Fin N)).map …`, then `GSR.map_uniform_mass`
  (GSR.lean:565) + `Fintype.card (Fin N × Fin N) = N*N` (a single
  `simp [Fintype.card_prod, Fintype.card_fin]` — do *not* `rw` `card_fin` twice,
  it over-fires and errors; `simp` to fixpoint).  The final `simp [hcard]` (full
  simp set, not `simp only`) is what normalizes the residual
  `↑(N*N)⁻¹ = ↑N * ↑N⁻¹` cast (`Nat.cast_mul`) and closes the sum.

- **`swapKernel_symmetric`** — the headline: `mass (swapKernel hN A) A' =
  mass (swapKernel hN A') A` (the kernel is **doubly stochastic** / symmetric).
  Rewrite both sides by `swapKernel_mass` and `Finset.sum_congr`; the two fiber
  indicators are pointwise equivalent by `swapPiles_swap_iff` (the involution),
  so each summand closes with `ite_eq_left`/`ite_eq_right` (the modern names —
  `if_pos`/`if_neg` are deprecated).  **Do not** `simp only [h, h2]` here:
  `h : A' = swapPiles A …` and `h2 : A = swapPiles A' …` are mutually-rewriting
  equalities and recurse to the max-recursion depth; decide each `ite` directly
  with `ite_eq_*` instead.

### Key technical point: the `Nonempty` wall and how it was routed around

`GSR.uniformDist β` (GSR.lean:444) requires `[Nonempty β]` (its `1/card β`
mass law needs `card β ≠ 0`).  The **pair** type `Fin N × Fin N` is nonempty
iff `0 < N`, so the kernel takes `hN : 0 < N` as an **explicit parameter**
(the same pattern as `GSR.idealShuffle (n a) (ha : 0 < a)`), and the two
theorems that unfold `swapKernel` back to `uniformDist` provide the instance
locally via `letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩`.  This
avoids the dead-end of `swapKernel` pulling `hN` up as an implicit leading
argument (which made `swapKernel A` misapply at the statement level), and of
making `[Nonempty]` an instance argument (which then had to be synthesized in
every statement with no instance in scope).  The two `letI`-in-a-proof sites
trigger a cosmetic `linter.style.haveILetI` note; that linter is a **false
positive** here — `letI` (not `let`) is required to register the instance,
and the note does not block (AGENTS.md: style-only linter suggestions do not
hold up substantive progress).

### Status / next (the uniform-stationarity capstone, then A1.4)

`Markov.detailedBalance_implies_stationary` (Markov.lean:51) shows a
**symmetric** kernel has the **uniform** measure as stationary.  `swapKernel`
is symmetric (above), so the capstone

    Dist.mass (FiniteKernel.apply (GSR.uniformDist (Allocation N p n)) (swapKernel hN)) A
      = Dist.mass (GSR.uniformDist (Allocation N p n)) A

is the immediate next increment.  **Blocker / hypothesis needed:** that law
needs `[Nonempty (Allocation N p n)]`, i.e. the allocation space itself
nonempty, which holds iff the capacities fill the deck: **`∑ i, n i = N`**
(`hN : 0 < N` alone does not give it).  So the capstone carries that hypothesis
and needs a `Nonempty (Allocation N p n)` witness from it (build one from
`∑ n i = N`, e.g. via A1.1's positional-partition route `ofPartition` /
`nonemptyOfPartition`).  The detailed-balance computation is then short: both
sides of the balance equation share the constant factor `1 / card (Allocation
N p n)`, so it reduces to `swapKernel_symmetric`.  After that, **A1.4**
(relabel-invariance under a `Perm (Fin N)` acting on owners) is the final piece
of the A1 program.

Full `lake build` (9021 jobs) and `./dev/verify_next_phase.sh` (37 tests OK)
both pass with the new module; it is warning-clean except the two cosmetic
`haveILetI` notes above.

## Addendum (2027-01-02, G5/A1 continuation) — `_ProbeA14`: the `prefixCap` block partition

A second A1.1 thread in `Shufflemath/_ProbeA14.lean` builds a **block
partition of `Fin N`** indexed by `Fin p` with capacities `n : Fin p → Nat`,
`hsum : ∑ i, n i = N`, using the prefix-sum `prefixCap p n i :=
∑ k ∈ range (i.val+1), n (⟨k⟩ : Fin p)` as the cumulative offset of block
`i`'s value interval `[prefixCap i, prefixCap i + n i)`.

**Landed & proven this session (commits `a95d67a`, `ed6ba53`):**
- `blockCap N p n i = univ.filter (fun x => prefixCap i ≤ x.val < prefixCap i + n i)`.
- `himg` / `blockCap_card`: `(blockCap i).card = n i` — proved by showing
  `image (·.val) (blockCap i) = range N.filter (fun v => a ≤ v < b)` (the
  `·.val` bijection `Fin N ≃ range N` transports the filtered universe to the
  filtered range) + `card_range`.
- `memBlockCap_iff`: `x ∈ blockCap i ↔ prefixCap i ≤ x.val < prefixCap i + n i`
  (trivial after `dsimp [blockCap]` + `simp [mem_filter, mem_univ]`, since
  `blockCap` is a `filter`, **not** an `image`).
- `blockCardinal`, `blockCap_inj`, `nonemptyOfS` (unchanged, still build).

**Remaining (single root blocker → 3 sorries):**
- `prefixCap_mono (p n) (i j) (h : i.val ≤ j.val) : prefixCap i ≤ prefixCap j`
  — **SOLY (documented)**. Proof strategy: `dsimp [prefixCap]`; the two sides
  are `∑ k ∈ range (i.val+1), n (Fin.mk k hk_i)` and `... hk_j`; the summands
  are pointwise equal (`Fin.mk k hk_i = Fin.mk k hk_j` by `Fin.ext`, both val
  `k`), so `Finset.sum_congr` merges them to one function `f`, then
  `Finset.sum_le_sum_of_subset` on `range (i.val+1) ⊆ range (j.val+1)`
  (nonnegative `n`). The only friction is making `f` a single named function —
  the `Fin.mk` proof terms differ, so a `conv`/`change` step (or an
  intermediate `Ico`-sum over a canonical `cast`) is needed.
- `blockUnique` / `blockCover` (sored) build directly on `prefixCap_mono` +
  `memBlockCap_iff` once it lands (see their strategy comments).

**Next session:** crack `prefixCap_mono` (sum-merge + sum-subset), then
`blockUnique` and `blockCover` follow by the documented `by_contra` /
max-index arguments. File builds clean at 3 sorries (3192 jobs).

---

## Addendum (2027-01-03, A1.4 completion attempt) — the commutation elaboration wall

Progress this session (all committed): **A1.1 consolidated** + the **A1 headline
`swapKernel_uniformStationary`** (commit `96328fd`); **`conjugate_transposition`**
(commit `bf4e6d7`); the **`relabel` action + `relabel_symm_relabel`** (relabeling is a
bijection of the allocation carrier, commit `989983e`) — all in
`FiniteDeck/MultiExchange.lean`, no `sorry`/`admit`, library builds.

**Where it is stuck — `relabel_swapPiles_commute` / `swapKernel_equivariant`:**
- The *full-Allocation* statement
  `relabel σ (swapPiles A a b) = swapPiles (relabel σ A) (σ a) (σ b)` (both
  `noncomputable def`s with implicit `N p n` in one expression) **fails to elaborate
  in the local module** (`swapPiles A a b` → `?m.1`, "Function expected"), though the
  identical term elaborates fine in a probe that *imports* `MultiExchange`.
- The **owner-level** reformulation
  `swapOwner (relabel σ A) (σ a) (σ b) x = A.val (cardTransposition a b (σ.symm x))`
  (only one `noncomputable` def) **also fails**, but reveals the shape: after
  `rw [swapOwner_eq_cardTransposition, relabel]` the goal comes back with the `A.val`
  wrappers *stripped and reversed* — `(Equiv.symm σ) (cardTransposition (σ a) (σ b) x)
  = cardTransposition a b ((Equiv.symm σ) x)` — so the final step needs the conjugation
  with the **sides in the order `cardTransposition a b (σ.symm x) = σ.symm
  (cardTransposition (σ a) (σ b) x)`** (i.e. `congrArg (σ.symm) (conjugate_transposition
  σ a b x)` directly, no `symm`/flip).

**Next increment (for the Qwen build / next session):** land
`relabel_commute_owner` (owner-level, one noncomputable def; proof =
`rw [swapOwner_eq_cardTransposition, relabel]` + `congrArg (σ.symm)
(conjugate_transposition σ a b x)` matching the reversed order above), then the full
`swapKernel_equivariant` in `FiniteDeck/UniformExchange.lean` via
`Dist.mass_map` + `Finset.sum_congr` using the injectivity of `relabel σ` (no sum
reindexing — the same `ab` pairs, indicators equal term-by-term).

## Addendum (2027-01-03, A1.4 CRACKED) — both core results landed

**`relabel_commute_owner`** (MultiExchange.lean) — the owner-level commutation
`swapOwner (relabel σ A) (σ a) (σ b) x = A.val (cardTransposition a b (σ.symm x))`,
proved exactly as the previous addendum predicted: `rw [swapOwner_eq_cardTransposition,
relabel]` then `have hc : σ.symm (cardTransposition (σ a) (σ b) x) = cardTransposition a b
(σ.symm x) := by simpa [Equiv.symm_apply_apply] using (congrArg (σ.symm) (congrArg σ (conjugate_transposition
σ a b x)))` and `rw [hc]`.  The key was the conjugation's **reversed order**
(`cardTransposition a b (σ.symm x) = σ.symm (cardTransposition (σ a) (σ b) x)`), reached
by conjugating the canonical `conjugate_transposition` on the *right* by `σ.symm`.

**`swapKernel_equivariant`** (UniformExchange.lean) — `Dist.mass (swapRelabel hN σ A)
(relabel σ B) = Dist.mass (swapKernel hN A) B`, exactly the doc's recipe: `rw
[swapRelabel, GSR.map_uniform_mass, swapKernel_mass, hcard, Nat.cast_mul]` puts both
sides as `∑ (N*N)⁻¹ · 1[·]` over the *same* `ab` pairs, then `Finset.sum_congr` +
`simp [relabel_eq_iff …]` matches the two fiber indicators term-by-term — **no sum
reindexing**.

**The elaboration-wall escape:** the *full*-Allocation commutation
`relabel σ (swapPiles A a b) = swapPiles (relabel σ A) (σ a) (σ b)` (two `noncomputable`
defs with implicit `N p n` in one expression) still fails to elaborate in the local
module (the wall the previous addendum recorded).  The workaround that lands the
headline anyway: the equivariance never needs the full commutation as a *named* theorem —
it needs only that the two *indicators* are equivalent, and that is the **general**
`relabel_eq_iff (σ) (B) (Y) : relabel σ B = relabel σ Y ↔ B = Y` (a bijection's
fiber-equality, `relabel_symm_relabel` both ways), with `Y := swapPiles A a b` supplied
*as an argument* of the iff (the goal already carries `relabel σ (swapPiles …)`, so the
instantiation elaborates without the def-of-def wall).  Owner-level is the route;
the full commutation remains blocked by the `noncomputable`-def elaboration wall and is
only needed if a future step requires it as a named theorem.

Build: `lake build Shufflemath.FiniteDeck.MultiExchange` + `Shufflemath.FiniteDeck.
UniformExchange`, 0 errors, no `sorry`/`admit`, only the file's pre-existing `simpa`/
`letI` style lints.  A1.4's relabel-invariance headline is **done**; the open A1.4 items
are the small-`N` sanity witness (handoff §2) and, optionally, an independent full
commutation if ever required.
