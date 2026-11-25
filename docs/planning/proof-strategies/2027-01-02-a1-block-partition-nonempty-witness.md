# A1 handoff — block-partition Nonempty witness (2027-01-01)

**This is the handoff for the A1 track (allocation-carrier + Fintype +
swap-kernel ergodicity) after the A1.1 territory was mapped.**  Prior sessions
landed A1.1–A1.4 (the Fintype instance + swap-kernel non-triviality + uniform
deterministic pushforward); this session (a) completed **A1.3b** and (b) **mapped
the A1.1 block-partition foundation** (the `Nonempty (Allocation N p n)` witness
from the roadmap's "A1.1 … Nonempty (Allocation N p n)" bullet).

**Committed this session:**
- `1c795c1` **A1.3b** — `swapPiles_pileCounts (hN) A (i,j) = (n.swap (fin i) (fin j)) A`
  (a `Fin 2 × Fin 2` swap is a `Fin p` swap with both indices in `i ⊔ j`, the only
  two piles it touches; the other `p-2` piles match pointwise). Committed inside
  `UniformExchange.lean` and exported via the aggregator.
- `fce942a` **A1.1 block-partition foundation** — `Shufflemath/_ProbeA14.lean`.

---

## A1.1: what builds (all in `Shufflemath/_ProbeA14.lean`, namespace `Shufflemath.FiniteDeck`)

| Declaration | Status |
|---|---|
| `def prefixCap (p : Nat) (n : Fin p → Nat) (i : Fin p) : Nat` | **proven** (def) — cumulative capacity before pile `i`, written as a conditional `Finset` sum over `Fin p` |
| `def blockCap (N p : Nat) (n : Fin p → Nat) (i : Fin p) : Finset (Fin N)` | **proven** (def) — pile `i` = deck positions `x` with `prefixCap i ≤ x.val < prefixCap i + n i` |
| `theorem iteSingleSum (p) (n) (i)` | **proven** — `∑_k (if k = i then n k else 0) = n i` (one-line `simp`) |
| `theorem prefixCap_le_total (N p) (n) (hsum) (i)` | **proven** — **the keystone**: `prefixCap i + n i ≤ N` when `∑ n = N`. Proof: write `prefixCap i + n i` as `∑_k [(if k<i) n k] + [if k=i] n k]` (`iteSingleSum` + `sum_add_distrib`), `= ∑ n = N` (`hsum`), then `sum_le_sum` on a pointwise `≤`. This is the lemma that stuck for ~40 earlier turns (it needed the explicit-`Fin`-sum conditional form, not a `Finset.range i` sum). |
| `theorem blockCap_card (N p) (n) (hsum) (i)` | **2 `sorry`s** (`himg`, `h2`) — body otherwise complete |
| `theorem blockCover (N p) (n) (hsum) (x : Fin N)` | **1 `sorry`** — `∃ i, x ∈ blockCap i` |
| `theorem blockUnique (N p) (n) (hsum) (i j) (x : Fin N)` | **1 `sorry`** — `x ∈ blockCap i → x ∈ blockCap j → i = j` |
| `theorem blockIsPartition (N p) (n) (hsum)` | **proven** — `IsPartition (blockCap N p n)`, from `blockCover` + `blockUnique` |
| `theorem nonemptyOfSumCapacities (N p) (n) (hsum)` | **proven** — **the A1.1 Nonempty witness**: `let P := blockCap N p n; let hP : IsPartition P := blockIsPartition …; have heq : (λ i, (P i).card) = n := funext blockCap_card; exact heq ▸ Allocation.nonemptyOfPartition P hP`. |

**The probe builds** (`lake build Shufflemath._ProbeA14` → 3192 jobs, only the 4
`sorry`-use warnings). It is a `_Probe` (exploratory), not yet in the aggregator.

## The four remaining `sorry`s — how to fill them

1. **`himg`** (in `blockCap_card`): `Finset.image (·.val) (blockCap N p n i) =
   (Finset.range N).filter (fun v => a ≤ v ∧ v < b)`, with `a = prefixCap i`,
   `b = a + n i`.  Strategy: `blockCap i = Finset.univ.filter (fun x => a ≤ x.val
   ∧ x.val < b)`; `image (·.val)` of `univ : Fin N` is `Finset.range N` (find the
   val-image lemma, e.g. search `image … range` in `Mathlib/Data/Finset`); a
   `Finset` filter commutes with an injective `image` (`x ↦ x.val` is injective
   by `Fin.ext`).  `ext v; simp [Finset.mem_image, Finset.mem_filter, blockCap]`
   is the entry point — the `omega`-unfriendly range-membership bound from last
   session means use the explicit `a ≤ v ∧ v < b` form (already done) rather than
   a `Finset.Ico`.
2. **`h2`** (in `blockCap_card`): `(Finset.range N).filter (fun v => a ≤ v ∧ v < b)
   = Finset.range b \ Finset.range a`.  Since `a ≤ b` (from `prefixCap_le_total`
   + `b = a + n i`), `v < b ∧ v ≥ a ↔ v ∈ range b \ range a`.  `ext v; simp [
   Finset.mem_range, Finset.mem_sdiff]` then `omega`.
   Once `himg` + `h2` are filled, `blockCap_card` closes by the existing
   `card_sdiff_of_subset` + `card_range` + `Nat.add_sub_cancel_left` tail.
3. **`blockCover`**: needs the block-continuity fact `prefixCap (i+1) =
   prefixCap i + n i` for successor `i` (the blocks are contiguous half-open
   intervals tiling `[0, N)`).  Then for `x : Fin N`, `x.val < N = ∑ n = prefixCap
   (last) + n (last)`, so `x.val` falls in some block.  The successor-index
   arithmetic in `Fin p` (successor needs `i.val < p`) is the friction — consider
   indexing by `Fin (p+1)` or proving the continuity via the `prefixCap` sum form.
4. **`blockUnique`**: the blocks are pairwise disjoint because consecutive
   half-open intervals `[a_i, a_i + n_i)` with `a_{i+1} = a_i + n_i` do not
   overlap.  Again needs the continuity fact from (3).  `intro h1 h2` gives the
   two interval memberships; `omega` on the `prefixCap`/`n` arithmetic (with the
   continuity) closes it.

## **Important:** the A1 capstone is NOT a `FiniteKernel` statement (do not stub it that way)

`swapKernel (hN : 0 < N) (A : Allocation N p n) : Dist (Allocation N p n)` is a **bare
transition** (`Allocation → Dist Allocation`), **not** a `FiniteKernel (Allocation)
(Allocation)`.  Consequently `DetailedBalance` and `FiniteKernel.apply` (both of which
take a `FiniteKernel`) do **not** apply to it directly — this is the mistake that cost
several builds this session.  The correct capstone statement:

> **`swapKernel_uniformStationary`.**  For feasible capacities (`∑ n = N`), the
> **uniform law over allocations is stationary** under the swap transition:
> `∑_A mass (uniformDist) A · mass (swapKernel hN A) B = mass (uniformDist) B`
> for each `B`.

**Proof outline** (all ingredients proven in `UniformExchange.lean`):
- **Row-stochasticity** `∑_A mass (swapKernel hN B) A = 1`: from `swapKernel_mass`,
  `mass (K B) A = ∑_{s : Fin N × Fin N} (N*N)⁻¹ · [A = swapPiles B s]`; summing over
  `A` collapses the `[A = …]` to `1` (each `swapPiles B s` is exactly one allocation),
  giving `N² · (N²)⁻¹ = 1`.  (Needs `Fintype (Allocation N p n)`, proven A1.1.)
- **Symmetry** `mass (K A) B = mass (K B) A` = `swapKernel_symmetric hN A B` (proven).
- **Stationarity**: `∑_A mass(K A) B = ∑_A mass(K B) A` (sum the symmetry) `= 1`
  (row-stochasticity), so `∑_A (1/card) · mass(K A) B = (1/card) · 1 = 1/card =
  mass (uniformDist) B`.

This is a clean, finite, exact-arithmetic proof; it just has to be stated for the
**transition**, not wrapped as a `FiniteKernel`.  The `∑_A …` sums over the `Fintype`
of `Allocation N p n` (A1.1 provides the instance).

## A1.3b (this session, committed in `UniformExchange.lean`)

`swapPiles_pileCounts (hN) A (i,j) = (n.swap (fin i) (fin j)) A`.  Key step: a
`Fin 2 × Fin 2` swap `(i,j)` is an `Fin p` swap with both indices in `i ⊔ j` (the
two piles it touches), so the `p`-ary `swapPiles` equals the `2`-ary one on
`i ⊔ j` (an `Equiv`-transport) and matches pointwise on the other `p-2` piles.
`swapPiles_swapPile` (the 2-ary swap) and `swapPiles_permute` (the `Fin p` permute)
are the two `swapPiles` overloads (different arities — do not confuse them).

## Status vs roadmap (`2026-11-15-arbitrary-finite-deck-generalization.md`)

- **A1.1** (Fintype + Nonempty): **Fintype done** (prior); **Nonempty now mapped**
  (block-partition foundation builds, 4 `sorry`s remaining as above).
- **A1.2** (swapPiles is a bijection): done (prior).
- **A1.3** (swapPiles preserves pile counts): **A1.3a done** (prior); **A1.3b done
  (this session)** → **A1.3 complete**.
- **A1.4** (swapKernel is a permutation of allocations): done (prior).
- **A2** (swapKernel non-triviality), **A3** (uniform pushforward), **A4**
  (ergodicity): open — next after the 4 A1.1 `sorry`s are filled and the capstone
  is stated for the transition.

**Do-not-stop deadline is past (2026-11-24); user has not re-armed a deadline — keep
making incremental, committed progress.**  Small-batch commit gates, the compaction
resume protocol, and the stuck protocol still apply.  When stuck on a specific Lean
tactic, write the exact target state + what was tried + the next candidate to
`/tmp/` before switching tracks.
