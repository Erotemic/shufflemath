# F4.1 sorting-compatibility: exact state and the `List.range` wall

**Status (2026-11-12):** Open. The *label-law* half of F4.1 is complete
(committed); the *sorting* half — showing the single combined-label stable sort
equals the lexicographic stable sort — is the remaining piece. This note
captures exactly what is proved, the exact open statement, and why it is
hard, so the next attempt does not repeat the failed routes.

## What is already proved (green, committed)

In `Shufflemath/GSR.lean` (all inside `namespace GSR`):

- `encodeLabel ha (k : Fin (a*b)) : Fin b × Fin a` and
  `decodeLabel ha hb (Fin b × Fin a) : Fin (a*b)`, with both inverse laws
  (`decodeLabel_encodeLabel`, `encodeLabel_decodeLabel`). The numeric encoding
  is `major*a + minor`.
- `combineLabels`/`splitLabels` and the `labelReparam : (Fin n → Fin a) ×
  (Fin n → Fin b) ≃ (Fin n → Fin (a*b))` bijection.
- `map_bijective_uniformDist`, `productLabels_pushforward_uniform`: a uniform
  `Fin (a*b)` label law equals the independent product of a uniform `Fin b`
  and a uniform `Fin a` label law pushed through `labelReparam`. **This is the
  label-law half of F4.1** — the two shuffles have the *same label
  distribution*.
- `stableBuckets_comp`: `stableBuckets b major (stableBuckets a minor deck) =
  lexBuckets a b minor major deck` (via `filter_flatMap`).
- **`mixedRadix_unique`** (this session): `x*a + y = j*a + i` with `y < a`,
  `i < a` forces `x = j` and `y = i`. Proved via the residue of each side
  modulo `a` plus cancellation of the common `·a` term — **no `div`/`mod` of
  the full number**, so it does not trigger `List.range`/`Nat.div` rewrite
  loops.
- **`combinedLabel_pred`** (this session): per card,
  `(major c).val * a + (minor c).val = j*a + i ↔ (major c).val = j ∧
  (minor c).val = i` (for `i < a`). This is `mixedRadix_unique` applied per
  card and is the *pointwise* bridge between the combined-label bucket and the
  `(major, minor)` lexicographic bucket.

## The exact open statement

```lean
theorem stableBuckets_combine_eq_lex {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (deck : List (Fin n)) :
    stableBuckets (a*b) (combineLabels ha hb minor major) deck =
      lexBuckets a b minor major deck
```

Once proved, the F4.1 kernel equality follows by composing with
`productLabels_pushforward_uniform`:

```lean
-- productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b) (a*b)
```
because `productLabelShuffle`'s body is `lexBuckets` on the product labels and
`idealShuffle (a*b)`'s body is `stableBuckets (a*b)` on the `(a*b)`-labels, and
the two label laws coincide (pushforward) and the two sorts coincide (this
lemma).

## Why it is hard: the `List.range` wall

`List.range` is a **core Lean definition by non-structural recursion**
(`List.range.loop`), so it does **not** `rw`/`simp` into structural pieces.
Every route to the above equality needs to relate the *bucket order*
(`List.range (a*b)` = `0,1,…,a*b-1`) to the *lexicographic order* of the
`(major, minor)` pairs, and that relation is exactly a `List.range`
reindexing that `rw` refuses.

Concretely, the equality needs one of:

1. **A `List.range` block split.** E.g.
   `List.range (a*b) = (List.range b).concat (fun j => List.range' (j*a) a)`
   (where `List.range' n m = [n, …, n+m-1]`). Then the LHS flatMap regroups
   into the `j`/`i` double flatMap of the RHS, and `combinedLabel_pred`
   closes the per-card predicate. The obstacle is *proving* the split lemma
   itself: `List.range (m + n) = List.range m ++ List.range' m n` resists
   `rw` and `simp` on `List.range`; it must be proved by induction on `n`
   using the recursive unfolding, and no `range_succ`/`range_append` simp
   lemma for `List.range` (as opposed to `Finset.range`/`Multiset.range`) is
   exposed in this Mathlib build.

2. **A stable-sort-uniqueness argument.** Show both sides are the unique
   stable sort of `deck` by their (equal) total order. This needs a
   rank function `Fin n → Fin (a*b)` (namely `combineLabels`) plus a lemma
   that stably sorting by an order-reflecting relabeling is invariant. That
   is a fresh, general lemma and is not currently in the library.

3. **The cons-insertion induction** (the route this session probed). Define
   `stableBuckets K f (c :: rest) = (stableBuckets K f rest).filter (f _ <
   f c) ++ [c] ++ (stableBuckets K f rest).filter (f _ == f c) ++
   (stableBuckets K f rest).filter (f _ > f c)` (a `c` lands at the front of
   its bucket). Inducting on `deck` then reduces the theorem to showing the
   `List.range K` flatMap equals the `<`/`=`/`>` regrouping — again the
   `List.range` order. `List.cons_filter`/`List.filter_cons` (the names
   tried) do not exist; the cons-filter split is `List.filter_cons`-style and
   must be located or inlined.

## Recommended next move

The cleanest single lemma that unlocks everything is the **`List.range` block
split**:

```lean
-- PROPOSED (unproved): List.range (a * b) =
--   (List.range b).concat (fun j => List.range' (j * a) a)
```

Prove it by induction on `b` (base `b = 0`: both `[]`; step: use
`List.range (m+n.succ) = List.range (m+n) ++ [m+n]` and
`List.range' n (m+1) = List.range' n m ++ [n+m]`, both provable by a direct
induction on the recursive `loop` definition). Then:
- `stableBuckets (a*b) (combineLabels ...) deck` flatMap regroups over the
  blocks into a `(List.range b)`-outer / `(List.range a)`-inner double flatMap,
- the per-card predicate becomes `combinedLabel_pred` at `i`,
- and `filter_flatMap`/`filter_filter` close it to `lexBuckets`.

## Dependencies / gotchas

- In this Mathlib build `Finset.range` *does* have `range_add`/`range'`
  theorems, but `List.range` does **not** (it is a core `loop` def). Do not
  assume `List.range` simp lemmas.
- `List.cons_filter` and `List.filter_cons` do not exist; use
  `List.filter`'s `@[simp]`/`grind` lemma or inline the split.
- `combinedLabel_pred` only needs `i < a` (the minor bucket bound) and `ha`;
  it does *not* need `j < b`, matching how `mixedRadix_unique` is stated.
- Default `simp` is safe *inside* `GSR.lean` for `List`/`Fin`/`Nat` terms here
  (no `Equiv.Perm (Fin 99)` terms appear in this file), but keep it to
  `stableBuckets`/`lexBuckets`/`filter_*` as in `stableBuckets_comp`.
