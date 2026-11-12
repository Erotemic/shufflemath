# F4.1 sorting-compatibility: exact state and the remaining `Bool` bridge

**Status (2026-11-12):** The *label-law* half of F4.1 is complete, and the
*sorting* half is now down to a small `Bool`/`decide` bridge. The old
"`List.range` wall" is **broken**: `List.range_add`
(`List.range (m + n) = List.range m ++ List.map (fun x => m + x) (List.range n)`,
which exists in this build) gives the block decomposition, and the index-level
reindexing is now **proved and committed** as `rangeMap_divmod_eq_nested`. What
remains is (a) the per-card filter predicate in the `==`/`&&`/`Bool` world and
(b) assembling the flatMap — a mechanical but fiddly `Bool`/`decide` bridge.

## What is already proved (green, committed)

In `Shufflemath/GSR.lean` (all inside `namespace GSR`):

- `encodeLabel`/`decodeLabel` with both inverse laws (numeric `major*a + minor`);
  `combineLabels`/`splitLabels`; `labelReparam`.
- `map_bijective_uniformDist`, `productLabels_pushforward_uniform` (the
  label-law half of F4.1).
- `stableBuckets_comp`, `mixedRadix_unique`, `combinedLabel_pred` (the
  `=`/`Prop`-world per-card bridge).
- **`div_block` / `mod_block`** (this session): for `x < a`,
  `(a*b' + x) / a = b'` and `(a*b' + x) % a = x`. Proved via
  `Nat.div_le_iff_le_mul` / `Nat.div_lt_iff_lt_mul` (with the `b'*a = a*b'`
  commutativity fed by `ring` + `omega`) and `Nat.add_mod` +
  `Nat.mod_eq_of_lt` respectively.
- **`rangeMap_divmod_eq_nested`** (this session, the crux): the `(div, mod)`
  sequence over `List.range (a*b)`,
  `(List.range (a*b)).map (fun k => (k / a, k % a))`, is *exactly* the nested
  `(j, i)` sequence `(List.range b).flatMap (fun j => (List.range a).map (fun i
  => (j, i)))` in lexicographic order. Proved by induction on `b` using
  `List.range_add` for the block split, `List.map_append`/`List.map_map` on the
  left, `List.range_succ`/`List.flatMap_append`/`List.flatMap_singleton` on the
  right, and `div_block`/`mod_block` to simplify the last block.

## The exact open statement

```lean
theorem stableBuckets_combine_eq_lex {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (deck : List (Fin n)) :
    stableBuckets (a*b) (combineLabels ha hb minor major) deck =
      lexBuckets a b minor major deck
```

## What remains and why it is still fiddly

The index-level content is done. The remaining work is to thread it through the
`List.filter` predicates, which live in the **`Bool` world** (`Nat.beq` `==` and
`Bool` `&&`), whereas `combinedLabel_pred` and the division lemmas live in the
**`Prop` world** (`=` and `∧`):

1. **Per-card filter bridge.** Show, for the card `c` and index `k`:
   `((major c).val * a + (minor c).val == k) ↔
    ((major c).val == k/a && (minor c).val == k%a)` (Bool).
   The `=`-world content is `combinedLabel_pred` at `j = k/a`, `i = k%a` plus
   `k = (k/a)*a + (k%a)` (`Nat.div_add_mod`). The bridge
   `simp [Nat.beq_eq]` *does* convert a bare `(x == j && y == i) ↔ (x = j ∧ y =
   i)`, but the goal left by `List.filter_congr` is a `Bool` *equality*
   `p c = q c` (i.e. `(A == k) = (B && C)`), for which `simp [Nat.beq_eq]` makes
   no progress in this build. The workable route is a **`by_cases` / `split_ifs`
   on the three `==` bools** (the `==` on a `Nat` comparison is a `Bool`, so
   branch on `h : (x == y) = true` / `h : (x == y) = false`), using `h3` in each
   case to force the two Bools to agree.
2. **Assemble the flatMap.** Once the per-card filter is identified, rewrite
   `stableBuckets`'s single `List.range (a*b)` flatMap into the nested
   `(List.range b)`-outer / `(List.range a)`-inner flatMap of `lexBuckets`
   using `rangeMap_divmod_eq_nested` plus `List.flatMap_map`
   (`List.flatMap g (List.map f l) = List.flatMap (fun a => g (f a)) l`) and the
   flatMap-associativity step `((L).map h).flatMap f = L.flatMap (f ∘ h)`
   (induction, trivial).

Once (1) and (2) are in place, `stableBuckets_combine_eq_lex` follows, and the
F4.1 kernel equality `productLabelShuffle a b (uniform) (uniform) =
idealShuffle n (a*b) (a*b)` follows by composing it with
`productLabels_pushforward_uniform`.

## Dependencies / gotchas

- `List.range_add` **does** exist in this build; the old "no `range_*` for
  `List.range`" note is obsolete. `List.range_succ`, `List.map_append`,
  `List.map_map`, `List.flatMap_append`, `List.flatMap_singleton`,
  `List.flatMap_map`, `List.map_eq_map_iff`, `List.mem_range` all exist.
- `Nat.div_eq_of_lt_mul`, `Nat.div_mul_add_mod`, `List.cons_filter`,
  `List.filter_cons` do **not** exist. Use `Nat.div_le_iff_le_mul` /
  `Nat.div_lt_iff_lt_mul` and `Nat.div_add_mod` instead.
- `Nat.beq_eq : (x.beq y = true) = (x = y)` bridges a *bare* `==`/`=` comparison
  but not a `Bool`-equality goal; for the filter predicate use explicit
  `split_ifs`/`by_cases` on the `Bool`s.
- Default `simp` is safe inside `GSR.lean` for these `List`/`Fin`/`Nat` terms
  (no `Equiv.Perm (Fin 99)` terms in this file).
