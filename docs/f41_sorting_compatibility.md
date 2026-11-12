# F4.1 sorting-compatibility: exact state and the remaining `Bool` bridge

**Status (2026-11-12): F4.1 is substantially along; the goal remains open on
one bridge.** The *label-law* half is complete, and all the *mechanism
ingredients* for the *sorting* half are proved and committed. The **F4.1 goal**
is the kernel equality `productLabelShuffle a b (uniform a) (uniform b) =
idealShuffle n (a*b)`, which *follows from* the list-level
sorting-compatibility `stableBuckets (a*b) (combineLabels …) deck =
lexBuckets a b minor major deck`. That list-level lemma is the remaining open
item; its last step is the `Bool`/`==`/`&&` filter bridge. Proved and committed:

- **`productLabels_pushforward_uniform`** — the *label-law* half: the uniform
  `(a*b)`-alphabet label law equals the pushforward of the independent product
  of a `b`- and an `a`-alphabet uniform label law through `labelReparam`
  (`combineLabels`/`splitLabels`).
- **`labelShuffle_comp`** — the F4.4 two-ruffle composition law: composing an
  `a`-label stable shuffle and a `b`-label stable shuffle has the law of
  independently sampling both and sorting by the combined `(b,a)`-lex label
  (`productLabelShuffle`, built from `lexBuckets`).

The old "`List.range` wall" is **broken**: `List.range_add` (`List.range
(m + n) = List.range m ++ List.map (fun x => m + x) (List.range n)`, which
exists in this build) gives the block decomposition, and the index-level
reindexing is **proved and committed** as `rangeMap_divmod_eq_nested`.

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

- **`combineVal_pred_eq`** (this session): per card, its combined numeric value
  equals `k` **iff** its major/minor are exactly `(k/a, k%a)`: `=
  (combineLabels ... c).val = k ↔ (major c).val = k/a ∧ (minor c).val = k%a`. This
  is the `=`/`Prop`-world per-card bridge (the `Bool`/`==`/`&&` filter predicate
  is its `Nat.beq_eq` lift). Proven with `change`/`rfl` for the `decodeLabel`
  value (avoids the `simp` recursion loop) and `rw` + `combinedLabel_pred` +
  `Nat.div_add_mod` for the rest.

## What remains and why it is still fiddly

The index-level content and the `=`/`Prop` per-card fact are done. What remains
is to lift `combineVal_pred_eq` into the `Bool`/`==`/`&&` world that
`List.filter` uses, then assemble the flatMap:

1. **`Bool`/`==`/`&&` lift.** `List.filter` predicates are `Bool`s (`Nat.beq`
   `==`, `Bool` `&&`), while `combineVal_pred_eq` is `=`/`∧`. `Nat.beq_eq`
   (`(x.beq y = true) = (x = y)`) bridges a *bare* `==`↔`=` comparison, and
   `(b1 && b2) = true ↔ (b1 = true) ∧ (b2 = true)` and `b1 = b2 ↔
   (b1 = true) = (b2 = true)` are `simp`-able, but the **`Bool`-equality goal
   left by `List.filter_congr`** (`(A == k) = (B && C)`, where the outer `=` is
   `Bool` equality) does **not** close with `simp [Nat.beq_eq]` in this build,
   and a `by_cases`/`split_ifs` on the three `==` bools keeps hitting
   `Bool`-vs-`Prop` / `decide` elaboration mismatches. The remaining content is
   small: `X = true ↔ (combine c).val = k` and `B = true ↔ (major c).val = k/a`,
   with `combineVal_pred_eq` equating the two `=` statements.
2. **Assemble the flatMap.** Once the per-card `Bool` filter is identified,
   rewrite `stableBuckets`'s single `List.range (a*b)` flatMap into the nested
   `(List.range b)`-outer / `(List.range a)`-inner flatMap of `lexBuckets`
   using `rangeMap_divmod_eq_nested` plus `List.flatMap_map`
   (`List.flatMap g (List.map f l) = List.flatMap (fun a => g (f a)) l`).

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
