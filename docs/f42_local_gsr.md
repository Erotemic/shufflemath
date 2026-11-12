# F4.2 — permutation-preserving local GSR (state)

**Task (from `lean_plan.md`):** define a local-GSR kernel that permutes the
*ordered* cards within each fixed pile, and prove it cannot change the
membership state. This is the GSR-side counterpart of F3 (the exchange side):
a physical riffle never changes `leftCards`, so both local models must respect
the `k`-invariant.

## Done (committed in `Shufflemath/CommanderLocalGSR.lean`)

- **`pileRelabelFn pl pr`** — the position map: left positions `p.val < 50` go
  to `leftPosition (pl ⟨p.val⟩)`; right positions `p.val ≥ 50` go to
  `rightPosition (pr ⟨p.val - 50⟩)`. `pl : Equiv.Perm (Fin 50)`,
  `pr : Equiv.Perm (Fin 49)`. It never sends a card across the pile boundary.
- **`pileRelabelFn_left` / `pileRelabelFn_right`** — the map reduces to
  `leftPosition ∘ pl` / `rightPosition ∘ pr` in the two cases.
- **`permutedLeftCards_eq`** — the **core**: the left-card set of the permuted
  deck equals the original left-card set, for *any* `pl`, `pr`. This is the
  membership-preservation theorem: a within-pile relabel cannot change which
  cards are left-original.
- **`univImage_reindex`** — the general reindexing lemma: any injective `f`
  satisfies `univ.image f = univ.image id` (so a bijection leaves the full
  image unchanged). The core is proved by this.
- **`pileRelabelFn_leftVal` / `pileRelabelFn_rightVal`** — a left position maps
  to a left position and a right to a right. The `if` in `pileRelabelFn` has a
  fresh binder, so the reduction is driven by `by_cases` on the same condition
  (which `simp` then uses to close the `if`) rather than the hypothesis
  directly. These are the building blocks for the injective/surjective proof.

## Remaining: package as a `FiniteKernel Deck Deck`

To turn `pileRelabelFn` into a valid `Deck = Equiv.Perm (Fin 99)` (and hence a
`FiniteKernel Deck Deck`), it must be shown **bijective**:

- **Injective**: case-split on `p.val < 50` / `q.val < 50`. Same-pile cases use
  `leftPosition_injective`/`rightPosition_injective` and `pl`/`pr`
  injectivity; cross-pile cases are disjoint (`val < 50` vs `50 ≤ val`).
- **Surjective**: a left `y` has preimage `leftPosition (pl.symm (…))`; a right
  `y` has preimage `rightPosition (pr.symm (…))`.

**Obstacles hit (Nov 12, 2026):** the `pileRelabelFn` body is an `if h :
p.val < 50`, so the helpers need `dsimp only [pileRelabelFn]` to expose the
`if` before `split_ifs`; the `leftVal` helper closes with
`dsimp [pileRelabelFn]; simp [h, leftPosition]`, but the `rightVal` helper
(`50 ≤ 50 + (pr _).val` after reduction) resists `omega`/`nlinarith` in this
build, and the cross-pile `disjoint` steps leave `Fin`/`omega` goals. The
content is small (the two helpers + four case blocks); the fiddliness is the
`Fin`-val/`if`-reduction mechanics. Next agent: retry the `rightVal` helper
with `Nat.le_add_left`/`Nat.add_comm` (or `apply Fin.ext` on the `.val`) and
then lift to `Equiv.ofBijective`.

Once the bijection is in, `permuteWithinPiles d pl pr := d.comp (pileRelabel
pl pr)` is a `Deck`, and the GSR product over the two piles follows (compose
two `permuteWithinPiles` kernels / take the GSR `Equiv.Perm` product).
