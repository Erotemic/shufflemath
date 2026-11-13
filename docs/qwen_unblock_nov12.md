# November 12 intervention: direct proof routes for F3, F4.1, and F4.2

**Source basis:** snapshot `c935088` (2026-11-12 17:15 EST). This overlay
adds independent proof candidates and a numeric regression. It does not replace
Qwen's Lean modules or current handoff files. Compile candidates before moving
their contents into production modules; they have not been Lean-compiled in the
overlay environment.

## 1. F4.1: solve the Boolean wall without `split_ifs`

`dev/QwenGSRBridge.lean` contains two candidate theorems:

- `qwen_combinedLabel_bool_bridge`: the equality of `Bool` predicates needed
  for `List.filter`, obtained by `Bool.eq_iff_iff.mpr` then
  `simp only [Nat.beq_eq, Bool.and_eq_true_iff]` and the **already proved**
  `combineVal_pred_eq`. All boolean case splits are unnecessary.
- `qwen_stableBuckets_combine_eq_lex`: assemble the sorting identity by
  transporting the bucket list along `rangeMap_divmod_eq_nested`, then applying
  `List.flatMap_map` and `List.flatMap_assoc`.

Run:

```bash
lake env lean dev/QwenGSRBridge.lean
```

If a single rewrite fails, inspect that goal and adjust the local `change`
/ `simp only` expression; do not unfold `combineLabels`/`decodeLabel` or
restart the mixed-radix arithmetic. Upon success, move the lemmas into
`Shufflemath/GSR.lean` under final names and build `Shufflemath.GSR`.

**A distinct obligation remains after sorting:** `productUniformLabels ha hb`
is the uniform distribution on the *pair* of label arrays, while
`productLabelShuffle` **samples two independent uniform arrays by nested
`FiniteKernel.apply`**. To conclude the kernel equality, prove that the joint
sampling law equals `productUniformLabels`. The already proved
`productLabels_pushforward_uniform` only identifies the pushforward of
`productUniformLabels` by the bijection; it does **not** itself establish the
nested-sampling/product-uniform equality. Make this joint-distribution bridge
an explicit lemma. `Dist.apply_mass` and the cardinality identity
`Fintype.card (X × Y) = Fintype.card X * Fintype.card Y` are available starting
points; use exact `Rat` arithmetic.

## 2. F4.2: replace manual bijectivity with an existing `Equiv`

`dev/QwenLocalPermutation.lean` contains `qwenPileRelabelEquiv`, whose core is

```lean
((finSumFinEquiv (m := 50) (n := 49)).symm).trans
  ((Equiv.sumCongr pl pr).trans (finSumFinEquiv (m := 50) (n := 49)))
```

This is a **full `Deck = Equiv.Perm (Fin 99)` by construction**, without any
four-case proof of injectivity or explicit inverse witnesses. It transports a
left permutation and a right permutation through the canonical
`Fin 50 ⊕ Fin 49 ≃ Fin 99` equivalence. Candidate lemmas show it acts as
`leftPosition (pl i)` and `rightPosition (pr j)` on the respective halves, and
that precomposing the deck with it preserves `leftCards`.

Run:

```bash
lake env lean dev/QwenLocalPermutation.lean
```

Mathlib names checked against the public API:
`finSumFinEquiv`, `finSumFinEquiv_apply_left`,
`finSumFinEquiv_apply_right`, `finSumFinEquiv_symm_apply_castAdd`,
`finSumFinEquiv_symm_apply_natAdd`, `Equiv.sumCongr_apply`.

If it compiles, the older `pileRelabelFn` can be retained for compatibility
and related by extensional equality, or retired once callers use the Equiv.
There is no reason to finish the manual case split first. The GSR product
kernel on the two pile **orderings** is a separate follow-up after the
permutation is available.

## 3. F3: use reversibility and an overlap count, bypassing group-action uniformity

Current `docs/f3_membership_exchange.md` splits the proof into the
hypergeometric count law and a separate transitivity/uniformity argument.
There is a more direct point-mass approach.

Let `S,T : Membership`, with `|S|=|T|=m=50`, `n=99`, exchange size `k=25`.
Every selected pair of card subsets `A ⊆ S`, `B ⊆ Sᶜ`, each of size `25`,
produces `T=(S \ A) ∪ B`. The map `(A,B) ↦ T` is injective because
`A=S \ T` and `B=T \ S`. Such a pair exists precisely when

```
|(S : Finset (Fin 99)) ∩ T| = m-k = 25.
```

Thus the **membership-level** transition is symmetric:

```
K(S,T) = if |S ∩ T| = 25
         then 1 / (choose(50,25) * choose(49,25))
         else 0.
```

This removes all dependence on the original deck's within-pile ordering.
To connect the already implemented deck/position sampler to this form,
prove that the card-images of the 25 selected left and right positions
are in bijection with the 25-subsets of `S` and of `Sᶜ`, using the
left/right restriction of the `Deck` equivalence.

Now fix target `T` containing `y` marked cards and count old memberships
`S` containing `x` marked cards with `|S ∩ T|=25`. Partition the 99
identities into four disjoint bins relative to `T` and the marked/unmarked
partition:

| Bin | Size | Number selected into S |
|---|---:|---:|
| Marked in T | `y` | `t` |
| Marked outside T | `50-y` | `x-t` |
| Unmarked in T | `50-y` | `25-t` |
| Unmarked outside T | `y-1` | `25-x+t` |

Consequently,

```
Overlap(x,y) = Σ_{t=0}^{25}
  choose(y,t) * choose(50-y,x-t) *
  choose(50-y,25-t) * choose(y-1,25-x+t).
```

**Key identification:** `Overlap(x,y) = transitionNumerator(99,50,50,25,y,x)`
(the *reversed* transition numerator). This holds because a start membership
`S` with the required overlap is uniquely obtained by exchanging 25 cards
from the fixed membership `T`, and the existing numerator counts such
choices by the number of marked cards removed. One may prove the four-bin
sum directly or reuse the existing counting fiber in
`Shufflemath/BernoulliLaplaceFiber.lean` (`fiberABcount`, `fiberSum_eq`).

Let `F(z) = choose(50,z) * choose(49,50-z)`. The mass of a fixed `T` is

```
Overlap(x,y) / (F(x) * choose(50,25) * choose(49,25)).
```

Detailed balance gives

```
F(y) * transitionNumerator(y,x)
  = F(x) * transitionNumerator(x,y).
```

Therefore the previous mass equals

```
transitionWeight(99,50,50,25,x,y) / F(y),
```

which is exactly `commanderExchange25.comp membershipLift` evaluated at T.
**Uniformity within fixed y now follows from the same computation**; a
separate action of `Sym(50) × Sym(49)` on membership states is unnecessary.

The existing theorem to reuse is
`BernoulliLaplaceGeneral.detailedBalance commanderBLParams
  (commanderToBL x) (commanderToBL y)`.
Import `Shufflemath.BernoulliLaplaceFiber` and
`Shufflemath.BernoulliLaplaceCommanderBridge` into the eventual dedicated
proof module; check import direction first. `transitionWeight_general_eq_commander`
and `commanderStationary_matches_blStationary` already connect the general
and concrete chains. To avoid rational-denominator manipulations in the
combinatorial lemmas, first extract the natural-number balance identity,
then use it to normalize the point masses.

**Suggested sublemmas in order:**

1. `exchange_card_pair_of_memberships`: for fixed `S,T`, choices `(A,B)`
   producing `T` form a singleton exactly when `|S ∩ T|=25`, otherwise empty.
2. `rawExchangeMembership_mass_via_membership`: the actual deck-position
   sampler yields `K(membership d,T)` described above.
3. `count_overlap_eq_reverse_transitionNumerator`: the four-bin count (or
   reuse of `fiberABcount`) for a fixed `T` with macro count `y`.
4. `count_fiber_detailed_balance`: extract the integer identity from the
   existing BL detailed-balance theorem.
5. Close the desired `FiniteKernel` equality with `FiniteKernel.apply_mass`
   and `StdSimplex.weights_inj`; use `simp only` on permutation-dependent
   terms to avoid the F2 elaboration failure.

**4th-session refinement (2026-11-12) — the identity reduces to one
counting lemma.** The general identity
`overlap_count (n m r k) x y = transitionNumerator (n m r k) y x`
need not be attacked as the raw hypergeometric convolution (under the
index substitution `a = y - t` three of the four `choose` factors match
exactly; the fourth, `choose(m-y,(m-k)-t)` vs `choose(m-y,k-y+t)`, is the
gap). Instead it follows from three pieces:

- (i)  **the fiber-counting lemma (CL):** `fiberSum p x y =
  choose(r, y) * choose(N - r, m - y) * overlap_count (N m r k) x y`,
  where `choose(r, y) * choose(N - r, m - y)` is the number of `m`-subsets
  carrying `y` marked cards (the stationary-weight numerator — note the
  plain factor is `N - r`, **not** `N - m`; they coincide only when `r = m`,
  as for the Commander `99/50/50`).  **This is the one new lemma; it is
  verified on the three small decks** (`fiberCounting_{6321,7442,8431}` in
  `ExchangeOverlap.lean`, `native_decide`).  Combinatorially: `fiberSum p x y`
  counts the `(S, A, B)` triples with `|S|=m`, `x` marked, `|A|=k ⊆ S`,
  `|B|=k ⊆ Sᶜ`, target `(S\A) ∪ B` carrying `y` marked; the target
  `T = (S\A) ∪ B` has `|S ∩ T| = m-k` and is recovered uniquely, so the
  7-way sum reorganizes to the `(S, T)` double count = "(number of `y`-targets)
  × (sources per fixed target)".
- (ii) `fiberSum p x y = fiberSum p y x` — already proved
  (`BernoulliLaplaceFiber.fiberSum_swap`).
- (iii) `fiberSum p x y = choose(r, x) * choose(N - r, m - x) *
  transitionNumerator (N m r k) x y` — already proved (`fiberSum_eq`).

From (CL) at `(x, y)` and `(y, x)` plus `fiberSum_swap`, the stationary factors
satisfy `choose(r, y) * choose(N-r, m-y) * overlap_count (N m r k) x y =
choose(r, x) * choose(N-r, m-x) * overlap_count (N m r k) y x`; combined with
(iii) the `choose` factors cancel and the target identity
`overlap_count (N m r k) x y = transitionNumerator (N m r k) y x` follows by
pure algebra. **The single remaining piece is the general (symbolic) proof of
(CL)** — reindexing the 7-way `fiberSum` sum to the `(S, T)` double count —
which the small-deck `native_decide` instances confirm pointwise.

`tests/test_exchange_overlap_identity.py` independently verifies the overlap
formula against actual membership enumeration on three small decks and
all **2,500** Commander `(x,y)` pairs using exact `int` arithmetic. Run:

```bash
python3 -m unittest discover -s tests -p 'test_exchange_overlap_identity.py' -v
# or run the normal complete test suite:
python3 -m unittest discover -s tests -v
```

## Build/merge sequence

Build the two candidates separately; merge whichever compiles cleanly before
moving to the next. Keep the original source definitions untouched until each
replacement has a compiled bridge. The Python test may be committed
independently. Once a new result is in a production module, remove its
trial file to avoid parallel implementations; update `docs/agent_handoff.md`
and `docs/lean_plan.md` to reflect **what actually compiled**. Use the
repository's current-model Git co-author trailer on every authored commit.
