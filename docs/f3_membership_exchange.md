# F3 item 3 core: the `hMembershipExchange` counting identity

**Status (2026-11-12):** Open. The structural reduction is done and committed
(`hMembershipExchange_lhs_reduces`, commit `958d5f5`); what remains is a single
*counting* identity between two `FiniteKernel CommanderState Membership` laws.
This is the hard part of F3, on the critical path for F3 item 4 (the
unconditional 2-exchange TV theorem) and F4.5.

## The exact statement to prove

In `Shufflemath/CommanderPhysicalExchange` (all symbols already defined there
or imported):

```lean
theorem hMembershipExchange :
    FiniteKernel.comp
      (FiniteKernel.comp (FiniteKernel.comp membershipLift localLift) rawExchange)
        (FiniteKernel.deterministic membership) =
      FiniteKernel.comp BernoulliLaplace.commanderExchange25 membershipLift := by
  rw [hMembershipExchange_lhs_reduces]
  -- reduce to the core:
  change FiniteKernel.comp (FiberDisintegration.fiberLaw project project_surjective)
      rawExchangeMembership =
      FiniteKernel.comp BernoulliLaplace.commanderExchange25 membershipLift
  -- ... (counting, below)
```

Both sides are `FiniteKernel BernoulliLaplace.CommanderState Membership`
(`CommanderState = Fin 50`, so a state `x` has left-original count
`commanderLeftCount x = x.val + 1`).

## The mass-at-a-point reduction

`FiniteKernel.ext`/`ext` reduces the equality to: for every input state `x` and
target membership `m`, the two kernels put the same mass on `m`.

- **LHS mass** at `m` from `x`:
  ```
  |{ (d, (L,R)) : project d = x, newLeftCards d L R = m }|
    / ( |fiber project x| · choose 50 25 · choose 49 25 )
  ```
  where `|fiber project x| = Fintype.card {d : Deck // project d = x}` and the
  `(L,R)` count is `N = choose 50 25 * choose 49 25`. (The two-layer law
  `fiberLaw project` is uniform over the project fiber, and
  `rawExchangeMembership` is the uniform pushforward over the `(L,R)` pairs.)

- **RHS mass** at `m` from `x`:
  ```
  transitionWeight 99 50 25 (commanderLeftCount x) (commanderLeftCount m)
    / |{m' : Membership : commanderLeftCount m' = commanderLeftCount m}|
  ```
  (Because `commanderExchange25 x` is the count-level transition
  `∑_y transitionWeight (count x) (count y) · pointMass y`, and
  `membershipLift y` is uniform over the memberships with count `count y`;
  exactly one `y` has `count y = count m`, so the inner sum collapses.)

So the **exact counting identity** to prove is:

```
|{ (d,(L,R)) : project d = x, newLeftCards d L R = m }|
  · |{m' : Membership : count m' = count m}|
= transitionNumerator 99 50 25 (count x) (count m)
  · |fiber project x| · choose 50 25 · choose 49 25
```
(everything exact, no `Rat`; `transitionWeight = transitionNumerator /
transitionDenominator` with `transitionDenominator 99 50 25 =
choose 50 25 · choose 49 25`).

## The two parts

**(i) The count transition matches `transitionWeight`.** Decompose the LHS by
the *new count*. Let `x = count d` (old count), and for the chosen `(L,R)` let
`i = markedInLeft d L` (marked cards leaving the left pile) and
`j = markedInRight d R` (marked cards entering). Then
`count(newLeftCards d L R) = x - i + j` (by `newLeftOriginalCount_eq`).

Key counting fact (independent of the specific deck `d`, only of the count `x`):

- The left pile has `x` marked / `50 - x` unmarked cards. The number of
  25-subsets `L` of the 50 left positions with `markedInLeft d L = i` is
  `choose(x, i) · choose(50 - x, 25 - i)`.
- The right pile has `50 - x` marked / `x - 1` unmarked cards. The number of
  25-subsets `R` with `markedInRight d R = j` is
  `choose(50 - x, j) · choose(x - 1, 25 - j)`.
- `i` (a function of `L`) and `j` (a function of `R`) are independent; the
  `|fiber project x|` factor cancels against the sum over `d`.

Therefore
```
P(new count = y) =
  ∑_{i,j : x - i + j = y}
    choose(x, i)·choose(50-x, 25-i)·choose(50-x, j)·choose(x-1, 25-j)
    / (choose 50 25 · choose 49 25)
```
which is *exactly* `transitionWeight 99 50 25 x y` (the numerator is the
`a := i`, `b := y - (x - i)` term of `transitionNumerator`). This is the
count-level part and is the more mechanical of the two.

**Suggested Lean lemmas for (i):**
- `leftHyper : |{L ⊆ 50-positions : |L| = 25, markedInLeft d L = i}| =
    choose (leftOriginalCount d) i · choose (50 - leftOriginalCount d) (25 - i)`
  (bijection between such `L` and `i`-subsets of `markedLeftPos d` ×
  `(25-i)`-subsets of its complement).
- `rightHyper` (the `Fin 49` / `50 - x` marked / `x - 1` unmarked analogue).
- The `|fiber project x|` cancellation: the counts above are *independent of
  `d`*, so summing over the (uniform) project fiber is a factor of
  `|fiber project x|`.

**(ii) Within-count uniformity (the harder half).** *Given* the new count `y`,
the new membership `newLeftCards d L R` must be **uniform** over the
`y`-fiber (the memberships with count `y`), *not* biased toward some of them.

This is a *symmetry* statement: the exchange treats all count-`y` memberships
equivalently, so the mass
`|{ (d,(L,R)) : project d = x, newLeftCards d L R = m }|` is *independent of
the specific `m`* for fixed `count m = y`. A clean formalization: there is a
`Deck`-permutation (preserving the marked/unmarked division) carrying any
count-`y` membership `m` to any other count-`y` membership `m'` while
commuting with the exchange action, giving a bijection between the two preimage
sets. Alternatively, argue the mass depends on `m` only through `count m`.

This is the genuinely hard half and the main open sub-goal.

## What is already in the file (green, committed)

- `newLeftCards d L R`, `newLeftOriginalCount_eq`, `newLeftCards_card`.
- `leftChoices`/`rightChoices`/`exchangeChoice` (uniform `(L,R)` choice type,
  `Fintype` via `Finset.fintype`, `Nonempty` via the `{0,…,24}` witnesses).
- `newMembership d L R`, `rawExchangeMembership : FiniteKernel Deck Membership`,
  `rawExchange : FiniteKernel Deck Deck`.
- `rawExchange_membership_pushforward`
  (`comp rawExchange (deterministic membership) = rawExchangeMembership`).
- `hMembershipExchange_lhs_reduces` (the LHS = `comp (fiberLaw project) rawExchangeMembership`).

## Dependencies and gotchas

- `membershipLift_localLift_eq_fiberLaw` (F2 capstone) gives the two-layer law
  = `fiberLaw project project_surjective`.
- **Default `simp` / `field_simp` recurse** over `membership`/`leftCards` (they
  unfold into `Equiv.Perm (Fin 99)` terms). Use `simp only` with an explicit
  lemma list, `by_cases`/`split_ifs` on `Membership`/`Nat` equalities, and
  exact `Rat`/`Nat` arithmetic. Do *not* enumerate `99!` with `native_decide`.
- `commanderExchange25 = Matrix` kernel built from `commanderExchange25Matrix`
  (`transitionWeight 99 50 25`); `membershipLift y` is uniform over the
  count-`count y` membership fiber (F2c).
- The `Membership` type is `{S : Finset (Fin 99) // S.card = 50}`;
  `membershipCount m = (m.1 ∩ leftOrigSet).card` is its count.

## F3 item 3 part (i): the hypergeometric count — approach and current wall

The count-level part (i) reduces to the standard hypergeometric fact: the
`k`-subsets of `s = a ∪ b` (disjoint) with exactly `i` elements in `a` are
`choose |a| i · choose |b| (k - i)` (for `i ≤ k`). This is a bijection with
`(i`-subsets of `a`) × (`(k - i)`-subsets of `b`), via the disjoint-union
decomposition `L = (L ∩ a) ∪ (L \ a)` and `L \ a ⊆ b`.

**Committed foundation (Nov 12, `Shufflemath/FinsetCombinatorics.lean`):**
`union_inter_parts` — for `A ⊆ a`, `B ⊆ b`, `a ∩ b = ∅`:
`(A ∪ B) ∩ a = A` and `(A ∪ B) ∩ b = B`. The disjoint-union decomposition is
unique, so the `(A, B)` pair is recoverable from its union.

**Wall hit (Nov 12):** the next lemma, `sdiff_in_complement`
(`L \ a ⊆ b ∧ (L ∩ a) ∪ (L \ a) = L`), trips on applying the subset hypothesis
`hLs : L ⊆ s` to a membership `hxL : x ∈ L` to get `x ∈ s`. In this build,
`Finset ⊆` is `s.1 ⊆ t.1` (a `Set`/`Multiset`-based relation, see
`Finset.subset_def`/`mem_coe`), and:
- `exact hLs hxL` **succeeds when `x ∈ s` is the direct goal**;
- but `have hxs : x ∈ s := hLs hxL` (and `:= by exact hLs hxL`) **fail** with
  "Type mismatch: After simplification, term" / "assumption failed".

The `rcases`-derived `hxL` also behaves differently from a binder-derived
`hxL`. The clean fix is to route the membership through `Finset.mem_coe`
(`x ∈ (L : Set) ↔ x ∈ L`) explicitly, or to prove the two parts via the `Set`
coercion where `hLs` applies cleanly. Once `sdiff_in_complement` is in, the
`inter_powersetCard_count` counting lemma follows by showing the `Finset.image`
of the map `L ↦ (L ∩ a, L \ a)` over the filtered `k`-subsets equals the
`(i`-subsets of `a`) × (`(k - i)`-subsets of `b`) `Finset` product (whose
cardinality is the product of the two `choose`s), with injectivity via
`union_inter_parts`.

Next agent: rework `sdiff_in_complement` with an explicit `Finset.mem_coe`
conversion for the `hLs` application, then build `inter_powersetCard_count`,
then instantiate for the left pile (`leftHyper`) and right pile (`rightHyper`)
to close part (i). Part (ii) (within-count uniformity) remains the genuinely
hard symmetry statement.
