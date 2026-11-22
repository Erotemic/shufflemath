# Gate 6 batch-5b handoff: `rhoRoundIdeal 99 50 … = localLift segMembership`

**Status (2026-11-24):** The headline is **fully decomposed and 6 of its
components are landed** (4 in `Shufflemath.GSRSegHeadline`, 2 membership bridges
in `Shufflemath.GSRSegMembership`). The last two pieces
(`roundImage_iff_segMembership` and the headline assembly itself) are blocked by
a **genuine definition-network elaboration/heartbeat wall**, not by missing
mathematics. This note records exactly where things stand, the 7 approaches
tried, and the structural fix the next session should pursue.

## The statement (verified type-correct)

```lean
theorem rhoRoundIdeal_eq_localLift_segMembership
    (h99 : 50 ≤ 99) (hL : 50 ≤ 99) (hR : 49 ≤ 99) (a : Nat) (ha : 0 < a) :
    rhoRoundIdeal 99 50 h99 hL hR a ha = localLift segMembership := …
```

Both sides are `Dist (Equiv.Perm (Fin 99))`:
- `rhoRoundIdeal 99 50 …` = `distProduct (uniformDist (Perm 50)) (uniformDist
  (Perm 49)) |>.map (roundEmbedMap 99 50)`.
- `localLift : FiniteKernel Membership Deck = Membership → Dist Deck`, and
  `localLift = fiberLaw membership membership_surjective` (the uniform
  fiber-law). `localLift segMembership d = (if membership d = segMembership then
  (fiberSet membership segMembership).card⁻¹ else 0)` by the ready-made
  `fiberLaw_mass` — **so the RHS needs no work beyond `rw [localLift,
  fiberLaw_mass]`**.

Both sides assign `(fiberSet membership segMembership).card⁻¹ = (50!·49!)⁻¹`
to each deck in the segregated fiber and `0` elsewhere.

## Landed (all build clean, full verify green)

In `Shufflemath.GSRSegHeadline`:

| lemma | role |
| --- | --- |
| `finiteDeck_leftCards_99_50_eq_commander` | the 99-card ↔ `FiniteDeck` frame bridge (`leftCards` at `N=99,m=50` equal) |
| `roundEmbedMap_eq_fiberOrbit_val` | `roundEmbedMap p = (fiberMap id p).val` (the structural link) |
| `distProduct_uniform_is_uniformProd` | the two one-sided uniforms = the product uniform |
| `segStart` | `Equiv.refl (Fin 99)` as the segregated start |
| `roundEmbedMap_99_50_injective` | distinct within-pile pairs give distinct image decks (via `fiberMap_injective` + the structural link) |
| `fiberSet_segMembership_card` | `fiberSet segMembership` has `50!·49!` decks (via `Fintype.card_subtype` + `fiberSegMembership_card`) |

In `Shufflemath.GSRSegMembership` (kept in the light import context — no
`WithinPileOrbit` — so the `Membership` proof-field never blows up `whnf`):

| lemma | role |
| --- | --- |
| `segMembership_one_eq_segLeft` | `segMembership.1 = segLeft` (light `.1` projection) |
| `membership_iff_leftCards (d)` | `membership d = segMembership ↔ leftCards d = segLeft` (via `Subtype.ext`/`congrArg Subtype.val` on `.1` only) — the membership-side bridge the headline's (1) needs |

## Remaining (2 pieces)

1. **`roundImage_iff_segMembership (d) : (∃ p, roundEmbedMap p = d) ↔
   membership d = segMembership`** — the image of the within-pile round is
   exactly the segregated fiber. **Both halves are otherwise complete** (forward =
   `fiberMap`'s fiber-field + the frame bridge; reverse = the landed
   `fiberOrbit_surjective`). The wall, **definitively characterized this session
   (7 independent attempts, all failing)**: the membership↔left-card bridge
   `membership d = segMembership ↔ leftCards d = segLeft` is **light in
   isolation** (proved in `GSRSegMembership` as `membership_iff_leftCards` —
   committed), but `roundImage_iff_segMembership` must live in a module importing
   `FiniteDeck.WithinPileOrbit` (for `fiberOrbit_surjective`) **and** mention
   `membership d = segMembership` in its statement; that combined context makes
   even the *statement* hit `whnf` maxHeartbeats (200000, and still failing at
   1200000 = 6×). The pathology is a **super-linear elaboration interaction**
   between the 99-card `FiniteDeck.leftCards 99 50 h99` (a 50-element `image` of
   `leftPositions`) and the `Membership`/`fiberMap`/`fiberOrbit` definitions —
   not a proof-phrasing issue and not fixable by a heartbeat bump or by using the
   pre-proven bridge by reference.

2. **The headline assembly** — once (1) lands it is short (see below), but its
   LHS `rw [hstep, map_mass_eq_univ_fiber]` chain over `rhoRoundIdeal`/`membership`
   hits the same combined-context pathology.

**Conclusion:** this is a *definition-network elaboration-performance* blocker,
not a missing theorem. The fix is structural — most likely restructure `Membership`
/`leftCards` to a lighter form (plain `Finset` + a separate card invariant) so
the 99-card membership no longer carries a heavy proof-field that `whnf` blows up
on, OR move the 99-card `FiniteDeck.leftCards`/`fiberMap` normalization into a
`reducible`/opaque split. That is a definition-level change touching
`CommanderMembershipKernels`/`FiniteDeck`, best done as its own focused task with
a dedicated elaboration-perf investigation, not an incremental grind.

## Workaround options for the next session (in order of preference)

**What was established this session (do not re-derive):**
- The `Membership` proof-field blowup is **context-dependent, not a fixed
  constant**: the `.1`-projection bridge `segMembership.1 = segLeft` (via
  `dsimp only [segMembership]`, never touching the `.2` field) is **light in a
  minimal import set** (`GSRSegMembership` + `CommanderPermutation` +
  `CommanderMembershipKernels` only) but **blows up `whnf` once
  `FiniteDeck.WithinPileOrbit` / `GSRDeckRound` are imported** — even the trivial
  projection lemma times out in that environment. So the cost is a
  super-linear interaction between the `Membership`/`leftCards`/`fiberMap`/
  `fiberOrbit` definitions, not a one-off heavy constant.
- A **`set_option maxHeartbeats := 1200000` (6× default) does NOT fix it** — the
  same `whnf` timeout persists. A still-larger bump is *not* a viable path
  (it would be an unbounded, un-reviewable hack, and AGENTS.md steers away from
  heartbeat-limit hacks). **Do not pursue a heartbeat bump for this.**
- The `membershipFiber_iff_leftCardsFiber` lemma and any `rw [segMembership]` /
  `rw [membership]` (full-constructor) unfolding all blow up in the full context;
  only `.1`/`.val` projections stay light in isolation.

**Recommended structural fix (pick one):**
1. **Light-module split (lowest risk).** Prove the two membership bridges in
   their own small modules whose import graph excludes
   `FiniteDeck.WithinPileOrbit`/`GSRDeckRound`:
     - `segMembership_one = segLeft` : `segMembership.1 = segLeft` (`dsimp only
       [segMembership]` — light), and
     - `membership_iff_leftCards (d) : membership d = segMembership ↔
       leftCards d = segLeft` (via `Subtype.ext` on `.1` only — light in that
       context).
   Then prove `roundImage_iff_segMembership` in a module that imports those two
   *already-reduced* bridges + the fiber-orbit machinery, so the heavy
   `Membership` normalization never happens in the same elaboration pass as the
   `fiberMap`/`fiberOrbit` unfolding. (This is the most likely to succeed.)
2. **Restructure `Membership`** to a lighter form (e.g. a plain `Finset (Fin 99)`
   with the `card = 50` invariant carried separately, or a `Sigma` with a
   `DecidableEq`-only predicate), so equality of memberships stops forcing a
   heavy cardinality-proof normalization. Larger blast radius (touches
   `CommanderMembershipKernels` + dependents); use only if option 1 fails.

**Once `roundImage_iff_segMembership` lands**, the headline itself is short:
`ext d`, LHS = `rw [distProduct_uniform_is_uniformProd, map_mass_eq_univ_fiber]`
collapsing the preimage sum to one term (via `roundEmbedMap_99_50_injective` +
the iff + `fiberSet_segMembership_card`); RHS = `rw [localLift, fiberLaw_mass]`.
Watch the same context interaction there — if the LHS `rw` chain over
`rhoRoundIdeal` blows up, split it into small light lemmas the same way.

## Notes / invariants

- **No `propext`/`Classical` in the headline itself** — it's an equality of
  `Dist`s; the only `classical` is inside the already-proven `localLift` def
  (a documented dependency).
- Do **not** use the `open FiniteDeck` context for the 99-card lemmas without
  explicit `CommanderPermutation.`/`CommanderMembershipKernels.` prefixes —
  bare `leftCards`/`membership`/`Deck` are ambiguous between the two frames.
  All landed lemmas use the explicit prefixes.
- The probe workflow that worked: write the lemma in a `_Probe*.lean`, build
  `lake env lean` on it, iterate on the specific errors, then promote to
  `GSRSegHeadline` and run full verify.
