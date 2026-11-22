# Gate 6 batch-5b handoff: `rhoRoundIdeal 99 50 … = localLift segMembership`

**Status (2026-11-22):** The headline is **fully decomposed and 4 of its
components are landed** in `Shufflemath.GSRSegHeadline`. The last two pieces
(`roundImage_iff_segMembership` and the headline assembly itself) are blocked by
a **genuine elaboration/heartbeat wall**, not by missing mathematics. This note
records exactly where things stand and the specific workaround options.

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

## Landed (in `Shufflemath.GSRSegHeadline`, all build clean, full verify green)

| lemma | role |
| --- | --- |
| `finiteDeck_leftCards_99_50_eq_commander` | the 99-card ↔ `FiniteDeck` frame bridge (`leftCards` at `N=99,m=50` equal) |
| `roundEmbedMap_eq_fiberOrbit_val` | `roundEmbedMap p = (fiberMap id p).val` (the structural link) |
| `distProduct_uniform_is_uniformProd` | the two one-sided uniforms = the product uniform |
| `segStart` | `Equiv.refl (Fin 99)` as the segregated start |
| `roundEmbedMap_99_50_injective` | distinct within-pile pairs give distinct image decks (via `fiberMap_injective` + the structural link) |
| `fiberSet_segMembership_card` | `fiberSet segMembership` has `50!·49!` decks (via `Fintype.card_subtype` + `fiberSegMembership_card`) |

## Remaining (2 pieces, both blocked by the heartbeat wall)

1. **`roundImage_iff_segMembership (d) : (∃ p, roundEmbedMap p = d) ↔
   membership d = segMembership`** — the image of the within-pile round is
   exactly the segregated fiber. The forward half (image ⇒ keeps fiber) is a
   few `rw`s of landed lemmas; the reverse half uses the landed
   `fiberOrbit_surjective`. The blocker is the **`membership d = segMembership ↔
   leftCards d = segLeft` bridge** (`hL`): `membership d = ⟨leftCards d,
   leftCards_card d⟩` and `segMembership = ⟨segLeft, leftPositions_card⟩` are
   `Membership`-subtypes, and equating them (or even `Subtype.ext`-ing the two
   proof-field cardinality proofs) triggers **`whnf` maxHeartbeats (200000)**
   in every attempt — the 99-card `Membership` def + its proof-field is too
   heavy to unfold inside the nested equality, regardless of proof phrasing.

2. **The headline assembly** — once (1) lands it is short: `ext d`, `rw [hstep,
   map_mass_eq_univ_fiber]` on the LHS (uniform product pushed through
   `roundEmbedMap`), collapse the preimage sum to a single term via
   `roundEmbedMap_99_50_injective` + (1) + `fiberSet_segMembership_card`, and
   `rw [localLift, fiberLaw_mass]` on the RHS. The `rw [hstep,
   map_mass_eq_univ_fiber]` chain over the heavy `rhoRoundIdeal`/`membership`
   defs is where the earlier full-chain attempt also hit the heartbeat wall.

## Workaround options for the next session (in order of preference)

1. **Per-lemma `set_option maxHeartbeats := <large>`** (e.g. `400000`) around
   *just* `roundImage_iff_segMembership` and the headline. AGENTS.md says to
   avoid *globally* disabling heartbeat limits; a targeted, justified opt-in on
   the two heavy theorems (with a comment explaining the `Membership`
   proof-field blowup) is defensible. This is the lowest-risk way to land it.
2. **Restructure `Membership`** to drop the redundant proof-field (make it a
   plain `Finset (Fin 99)` with the card constraint carried separately, or a
   `Sigma` with a `DecidableEq`-only predicate), so `Subtype.ext` on
   memberships stops unfolding a heavy cardinality proof. Bigger change; touches
   `CommanderMembershipKernels` and its dependents.
3. **`HEq`/`proofIrrelevance` route**: state the `hL` bridge at the level of
   the `.1` field (`leftCards`) only and use `Subtype.ext` with
   `proofIrrelevance` for the `.2` field, avoiding the heavy `simpa` on the
   proof-field. Worth a probe before option 1.

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
