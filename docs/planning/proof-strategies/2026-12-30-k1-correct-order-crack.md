# Gate-6 K1 — the **correct-order** crack (2026-12-30)

Resolves the "open question" at the bottom of
`docs/planning/proof-strategies/2026-12-30-k1-count-split-whnf-wall.md` and cracks the
ideal Gate-6 K1 capstone. **Bottom line:** the residual sub-lemma the opposite-order
reduction lands on, `k1_swapLift_eq_exchangeLift`, is **false as stated** — but not for
the reason the 2026-12-25 note suspected. The real cause is a **composition-order
category error**: `Gate6Crux.fullRoundIdeal = conv rho99Ideal swapLaw` is the
*local-then-swap* round, while the goal specifies the physical round as
*swap-then-local* = `conv swapLaw rho99Ideal`. In the correct order the ideal side
keeps the deck-specific exchange law, and the capstone is a clean consequence of two
already-committed lemmas. The correct-order theorem **now builds** (see §4).

## 1. The composition-order fact (verified from definitions, not the notes' labels)

The notes disagree about which order is which (the `Gate6Crux` comment calls
`conv rho99Ideal swapLaw` "swap first"; the 2026-12-25 "settled" note labels
`comp (PAK swapLaw) (PAK rho99Ideal)` "Riffle-first"). Resolved directly from the
definitions:

- `conv μ ν = (μ × ν).map (fun (x, y) => x * y)` (`FiniteDeck/ActionConvolution.lean:70`).
- `act (a * b) d = act b (act a d)` (`act_composition`) ⇒ the product `x * y` acts as
  "**x first, then y**".
- `convAsApply`: `conv μ W = apply μ (permutationActionKernel W)` ⇒ **`conv μ W`
  applies `μ` first, then `W`.**

Therefore `Gate6Crux.fullRoundIdeal = conv rho99Ideal swapLaw` = **within-pile riffle
first, then the literal swap = local-then-swap** — the *opposite* of the goal's
"swap-then-local". The `Gate6Crux` comment on `fullRoundFinite`/`fullRoundIdeal`
("physical order … swap first") is wrong and should be fixed (follow-up; the TV bound
`gate6_crux` is order-independent via `convContraction`, so it is cosmetic).

## 2. Why the opposite-order residual is false

The 4-step reduction in `_ProbeK1cap2` / `_ProbeGate6K1` (all steps valid:
`k1_lhs_bookkeeping`, `k1a_riffle_half`, `← apply_comp`, `apply_pointMass`) sends the
opposite-order capstone to

```
k1_swapLift_eq_exchangeLift :
  apply (localLift (membership d)) (PAK swapLaw) = apply (rawExchangeMembership d) localLift
```

- **LHS is fiber-symmetric**: `localLift (membership d)` depends on `d` only through
  `membership d`, and `PAK swapLaw` is a fixed kernel, so the whole LHS is a function
  of `membership d` alone.
- **RHS is deck-specific**: at a deck `X` it equals
  `(1/F) · mass (rawExchangeMembership d) (membership X)` (by `localLift`'s support),
  and `rawExchangeMembership d` reads the *specific cards at specific positions of
  `d`* — `newLeftCards d L R = {d (leftPosition l) : l ∉ L} ∪ {d (rightPosition r) :
  r ∈ R}` (`CommanderPhysicalExchange.lean:60`). So the mass at `membership X`
  depends on `d`'s card *arrangement*, not just its 50-card membership.

A function of `membership d` cannot equal a function of `d`'s full arrangement for all
`d`: two decks with the same membership but different arrangements give the same LHS
but (generically) different RHS (the membership fiber has `50!·49! ≫ 1` members). So
`k1_swapLift_eq_exchangeLift` — and hence the opposite-order capstone — is **false**.

The step that causes the damage is `k1a_riffle_half` being applied to the *whole* ideal
half: it fiber-averages `apply (pointMass d) (PAK rho99Ideal)` into the fiber-uniform
`apply (pointMass (membership d)) localLift`, **discarding the deck-specific
arrangement** that the exchange side still carries. That averaging is correct for the
*isolated* ideal riffle, but it is a category error when composed into the round at
the local-then-swap order.

## 3. Why the correct order works

With `fullRoundIdealCorrect = conv swapLaw rho99Ideal` (swap first, then riffle), the
ideal side never loses the specific-deck information before the riffle, and the riffle
only *coarsens to the membership and then uniformizes* — exactly the
exchange-then-local-reset. No fiber-averaging of a deck-specific term occurs at a stage
that must keep it.

## 4. The crack (`Shufflemath/_ProbeK1correctOrder.lean` — builds, no `sorry`)

```
fullRoundIdealCorrect.map (fun x => act x d) = apply (rawExchangeMembership d) localLift
```
where `fullRoundIdealCorrect = conv swapLaw rho99Ideal`. Proof, four committed lemmas
+ one new linearity lemma:

1. `convPush_eq_pointMassComp` (generic; `_ProbeGate6K1`) — LHS
   `= apply (pointMass d) (comp (PAK swapLaw) (PAK rho99Ideal))`.
2. `← apply_comp` — `= apply (apply (pointMass d) (PAK swapLaw)) (PAK rho99Ideal)`.
3. **`riffleApply` (new)** — `apply μ (PAK rho99Ideal) = apply (μ.map membership)
   localLift` for *any* deck-law `μ`: the ideal riffle preserves the membership and
   uniformizes within each fiber, so it depends on `μ` only through `μ.map membership`.
   Proved from `k1a_riffle_half` (point-mass form) + `paK_rho99Ideal_eq_localLift`
   (the kernel-row form) + `StdSimplex.map_map`. This is the whole new content.
4. `hswapmap` — `((apply (pointMass d) (PAK swapLaw)).map membership) =
   apply (pointMass d) (rawExchangeMembership)`, from
   `k1_swapMembership_eq_exchangeMembership` (`comp (PAK swapLaw) (deterministic
   membership) = rawExchangeMembership`) + `apply_deterministic_eq_map` +
   `apply_comp`. Then `apply_pointMass` closes it.

No `99!`/`99!³` enumeration, no `maxHeartbeats 0`, no K1b extensive counting, no
right-pile fiber-bijection crux. The only new mathematical content is `riffleApply`
(linearity of the ideal riffle), which is a direct corollary of the already-committed
`k1a_riffle_half`.

## 5. What this means for the goal / next steps

The direct-K1 milestone (`.pi-glla/goals/2026-11-24-direct-k1-milestone.md`) prescribed
exactly this: *"Define correct-order `conv swapLaw rho99Ideal` and `conv swapLaw
rho99Finite`, prove their ideal kernel equality directly via the already-proved
`k1a_riffle_half`."* The ideal kernel equality is now **promoted to a real module**:

1. ✅ **Promotion (DONE, 2026-12-30).**  Two new real modules, both in the
   `Shufflemath.lean` aggregator + `dev/verify_next_phase.sh` (verify passes, 37 tests
   OK): **`Shufflemath/K1Wall.lean`** (the per-deck orbit-fiber uniformity
   `k1wall_riffle_push_mass_factorial` + `rho99Ideal_pairs` + the `P99` pair-space
   lemmas — promoted verbatim from `_ProbeK1wall`; all-real-module deps) and
   **`Shufflemath/Gate6K1Capstone.lean`** (`convPush_eq_pointMassComp`,
   `k1a_riffle_half`, `paK_rho99Ideal_eq_localLift`, `riffleApply`,
   `fullRoundIdealCorrect`, `k1_capstone_correct` — importing `K1Wall` + the real
   modules, **no probe imports**). The old probes `_ProbeK1wall` / `_ProbeGate6K1`
   are marked superseded (retained only for their opposite-order dependents), and the
   probe `_ProbeK1correctOrder` was deleted (fully superseded by `Gate6K1Capstone`).
   The two new modules' names duplicate the probe copies but live in **disjoint
   import graphs** (the aggregator imports no probes), so no name collision.

Remaining to fully close Gate-6 K1:

2. ✅ **Finite version (DONE, session 80).**  `fullRoundFiniteCorrect = conv
   swapLaw rho99Finite` (the physical swap-then-local finite round) is defined and
   its TV-from-ideal bound is proved, both in **`Shufflemath/Gate6K1Capstone.lean`**
   (next to `fullRoundIdealCorrect` / `k1_capstone_correct`):
   - **`gate6_crux_correct`** : `TV(fullRoundFiniteCorrect, fullRoundIdealCorrect) ≤
     2401/8388608 = δ1` — the mirror of `Gate6Crux.gate6_crux` but in the correct
     order: the fixed swap law is on the *left*, so the bound is the left-convolution
     contraction `convContractionLeft` (item 3 above) composed with the committed G6.1
     `oneRoundDeckTV_le_delta1` — a three-step calc, no collision counting, no 99!.  The
     old `Gate6Crux.gate6_crux`/`fullRoundFinite`/`fullRoundIdeal` are the *opposite*
     (local-then-swap) order; they stay as-is (still true, cosmetic).
   - **`fullRoundDeck_correct_le_delta1`** : one physical round from deck `d` is within
     `δ1` of the perfect round (one `tv_map_contraction` on `gate6_crux_correct`),
     mirroring `Gate6Crux.fullRoundDeck_le_delta1` in the correct order.
3. ✅ **One-round TV bound (DONE, 2026-12-30 / session 80).**  The milestone's
   "generic left-convolution contraction" (the `convContraction`-style
   non-expansion, but on the *left* factor: `conv S I` vs `conv S F`) is proved as
   **`Shufflemath.ConvContractionLeft.lean`, `convContractionLeft`** (in the
   aggregator, builds, no `sorry`): `TV(conv S F, conv S I) ≤ TV(F, I)`.  It is the
   mirror of `Gate6Crux.convContraction` (which fixes `S` on the *right*); the
   correct-order finite headline has the fixed swap law `S` on the *left*, so this
   is the contraction it needs.  Fintype-free: `conv` is re-expressed as
   `FiniteKernel.apply` over the swap support and the inner per-row mass
   difference is bounded by the TV of the two permutation-action kernels via
   `tv_bijective_invariance` (a pushforward-TV equality), so it never forces a 99!
   reduction.
4. **Fix the `Gate6Crux` comment** (it mislabels the order; cosmetic only).

The opposite-order file (`_ProbeGate6K1` / `_ProbeK1cap2`) and its `sorry`'d
`K1_oneRoundLaw_eq_exchangeThenLocalReset` are marked dead (see the header notes) —
it proves the wrong round and the residual is false, so no amount of work on
`k1_swapLift_eq_exchangeLift` can close it.
