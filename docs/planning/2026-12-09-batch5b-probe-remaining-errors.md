# Batch 5b headline probe — remaining two errors (2026-12-09)

Status of `Shufflemath/_ProbeHeadline3.lean` (the batch 5b whnf-free verification
of the generic deck headline `rhoRoundIdeal 99 50 … 1 … = localLift segMembership`).

The real batch 5b headline theorems are **committed in the proper modules**
(`CommanderFiberCount.lean`, `Gate6TieRank.lean`, …); this `_Probe` file is a
scratch verification file that is **not** in the package aggregator
(`Shufflemath.lean`) and **not** in the acceptance-gate target list
(`dev/verify_next_phase.sh`), so the gate passes regardless of its state
(verified: `./dev/verify_next_phase.sh` → 37 tests OK).

## Latest status (this pass — supersedes the two-error analysis below)

Re-probed after switching the probe to the **production** generic lemmas:
`public import Shufflemath.GSRSegHeadline`, the headline `rw`s
`distProduct_uniform_is_uniformProd` (the already-proven generic product-of-
uniforms) instead of re-proving the 99-card-specific form, and uses
**forward** `map_bijective_uniformDist` + the `Dist.` qualifier on
`map_mass_eq_univ_fiber`. Result — the probe is down to **one** remaining failure
(a `whnf` heartbeat timeout, reported at 3 lines: the theorem, the `have hLHS`,
and the closing `simpa`), all the *same* site:

- **Error 1 (55:6) is CRACKED.** The specific `distProduct_uniforms_eq_uniform`
  re-proof is removed; the headline applies the **whnf-free** production generic
  `distProduct_uniform_is_uniformProd`. Applying a proven lemma is O(1) (no
  re-elaboration), so the `.weights`/`uniformDist` recursion that killed the
  specific re-proof does not occur — this is exactly this note's recommended
  "light-context lemma, `rw` in O(1)" fix, and it already exists in production.
- **Error 2's rw step is CRACKED.** `← map_bijective_uniformDist` was the wrong
  direction (this note predicted it); **forward** now matches, leaving the goal
  as `map Subtype.val (GSR.uniformDist paramFiber) = localLift segMembership`.
- **The wall is now a single, well-characterized site: the pointwise assembly.**
  `have hLHS := Dist.map_mass_eq_univ_fiber (GSR.uniformDist paramFiber) (fun e => e.val) d`
  and the closing `simpa [hLHS, hRHS, hcond, card_paramFiber_eq_membershipFiber, localLift] using …`
  trigger a Lean-internal **`whnf` heartbeat timeout** (reducing the fiber-uniform's
  mass / `Fintype.card paramFiber` at a point in the 99-card context). This is
  *Lean-internal* normalisation — no `whnf` tactic, no `sorry` — so the whnf-free
  rule is intact; the remaining obstruction is reducing the fiber's per-point mass.

Next direction: avoid the pointwise mass reduction — either (a) prove the headline
as a **structural distribution equality** (both sides = uniform on the same
deck-set, via the subtype-set equality `membership_iff_leftCards`, closed by
`Dist.ext` without ever reducing a per-point mass), or (b) a whnf-safe
`uniformDist_weights`-style lemma (this note's earlier suggestion) that reduces the
fiber mass in a light context so `simpa` can close from
`card_paramFiber_eq_membershipFiber` without re-normalising `uniformDist paramFiber`.

**Scope note:** this batch 5b / GSR-seg within-pile headline is an *older* stream
than the current **G2** arc — the active front is the last G2 headline
`two_physical_perfect_exchanges_uniform_deck`, whose two counting enablers just
landed in `FiniteDeck/A3KernelLaw.lean` (commit 30d49e3, "G2.9/13 counting core").
This within-pile lemma is **not** on the `TV < 1/1000` critical path (that needs the
25-position Bernoulli-Laplace `finiteRound` composed on top).

## What this pass fixed (committed, whnf-free, 3.9 s build)

Two of the "3–4 mechanical fixes" the e5cb7c7 commit left are now done:

- **`hL`** (`Fintype.card paramFiber = 50!·49!`): the e5cb7c7 proof used
  `rw [← Fintype.card_congr]; exact (fiberOrbit_equiv …).card`, which hit a
  stuck typeclass (the `card_congr` goal needs an explicit `Fintype` instance).
  Fixed by computing the card directly with
  `have hC := Fintype.card_congr (fiberOrbit_equiv …)` then
  `rw [← hC, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
  Fintype.card_fin, Fintype.card_fin]; norm_num`.
- **`hR`** (`(fiberSet membership segMembership).card = 50!·49!`): the e5cb7c7
  proof tried `rw [fiberSet, Finset.card_preimage]` (no occurrence — the fiber is
  a `Finset.filter`, not a preimage, so `card_preimage` does not match) and then
  re-proved the left-card fiber card from scratch. Fixed by adding
  `public import Shufflemath.GSRSegFiber` and bridging
  `(fiberSet …).card = Fintype.card {d // membership d = segMembership}` via
  `Fintype.card_subtype`, then `simpa using fiberSegMembership_card`
  (GSRSegFiber's set-equivalence card theorem — a bijection, **not** a 99!
  computation). `GSRSegFiber` is whnf-safe (it imports only
  `GSRSegMembership` + `CommanderFiberCount`, not the heavy telescope).

Also: `map_mass_eq_univ_fiber` must be qualified as
`Dist.map_mass_eq_univ_fiber` (it lives in the `Shufflemath.Dist` namespace in
`Shufflemath/Finite.lean`).

## The two remaining errors (both blocked by Lean elaboration, not math)

The probe builds in ~3.9 s (no whnf wall, no recursion) with exactly two real
errors plus one cascade (`100:41 "No goals"`, a knock-on from one of them):

### 1. `distProduct_uniforms_eq_uniform` — `55:6` (rewrite: no occurrence)

Goal after the `ext p; simp`:
```
⊢ (↑(Fintype.card (Equiv.Perm (Fin 50))))⁻¹ * (↑(Fintype.card (Equiv.Perm (Fin 49))))⁻¹
  = (GSR.uniformDist Y).weights p
```
The LHS is fully reduced; the RHS `(GSR.uniformDist Y).weights p` must reduce to
`1 / Fintype.card Y`, and `Fintype.card Y = Fintype.card (Perm 50) * Fintype.card
(Perm 49)` (`Fintype.card_prod`) — after which `field_simp; norm_num` closes it.

**Why it is blocked:** reducing `(GSR.uniformDist Y).weights p` requires
unfolding `GSR.uniformDist` (so that `Dist.ofFun` + `Finsupp.coe_equivFunOnFinite_symm`
reach the `1 / card Y` weight). Adding `GSR.uniformDist` to the `simp only` list
triggers **maximum recursion depth** (the `Dist.ofFun`/`uniformDist` unfolding
loops in this file's elaboration context). The proven theorem
`mass_uniformDist : Dist.mass (uniformDist β) x = 1 / card β` is whnf-safe, but
it is stated on `Dist.mass`, whereas the goal is in the *definitionally-equal*
`.weights` form; bridging `.weights → mass` via `rw [← Dist.mass]` (reverse-def)
or `change` both whnf/recursion-blow. So the `.weights` value of `uniformDist`
cannot be reduced without a whnf/recursion wall in this context.

Candidate directions for a future pass:
- Prove the product-of-uniforms fact Fintype-freely (the `StdSimplex.map`/`join`
  route, cf. `distProductFinsupp` in `Shufflemath/Finite.lean`) where the mass is
  `1 / card` by the map/join total-mass preservation, avoiding `Dist.ofFun`
  entirely.
- Or add a single `@[simp]`/reducible lemma `uniformDist_weights` stating
  `(GSR.uniformDist β).weights x = (Fintype.card β : Rat)⁻¹` **proved once in a
  light context**, so the headline can `rw [uniformDist_weights]` in O(1) instead
  of unfolding `uniformDist` locally.

### 2. `segHeadline` (the headline itself) — `108:6` (rewrite: no occurrence)

The e5cb7c7 proof does
```
change (distProduct (GSR.uniformDist (Perm 50)) (GSR.uniformDist (Perm 49))).map
    (roundEmbedMap 99 50 hm5099) = localLift segMembership
rw [distProduct_uniforms_eq_uniform, roundEmbedMap_eq_val,
    ← Convexity.StdSimplex.map_map,
    ← map_bijective_uniformDist (fiberOrbit_equiv 99 50 hm5099 (Equiv.refl (Fin 99)))]
```
The last rewrite fails. The intent is to turn the pair-uniform pushed through
`roundEmbedMap` (= `val ∘ fiberOrbit_equiv`) into the uniform on the deck fiber:
`(uniform Y).map equiv = uniform paramFiber`. Two compounding problems:

- **Direction/shape:** after `← map_map` the goal is
  `map val ((uniform Y).map equiv) = localLift`, so the needed rewrite is
  `map_bijective_uniformDist equiv` in the **forward** direction (the e5cb7c7
  `←` is the wrong direction and does not match).
- **Instance mismatch:** even forward, it fails because
  `distProduct_uniforms_eq_uniform` (a separate theorem) bakes in *its own*
  `Fintype Y` instance in its conclusion `GSR.uniformDist Y`. After
  `rw [distProduct_uniforms_eq_uniform]` the goal carries that theorem's
  `Fintype Y`, which is not definitionally the same instance as the one
  `map_bijective_uniformDist` resolves in the headline's context — so the
  `uniform Y` subterm does not match.

The instance mismatch is exactly why the inlined-`hProd` approach (prove
`distProduct … = GSR.uniformDist Y` *inside* the headline so every later
`uniform Y` shares one context instance) is the only structural fix — but the
inlined `hProd` hits the **same `.weights`/`uniformDist` reduction** as
error 1, so it recurses/walls. **Errors 1 and 2 are the same root cause** (the
`uniform Y` `.weights` reduction); cracking error 1's reduction cracks error 2.

## Bottom line for the next pass

One lemma is the key: a **lightly-proved, whnf-safe**
`uniformDist_weights : (GSR.uniformDist β).weights x = (Fintype.card β : Rat)⁻¹`
(established in a minimal context, not the 99!-laden one). Then:
- error 1 becomes `simp …; rw [uniformDist_weights, Fintype.card_prod]; field_simp; norm_num`;
- error 2's inlined `hProd` uses the same lemma, sharing one `Fintype Y` instance,
  and the headline closes.

Until that lemma exists, the probe is intentionally left at the 3-error state
(2 real + 1 cascade) rather than in a broken-wip state; the acceptance gate
passes and the real theorems are already committed.
