# Batch 5b headline — whnf-free assembly + exact remaining glue (2026-11-25)

Status: **the headline `rhoRoundIdeal 99 50 hm5099 (by norm_num) (by norm_num) 1 (by norm_num)
= localLift segMembership` is provable WITHOUT the 99!-enumeration whnf wall.** The probe
`Shufflemath/_ProbeHeadline3.lean` assembles it in **3.7 s** (no whnf/heartbeat) with only
*mechanical* lemma-level errors remaining. This doc records the breakthrough, the complete
structure, and the exact remaining fixes so the final landing is 1–2 focused builds.

## The breakthrough: whnf is import-context-dependent

- Importing `Shufflemath.GSRSegHeadline` (or the old `GSRDeckBridge` chain) makes `lake build`
  of this headline **blow up** (whnf > 36 s / heartbeat). The old "f4 equinumerosity is whnf
  wall" verdict (`docs/planning/proof-strategies/2026-11-19-f4-local-lift-whnf-blocked.md`)
  was a *build-context* artifact, not a theorem-level obstruction.
- The **whnf-free import set** (all light, pre-compiled):
  `Shufflemath.Finite`, `Shufflemath.GSR`, `Shufflemath.FiniteDeck.WithinPileOrbit`,
  `Shufflemath.GSRSegMembership`, `Shufflemath.CommanderPermutation`,
  `Shufflemath.FiberDisintegration`, `Shufflemath.CommanderMembershipKernels`,
  `Shufflemath.GSRDeckRound`, `Mathlib.Tactic` — wrapped in `namespace Shufflemath`.
- The proof stays on the **deck side** and only touches the *membership* kernel through
  pre-compiled lemmas (`membership_iff_leftCards`, `localLift_mass`), so it never forces the
  99! membership structure to whnf.

## Complete proof structure (all lemmas pre-compiled except two small local ones)

The headline reduces, step by step, to the fiber law:

1. **`distProduct_uniforms_eq_uniform`** (local, in the probe): the product of the two
   within-pile uniform laws is the uniform on the pair product `Y = Perm (Fin 50) × Perm (Fin 49)`.
   Proof: `ext p; simp [distProduct, Dist.ofFun, Dist.mass_ofFun, mass_uniformDist,
   Finsupp.coe_equivFunOnFinite_symm, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin];
   norm_num`.  (Both sides `= 1/(50!·49!)` pointwise.)
2. **`roundEmbedMap_eq_val`** (local): `roundEmbedMap 99 50 hm5099 = fun p => (fiberOrbit_equiv
   99 50 hm5099 (Equiv.refl (Fin 99)) p).val`.  `funext p; cases p; simp [roundEmbedMap,
   fiberOrbit_equiv, Subtype.val]`.  (`fiberOrbit_equiv` is `Equiv.ofBijective (fiberMap …)`,
   and `fiberMap … p = roundEmbedMap … p`.)
3. **`Convexity.StdSimplex.map_map`** (mathlib, `Analysis/Convex/BetweenList.lean`):
   `(M.map f).map g = M.map (g ∘ f)` — carried in reverse to rewrite
   `(uniform Y).map (val ∘ equiv)` as `((uniform Y).map equiv).map val`.
4. **`map_bijective_uniformDist`** (GSRDeckRound:578, pre-compiled):
   `uniformDist X.map (e : X ≃ Y) = uniformDist Y` — turns `((uniform Y).map equiv)` into
   `uniformDist paramFiber`.  After 3+4 the LHS is `(uniformDist paramFiber).map val`.
5. **`map_mass_eq_univ_fiber`** (Finite:556, pre-compiled): point mass of
   `(uniformDist paramFiber).map val` at `d` is `(if ∃ e : paramFiber, e.val = d then
   1/card paramFiber else 0)`.
6. **`localLift_mass`** (CommanderMembershipKernels:158, pre-compiled): point mass of
   `localLift segMembership` at `d` is `(if membership d = segMembership then
   1/card (fiberSet membership segMembership) else 0)`.
7. **`membership_iff_leftCards`** (GSRSegMembership:94, pre-compiled):
   `membership d = segMembership ↔ leftCards d = segLeft`.  This is the *fiber law* and the
   equinumerosity the old "wall" pointed at — but it is a **set equivalence, already proved**,
   not a 99! enumeration.  `paramFiber`'s predicate is exactly `leftCards e = segLeft`
   (`segLeft = leftPositions 99 50 hm5099 = leftCards (Equiv.refl)`), so
   `∃ e : paramFiber, e.val = d ↔ membership d = segMembership`.
8. **`card_paramFiber_eq_membershipFiber`** (local): `Fintype.card paramFiber =
   (fiberSet membership segMembership).card` — both are `50!·49!` (the same set of decks).

Then `ext d` + `simpa [hLHS, hRHS, hcond, card_…]` closes it: both point-mass formulas are
`1/(50!·49!)` on the same fiber deck-set, `0` elsewhere.

## Exact remaining fixes (3–4 mechanical steps)

The probe currently fails on these — all diagnosed, none mathematical:

1. **`Fintype.card Y` computation** (in `distProduct_uniforms_eq_uniform` and
   `card_paramFiber_eq_membershipFiber`): `Fintype.card (Equiv.Perm (Fin 49))` does not reduce
   under `norm_num` because the `Fintype (Perm 49)` instance is left as a stuck metavariable.
   **Fix:** use the exact lemmas `Fintype.card_prod` (Data/Fintype/Prod.lean:56) and
   `Fintype.card_perm` (Data/Fintype/Perm.lean:155, `Fintype.card (Perm α) = (Fintype.card α)!`)
   + `Fintype.card_fin`, *then* `norm_num`; add explicit
   `haveI : Fintype (Equiv.Perm (Fin 50)) := inferInstance` / `… (Fin 49)` / `… Y := inferInstance`
   before the `rw` so the instances are not metavariables.  (`Fintype.card (Perm (Fin n)) = n!`.)
2. **`hR` / membership-fiber card** (`card_paramFiber_eq_membershipFiber`): the
   `rw [Finset.card_preimage]` and the `Finset.card_congr`/`Finset.filter_congr` over
   `membership` — order them so the `membership_iff_leftCards d` rewrite happens *inside*
   `filter_congr`, then close with `Finset.card_univ_filter`-style set equality against
   `paramFiber` (both are `{d // leftCards d = segLeft}`).
3. **Headline `rw` sequencing** (`segHeadline`): after the `change` to
   `(distProduct …).map (roundEmbedMap 99 50 hm5099) = localLift segMembership`, the
   `rw [distProduct_uniforms_eq_uniform, roundEmbedMap_eq_val, ← Convexity.StdSimplex.map_map,
   ← map_bijective_uniformDist (fiberOrbit_equiv …)]` — one of these (likely `← map_map`)
   needs the composition written as `Function.comp` (the probe's `roundEmbedMap_eq_val` uses a
   `fun p => (… p).val`, so use `← Convexity.StdSimplex.map_map` after `simp [Function.comp]`
   or write the LHS directly as `(uniformDist paramFiber).map (Subtype.val)`).
4. **`Nonempty paramFiber` witness** — the probe uses `⟨⟨Equiv.refl (Fin 99), by simp [leftCards]⟩⟩`;
   confirm the `simp [leftCards]` gives `leftCards (Equiv.refl) = segLeft` (may need
   `leftPositions` + the `i < 50` case).

## Files

- Probe / WIP: `Shufflemath/_ProbeHeadline3.lean` (this is the starting point — build it with
  `lake build Shufflemath._ProbeHeadline3`, ~3.7 s, no whnf).
- Landing target: `Shufflemath/GSRSegHeadline.lean` (replace its `private theorem headline :=
  by sorry` once the probe builds), or a new `Shufflemath/GSRSegHeadlineProved.lean`.

## Next session

Apply the 4 fixes to `_ProbeHeadline3.lean`, rebuild (expect it to close), then move the two
local lemmas + the headline into `GSRSegHeadline.lean` (public), wire it into `Shufflemath.lean`,
and run `./dev/verify_next_phase.sh`.  No new imports beyond the whnf-free set above; keep the
membership kernel usage to the pre-compiled lemmas only.
