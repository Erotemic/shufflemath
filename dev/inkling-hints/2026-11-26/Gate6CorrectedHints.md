# Gate 6 orientation correction (M5c/M5d) — session 89

Candidate note for the orientation-corrected stable-sort round, seeded from the
codebase's own symbols. Not a promotion claim — contents below live in the
canonical module `Shufflemath/FiniteDeck/Gate6Corrected.lean`.

## Correction structure (no correction term needed)
The label law `gsrPermutationLaw` maps a label vector to `rank`
(old position -> new position); the physical pullback is `rank.symm`.
Because the deck is built from the pair-embedding through a *fixed* map
`roundEmbedMap`, the inversion is exactly the law inversion applied through
`symm` — and the *ideal* side (uniform embedded product law) is invariant
under it.

Key lemmas (all proven in the canonical module):
* `embed_m_symm` — `(embed_m pl pr).symm = embed_m pl.symm pr.symm` — pure
  `simp` through `finSplit` (sumCongr functorial, `finSplit` is an
  involution sandwich) + `Equiv.trans_assoc`. The `simp only [..., trans_assoc]`
  closure needs the explicit `rw [← Equiv.trans_assoc]` in this Mathlib.
* `embed_m` lives in `FiniteDeck` namespace — qualify as
  `FiniteDeck.embed_m` (the bare identifier is autoImplicit-bound and
  "Function expected"s).
* `rhoRoundIdealCorrected_eq_rhoRoundIdeal` — the full chain:
  `distProduct_uniform_is_uniformProd` (product = uniform on the product
  type), `permInverseEquiv` bijection-invariance via
  `GSR.map_bijective_uniformDist` (the pair-level pushforward is the same
  product law), then push the symm through `roundEmbedMap` via
  `Convexity.StdSimplex.map_map` in both directions and close. The map-map
  patterns need to be pushed onto the *inner* map argument (a function value,
  not an equiv) — the equiv-form (`⇑(prodCongr e)`, `.toFun`) is not a
  syntactic match for `fun z => (z.1.symm, z.2.symm)`, so bridge with a
  `funext z; rfl` equation first.
* The corrected laws' TV vs the uncorrected = `tv_bijective_invariance
  (permInverseEquiv (Fin 99))` — the uncorrected bound then applies verbatim.

## Gotchas recorded
* `rw [hdef]` on a `let prodLaw := ...`-bound local does NOT see the `let`'d
  value in the goal — use the full `distProduct (GSR.uniformDist ...)` term
  directly in the pattern, or `set` correctly.
* `simp only [correctedFiniteLaw99]` unfolds `noncomputable` defs — `unfold`
  is unreliable for the same (it silently leaves the def name in the goal).
* The `relabel_equiv` transport needs `UniformDeckRelabelInvariance` +
  `tv_bijective_invariance` in that order; `uniformDeck_relabel_invariant 99 d`
  is the right call for the uniform deck law.
* Lean 4.34: `rw [Convexity.StdSimplex.map_map]` rewrites the outer/inner
  map in one step only when the syntactic shapes match exactly (the two
  `.map`s must literally be `(map f).map g`, not `map (f ∘ g)` already).
