# Gate 6 orientation correction (M5c/M5d) — session 89 follow-up: what's left

## Orientation correction (DONE, committed 6bc5cbb)
`Shufflemath/FiniteDeck/Gate6Corrected.lean`: `embed_m_symm`/`roundEmbedMap_symm`
(deck-level inverse = product of per-pile inverses); `rhoRoundFiniteCorrected` /
`rhoRoundIdealCorrected`; `rhoRoundIdealCorrected_eq_rhoRoundIdeal` (ideal law
invariant under the inversion — `distProduct_uniform_is_uniformProd` +
`GSR.map_bijective_uniformDist` under `permInverseEquiv`); `correctedFiniteLaw99` /
`correctedIdealLaw99`; `correctedFiniteLaw99_tv_eq_rho99Finite` (TV unchanged
under the common bijection); `correctedFiniteRound` / `correctedIdealRound`;
`corrected_kernelDiscrepancy_le_delta1` (sub-lemma A for the corrected round);
`corrected_threeRound_headline` (base headline, same assemble as
`g6Deterministic_headline`); `corrected_threeRound_headline_anyDeck` (M5d,
any-deterministic-deck transport). Verified: full `lake build` green (9029 jobs),
`./dev/verify_next_phase.sh` green (37/37), 0 sorry.

## G5capstone — the remaining headline (parked at a wall)
`G5capstone` (the k×c multi-pile exchange kernel-equality — fiber structure tied
to the exchange dynamics) is still the only open G5 item.  Two-pile/two-color is
landed (`histogramTransition_stationary` / `histogramTransition_eq_sum_lumpedTransition` /
`HistogramFiber.lean`); the general-k×c version is reached by Sigma-lumping and is
Fintype-walled (the same dependent-subtype-rewrite wall as
`g5-multipile-twoPile-reduction.md`, documented in
`2026-12-31-g5-multipile-state-and-walls.md`).  Do not re-attempt by hand; the
roadmap's honest disposition is to leave it parked / reduce it to two-pile.

## batch-5b — also parked (elaborator wall)
`rhoRoundIdeal 99 50 … = localLift segMembership`: the remaining "image ⊆
fiberSet" pointwise 99!-universe `Finset.mem` recurses (see
`.pi-glla/5b_subset_wall_20261230.md`).  The three wall-free lemmas are committed;
the disposition is to leave it parked.  Do not bump heartbeats.
