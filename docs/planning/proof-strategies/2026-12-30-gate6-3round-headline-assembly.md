# Gate 6 three-round headline — exact assembly plan (correct order)

Session 81 handoff. The K1 milestone is closed (commits `32cc450` … `f14e499`)
and the **linchpin bridge** is proven + committed (`d2793d8`):

- `_ProbeG6ThreeRound.g6_3round_idealKernel_eq_fullRound`:
  `exchangeThenLocalReset membership localLift rawExchange
     = comp (PAK gsrDeck99_swapLaw) (PAK gsrDeck99_rho99Ideal)`.
  (Pure kernel algebra: `rw [← comp_assoc, rawExchange_membership_pushforward,
  ← K1_swapFirst_eq_exchangeLift]` after unfolding `exchangeThenLocalReset` and
  `localReset`.)
- `_ProbeK1close.K1_swapFirst_eq_exchangeLift`: the corrected swap-first
  assembly `comp (PAK swapLaw) (PAK rho99Ideal) = comp rawExchangeMembership
  localLift` via `rw [hH, ← comp_assoc, hK]` from the two proven halves.
  (The old riffle-first / `sorry` investigation in that file is dropped.)

So the `q3` A3 kernel (three exchange-and-local-resets) is **exactly** the
correct-order full-round ideal kernel `L = comp (PAK swapLaw) (PAK
rho99Ideal)`. The 3-round Gate 6 headline is now a **well-defined assembly**,
not a wall:

```
TV( apply mu (compList [K, K, K]), uniform )  ≤  q3 + 3·δ1  <  1/1000
```

where
- `mu  = apply (pointMass commanderSegregatedState) (fiberLaw project project_surjective)`
  (the natural fiber-uniform start — the exact start of
  `three_physical_perfect_exchanges_uniform_unconditional`);
- `K = comp (PAK gsrDeck99_swapLaw) (PAK gsrDeck99_rho99Finite)` (physical round: exchange + 23-riffle);
- `L = comp (PAK gsrDeck99_swapLaw) (PAK gsrDeck99_rho99Ideal)` (ideal round: exchange + perfect local reset) = `exchangeThenLocalReset …` (bridge).

## Assembly (adapt `GSRGate6Telescope.gate6_headline_telescope`, make `hq3` unconditional)

The existing `gate6_headline_telescope` proves `≤ q3 + 3·δ1` *given* `hq3` for
state-INDEPENDENT `gsrRound99Finite`/`Ideal` and leaves `hq3` as a hypothesis
(documented as "false for the within-pile-only ideal"). The correct-order
version discharges everything:

1. **`hlen`** — trivial (`simp`).
2. **`hΔle`** — `∀ a, a ∈ (List.map (fun p => kernelDiscrepancy p.1 p.2)
   ([K,K,K].zip [L,L,L])) → a ≤ δ1`, i.e. `kernelDiscrepancy K L ≤ δ1`
   (sub-lemma A below).
3. **Telescope** — `compList_telescope_nstep_le_n_times_d [K,K,K] [L,L,L] hlen
   δ1 (by rw [δ1_eq_2401_over_8388608]; norm_num) hΔle mu`
   → `TV(apply mu (compList [K,K,K]), apply mu (compList [L,L,L])) ≤ 3·δ1`.
4. **`hq3` (now proven, not a hypothesis)** — `TV(apply mu (compList [L,L,L]),
   uniform) ≤ q3` (sub-lemma B below).
5. **Triangle + `gate6_headline_lt_thousandth`** — exactly as in
   `gate6_headline_telescope`; gives `≤ q3 + 3·δ1 < 1/1000`.

## Sub-lemma A: `kernelDiscrepancy K L ≤ δ1` (per-deck discrepancy)

`kernelDiscrepancy K L = (Finset.univ.image (fun x => TV (K x) (L x))).max'`
(`Perturbation`), so bound each point. **Key reduction** — `K x` and `L x`
share the *same* input and differ only in the riffle kernel:

```
K x = apply (apply (pointMass x) (PAK swapLaw)) (PAK rho99Finite)
    = apply (swapLaw.map (·.trans x)) (PAK rho99Finite)        (permutationActionKernel_eq_map, definitional)
L x = apply (swapLaw.map (·.trans x)) (PAK rho99Ideal)
```

So `TV(K x, L x) ≤ kernelDiscrepancy (PAK rho99Finite) (PAK rho99Ideal)
≤ TV(rho99Finite, rho99Ideal) ≤ δ1`, via three small ingredients:

- **A1** `TV(apply ν K, apply ν L) ≤ kernelDiscrepancy K L` for an arbitrary
  mixture `ν` (a mixture is a TV-convex combination of its rows; the sup over
  rows bounds it). FIND in `Perturbation`/`Finite` (the point-mass case is
  `rowTV_le_kernelDiscrepancy`); if only the point-mass form exists, prove the
  mixture form (should be `Finset.sum_le` over `ν`'s support + contraction).
- **A2** `kernelDiscrepancy (PAK A) (PAK B) ≤ TV(A, B)`: per `q`,
  `(PAK A) q = A.map (·.trans q)` (definitional) and
  `TV(A.map (·.trans q), B.map (·.trans q)) ≤ TV(A, B)` by
  `TotalVariation.tv_map_contraction`; sup over `q` gives the bound.
- **A3** `TV(rho99Finite, rho99Ideal) ≤ δ1` — the single 23-riffle collision
  bound. FIND in `GSRF42`/`CommanderDeckGSR`/`FiniteDeck/Gate6TieRank`; if not
  present, it is a clean 23-riffle collision computation (≤ the 99-deck
  collision `δ1`). This is the only possibly-new collision count.

Then `Finset.max'_le` / `sup_le` closes `kernelDiscrepancy K L ≤ δ1` (no 99!
enumeration: `Equiv.Perm (Fin 99)` has a compact `Fintype`, and the bound is
proved pointwise, not by evaluation).

## Sub-lemma B: `TV(apply mu (compList [L,L,L]), uniform) ≤ q3`

- `L = exchangeThenLocalReset membership localLift rawExchange` (bridge).
- `compList [L,L,L]` applied to `mu` = `run (exchangeThenLocalReset …) 3 mu`
  (align `compList`/`run`; `Finite.run` is the `Nat.recOn` iteration).
- `mu = apply (pointMass commanderSegregatedState) (fiberLaw project
  project_surjective)` = exactly the start of
  `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`,
  which states that TV **= q3** (not just ≤). So sub-lemma B is a `simpa`
  chaining the bridge + `compList↔run` + that theorem.

## Numeric close

`gate6_headline_lt_thousandth` (GSRGate6Telescope) already proves `q3 + 3·δ1
< 1/1000`. Apply it to the assembled bound.

## Files / build

- New module or extend `_ProbeG6ThreeRound`:
  `import GSRGate6Telescope, Perturbation, FiniteDeck.Fiber,
  FiniteDeck.Gate6FiniteGSR, ConvContractionLeft, TotalVariation`.
- Probes build via `lake build Shufflemath._ProbeG6ThreeRound`
  (`grep -iE "error|Build completed"`). `q3`, `δ1`, `commanderSegregatedState`,
  `gsrDeck99_swapLaw/rho99Finite/rho99Ideal`, `fiberLaw`, `project`,
  `project_surjective`, `exchangeThenLocalReset`/`localLift`/`rawExchange`
  (A3KernelLaw), `PAK = FiniteDeck.permutationActionKernel`, `comp`, `compList`,
  `run`, `kernelDiscrepancy`, `tv_map_contraction`,
  `permutationActionKernel_eq_map`, `three_physical_perfect_exchanges_uniform_unconditional`,
  `compList_telescope_nstep_le_n_times_d`, `gate6_headline_lt_thousandth`
  are all already proven/defined.
- Promote to a named module (e.g. `Shufflemath/FiniteDeck/Gate6ThreeRound.lean`)
  and add to the `Shufflemath.lean` aggregator once it builds, mirroring how
  `gate6_headline_telescope` lives in `GSRGate6Telescope`.

## Status

Bridge: **done, committed** (`d2793d8`). Remaining: sub-lemma A (3 small
ingredients A1–A3; A1/A3 are "find or prove small lemmas"), sub-lemma B
(`simpa`), main assembly (adapt `gate6_headline_telescope`), numeric close.
All bounded; no new collision counting beyond A3. This is the final Gate 6
deep-work item; the on-mission `TV < 1/1000` is already met independently by
`DobrushinDecay99` (41 exchanges).
