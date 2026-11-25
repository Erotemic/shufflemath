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
- **Session 82** (this file's successor): `_ProbeCompListRun.g6_threeRound_`\
  `compList3_eq_run` — the `compList`↔`run` alignment
  (`apply μ (compList [K,K,K]) = run K 3 μ`), the ingredient sub-lemma B's
  second bullet needs. Committed `803ee38`. Note: `_ProbeG6ThreeRound.lean`
  stays the clean single-bridge file; an exploratory `g6_threeRound_*` rewrite
  (which renamed the bridge and re-derived `_ProbeK1close`/`Gate6K1Capstone`
  work) was reverted to the committed form, and its one new artifact — the
  `compList↔run` bridge — was preserved as the standalone `_ProbeCompListRun`.

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

## Sub-lemma A: `kernelDiscrepancy K L ≤ δ1` (per-deck discrepancy) — **DONE (session 83)**

Proven as `_ProbeG6ThreeRoundKernelDelta.g6_threeRound_kernelDiscrepancy_le_δ1`
(commit following `f9f8435`). The proof decomposes each row `x` through the
swap law's action law, so **both** `K x` and `L x` become `apply νx (PAK
rho99·)` with `νx = swapLaw.map (·.trans x)`:

```
K x = apply νx (PAK rho99Finite)
L x = apply νx (PAK rho99Ideal)
```

so `TV(K x, L x) ≤ kernelDiscrepancy (PAK rho99Finite) (PAK rho99Ideal)` by the
**mixture** bound `apply_discrepancy_bound` (A1, `Perturbation` — `rowTV_le_`
`kernelDiscrepancy` is only the point-mass case; the mixture form exists and is
the right tool here), then `≤ TV(rho99Finite, rho99Ideal)` by
`tv_map_contraction` on the per-row `·.trans x` (A2), then `≤ δ1` by the
already-proved `oneRoundDeckTV_le_delta1` (A3, the 23-riffle bound — found in
`GSRDeckRound`, no new collision counting). Closed with `Finset.max'_le` +
`Finset.mem_image.mp` over `kernelDiscrepancySet = univ.image (fun x => TV(K x)(L x))`.

**`convContraction` is NOT the route** (contrary to the first sketch above):
it contracts the TV of a *left*-compounded kernel pair (`(K1;K2)` vs `(K1';K2)`,
shared inner `K2`), but here the two kernels that differ (finite vs ideal A3
round) are the **inner/right** factor while the shared `PAK swapLaw` is the
**left/outer** factor — `convContraction` cannot bind a left factor, so the
row decomposition through the `PAK` action law is the right route. (No oracle,
no `native_decide`, no `native_defeq`/`WHNF` wall; the `max'` is over a compact
`Equiv.Perm (Fin 99)` `Finset`, bounded pointwise — never enumerated.)

**Isolation note:** sub-lemma A is proven in its own module
`_ProbeG6ThreeRoundKernelDelta.lean` (imports only core: `Finite`, `Perturbation`,
`TotalVariation`, `PositionAction`, `Gate6Crux`, `GSRDeckRound`,
`Gate6FiniteGSR`, `CommanderPermutation`) — *not* in `_ProbeG6ThreeRoundHeadline`,
because the combined file (sub-lemma A + B + headline) hit `whnf`/heartbeat
exhaustion in the headline's `hΔle` list-decomposition, reported at the
sub-lemma-A line. Isolated, sub-lemma A builds in ~6 s.

## Sub-lemma B: `TV(apply mu (compList [L,L,L]), uniform) ≤ q3` — **DONE (session 82)**

Proven as `_ProbeG6ThreeRoundHeadline.g6_threeRound_finiteRun3_tv_le_q3`. It is
a two-rewrite `simp` (no equinumerosity / `native_decide` / 99! enumeration):

1. `compList [L,L,L]` applied to `mu` = `run L 3 mu` — the committed
   `_ProbeCompListRun.g6_threeRound_compList3_eq_run` (unroll `compList` to the
   nested `comp` chain / triple `apply` = the three `run_succ` steps).
2. The already-proved
   `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_
   unconditional` states `TV (run L 3 mu) (uniform) = q3` (the exact 3-round
   ideal residual; `q3` *is* that fraction, `FiniteDeck/Gate6FiniteGSR`), whence
   `≤ q3`.

Here `L = exchangeThenLocalReset membership localLift rawExchange` and
`mu = apply (pointMass commanderSegregatedState) (fiberLaw project
project_surjective)` — the exact kernel/start of that theorem, so the second
`rw` matches after a `dsimp` of the two local defs. (No `Gate6Crux.swapLaw`
TV-identity is needed: the q3 theorem already fixes the TV to the ideal value.)

So sub-lemma B needs no swapLaw argument — the finite 3-round run is TV-`q3`
from uniform, and the only remaining headline gap is the per-round collision
budget `3·δ1` (sub-lemma A).
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

- **Bridge**: done, committed (`d2793d8`).
- **Sub-lemma B** (`TV(apply mu (compList [L,L,L]), uniform) ≤ q3`): done,
  committed (`f9f8435`, `_ProbeG6ThreeRoundHeadline.g6_threeRound_`
  `finiteRun3_tv_le_q3`).
- **Sub-lemma A** (`kernelDiscrepancy K L ≤ δ1`): done, committed (session 83,
  `_ProbeG6ThreeRoundKernelDelta.g6_threeRound_kernelDiscrepancy_le_δ1`) — row
  decomposition through the PAK action law + `apply_discrepancy_bound` (A1) +
  `tv_map_contraction` (A2) + `oneRoundDeckTV_le_delta1` (A3). `convContraction`
  is NOT applicable (the differing kernels are the inner/right factor).
- **Headline assembly** (`g6_threeRound_headline`): **the last piece.** Combines
  sub-lemma A (finite-vs-ideal 3-run `≤ 3·δ1` via
  `compList_telescope_nstep_le_n_times_d`) + sub-lemma B (`≤ q3`) +
  `tv_triangle` + `gate6_headline_lt_thousandth` (`q3 + 3·δ1 < 1/1000`).
  - The only fiddly part is the telescope's `hΔle` argument: after
    `rcases List.mem_map.mp ha`, decompose `a ∈ ([K,K,K].zip [L,L,L]).map (fun p
    => kernelDiscrepancy p.1 p.2)` to the single repeated pair `kd K L ≤ δ1`
    (4-branch `rcases` on the `∨ False` chain; `dsimp` to compute the zip;
    `rw [δ1_eq_2401_over_8388608]; norm_num` for `0 ≤ δ1`).
  - **Heartbeat caution**: the combined file (sub-lemma A + B + headline in one
    module) exhausts `whnf`/heartbeat budget (the big `g6ThreeRoundFiniteKernel`/`PAK`
    defs get unfolded repeatedly in the `hΔle` simp). Build the headline in a
    separate module importing sub-lemma A (`_ProbeG6ThreeRoundKernelDelta`) and
    sub-lemma B (`_ProbeG6ThreeRoundHeadline`) + the bridge (`_ProbeG6ThreeRound`) —
    or trim the `hΔle` to avoid `simp`/`dsimp` on the big kernel defs (use
    explicit `rw [hK, hF, g6_3round_idealKernel_eq_fullRound]` + `exact`).
  - **Import-collision note**: `_ProbeCompListRun` (sub-lemma B's dep) imports
    `K1Wall`; `_ProbeG6ThreeRound` (the bridge) → `_ProbeK1close` →
    `_ProbeGate6K1` → `_ProbeK1wall`. Both define `rho99Ideal_pairs` in namespace
    `Shufflemath`, so a file importing both fails. **Trim `_ProbeCompListRun`'s
    imports to `Mathlib`/`Finite`/`Perturbation`** (its theorem is pure kernel
    algebra; the `K1Wall`/`Gate6K1Capstone`/… imports are unused) — done locally
    this session; re-apply if reverted (the file is tracked, so commit the trim).

This is the final Gate 6 deep-work item; the on-mission `TV < 1/1000` is already
met independently by `DobrushinDecay99` (41 exchanges).
