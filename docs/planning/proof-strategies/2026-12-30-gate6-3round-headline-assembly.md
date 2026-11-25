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

**✅ COMPLETE (session 83, Dec 30 build). The Gate 6 three-round physical
`TV < 1/1000` headline is proven and committed — all three sub-lemmas plus the
final assembly build, 0 `sorry`.**

- **Bridge**: done, committed (`d2793d8`) — `g6_3round_idealKernel_eq_fullRound`:
  `exchangeThenLocalReset … = comp (PAK swapLaw) (PAK rho99Ideal)`.
- **Sub-lemma B**: done, committed (`f9f8435`) — `g6_threeRound_finiteRun3_tv_le_q3`:
  the 3-round finite run from the fiber-uniform start is TV `≤ q3` from uniform.
- **Sub-lemma A**: done, committed (session 83) — `g6_threeRound_kernelDiscrepancy_le_δ1`:
  `kd (comp (PAK S)(PAK F)) (comp (PAK S)(PAK I)) ≤ δ1`.
- **Headline assembly**: done, committed (session 83) —
  `_ProbeG6ThreeRoundCapstone.g6_threeRound_headline`:
  `TV (apply g6ThreeRoundStart (compList [g6ThreeRoundFiniteRound ×3])) (uniform) < 1/1000`.
  Assembled from: **hAccum** = the n-step telescope
  (`compList_telescope_nstep_le_n_times_d`) with per-row bound = sub-lemma A
  (`≤ 3·δ1`); **hIdeal** = sub-lemma B (`≤ q3`); `gate6_headline_lt_thousandth`
  (`q3 + 3·δ1 < 1/1000`) + `Dist.tv_triangle`.

**Key unblocking tricks (session 83):**
1. **Isolation** — sub-lemma A and the headline each live in their own module
   (importing only the pieces they need), so the combined file's `whnf`/heartbeat
   cascade is avoided.
2. **`Eq.subst` (`hL ▸ …`) instead of `rw [hL]`** — the hΔle branch must transport
   sub-lemma A's bound (stated for `comp (PAK S)(PAK I)`) across the bridge
   `hL : g6ThreeRoundFiniteKernel = comp (PAK S)(PAK I)`. `rw [hL]` *unfolds*
   `g6ThreeRoundFiniteKernel` (the big `exchangeThenLocalReset` def) to match, and
   that recursion is exactly what killed the combined file. `hL ▸ t` uses the
   equality as a type-transport (no unfolding) — no recursion.
3. **Import-collision hygiene** — `_ProbeCompListRun` (sub-lemma B's dep) and
   `_ProbeK1wall` (the bridge's `_ProbeK1close → _ProbeGate6K1` chain) both used to
   define `rho99Ideal_pairs`; trimming `_ProbeCompListRun` to `Mathlib`/`Finite`/
   `Perturbation` removed `K1Wall` from the graph so only `_ProbeK1wall` remains.
   Also removed sub-lemma A's redundant `g6ThreeRoundDeck` `abbrev` (it collided
   with `_ProbeCompListRun`'s, which is used by its theorem).

This closes the last Gate 6 deep-work item. The on-mission `TV < 1/1000` is now
met BOTH on-mission (`DobrushinDecay99`, 41 exchanges) and via the 3-round
physical certificate. (The within-pile batch-5b headline remains a separate
side-result, off this path.)

**Follow-up (not blocking):** promote `_ProbeG6ThreeRound*` to canonical names and
add the headline to the `Shufflemath.lean` aggregator once the `_Probe` → canonical
renames are batched.
