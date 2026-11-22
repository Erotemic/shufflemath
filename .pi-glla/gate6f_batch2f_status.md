# Gate 6F (`_ProbeGate6F.lean`) — precise status & next step

**Committed** at `805c6ab` ("Probe: Gate 6F batch 2 — TV(ν_{n,a}, U_{S_n}) ≤ #bad/a^n theorem core proven").
The probe is standalone (NOT in the lakefile / main build); the main build is green.

## What's PROVEN in `_probeF_main` (the distributional-law pattern)
- **hT** (Key fact A): `μ.map tieFn = U` — via `tieRankLaw_uniform` (pushforward = uniform S_n).
- **hMarg** (Key fact C): `μ.map Prod.fst = uniformLabels` — full Fubini over the
  label×perm product; `hUnivProd` (`(Finset.univ : Finset (ΩTieRank n a)) =
  Finset.product (Finset.univ : Finset (Fin n → Fin a)) (Finset.univ : Finset
  (Equiv.Perm (Fin n)))`, by the definitional `Equiv` `Finsupp.equivFunOnFinite_symm`
  + `Equiv.prodEquiv`) + `Finset.sum_product` + per-label fiber mass
  `n!/(cardΠ·n!) = 1/cardΠ`, with `Fintype.card_pi`/`card_fin` reducing
  `card (Fin n → Fin a) = a^n`. `hSum1` (δ_ℓ sum) + `hR` (`field_simp [show (a^n:ℚ)≠0]`).
- **hV**: `μ.map rankFn = ν` — `StdSimplex.map_map` + a `change` to the
  `μ.map Prod.fst` form + `hMarg` + `rfl` (since `gsrPermutationLaw n a hn x
  = (GSR.uniformLabels n a ha).map (fun ℓ => rankEquiv ℓ)` — line 56 of GSR.lean).
- **le_trans**: `tv (μ.map rankFn) (μ.map tieFn) ≤ (mismatch mass) ≤ #bad/a^n`,
  wired via `le_trans (Dist.tv_maps_le_mismatch μ rankFn tieFn)`.

## What REMAINS (well-characterized)
1. **`hBadSum` batch 2f** — the mismatch-mass collapse
   `∑_p, (if p.1 ∈ bad then mass p else 0) = #bad/a^n`.
2. **`_probeF_fibered`** — adds a fibered-TV + uniform-fiber step after the
   `hBadSum` (same hT/hMarg/hV/hBadSum, plus `FiberTV` + `TV_le` to
   `fiberedTV (μ.map tieFn) (μ.map rankFn) + #bad/a^n`).
3. **`_probeF_nonempty`** — `Nonempty` case split on `n > 0` or `a > 0`.

## EXACT technical blockers to AVOID (learned the hard way)
- **`hInn` must be stated with the `if` OUTSIDE the sum**:
  `(if ℓ' ∈ bad then ∑_σ, mass (ℓ',σ) else 0) = (if ℓ' ∈ bad then 1 else 0)/cardΠ`.
  `split_ifs` reconstructs the `if` *outside* the sum, NOT inside. If hInn is
  stated if-inside (`∑ σ, if ℓ' ∈ bad then mass (ℓ',σ) else 0`), the proved
  term (if-outside) won't type-match the statement.
- **`(x,y).1` vs `x` matching**: after `Finset.sum_product`, the goal has
  `(x,y).1`; use `simpa [Prod.fst]` (or `rw [hUnivProd, Prod.fst]`) to rewrite it
  to `x`. The `simpa using hInn x` form needs `[Prod.fst]` in the simp set.
- **nonzero side goal for `cardΠ = a^n`** in `field_simp`: `Nat.pow_ne_zero` and
  `one_le_pow_of_le` are NOT in scope in this file. Use:
  ```lean
  field_simp [Nat.factorial_ne_zero n,
    show (Fintype.card (Fin n → Fin a) : Rat) ≠ 0 from by
      exact_mod_cast (show Fintype.card (Fin n → Fin a) ≠ 0 from by
        rw [Fintype.card_fun, Fintype.card_fin]
        have h1 : 1 ≤ a ^ n := by
          induction n with
          | zero => norm_num
          | succ k ih =>
            simp [Nat.pow_succ]
            nlinarith [Nat.le_of_lt ha, ih]
        exact Nat.pos_iff_ne_zero.1 (Nat.zero_lt_one.trans_le h1))]
  ```
  (`field_simp [h, h2]` with the facts in the set — do NOT use `· exact` sub-goals,
  which mis-parse because `field_simp` produces a single main goal, not two side goals.)
- **Alternative clean route for hBadSum** (avoids the (x,y).1 fiddliness): since
  `badLabels n a ⊆ (Finset.univ : Finset (Fin n → Fin a))` (it's a Finset of
  `Fin n → Fin a`), use the reverse `Finset.sum_ite`:
  `∑ (x,y) ∈ univ×ˢuniv, (if x ∈ bad then mass (x,y) else 0)
   = ∑ (x,y) ∈ (univ×ˢuniv).filter (fun (x,y) => x ∈ bad), mass (x,y)`
  and `(univ×ˢuniv).filter (fun (x,y) => x ∈ bad) = bad ×ˢ univ` (since `bad ⊆ univ`).
  Then `∑ x ∈ bad, ∑ y, mass (x,y) = ∑ x ∈ bad, 1/cardΠ = bad.card/cardΠ = bad/a^n`
  (Fibonacci: sum_product + the per-label fiber mass from hMarg's `hCard` +
  `Finset.sum_const` + `hCard : cardΠ = a^n`). This is the least-fiddly path.

## Verified facts (reuse, don't re-derive)
- `Finsupp.equivFunOnFinite_symm (finsetEquivFinsupp s) : (s → β) ≃ (s →₀ β)` — the
  product-Fintype `Equiv` is definitional (`s := Fin n → Fin a`, `β := Equiv.Perm (Fin n)`).
- `gsrPermutationLaw n a hn x = (GSR.uniformLabels n a ha).map (fun ℓ => rankEquiv ℓ)`.
- `Fintype.card_pi (Fintype.card (Fin n)) (Fintype.card (Fin a)) = Fintype.card (Fin n → Fin a)`.
- `Fintype.card_fun : Fintype.card (α → β) = Fintype.card β ^ Fintype.card α`.
- `Fintype.card_perm : Fintype.card (Equiv.Perm α) = (Fintype.card α)!`.

## Commands
```bash
cd ~/code/shufflemath
lake exe cache get
timeout 2000 lake build Shufflemath._ProbeGate6F   # probe (isolated)
./dev/verify_next_phase.sh                          # main build (stays green)
```

## ✅ RESOLVED (2026-11-25, session 80)
`_probeF_main` now BUILDS in full. The hBadSum is proved by the Fubini path above:
- `hInn ℓ'`: per-label fiber sum `∑_σ mass μ (ℓ',σ) = (if ℓ'∈bad then 1 else 0)/cardΠ`,
  with the fiber mass `1/(cardΠ·n!)` (from `Fintype.card_prod` + `card_perm`) and the
  pos-branch closed by `simp only [one_div, mul_inv_rev, smul_eq_mul, nsmul_eq_mul]; field_simp`.
- `hInner`: `sum_congr` + `by_cases (ℓ'∈bad)` + `simpa [hbx] using hInn x`.
- `hOut`: `∑ (if ℓ'∈bad then (1:Rat) else (0:Rat))/cardΠ = (#bad:Rat)/cardΠ` via
  `← sum_div` + `sum_ite`/`card_filter` (explicit `(1:Rat)/(0:Rat)` annotations fix the
  `?m` ite-type inference).
- `hCard`: `cardΠ = a^n` via `Fintype.card_fun` + `Fintype.card_fin` + `Nat.cast_pow`.
- step 6: `sum_le_sum`; `ℓ∈bad` → `split_ifs` (0≤mass / mass≤mass); `ℓ∉bad` → `by_cases
  rankFn=tieFn` (simp / contradiction by Key fact B + `absurd hEq (fun h => hfg h.symm)`).

Remaining for the (f) headline (separate, not yet in this file):
- `#bad ≤ choose(n,2)` already lands as batch 2 (c). So `TV ≤ #bad/a^n ≤ choose(n,2)/a`
  is the full (f) bound — compose with `le_trans` and the (c) bound when promoting to the
  canonical `Gate6TieRankF` module.
- Promote `_ProbeGate6F.lean` → `Gate6TieRankF.lean` (or the canonical Gate 6 file) and add
  to the `Shufflemath.lean` aggregator + `dev/verify_next_phase.sh` target list.

## ✅ FULL (f) HEADLINE (2026-11-21)
`_probeF_headline` added and BUILDS:
  `TV(gsrPermutationLaw n a, U_{S_n}) ≤ (n.choose 2 : Rat) / a`
via `le_trans (_probeF_main n a ha hn) (badLabels_uniform_bound n a ha)` — the (c) headline
`#bad/a^n ≤ choose(n,2)/a` composed with this file's `#bad/a^n` TV bound. Batch 2 (f) is
COMPLETE at the probe level. Remaining promotion: canonical module name + aggregator +
verify_next_phase.sh target, then fold into the F5 telescope for the 99-card `< 1/1000`
certification (separate, larger step).
