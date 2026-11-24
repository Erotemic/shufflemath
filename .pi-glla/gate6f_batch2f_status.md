# Gate 6: executable mathematical bridges — §2/§3 generic interfaces (2026-12-09)

## Status
Built `Shufflemath/Gate6K1Direct.lean` — the **small generic interfaces** the
`docs/planning/proof-strategies/2026-11-24-gate6-executable-mathematical-bridges.md`
guide requires, proved at **abstract types** (no 99, no `Fintype` of the deck
space, no `native_decide`), so the 99-card specialisations are one-line
applications:

| § | Theorem | Content |
|---|---|---|
| 2.2 | `supportMapTV` | TV contraction for arbitrary deterministic maps, **Fintype-free**: `tv(u.map f, v.map f) ≤ tv(u,v)` via the Fintype-free monadic unit (`apply_deterministic`) + `kernel_apply_lipschitz` |
| 2.2 | `supportTVSelf` | `tv(u,u) = 0` (Finsupp level, abstract — never enumerates the support) |
| 2.3 | `convTVBoth` | `TV(A*B, C*D) ≤ TV(A,C) + TV(B,D)` at any `N`: product-TV subadditivity + one map contraction — no summation interchange |
| 2.3 | `convTVCommonLeft` | common-left-factor specialisation `TV(S*F, S*I) ≤ TV(F,I)` |
| 2.4 | `powConv_zero` / `powConv_succ` | definitional recursor steps (kept, cheap, `@[simp]`) |
| 3   | `kernelOfFiberRows` | a kernel equal to the lifted-map on every point mass equals `deterministic f ; L` — the `H = M ; L` form (§3.2) |
| 3   | `mapMapOfPointwise` | `(u.map s).map f = u.map g` from pointwise agreement — the `K ; M = E` form (§3.3) |
| 3   | `fuseSwapLocal` | `K ; (M ; L) = E ; L` from `H = M ; L` and `K ; M = E` — the K1 fusion (§3.4) |

Reuses (does NOT re-prove) the already-in-production Fintype-free monadic unit
`CommanderPermutation.apply_deterministic` and the kernel/TV library
(`kernel_apply_lipschitz`, `distProductFinsupp_tv_subadditive`,
`FiniteKernel.comp_assoc`).

## Parked / next
- **`powConvTV` (§2.4, the power telescope `TV((W_f)^t,(W_i)^t) ≤ t·TV(W_f,W_i)`)
  is PARKED.** The induction step must instantiate `convTVBoth` on `powConv`
  terms; the `Nat.rec`-of-`conv` shape explodes WHNF far past any bounded
  heartbeat cap (1,000,000 already exceeded, and a global `0` cap is forbidden
  by the guide's §9). Re-attack with a formulation that keeps the `powConv`
  distributions **opaque** in the one-step bound (e.g. a `telescopeTV` helper
  whose arguments are opaque variables, specialised only once at the end).
- **K1 closure (§0.3 / §3.2 / §3.3, the next step):** relocate the point-mass
  facts `k1a_riffle_half` and `K1a_stmt_only` (currently in the K1 probes
  `_ProbeK1b/_ProbeK1i/_ProbeK1k`) into production, then close
  `K ; H = E ; L` by composing:
  1. `k1a_riffle_half` → `H = M ; L` via `kernelOfFiberRows`;
  2. `K1a_stmt_only` → `K ; M = E` via `mapMapOfPointwise`
     (define `choicePerm c` / `postChoice d c` as the map bodies of
     `swapLaw` / `rawExchangeMembership d`);
  3. `fuseSwapLocal` → `K ; H = E ; L`.
  Since `rawExchange = E ; L` by definition, this gives `swap-then-ideal =
  rawExchange`, the K1 headline. No new counting; the `sorry` in
  `_ProbeGate6K1` is discharged by this composition.
- `Gate6K1Direct` is **not yet** in the `Shufflemath.lean` aggregator (keeps the
  incremental build fast while the K1 assembly lands); add it once the K1
  headline is complete.

## Verification
`lake exe cache get && lake build Shufflemath.Gate6K1Direct` → builds in ~7s
(olean 324 KB, 23 declarations). No `sorry`/`admit`. The only linter noise is
in the pre-existing `BLRefinement` module (unchanged here).
