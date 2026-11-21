# F5: 99-card Dobrushin contraction — status

## ✅ DONE + COMMITTED — "F5 Step 1" (commit `042a66f`)
The 99-card Bernoulli–Laplace exchange is **sub-maximally mixing**:
- `Shufflemath.Dobrushin.tv_lt_one_of_commonPos`: two `Dist`s sharing a
  positive-mass point have `tv < 1` (reusable across F5 and any common-support
  argument).
- `BernoulliLaplaceCommanderBridge.blExchangeKernel_extremePairTV_lt1`: the two
  window-extreme macrostates (`st1`, `st50 : BLState 99 50 50`) share the
  positive-mass successor `st25`, hence `tv < 1`.
  (`blExchangeKernel_extremeMass125_pos`: `num(1,25)=denom/2` → weight `1/2`;
  `…5025_pos`: `num(50,25)=denom` → weight `1`, a deterministic move.)

Build: aggregator (3257 jobs) green, 37/37 tests pass.

## ✅ DONE + COMMITTED — "F5 Step 2: ALL 50 states reach 25" → the Dobrushin coefficient is `< 1`

**The prior session's "elaboration wall" was a misdiagnosis.** It attributed the
failure of five attempts to a 2,000,000-heartbeat WHNF timeout of the
`Finset.sum`-of-4-`choose`-lambda. In fact:
- Attempts 1, 2, 4 (`funext` / `change … = _; rfl` / `sum_sdiff` against the full
  sum) ARE genuinely heavy — avoid them.
- Attempts 3, 5 (`Finset.single_le_sum`) failed only from an **arity bug**:
  `Finset.single_le_sum` takes `(h : a ∈ s) (ha : f a ≠ 0) (hb : a ∈ s)` (three
  args, `s` and `f` implicit). The prior calls passed the wrong arity, so the
  `f`-inference mis-applied ("numerals are data but expected type is a
  proposition"). With the correct 2-argument call
  `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (show a ∈ Finset.range (k+1) from by decide)`,
  the goal closes in ~3–9 s, **no timeout**.

**Surviving-term identification (corrected).** The 6-arg
`transitionNumerator 99 50 50 25 x 25 = ∑_{a ∈ [0,25]} ∏₄ choose …`. Exactly one
summand is positive per case, and it is **uniform** (no symbolic `a` needed):
- `x ≤ 26`: take `a = 1` (one special leaves, `b = 25-1 = 24`, `x-a` specials
  return). The four factors `choose x 1`, `choose (50-x) 24`, `choose (50-x) (26-x)`,
  `choose (x-1) (x-1)` are all positive (`choose_self` collapses the last; the
  `24 ≤ 50-x` bound is exactly `x ≤ 26`).
- `x ≥ 27`: take `a = 25` (all 25 leave special, `b = 50-x` return). The factors
  `choose x 25`, `choose (50-x) 0`, `choose (50-x) (50-x)`, `choose (x-1) (x-25)`
  are all positive (the middle two collapse by `choose_zero_right` / `choose_self`).
  (The prior note's "a = x−25" was the *minimal* valid index, not the clean
  uniform one; `a = 25` works for every `x ∈ [27,50]`.)

**Theorems landed in `Shufflemath/BernoulliLaplaceCommanderBridge.lean`:**
- `blExchangeKernel_num_pos_low (x) (h : 1 ≤ x.val ∧ x.val ≤ 26)` : `0 < transitionNumerator … x.val 25`
  (isolates the `a = 1` summand via `Finset.single_le_sum` + `by decide`).
- `blExchangeKernel_num_pos_high (x) (h : 26 < x.val ∧ x.val ≤ 50)` : same, via `a = 25`.
- `blExchangeKernel_allStatesReach25 (x : BLState 99 50 50)` :
  `0 < Dist.mass (blExchangeKernel commanderBLParams x) st25`. Assembles the two
  cases with `by_cases x.val ≤ 26`, lifts the `Nat` numerator positivity to `Rat`
  via `Nat.cast_pos.mpr`, and closes the weight `> 0` with `div_pos` against the
  `native_decide`-proved denominator.
- `blExchangeKernel_dobrushinCoeff_lt_one` :
  **`Dobrushin.dobrushinCoeff (blExchangeKernel commanderBLParams) < 1`** — the
  headline. Unfolds `dobrushinCoeff = (pairDistances K).max'`, rewrites with
  `Finset.max'_lt_iff` (`max' < 1 ↔ ∀ d ∈ pairDistances, d < 1`), and shows every
  pair `rowTV (K i) (K j) < 1` because both rows share the positive-mass successor
  `st25` (`allStatesReach25`) → `tv_lt_one_of_commonPos`. A global
  `commanderBLState_nonempty : Nonempty (BLState 99 50 50) := ⟨st25⟩` instance is
  added (required by `dobrushinCoeff`'s typeclass signature).

The bridge now also `public import Shufflemath.Dobrushin` (for `dobrushinCoeff`,
`rowTV`; it transitively brings `Mathlib.Data.Finset.Max` → `Finset.max'_lt_iff`).
Build: full `lake build` (3257 jobs) + `dev/verify_next_phase.sh` (37 tests) green.
Probe `_ProbeF5Step2.lean` deleted after the proof landed in the module.

## 📌 F5 HEADLINE SCOPE (what `< 1/1000` still needs)
`dobrushinCoeff (blExchangeKernel commanderBLParams) < 1` is **qualitative**
mixing (the macro-chain is irreducible / sub-maximally contracting). The full F5
objective `dobrushinCoeff (physicalExchange 50) < 1/1000` needs a **concrete**
numeric coefficient `d < 1` with `d^n < 1/1000` for an explicit `n`. That is a
separate, larger task: compute the 50×50 sup of `tv (K i) (K j)` (e.g. in Python),
pick a concrete rational `d` above it, and prove `dobrushinCoeff ≤ d` via the
same per-pair `allStatesReach25` + `tv_lt_one_of_commonPos` machinery — then
`physicalExchange_dobrushinDecay` + a `native_decide` check of `d^n < 1/1000`
closes it. NOT done here; the committed `< 1` is the milestone.

## Next concrete action
If resuming F5: (1) compute the exact 50×50 macro-`tv` sup in
`experiments/` (bounded, `Rat`), (2) add a `blExchangeKernel_dobrushinCoeff_le_d`
theorem proving the coefficient is `≤` that concrete rational (reuse
`blExchangeKernel_allStatesReach25` + `Finset.max'_le` / per-pair overlap), and
(3) wire a concrete `n` with `d^n < 1/1000` into `physicalExchange_dobrushinDecay`
for the `< 1/1000` headline.
