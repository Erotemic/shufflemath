# Session note — Gate 6 batch-4 K1 bookkeeping (LHS/RHS normal forms done)

## What built (commit: pending)
`Shufflemath/_ProbeGate6K1.lean` — EXIT=0, single intentional sorry:

1. **`convPush_eq_pointMassComp`** (generic in N) —
   `(conv μ W).map (fun p => act p d) = apply (pointMass d) (comp (PAK μ) (PAK W))`.
   Proof: `refine (convMapEqApplyMap μ W d).symm.trans ?_` → `rw [← apply_comp]` →
   `congr` → `rw [apply_pointMass, permutationActionKernel_eq_map]` →
   `apply congrArg (fun f => μ.map f); funext p; rfl`.
2. **`k1_lhs_bookkeeping`** — 99-card instance (dsimp fullRoundIdeal + exact).
3. **`k1_rhs_bookkeeping`** — `apply (pointMass d) (exchangeThenLocalReset ...) =
   apply (rawExchangeMembership d) localLift` — apply_comp/apply_pointMass/hraw/
   apply_comp/hassoc/hident(localLift_preserves_membership)/comp_id_left —
   all in ONE final `rw [hassoc, hident, comp_id_left]`.
4. **`K1_oneRoundLaw_eq_exchangeThenLocalReset`** — statement in; both bookkeeping
   rws land; the sole `sorry` = the per-deck **orbit-fiber uniformity wall**:
   `apply (pointMass d) (comp (PAK rho99Ideal) (PAK swapLaw)) =
   apply (rawExchangeMembership d) localLift`.

## The three hard-won lessons (all cost a failed build each)
1. **Never let a concrete 99!-laden law reference (rho99Ideal, swapLaw,
   uniformDist-exchangeChoice, ...) enter an `rw` PATTERN-SEARCH goal.** The
   matcher whnfs every candidate subterm and dies (generic "Did not find an
   occurrence" — not a heartbeat error). Bisection proved it: the identical rw
   succeeds when the heavy refs are NOT in the goal. Fix: prove the identity
   GENERIC in N (variables whnf to themselves) and instantiate by `exact`
   (one isDefEq, no search).
2. **`act` vs `Equiv.trans` are two whnf forms.** `permutationActionKernel_eq_map`
   is `rfl` in the `Equiv.trans` form; `convMapEqApplyMap` is stated in the `act`
   form. `act p d = p.trans d` IS `rfl`-provable (instance-field unfolding) but
   `rw`/`simp` do NOT unfold `noncomputable def act` in lambda bodies. Keep a
   proof in ONE form (the crux never mixes them); bridge forms with
   `congrArg + funext + rfl`, never `simp`.
3. **Trailing-tactic phantoms:** when a `rw` auto-closes a goal, any LATER
   separate tactic in the block errors "No goals to be solved". Fold the tail
   into a SINGLE `rw [r1, r2, r3]` (rw silently stops once the goal is
   trivial) — this fixed a phantom that looked like a logical contradiction.

## Other facts recorded
- `StdSimplex.map`/`join` spine: `apply μ K = (μ.map (K ·)).join`;
  `conv μ W = (distProductFinsupp μ W).map (fun z => z.1 * z.2)`;
  `powConv W 0 = pointMass (Equiv.refl (Fin N))` (Nat.rec).
- `apply_pointMass (x) (K) : apply (pointMass x) K = K x` (`[simp]`, forward).
- `distUniform_weights` — uniformDist μ |>.map F — whnf-stable form (batch-5b).
- `localLift_preserves_membership : comp localLift (deterministic membership)
  = identity` — the fiber-resample-after-read is definitionally the identity.

## Next (in priority order)
1. **The wall**: prove
   `apply (pointMass d) (comp (PAK rho99Ideal) (PAK swapLaw)) =
    apply (rawExchangeMembership d) localLift`
   — i.e. within-pile-orbit kernel = oracle-exchange + fiber-resample, per deck.
   Candidate route: batch-5b headline machinery (run_tv_eq_macro + hrecover)
   adapted to KERNEL equality (both sides are Dist (Deck 99)); or reduce to
   fiber-cardinality equinumerosities (F3-style). Must keep 99! refs OUT of rw
   searches (lesson 1) — prove generic in the fiber structure where possible.
2. **K1a** (membership enabler) — not yet started; unblocks the gate after K1.
3. Promote the three bookkeeping lemmas + K1 to the production module
   (PhysicalExchangeReduction or a new Gate6ThreeRound file) with the
   statement in `.trans` form (bridge act≡trans by funext;rfl).

## Standing rules
Active until Wed Nov 24 23:59:59 EST 2026 — do not stop/ask/end; compaction is
not a stop; small-batch commit gates; verification = targeted lake build +
./dev/verify_next_phase.sh.
