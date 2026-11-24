# K1 capstone — assembly progress + exact remaining sub-lemma (2026-12-25 → Dec 30 batch)

Status: the **batch-5b bridge chain is DONE and committed**. The K1 capstone
(`K1_oneRoundLaw_eq_exchangeThenLocalReset` in `Shufflemath/_ProbeGate6K1.lean`,
sorry at line 194) is **reduced to a single, cleanly-stated sub-lemma** that is the
headline itself.

## Committed this session (the batch-5b bridge chain)
- `7c2bae6` — `UniformOrbitLaw.uniformOrbitLaw` (the batch-5b bridge: a uniform
  within-pile orbit IS the membership fiber law).
- `7e98c40` — `RhoRoundIdealLift.rhoRoundIdeal_eq_membershipLift` (the **generic
  (N,m)** version: `PAK (rhoRoundIdeal N m …) = comp (deterministic (membership N m))
  (fiberLaw-kernel)`, via `distProduct_uniform_is_uniformProduct` + `permutationActionKernel_eq_membershipLift`).
- `ecda74b` — `Gate6K1BridgeA.k1_bridgeA` (the **99/50 instance**:
  `PAK rho99Ideal = comp (deterministic membership) localLift`).

## The K1 capstone assembly (progress, ready to commit once the sub-lemma closes)

`_ProbeGate6K1.lean : K1_oneRoundLaw_eq_exchangeThenLocalReset`:
```
Gate6Crux.fullRoundIdeal.map (fun x => act x d)
  = apply (pointMass d) (exchangeThenLocalReset membership localLift rawExchange)
```
Full proof (verified — everything closes **except** the final sub-lemma):
```
rw [k1_lhs_bookkeeping d, k1_rhs_bookkeeping d]
--  →  apply (pointMass d) (comp (PAK rho99Ideal) (PAK swapLaw))
--        = apply (rawExchangeMembership d) localLift
rw [← FiniteKernel.apply_comp]      -- apply (apply (pointMass d) (PAK rho99Ideal)) (PAK swapLaw)
rw [k1a_riffle_half d]              -- inner = apply (pointMass (membership d)) localLift
rw [FiniteKernel.apply_pointMass]   -- = localLift (membership d)
-- REMAINING GOAL (verified by reveal):
--   apply (localLift (membership d)) (PAK swapLaw)
--     = apply (rawExchangeMembership d) localLift
```

## The exact remaining sub-lemma (the K1 headline itself)
```
k1_swapLift_eq_exchangeLift (d : Deck) :
    FiniteKernel.apply (CommanderMembershipKernels.localLift (CommanderMembershipKernels.membership d))
      (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
    = FiniteKernel.apply (CommanderPhysicalExchange.rawExchangeMembership d)
      CommanderMembershipKernels.localLift
```
i.e. *push the uniform membership-d fiber through the swap kernel = the physical
exchange-then-local-reset.*

### Facts already available (committed)
- `Gate6K1Swap.k1_swapMembership_eq_exchangeMembership`:
  `comp (PAK swapLaw) (deterministic membership) = rawExchangeMembership`
  (the swap's *membership distribution* = the exchange's membership distribution).
- `CommanderA3ExchangePushforward.rawExchangeMembership_pointMass`:
  `rawExchangeMembership d` is the **uniform** pushforward over `exchangeChoice` of
  `newMembership d …` (a *distribution* on Membership, not a point mass).
- `CommanderPhysicalExchange.rawExchangeMembership_conjugate`.

## ⚠️ OPEN QUESTION (verify before treating the sub-lemma as a routine next step)

> **✅ RESOLVED (2026-12-30, 77th session — see `docs/planning/proof-strategies/
> 2026-12-30-k1-correct-order-crack.md`).** Item 2's suspicion was right and the answer is
> **the composition order**: `Gate6Crux.fullRoundIdeal = conv rho99Ideal swapLaw` applies
> `rho99Ideal` (the riffle) *first*, i.e. it is **local-then-swap**, the opposite of the
> goal's physical **swap-then-local** = `conv swapLaw rho99Ideal`. The sub-lemma
> `k1_swapLift_eq_exchangeLift` (and the opposite-order capstone) is **false as stated**
> (fiber-symmetric LHS vs deck-specific RHS), and no work on it can close it. The
> **correct-order** capstone `k1_capstone_correct` in
> `Shufflemath/_ProbeK1correctOrder.lean` now **builds** (no `sorry`): it follows from
> `k1a_riffle_half` + `k1_swapMembership_eq_exchangeMembership` + a new `riffleApply`
> (linearity of the ideal riffle). Remaining: the finite version, the one-round TV bound,
> and promotion to a committed module.

The 4-rw reduction **builds** (it is algebraically valid), but the resulting sub-lemma
`k1_swapLift_eq_exchangeLift` has an **asymmetry that may make it false as stated**:

- **LHS** `apply (localLift (membership d)) (PAK swapLaw)` is **fiber-symmetric** — it
  depends on `d` **only through `membership d`** (the uniform fiber is arrangement-free).
- **RHS** `apply (rawExchangeMembership d) localLift` depends on the **specific deck `d`**:
  `rawExchangeMembership d` is the uniform-over-`exchangeChoice` pushforward of
  `newMembership d … = ⟨newLeftCards d L R, …⟩`, and
  `newLeftCards d L R = {d (leftPosition l) | l ∉ L} ∪ {d (rightPosition r) | r ∈ R}`
  reads the **specific cards at specific positions** — so it is **not** a function of
  `membership d` alone.

So the sub-lemma is NOT a fiber-symmetry statement; it asserts that pushing the
arrangement-free uniform fiber through the swap kernel **reproduces the specific-deck
exchange law**.  That is a strong claim. **Before building on it, verify it is true:**
  1. Concrete check: do two decks `d, d'` with the same `membership` give equal
     `rawExchangeMembership`? (The definition says NO in general — the non-`L` left
     positions hold different cards.) If NO, the sub-lemma as stated is false and the
     `k1a_riffle_half` reduction is the **wrong decomposition** for the headliner (it
     fiber-averages the LHS, losing the specific-deck information the RHS needs).
  2. If false: reconsider the decomposition. The headliner's LHS
     `fullRoundIdeal.map (fun x => act x d)` is specific-deck; the `k1a_riffle_half`
     step (ideal riffle → uniform fiber) discards deck-specific info, so it should only
     be applied to the *correct* stage. Re-derive which stage of the full round the
     uniform-fiber fact belongs to (the physical order is **swap first, then within-pile
     riffle** — check `conv rho99Ideal swapLaw`'s composition order vs `comp`'s argument
     order, and `k1_lhs_bookkeeping`'s exact statement), so the specific-deck exchange
     is preserved and only the *genuine* within-fiber uniformity is factored out.

### The two uniformity facts (needed only if the corrected decomposition lands here)
1. **`rawExchangeMembership` factors through `membership`** — see the caveat above; the
   definition suggests this is **false** in general, so it is probably NOT the right route.
2. **The swap is a uniform fiber-map**: a *uniform* fiber pushed through `PAK swapLaw`
   stays *uniform* on the image fibers (cf. `GSR.map_bijective_uniformDist`).

### Likely shape of the close (once the two facts land)
Decompose `apply (localLift (membership d)) (PAK swapLaw)` by
`apply_comp` into the membership stage (`rawExchangeMembership`, via fact 1 +
`k1_swapMembership_eq_exchangeMembership`) and the within-fiber stage (uniform by
fact 2 / `GSR.map_bijective_uniformDist`), then reassemble as
`apply (rawExchangeMembership d) localLift`.

## Next session
Prove the two uniformity facts (or a direct `k1_swapLift_eq_exchangeLift`), then fill
the `K1_oneRoundLaw_eq_exchangeThenLocalReset` sorry with the 4-rw reduction above +
the sub-lemma, promote the capstone + the bookkeeping lemmas
(`convPush_eq_pointMassComp`, `k1_lhs_bookkeeping`, `k1_rhs_bookkeeping`,
`k1a_riffle_half`, from `_ProbeGate6K1`) to a committed `Shufflemath/Gate6K1.lean`
module, and add the K1 headline to the aggregator + `lean_plan.md`.  The probe
`Shufflemath/_ProbeK1cap2.lean` holds the verified 4-rw reduction.

---

## 2026-12-31 progress: 2a proven, 2b wall located precisely

**Decomposition landed.** The monolith `_ProbeK1m` was split into two files:

- **`_ProbeK1r.lean` — the 25/25 branch, PROVEN and building clean** (`lake env lean
  Shufflemath/_ProbeK1r.lean` exits 0).  It holds `k1b_hitCount` (the hit-count spelled out
  once as an `abbrev`), `k1b_arith` (`(M.1 ∩ leftCards).card + (M.1 ∩ rightCards).card = 50`),
  and **`k1b_count_25`**: when `M`'s 50 cards split 25/25, exactly one exchange choice
  (the witness pair `Lstar`, `Rstar`) hits `M`.  This is the first provably-correct half of
  the K1b headline.
- **`_ProbeK1q.lean` — the 0-branch (WIP).**  It holds `k1b_oneHit_implies25` (a hit forces
  25 in each pile), `k1b_25contradiction` (the pure-Nat
  `25≤a ∧ a≠25 ∧ 25≤b ∧ a+b=50 ⇒ False`), `k1b_count_non25` (the 0-branch), and the
  reassembly `k1b_count_split`.  It imports `_ProbeK1r` for the shared `k1b_hitCount`/
  `k1b_arith`.

Both are standalone probes, **not** in the `lake build` import graph (only
`Gate6K1BridgeA` is), so a non-building probe does not break the full build.

### Why 2b is still the wall — the precise blocker

Every formulation of the 0-branch overflows the elaborator's recursion depth (`maximum
recursion depth has been reached`), because the premise **"`c` hits `M`"** is the big term
`newMembership Y c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2) = M`, and the
contradiction requires `25 ≤ (M.1 ∩ leftCards).card`, derived from that term via
`newMembership_set_eq` (which whnf's `swapLeftPart`/`newLeftCards`/`newRightCards` — the
exponential cascade).  Two attempts failed:

1. **Inline the `omega` in a fresh `have`** — insufficient: the `have` body still sees the
   big ambient hypotheses, so `omega` processes them and overflows.
2. **Extract `k1b_oneHit_implies25` / `k1b_25contradiction` and apply them from 2b** —
   insufficient: *passing the big `hx : newMembership Y c = M` as a theorem argument*
   (`rcases k1b_oneHit_implies25 Y M c hx`) itself triggers the whnf on the argument check.

`k1b_count_25` (2a) survives the same term because it introduces `hHit`/`hHit'` as `intro`
hypotheses (no cross-check of one big term against another); 2b additionally has to *compare*
the big premise against a theorem's parameter, which is the extra whnf that tips over.

### Next-session unblock candidates (in order of preference)

1. **Raise the elaboration recursion budget** for this file — e.g. `set_option maxRecDepth
   400` near the top of `_ProbeK1q`.  The overflow is a budget issue, not non-termination,
   so raising the limit should let 2a's technique finish 2b.
2. **Shrink the premise term.**  The 25-contradiction only needs the set equality
   `(newMembership Y c).1 = M.1`, not the full `Membership`-struct equality
   (`.1` set + `.2 : card = 50`).  Stating the per-`c` hypothesis as that single set
   equality may reduce the whnf enough to elaborate.
3. **Refactor `newMembership`** (in `CommanderPhysicalExchange`) so its `.1` is a smaller
   definition (the 2026-12-30 doc's item #3) — a larger change, deferred.

**Do not** weaken `k1b_count_non25` to `sorry` and commit it as a proof — the 0-branch is
the substantive half of the headline and is the next thing to crack.
