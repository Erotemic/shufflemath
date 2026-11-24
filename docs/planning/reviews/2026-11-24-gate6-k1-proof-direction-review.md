# Gate 6 K1 proof-direction review — 2026-11-24

**Snapshot:** `7d02441` (source archive `shufflemath-source-2026-11-24T090029-5-7d024410e6d5.tar.gz`).

**Purpose:** A dated technical intervention, not a replacement for historical reviews. Read the paired `../proof-strategies/2026-11-24-k1-direct-order-and-kernel-hints.md` **before attempting more K1b counting**. The core recommendation is to change the target representation, not the Lean resource limits.

## 1. What has actually advanced

- `Shufflemath/Gate6Crux.lean` proves the generic `convAsApply` and `convContraction` and the concrete finite-vs-ideal one-round TV bound `gate6_crux` (as recorded in the repository's successful targeted builds).
- `Shufflemath/_ProbeGate6K1.lean` now proves generic `convPush_eq_pointMassComp`, both K1 bookkeeping lemmas, and `k1a_riffle_half`: the **ideal within-pile permutation action produces the correct uniform membership-fiber law from any deck**.
- `Shufflemath/_ProbeK1b.lean` proves `K1a_stmt_only`: a literal swap of selected positions has the claimed membership effect, independently of the canonical pairing.
- `Shufflemath/_ProbeK1k.lean` proves `k1b_beta`, the involution/swap witness lemmas, several set-cardinality bridges, and the left/right witness decomposition.
- The numerical `q3 + 3δ1 < 1/1000` and collision-side mathematics are established in existing modules. The final end-to-end physical protocol theorem **is not**.

**Not closed:** `k1b_swap_half` in `_ProbeK1k.lean` and `K1_oneRoundLaw_eq_exchangeThenLocalReset` in `_ProbeGate6K1.lean` still contain `sorry`. The normal `dev/verify_next_phase.sh` builds `Gate6Crux` but does not certify these unfinished probe theorems. A green standard build is not an end-to-end Gate 6 certificate.

## 2. Critical missed connection: K1b solves the wrong-order commutation problem

The repository *already proves* `FiniteDeck.act_composition`:

```lean
act (a * b) d = act b (act a d)
```

Therefore `conv swapLaw rho99Ideal` means **swap, then perfect local shuffle**, whereas **the current definition**

```lean
Gate6Crux.fullRoundIdeal = FiniteDeck.conv rho99Ideal swapLaw
```

means **perfect local shuffle, then swap**. The finite law has the same reversal. The implementation in `FiniteDeck/PositionAction.lean` also contains some contradictory explanatory phrases; the defining expression and `act_composition` are authoritative, not prose comments.

The existing K1 proof tries to identify the local-then-swap law with `exchangeThenLocalReset`, which performs swap-then-local. To do so Qwen developed `k1b_swap_half`: an additional symmetry/commutation result. That is potentially true for a *uniform* within-pile local permutation law, but it is mathematically different from the intended construction and **does not justify commuting a finite GSR shuffle** with a swap.

**Recommendation:** stop pursuing the 230-line `k1b_count_split` assembly as the Gate 6 critical path. Introduce fresh **correct-order** laws, keep the old theorem as an optional symmetry investigation, and assemble K1 from two existing row-level statements plus elementary kernel associativity. Do not delete successfully proved K1b helper lemmas: they can be refactored later into a general subset-exchange bijection.

## 3. Immediate finish line, in dependency order

1. `correctIdeal := conv swapLaw rho99Ideal`; `correctFinite := conv swapLaw rho99Finite`. Preserve current definitions temporarily so downstream proof imports remain green.
2. Promote `k1a_riffle_half` from `_ProbeGate6K1` and `K1a_stmt_only` from `_ProbeK1b` into small, placeholder-free modules, without importing a file that still contains `sorry`.
3. Prove **`idealLocalKernel_eq_localReset`** by extensionality in the input deck, using `k1a_riffle_half` and `FiniteKernel.apply_pointMass`.
4. Prove **`swapLaw_membership_pushforward`** using `K1a_stmt_only` pointwise over the *same* uniform `exchangeChoice`; apply `Convexity.StdSimplex.map_map`. The canonical pairing disappears from membership by the proved lemma. This needs no 25/25 inverse-choice counting.
5. Compose the two equalities to prove **correct-order K1** on every input deck. Use `k1_rhs_bookkeeping` or `localLift_preserves_membership` to identify the RHS with `exchangeThenLocalReset`.
6. Prove a **generic left-convolution TV contraction** and apply `oneRoundDeckTV_le_delta1`. The old `convContraction` is right-convolution contraction and is not directly the needed inequality.
7. Use the real state-dependent action kernel / convolution power for three rounds; bridge deterministic segregated starts to the ideal mixing theorem and then use card relabeling for all deterministic starts.

The detailed mathematical chain, precise source identifiers, and two ways to prove step 6 are in the paired hint document.

## 4. Lean performance: change abstraction, not limits

- The hard 99-card expressions occur in a **specialization**, not in the abstract probability identity. Prove the abstract `comp`, `map`, `join` or `tvFinsupp` result first, then instantiate with `swapLaw`/`rho99Ideal` as opaque arguments. Do not `simp` the entire concrete 99-card law.
- Prefer `tvFinsupp`, `kernel_apply_lipschitz`, `distProductFinsupp_tv_subadditive`, `joinMapComm`, and `FiniteKernel.apply_comp`. Avoid `Dist.tv`'s `Finset.univ` and the `Fintype`-dependent `FiniteKernel.apply_deterministic_eq_map` in a large specialization if a Fintype-free monadic unit identity suffices.
- The handoff refers to `/tmp/k1b_count_split_handoff.md` as the next session's 230-line splice. This file is **not in the supplied source archive**. Do not rely on an ephemeral handoff that may be absent when the loop restarts.
- Current `docs/agent_handoff.md` and `docs/lean_plan.md` contain voluminous, partially outdated progress annotations. Read the active declarations and the targeted build outcomes; do not re-open already-proved Gate 6 collision or convolution work.

## 5. Loop-objective drift

The *active* `.pi-glla/goals/20261120183004-9jlt8s.md` still explicitly says **November 20** reviews, despite later goal and guidance files. Merely adding or committing a new goal document does **not** change that running loop. The paired `../goals/2026-11-24-direct-k1-milestone.md` contains a replacement user-submit prompt; it should be submitted to the loop explicitly (or its objective updated using the loop's supported interface).

The broader finite-deck roadmap remains the ultimate goal. Gate 6 is a milestone, not permission to stop before multi-pile, category, dealing/drawing, and cost-certificate work.

## 6. Verification and review scope

- As a separate mathematical sanity check, explicit enumeration of `N=4,m=2,k=1` and `N=6,m=3,k=2` confirms swap-then-uniform-local has exactly the same deck output law as membership exchange followed by uniform local lift. For `N=6,m=3,k=2`, a fixed local transposition can produce different output laws when the order is reversed. These are illustrative finite checks, **not** Lean proofs.
- The source archive's 37 Python unit tests pass (`python3 -m unittest discover -s tests -q`).
- No Lean/Lake executable or Mathlib cache is available in this review environment; current Lean build status is taken from source declarations and repository handoff, **not independently compiled**.
- The recommended Lean proof skeletons are explicitly uncompiled. There are no proposed changes to Lean source in this overlay.
- Do not claim the K1 gate is completed until its production theorem contains no `sorry`, is actually imported by a checked build target, and states the physical **swap-then-local** order.
