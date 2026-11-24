# Gate 6 evening proof-architecture review — 2026-11-23

**Snapshot:** `573d097` (`shufflemath-source-2026-11-23T215838`). This is a historical review of the snapshot, not a replacement for the active handoff. Read the companion `../proof-strategies/2026-11-23-swap-local-orbits-and-support-first-proofs.md` before resuming Gate 6.

## Executive finding

Qwen has **completed the convolution contraction problem that previously consumed 23 minutes and >10 GB**. `Shufflemath/Gate6Crux.lean` now has the generic `convAsApply`, `convContraction`, the concrete `gate6_crux`, and `fullRoundDeck_le_delta1`. It is no longer useful to attack the old `h3` WHNF problem or tune recursion depth for that proof.

The active problem has moved to **K1**, the identification of a sampled position-permutation round with the physical exchange + ideal local reset. The latest `Shufflemath/_ProbeGate6K1.lean` establishes both bookkeeping normal forms, but `K1_oneRoundLaw_eq_exchangeThenLocalReset` still ends in an explicit `sorry`. The probe is not part of the regular verification build. Its existence is **not** a proved K1 theorem.

The most useful intervention is a **change of representation and order of composition**. Qwen is trying to identify `conv rho99Ideal swapLaw` with a kernel that exchanges cards and **then** resets within each pile. However `FiniteDeck.act_composition` proves that `conv A B` executes `A` **first**, then `B`. Thus the current left side takes the perfect local shuffle **before** the cross-pile swap, while the target operates in the opposite order.

For the special ideal law, those kernels may agree by a nontrivial symmetry argument under uniform subset selections. But that commutation has not been proved, and it is needless work. For finite local laws it is **not generally valid**. The direct representation of the intended physical protocol is

```lean
FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal
FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Finite
```

with the common swap factor **first**. The companion hint document shows how to obtain the same `δ1` contraction bound for these corrected laws, and then establish K1 from the already-proved uniform within-pile orbit equivalence.

## Source-level evidence

| Topic | File/declaration | Evidence and limitation |
|---|---|---|
| Generic convolution/action | `FiniteDeck/ActionConvolution.lean`: `act_composition`, `convMapEqApplyMap`, `powConvRunEq` | Completed reusable bridge; `a * b` means act by `a`, then `b`. |
| One-round error | `Gate6Crux.lean`: `convAsApply`, `convContraction`, `gate6_crux`, `fullRoundDeck_le_delta1` | Generic-right-convolution TV theorem compiled according to the committed handoff. It proves the inequality for **local-then-swap** laws as currently defined. |
| K1 partial | `_ProbeGate6K1.lean`: `convPush_eq_pointMassComp`, `k1_lhs_bookkeeping`, `k1_rhs_bookkeeping` | The recorded build covers the bookkeeping. `K1_oneRoundLaw_eq_exchangeThenLocalReset` is explicitly unfinished (`sorry`). |
| Swap changes membership | `FiniteDeck/LiteralSwapKernel.lean`: `swapPerm_membership_eq`; `_ProbeK1a.lean`: `K1a_swapPerm_membership` | Independent of the chosen pairing; the K1a proof is in a *probe*, not an aggregator-imported production module. |
| Uniform fiber orbit | `FiniteDeck/WithinPileOrbit.lean`: `fiberOrbit_equiv`, `fiberMap`, `act_d_preservesMembership`; `FiniteDeck/Fiber.lean`: `fiberCount` | The needed bijection already exists at arbitrary `N,m`; its **uniform pushforward law** is the missing probability lemma. |
| Local reset and exchange | `CommanderMembershipKernels.lean`: `localLift_mass`, `localLift_preserves_membership`; `CommanderPhysicalExchange.lean`: `rawExchangeMembership`, `rawExchange` | RHS of K1 reduces to `apply (rawExchangeMembership d) localLift`, and that reduction is already in the K1 probe. |
| Collision error | `Gate6F.lean`, `GSRDeckRound.lean`: `oneRoundDeckTV_le_delta1` | The finite-vs-ideal within-pile permutation TV bound is established. No new collision counting is needed. |
| Arithmetic | `FiniteDeck/Gate6FiniteGSR.lean`: `gate6_headline_bound` | `q3 + 3 δ1 < 1/1000` is proved as rational arithmetic, but is **not** yet the physical three-round theorem. |
| Previous telescope | `GSRGate6Telescope.lean` | Uses *constant-row within-pile kernels*. Its conditional telescope cannot certify a real three-round physical shuffle; the source itself says the needed ideal `hq3` is false for those kernels. |
| Existing 3-round ideal result | `CommanderFullDeckDisintegration.lean`: `three_physical_perfect_exchanges_uniform_unconditional` | Starts from a **fiber-uniform segregated macrostate**, not a deterministic complete deck. The deterministic-start bridge still needs proof. |
| Loop objective | `.pi-glla/goals/20261120183004-9jlt8s.md` | Still explicitly tells Qwen to use **November 20** hints, even though the structural status has changed substantially. |

The checkout is clean at HEAD. All **37 Python tests pass** (`python3 -m unittest discover -s tests -v`). This audit environment has no Lean/Lake executable or Mathlib build cache; we have **not** independently checked the Lean modules. All new proposed theorem statements below are guidance, not compiled proofs.

## The non-obvious issue: the current order is backwards

In `FiniteDeck/ActionConvolution.lean` the actual proved equation is

```lean
act (a * b) d = act b (act a d)
```

Thus `conv rho99Ideal swapLaw` samples a local permutation, acts with it, and **then** applies a swap. `PositionAction.swapThenLocalKernel` instead computes `g.trans (s.trans d)` = swap **then** local, and `swap_then_local_matches_star` identifies that with `s * g`.

Changing the order does not invalidate the per-pile collision bound. It changes which **generic TV nonexpansion lemma** is needed: `convContraction F I S` currently handles the common factor on the **right**; the corrected laws share the factor on the **left**. Derive the mirror lemma at an abstract type, **without** specializing to `Fin 99` in its proof body.

This is not merely a naming issue. For example, with `N=6,m=3,k=2`, canonical sorted matching of the selected indices, a fixed local left transposition, and a uniform selection of the nine exchange choices, local-then-swap and swap-then-local have different outcome laws (direct small finite enumeration). Therefore one cannot commute a *finite* local shuffle past the physical swap by notation or a reflexivity proof. The ideal uniform-local law may have additional symmetry; proving it is avoidable.

## What is still genuinely hard

1. **Uniform-orbit pushforward:** show that applying an independent uniform element of the within-pile permutation group to an arbitrary deck produces the uniform distribution over that deck's *membership fiber*. This should follow from `fiberOrbit_equiv` plus one generic `uniformDist`-under-equivalence lemma, with no 99-card fiber sum.
2. **Swap membership pushforward:** show that choosing the uniform swap subsets and applying their literal position permutation has exactly the already-defined `rawExchangeMembership` law. This is pairing-independent by `swapPerm_membership_eq` and should use `map_map`, not probability expansion.
3. **K1 assembly:** swap-then-local ideal law equals `rawExchangeMembership` followed by `localLift`, hence equals `exchangeThenLocalReset` on point masses. Use `joinMapComm` and `FiniteKernel.apply` algebra. Avoid rewriting inside a specialized 99-card expression.
4. **Correct-order TV bound:** mirror `convContraction` via a left-noise Markov kernel; alternatively prove a generic shared-mixture TV bound. Instantiate a theorem whose arguments remain opaque until the final `exact`.
5. **Three-round telescope:** use state-dependent `permutationActionKernel` / `powConvRunEq`, not the constant-row `gsrRound99*` kernels, and derive a row-TV error inequality without `Finset.univ` over `Equiv.Perm (Fin 99)`.
6. **Initial condition:** show three perfect physical rounds started from a **fixed ordered segregated deck** have the same law as three rounds started from the *uniform segregated fiber*; relabeling invariance by itself does not prove this. Then extend to every deterministic start by card relabeling and, optionally, arbitrary input laws by convexity.

## Compilation architecture: where to spend effort

- Write abstract lemmas for `N,m`, or even arbitrary `α`, before using the concrete `rho99Ideal`, `swapLaw`, `localLift`, or `Finset.univ` in a rewrite pattern. The latest K1 status note confirms that `rw` searching expressions containing these concrete laws can cause the expensive WHNF normalization.
- Promote small successful probe lemmas to production modules only after their statements and dependencies are settled. `_ProbeGate6K1.lean` still has a `sorry`; the main verification script does not check it.
- Do **not** increase `maxRecDepth` or set `maxHeartbeats 0` to force a concrete `99!`-typed normal form. Increasing limits does not establish that the proof has a tractable structure. If normalization grows after introducing a concrete law, move the operation to a generic helper and try again.
- Do **not** replace the corrected physical kernel with a state-independent law or use `GSRGate6Telescope.gsrRound99Ideal` to discharge the physical ideal residual. It models within-pile reshuffling and has the wrong limiting distribution.

## Recommended order and acceptance

**A. Correct the physical-order representation.** Name separate laws `swapThenLocalFinite` and `swapThenLocalIdeal`; prove one small generic equality with `PositionAction.swapThenLocalKernel`. Do not delete the existing crux theorem; it remains a valid statement about the opposite order.

**B. Prove generic `uniformOrbitLaw`.** Its input is an arbitrary `N,m,d`; its output is the exact uniform membership-fiber law, not merely support containment.

**C. Finish K1** by composing the swap-membership pushforward with `uniformOrbitLaw`. K1 must be a complete theorem in a normal, imported module, not a probe containing a placeholder.

**D. Prove the common-prefix / left-convolution TV bound** and the correct one-round `≤ δ1` result. Reuse the committed `oneRoundDeckTV_le_delta1`.

**E. Establish a generic **three-round** discrepancy by a support-based telescope and identify the corrected ideal run with the existing exact ideal theorem.

**F. Close the deterministic-start theorem** and then the every-start theorem using relabeling. Prove that the final code applies position permutations to the current deck at every step.

A green generic proof of Step C is a better milestone than another long 99-card special-case probe. The goal's end condition is **an end-to-end, compiled physical certificate** `TV < 1/1000` from every deterministic initial deck, not merely the arithmetic inequality or a conditional telescope. Once established, resume the arbitrary-`N` and multi-pile roadmap.
