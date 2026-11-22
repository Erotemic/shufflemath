# 2026-11-22 — Gate 6 proof-architecture assessment for Qwen

**Source base:** `shufflemath` commit `4ff9478` (2026-11-22 10:40 EST); compare with the undisturbed 2026-11-21 review and deep hints in `docs/planning/`. **Purpose:** identify mathematical and proof-representation connections that unblock real theorems, not add a second status bureaucracy. **Companion:** `../proof-strategies/2026-11-22-finite-shuffle-structural-unblocking-hints.md`.

**Evidence level:** declaration statements and proof bodies inspected in this source snapshot; 37 Python tests pass. The source and handoff report green Lean builds via `dev/verify_next_phase.sh`; this review did not independently run Lean (Lake is not installed in the review environment). Proposed lemmas in the companion are NOT compiled. Only the previously verified source theorems should be called proved.

## 1. What changed since November 21

Qwen successfully used important parts of the earlier advice. Do not assign these proofs again.

| Earlier obstruction | Present source evidence | Assessment |
|---|---|---|
| Collision counting | `Gate6BadLabels.lean`: a bad-label event as a union of pair collisions and the exact probability bound | Closed |
| Conditional-on-injectivity GSR problem | `FiniteDeck/Gate6TieRank.lean`, `Gate6F.lean`: randomized tie-breaking, uniform tie-rank distribution, mismatch coupling, `gsrPermutationLaw_tv_bound` | Closed |
| Two-pile quantitative error | `Gate6F.twoPilePermutationTV_bound` and `GSRDeckRound.rhoRoundTransport_le_twoPile`, specialized by `oneRoundDeckTV_le_delta1` | Closed for the within-pile permutation law |
| Literal position swaps | `FiniteDeck/LiteralSwapKernel.swapPerm_membership_eq`; exchange-choice/pairing-to-permutation construction in `_ProbeGate6Fin2.lean` | Pointwise physical/membership bridge proved; full-round source still a probe |
| Numerical finite-protocol budget | `FiniteDeck/Gate6FiniteGSR.gate6_headline_bound`: `q3+3*δ1<1/1000` | Exact arithmetic proved; NOT an end-to-end finite-shuffle theorem |
| Generic count-to-deck TV recovery | `FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck` | Proved for the **perfect-local** process and a prescribed fiber-uniform initial law |
| Concrete decay certificate | `FiniteDeck/DobrushinDecay99.physicalExchange_decay_41_lt_thousand` | Proved for 41 **perfect-local** exchange steps starting **fiber-uniform** at any macrostate; NOT any deterministic starting deck |

Qwen's latest handoff calls the three remaining goals “definitively wall-bound”: full-round per-row discrepancy, the segregated ideal-local distribution equality, and the final `hq3` ideal-chain premise. It has tested several attempts that expand `Dist.tv`, `distProduct`, or point-mass fibers at concrete `Equiv.Perm (Fin 99)`; these trigger Lean recursion/elaboration failures. **The empirical blocker is real for those proof formulations. It is not evidence that the theorem requires a Lean kernel change.** The repository already contains alternative primitives that avoid a global `Finset.univ` over decks.

## 2. Highest-impact new finding: confusing noise laws with Markov kernels

`Shufflemath/GSRGate6Telescope.lean` defines:

```lean
noncomputable def gsrRound99Finite : FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => rhoRoundFinite 99 50 ...
```

Its ideal counterpart has the same shape. In `_ProbeGate6Fin2.lean`, the new `finiteRound` and `idealRound` are likewise `fun _ => fullRoundFinite/Ideal`.

That is a **constant-row kernel**: a fresh sample from an absolute distribution of *position permutations* is returned as though it were the new physical deck. For any constant-row kernel `C d = μ`, `run C n (pointMass d) = μ` for every `n ≥ 1`. Repeating it does not compose position permutations, and does not model shuffling the current arrangement. The source itself correctly notes that the `hq3` hypothesis of the within-pile-only telescope is false; the newly drafted full-round constant-row probe would have the **same semantic defect**, even after the TV proof compiled.

The correction is elementary but essential: **a state-independent random permutation law induces a state-dependent deck-transition kernel**. If decks are `Fin N ≃ Fin N` from position to card identity, and `p` is a position permutation, the new deck is `p.trans d`. Define the kernel as `fun d => noiseLaw.map (fun p => p.trans d)`. With an exchange `s` followed by local permutation `g`, the intended result is `g.trans (s.trans d)`; check explicitly how `Equiv.Perm` multiplication corresponds to this `trans` order. This change must precede any three-round proof.

**Acceptance test:** prove that the proposed kernel acts on its input deck and that one step agrees with the pointwise literal swap followed by local permutation. Use a tiny `N=4,m=2,k=1` case to guard composition orientation. Do not use a constant-row kernel as the final mixing model.

## 3. Highest-impact proof shortcut: support-based TV is already implemented

The strongest **underused assets for this particular Gate 6 proof** are in `Shufflemath/TotalVariation.lean`. Qwen actually implemented and documented much of this finite-support machinery during F4.3/F4.5; the missing connection is to use it end-to-end for the current physical-round goal, rather than revert to concrete `Dist.tv`/`distProduct` expansion:

- `tvFinsupp` (line ~898): half the L1 difference over finite **supports**, no `Fintype` over the ambient state type.
- `tv_eq_tvFinsupp` (~925): bridge to the existing `Dist.tv`, proved abstractly.
- `distProductFinsupp_tv_subadditive` (~1008): handles independent products without a global enumeration.
- `kernel_apply_lipschitz` (~1188): TV contraction for applying the same kernel, without `[Fintype]`.
- `mixtureTV_le` (~1290), `run_nonexpansive` (~1398): additional support-based ingredients.
- `GSR.apply_deterministic` (`GSR.lean:529`): identifies deterministic-kernel application with `Dist.map` without `Fintype`.

In contrast, `Finite.distProduct` uses `Dist.ofFun` and a `[Fintype α] [Fintype β]` normalization over the whole product, and `Dist.tv` expands `vectorTV` over `Finset.univ`. Their specialization at `Perm (Fin 99)` is precisely what Qwen's failing probes force Lean to inspect.

**Recommendation:** prove a generic support-only map contraction using `GSR.apply_deterministic` + `kernel_apply_lipschitz`; prove common-factor product contraction by specializing the **existing** `distProductFinsupp_tv_subadditive` with the same swap law in both products. Then formulate the full-round law with `distProductFinsupp`, apply the common deterministic permutation action by `map`, and transfer the already-proved per-pile GSR error into this metric through a *symbolic* `N,m` wrapper of `tv_eq_tvFinsupp`. Do not expand TV, `distProduct`, a deck `Fintype`, or permutation `Finset.univ` at `N=99`.

This reduces the blocker to two small generic lemmas and one opaque specialization. It is a concrete untried proof architecture, **not a guarantee of successful elaboration**. Keep each proof polymorphic until the final call.

## 4. The ideal-local equality should be a generic uniform-on-fiber theorem

`GSRSegHeadline.lean` already proves `distProduct_uniform_is_uniformProd`, `roundEmbedMap_eq_fiberOrbit_val`, injectivity, and the segregated fiber cardinality. `_ProbeHeadline3.lean` then gets stuck while expanding the mass of the pushforward on the **concrete 99-card deck**.

That final computation is avoidable. The general theorem should say:

> If `f : X → Y` is a surjective observation on finite types, `y : Y`, and `e : A ≃ {x : X // f x = y}`, then pushing uniform `A` through `(fun a => (e a).val)` equals `FiberDisintegration.fiberLaw f surj y`.

Prove this once for variables `X,Y,A,f,y,e`, using `GSR.map_bijective_uniformDist` and a generic `uniform subtype → fiberLaw` bridge. All cardinalities remain abstract. Apply it to `FiniteDeck.fiberOrbit_equiv` for arbitrary `N,m,d`, then reconcile the Commander membership type **after** the generic statement is compiled. Do not re-prove the denominator `50!*49!` pointwise inside a 99-card goal.

This unlocks two things at once: the `rhoRoundIdeal = localLift` assertion for the segregated start and, more usefully, the **for-every-deck** equality between uniform local position shuffling and perfect-local resampling conditional on the post-swap membership. The latter is what the three-round theorem actually needs.

## 5. Ideal `q3` has a direct quotient proof; avoid another enormous deck computation

The full ideal round must be the **literal cross-pile swap followed by a uniform within-pile position permutation**, acting on the current deck. Once the abstract orbit theorem proves that the local uniform action produces `localLift`, the exact generic exchange refinement (`FiniteDeck/A3KernelLaw.lean`, `BLDisintegration.lean`) supplies the same law as the perfect-local chain.

For the segregated ordered deck, all 50 distinguished cards start in the left pile. The corresponding count fiber at count 50 has **one membership**, but many ordered decks. After the first exchange+perfect-local step, the conditional output law depends only on that membership, not on its within-pile order. Therefore the first-step law from the single ordered deck equals the first-step law from its fiber-uniform distribution. At three steps, use the already-proved perfect-local deck/count TV identity, obtaining `q3`; **do not compute TV over `99!` outcomes**. An alternative direct first-step argument counts reachable membership sets; each target with 25 distinguished cards left is reached by a unique pair of selected card subsets.

Once a certificate holds from one reference ordered deck, **card relabeling symmetry** extends it to every deterministic starting deck: the noise acts on **positions**, while relabeling acts on **card identities**. These actions commute. Derive exact TV preservation under bijections using support-only map contraction in *both* directions. The fixed marking is used to analyze the reference deck, not to constrain other starts.

## 6. Scope correction and proof-engineering risk

The top of `docs/agent_handoff.md` currently says the “on-mission TV<1/1000 objective is met” because of the 41-step decay result. This is true as a **restricted perfect-local, fiber-uniform certificate** only. The requested Gate 6 headline remains open: **three finite physical rounds, 23 binary riffles per pile per round, TV<0.001 from every deterministic starting deck**. Keep those two claims separate in the next status update.

Additional source-level risks:

- `GSRGate6Telescope.gate6_headline_telescope` is a correct **conditional** theorem, but the `hq3` premise is false for its present constant within-pile kernels. Do not reuse it unchanged for a final certificate.
- The `_ProbeGate6Fin2.lean` full-round definitions have not been promoted to a semantically correct production kernel. Compiling this probe alone would not close the campaign.
- The current `GSRSegConfinement` module imports `_ProbeBridgeStruct`. Avoid adding more production imports of probe files merely to make a proposed theorem accessible.
- Existing `TelescopeF5` TV bounds of 2 or 3 are non-informative for an `<0.001` target. Avoid spending more effort optimizing those certificates.
- Some filenames in the snapshot are dated November 24/25 or December 9 even though this assessment is November 22. Treat the actual commit history and theorem statements as the evidence of present progress, not those filenames as future verification.

## 7. Ordered actions for Qwen

1. **Fix the model before the TV proof.** Define a generic `actionKernel` from a distribution on position permutations; prove the literal `swap → local shuffle → current deck` orientation. Do not promote a constant-row kernel.
2. **Move TV lemmas to finite supports.** Prove abstract map contraction and common-factor product contraction using `tvFinsupp` and existing Fintype-free results, then prove one per-round `≤ δ1` bound for the *correct action kernel*.
3. **Prove a generic uniform-fiber action bridge.** Use `fiberOrbit_equiv` and `GSR.map_bijective_uniformDist` to identify the ideal local shuffle with `localLift`; no specialized 99-card mass expansion.
4. **Recover the ideal three-round law at the segregated reference deck.** Apply the existing A3/BL disintegration and exact `q3` result. This is an equality of kernels/abstract laws, not a numerical enumeration.
5. **Prove a support-level, rowwise three-round telescope** (or pathwise common-noise coupling) with error `3δ1`, then combine with `q3 + 3δ1 < 0.001`.
6. **Extend to every deck by card-label equivariance**; optionally extend to arbitrary initial distributions by convexity/mixture.
7. **Only after the theorem is closed**, continue the arbitrary-`N`, multi-pile, and cost-certificate campaigns. The generic lemmas introduced here should be placed in reusable modules, not Commander files.

Each successful step must be reported with the **actual Lean theorem name and statement**, not only a passing `lake build` or a numerical bound. Keep this dated assessment as historical feedback; later corrections belong in new documents.
