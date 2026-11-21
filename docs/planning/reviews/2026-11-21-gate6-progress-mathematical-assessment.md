# November 21, 2026 — Gate 6 mathematical progress and semantic risks

**Source assessed:** `51423b0aefc8f7bdbb931bb22479eb0eb720c063`, reconstructed from the November 21 git-well incremental archive against its verified November 20 base `58de44b84aee`. **Status of this document:** dated assessment; retain for historical analysis. Its companion, `../proof-strategies/2026-11-21-gate6-nonobvious-proof-hints.md`, gives the actual proof routes. It is additive; no earlier review or handoff is superseded by a silent edit.

## Executive assessment

**Qwen has made real progress** on the previously recommended representation changes. The most valuable new completed infrastructure is the within-pile orbit equivalence and the actual position-swap permutation. The outstanding work is now primarily *distributional*: replacing list-valued label shuffles with a state-independent permutation law, bounding deviations from uniform, composing physical rounds, and obtaining a terminal theorem with the right start-state quantifiers.

The current headline `Gate6FiniteGSR.gate6_headline_lt_thousandth` proves a **rational inequality**, not the full finite physical shuffle certificate. No `finiteRound` deck-valued kernel or terminal TV theorem was found among the current Lean declarations. That distinction should remain prominent.

## Evidence and immediately reusable declarations

| Area | Current source | What is actually established | Remaining bridge |
| --- | --- | --- | --- |
| Generic fiber orbit | `Shufflemath/FiniteDeck/WithinPileOrbit.lean`: `fiberOrbit_equiv` | A pair of within-pile permutations parameterizes any given membership fiber | Distribution transport and uniformity, not a new orbit proof |
| Literal position swaps | `Shufflemath/FiniteDeck/LiteralSwapKernel.lean`: `swapFn_involution`, `swapPerm`, `swapPerm_membership_eq` | Genuine position permutation and its membership semantics; pairing-independent at membership level | Sample choices to make a deck-valued kernel; do not insert perfect reset |
| Inverse GSR | `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition`; `GSRPermutationLaw.gsrPermutationLaw`, `idealShuffle_canonical_eq_permLaw` | An a-shuffle of the **canonical list** is represented by a rank-permutation law | Natural transformation to arbitrary ordered piles and product-of-piles law |
| Exact ideal exchange | `FiniteDeck/BLRefinement.g4MacroIntertwining`; `FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck`; Commander specialization | Macro-vs-ideal full-deck equality from a **fiber-uniform macro start** | Single ordered start, then arbitrary start via colorblindness |
| Mixing estimate | `FiniteDeck/DobrushinDecay99.*`, especially `dobrushinCoeff_41_lt_thousand` and `physicalExchange_decay_41_lt_thousand` | An explicit 41-step bound on the **fiber-uniform input stated in Lean** | Any-deterministic-deck theorem is **not** this statement |
| Gate 6 arithmetic | `FiniteDeck/Gate6FiniteGSR.lean`: `q3`, `δ1`, `δ3`, `gate6_headline_lt_thousandth`, `cardPairEqSet` | `q3 + 3(2401/2^23) < 1/1000` and the pair-equality label count | Probability bound; same-randomness coupling; finite deck kernel and three-round telescope |
| Collision work | `_ProbeGate6Collision.lean`: `cardIjPairs`, `cardPairEqSet`, `biUnion_card_le_sum`, `collisionProb_le` | All but the collision probability headline; that one has a `sorry` | Resolve *event representation* and the typed-index mismatch before any heavy elaboration |

The 37 Python regression tests passed in this assessment. The repository's latest handoff reports targeted Lean builds as green, but Lean/Lake was not available in the assessment environment, so those builds were **not independently rerun**. Source-visible statements and verified Python tests are the evidence here; proposed lemmas in the companion document are **not** compiled theorems.

## Finding 1 — The immediate proof barrier has TWO separate causes

In `_ProbeGate6Collision.lean` the blocker is described as a WHNF/heartbeat limit caused by unfolding

```lean
((univ : Finset (Fin n × Fin n)).filter
  (fun p => decide (p.1 ≠ p.2) && decide (f p.1 = f p.2))).Nonempty
```

with arbitrary `f`. Treat the huge reduction as a **representation problem**. We do not need to decide a nested finite-set `Nonempty` proposition to state the bad-label event. Define it directly as the union of elementary equality events, with index `i<j`. The bound then starts from an identity, not a problematic witness extraction. See companion §1.

**A second issue is visible independently of WHNF:** `biUnion_card_le_sum` and `card_le_biUnion_sum` are declared using a single type `X` both for `s : Finset X` and for `(f x) : Finset X`. The intended application uses **different** types:

- index type `I := Fin n × Fin n`;
- event-element type `X := Fin n → Fin a`.

Even after repairing the collision witness, the current lemma cannot typecheck in that intended application. Generalize the lemma signatures to `{I X : Type*}`; the existing induction proof should largely transfer unchanged. This is a certain source-level type mismatch, not an inferred performance problem.

Do **not** make `set_option maxHeartbeats 0` the first resort. It makes the original large reduction possible in principle but leaves the mathematical representation and the second type mismatch unaddressed.

## Finding 2 — A semantic overstatement in the 41-step result

The doc comments in `FiniteDeck/DobrushinDecay99.lean` call its bound a result from *any 99-card deck*. The actual theorem `physicalExchange_decay_41_lt_thousand` begins with

```lean
FiniteKernel.apply (Dist.pointMass x0)
  (FiniteKernel.comp (uniformCountFiberMembership commanderBLParams)
    (localLift ...))
```

This **is not** a point mass on an arbitrary ordered deck. Count-process mixing alone does not imply full-deck mixing from arbitrary microscopic states.

An illustrative four-card example: two marked cards `{0,1}`, pile size two, one-card exchange, initial membership `{0,2}`. Conditional on the next marked count being one, the only possible target memberships are `{1,2}` and `{0,3}`; yet all four one-marked/one-unmarked memberships are possible in that macro fiber. Merely perfect-randomizing *within each pile* does not erase the residual membership information at that step.

**Good news:** the desired stronger claim is still plausibly accessible, but by an *additional theorem*. If a full-deck shuffle is a law on **position permutations independent of card identities**, its TV distance from uniform is invariant under arbitrary relabeling of the starting deck. Prove that structural lemma, anchor the ideal certificate at one segregated ordered deck using the one-membership extreme fiber, and transport. The resulting three-round worst-case statement could be substantially more useful than the current 41-round bound. See companion §§6–7.

The source theorem is valid for its stated starting distribution; this is a **commentary/claim-scope problem**, not evidence that Lean accepted an invalid proof.

## Finding 3 — The next structural shortcut is now available

The earlier November 20 guide mentioned the group-action approach as a future possibility. `fiberOrbit_equiv` now supplies the missing exact equivariance/bijection between within-pile permutation pairs and a membership fiber. As a result, there are now two viable pathways for the local TV estimate:

1. **Fastest certificate path:** same-source deterministic-map coupling on i.i.d. labels (and optional independent randomized tie-breakers), then TV ≤ probability of unequal outcomes. Does not require full-deck TV isometry.
2. **Reusable structural path:** product-GSR law on two permutation groups; compare with product uniform, push forward through `fiberOrbit_equiv` (TV contraction or exact isometry), then average over literal swap choices.

Both paths require establishing the **uniform rank law on collision-free labels**; neither requires calculating 99! probabilities.

## Finding 4 — The permutation-law proof has an important boundary

`GSRPermutationLaw.idealShuffle_canonical_eq_permLaw` is stated on `List.finRange n`, not on arbitrary current pile orderings. It is *not yet* the lemma that the physical shuffle kernel is a state-independent right-convolution. A naturality lemma for `stableBuckets` under injective renaming, plus uniform-label invariance under reindexing, is the right bridge. The orientation of rank `σ` versus `σ.symm` should be fixed by `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition`, not guessed.

## Finding 5 — The certificate's actual remaining dependency chain

1. A generic **bad-label union bound**, not the present Bool/Nonempty calculation.
2. A uniform-permutation distribution derived from the same random labels (conditionally on no ties, or via independent random tie-breakers).
3. A genuine finite local permutation law, applied to each pile after `swapPerm`.
4. A row-wise `TV(finiteRound d, idealRound d) ≤ δ1` for every input deck, with no enumeration of `Deck 99`.
5. A **three-step telescope**, using the already-established generic perturbation machinery with a supplied row bound rather than its full-deck `max'` definition.
6. A one-ordered-deck ideal-start bridge (unique segregated membership), and then optional all-start equivariance.
7. The already-proved exact inequality `q3+δ3<1/1000`.

Do not spend the next tranche re-proving finite fiber counts, `fiberOrbit_equiv`, `swapPerm_membership_eq`, or the 41-step macro Dobrushin bound. Nor should Gate 6 depend on optimality, a new general spectral theorem, or multi-pile abstractions.

## Scope and recommended next assignment

**Immediate:** generalize the union-bound lemma to two types, define bad labels as a union of pair-equality events, and prove its exact rational bound. Move that theorem into a tiny *production* module and stop extending `_ProbeGate6Collision` as a historical notebook. Then prove the label-permutation coupling, and **actually define** `finiteRound`.

**After Gate 6:** prove the universal right-convolution/card-relabeling theorem, then resume arbitrary finite piles and categories. Keep numerically specialized Commander certificates as corollaries of the generic theory, not as the foundation.

**Verification gaps:** `dev/verify_next_phase.sh` lists many legacy direct targets but not the current Gate 6 module, the literal swap module, or the orbit module as explicit build targets. Some are imported by `Shufflemath.lean`, but that aggregator is not itself on the script's `lake build` target list. Add targeted imports/build coverage when promoting the new proofs; do not infer that a green old script verified the new module.

**Administrative note:** the handoff contains historical next actions and even future-dated headings relative to this November 21 snapshot. Resolve the next lemma from the source and the handoff's active top section, not from stale headers. `AGENTS.md` still refers to `card_biUnion_pd` as the next action. A short current-task header is more helpful to a small model than repeatedly rereading the entire multi-thousand-line history.
