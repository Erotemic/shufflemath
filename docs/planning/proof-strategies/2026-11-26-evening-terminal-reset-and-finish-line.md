# 2026-11-26 evening — finish the campaign by deleting unnecessary proofs and unnecessary shuffles

Basis: `86480366a9fa`. Read this after the morning finish-line handoff. The user already updated the overarching loop goal; retain it. This document supplies the mathematics and explicit next steps for either Inkling2 or Qwen. Use the three new candidate modules in `dev/inkling-hints/2026-11-26-evening/` as seeds, not trusted compiled results. All suggested theorem names below are targets unless explicitly described as existing. Work in small canonical modules and integrate one verified interface at a time. Do not restart M1/M2 or change the meaning of the existing certificates.

## 0. Execution order (use this as the resume pointer)

1. A1–A3: prove the terminal-reset deletion identity and a new 99-card certificate using only one local shuffle at the end. This directly reuses the newly proved row factoring. Also prove the lower bound of A4. If the final Lean specialization stalls, commit the abstract identity first and move to C, then return.
2. B: prove the binary-riffle interpretation generically (not yet an exported theorem). Apply it to the old and new 99-card certificates. M5 then closed.
3. C: close arbitrary-length changing-capacity transport with one indexed-run theorem. Reuse it to combine deal/draw/discard; add the conditional hand law. M7 closed.
4. D: actual arbitrary fixed-pair k-subset exchange plus its quotient. E: general histogram factorial mass/feasibility. These close M3/M4. Do not reopen specialized two-color sums.
5. F: general multi-pile local comparison; derive terminal-only reset schedule result when exchange lumpability holds. M6 closed.
6. G: finite-N transposition coupling and meaningful cost frontier. M8 closed. All required theorem names must be in the canonical import/build path and have the hypotheses asserted in the acceptance checklist. Optional sharp descent/spectral research is not a blocking goal.

Run candidates with `lake env lean dev/inkling-hints/2026-11-26-evening/<file>.lean`. Use the repository module conventions in production. When a candidate fails, isolate the first failing declaration, adjust local syntax or representation, and compile again; do not increase global heartbeat/recursion limits or expand concrete Fintype instances. The generic proofs below do not require enumeration of deck permutations. `Eq.subst` and a narrow `change` are useful at a concrete specialization, as existing Gate 6 proofs demonstrate.

## A. New mathematical result: local shuffling between uniform exchanges is unnecessary

### A1. Derivation and hypotheses (this is not a heuristic)

Use execution-order kernel composition `S ; H = FiniteKernel.comp S H`. Let `S` be literal uniform-position swap, `P` deterministic deck-to-membership, `Q` the membership exchange kernel, `U` the uniform membership-fiber lift. Then the morning agent proved exactly the missing observation law:

```
S ; P = P ; Q              (k1_swapMembership_eq_exchangeMembership
                            + rawExchangeMembership_eq_comp_rowFactor)
U ; P = id                 (localLift_preserves_membership)
H = P ; U                  (k1_idealKernel_eq_membershipLift)
L = S ; H = P ; Q ; U      (K1_swapFirst_eq_exchangeLift)
H ; L = L                  (idealLocalReset_absorption)
```

Therefore for all t>=1 and every input law mu,

```
S^t ; H = L^t .
```

Inductive algebra: `S^1 ; H = L`. If `S^t ; H = L^t`, then
`S^(t+1) ; H = S^t ; L = S^t ; H ; L = L^t ; L`. There is no assumption that individual deck-swap rows or finite local shuffle commute! This identity is about a **terminal ideal reset**, and relies on sampling uniformly from positions anew in each exchange. It is false in general for nonuniform position selection depending on order. It is not a claim that deleting intermediate shuffles gives identical finite local-shuffle output distributions before the terminal reset.

The abstract `lastReset_run` seed in `LastResetSeeds.lean` is intentionally stated only using `H ; (S ; H) = S ; H`. Prove and export this first (no Fintype). Its proof is 1 induction and `apply_comp`, `run_succ`, no sums. A more general arbitrary schedule follows by observing that any intermediate kernel J with `J ; P = P` can be omitted when computing the membership projection. `preserved_observation_step` in the seed is the elementary composition proof. For variable exchange kernels `S_i` with `S_i ; P = P ; Q_i`, induction over the sequence gives `P ; Q_1 ; ... ; Q_t ; U` for the terminal ideal law; intermediate membership-preserving shuffles may be arbitrary (even state-dependent).

### A2. Assemble the cheap 99-card protocol using existing theorems

Do not modify `corrected_threeRound_headline_anyDeck` or reinterpret its existing operations. Add a new certificate. The proposed new protocol is:

1. Three independent 25-position exchanges between piles of sizes 50 and 49. Use the same `Gate6Crux.swapLaw` and literal pairing semantics as before. No local riffles between exchanges.
2. Independently shuffle each final pile using its inverse-GSR stable-sort law with `2^23` labels. This is 23 binary inverse riffles once B is proved.

Concrete constants in `Shufflemath.FiniteDeck`/`Shufflemath`:

```
S := FiniteDeck.permutationActionKernel Gate6Crux.swapLaw
H := FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal
F := FiniteDeck.permutationActionKernel correctedFiniteLaw99
L := FiniteKernel.comp S H
```

Create a *small* module (suggest `FiniteDeck/TerminalReset.lean`) importing `Gate6Corrected`, `Gate6Row`, and the promoted abstract theorem. Define these names locally or as new small defs. Prove `comp H L = L` as follows:

- `hH : H = idealLocalReset` is `k1_idealKernel_eq_membershipLift` with a definitional bridge to `idealLocalReset` (both are P;U). `hL : L = idealFullRound` is `idealFullRound_eq_physicalIdealRound.symm` or `K1_swapFirst_eq_exchangeLift`.
- Transport `idealLocalReset_absorption` across hH,hL (explicit `calc` or `Eq.subst`, not a broad unfold).
- Prove `apply (run S 3 mu) H = run L 3 mu` by applying `lastReset_run S H ... mu 2`. This theorem holds for all distributions, not just the reference deck.
- Establish the ideal bound from `segDeck`: use `g6_threeRound_finiteRun3_tv_le_q3`, `apply_segDeck_idealKernel_eq` (the first-round bridge), and `g6_threeRound_compList3_eq_run`. The exact sequence is in the `hbridge` block of `corrected_threeRound_headline`; isolate it as a reusable theorem `ideal3_point_tv_le_q3`. Rewrite only the kernel identity (`g6_3round_idealKernel_eq_fullRound` or existing equivalent), not deck distributions.
- To extend the ideal bound to all d, use `action_comp_eq_conv` (already in `Gate6K1Bridges`), expressing L as PAK of `conv swapLaw rho99Ideal`. Apply `action_run_tv_noise` twice, at d and segDeck. Both are equal to the TV of the SAME `powConv ... 3` law. No new proof about fixed deck relabeling is required. You may instead derive the bound from the reference-deck terminal-only finite protocol via this same symmetry. Do not infer a point-start bound directly from a fiber-uniform bound.

Target statement (namespace/type arguments may require adapting):

```
theorem terminal23_anyDeck (d : CommanderPermutation.Deck) :
  Dist.tv (FiniteKernel.apply
    (FiniteKernel.run S 3 (Dist.pointMass d)) F)
    (GSR.uniformDist CommanderPermutation.Deck) < (1 : Rat)/1000
```

For the last TV perturbation use the generic `apply_tv_of_row_bound` seed. For any d, the row distance between F and H is at most `Dist.tv correctedFiniteLaw99 Gate6Crux.rho99Ideal`, by `permutationActionKernel_eq_map` and `Dist.tv_map_contraction` (indeed equality by bijective relabeling, but no need). The proof of `corrected_kernelDiscrepancy_le_δ1` already contains this exact calculation in its inner block: use `correctedIdealLaw99_eq_rho99Ideal`, `correctedFiniteLaw99_tv_eq_rho99Finite`, `oneRoundDeckTV_le_delta1`, `δ1_eq_2401_over_8388608`. Extract a generic local row lemma to avoid repeating the `max'` proof. Apply it to nu=`run S 3 (pointMass d)`; do NOT bound the whole three-step run by 3*δ1. Triangle inequality against `apply nu H` gives `q3 + δ1 < 1/1000` (pure arithmetic in the seed). This is a single perturbation of the final kernel.

A first version may be stated with a positive `a = 2^23`-label law, followed by the binary-riffle bridge in B. As with the existing theorem, all physical exchanges assume uniform independent subsets and exact specified pairing; this is not a bound for human biased mash shuffles without a separate noise model.

### A3. Cheaper numerical certificates and real cost analysis

`q3 = 172379525755689183991816396516567920780192827919620440221147749 / 6691837923759692633601708022649918108038775216019298375918637677488`.

For last local shuffle alone, bound `q3 + 1225/2^rL + 1176/2^rR`. The previously compiled 23-per-pile law gives 46 pile riffles instead of 138; 22+22 gives 44; 22+21 gives 43, all below 0.001. The numerical checks in the included `check_math.py` are independent exact arithmetic, not Lean proofs.

Implement in that order. For 22+22 use `rhoRoundFiniteCorrected` at `a=2^22`, `rhoRoundIdealCorrected_eq_rhoRoundIdeal`, and `rhoRoundTransport_le_twoPile`. The ideal law is independent of a by definition; isolate a generic equality `rhoRoundIdeal ... a ... = rhoRoundIdeal ... b ...`, preferably `rfl`, before specializing. For unequal alphabets define the pullback product of two `gsrPermutationLaw` laws with `a_L,a_R` and map under `roundEmbedMap` then inverse. `twoPilePermutationTV_bound` already accepts distinct alphabets; `Dist.tv_map_contraction` handles the embedding and common inversion. The same proof from A2 now takes any local law and its known error bound. Prove the general interface once. All three proposed numerical bounds are in the seed; do not create three copies of the 99-card headline.

Use `CostedKernel` and `protocolCost` in `Cost.lean` / `ProtocolCertificate.lean` to count one uniform subset exchange as one operation (or a separately weighted operation), one binary riffle on one pile as one riffle. A terminal-only 22+21 schedule costs 3 exchange operations + 43 pile riffles under these declared units; not wall-clock human cost. If the allowed family uses only 25-position exchanges and local shuffles, a stronger necessary result is available below. If optimizing the sufficient collision bound at fixed three exchanges and a total integer riffle budget, enumerate only scalar `(rL,rR)` in a bounded range (no deck permutations). The smallest budget meeting the union-bound inequality is 43; the two possible 43-riffle splits can be tested. This is *optimality of the sufficient bound*, not proof that 42 riffles cannot actually mix sufficiently.

### A4. A real lower bound: two exchanges cannot suffice in this operation family

Every intermediate within-pile operation J preserves membership (`J;P=P`), so the observed membership law after t swaps is exactly Q^t for every such protocol. Applying a terminal ideal reset H to its output erases only within-pile order and gives L^t, by A1. Uniform decks are stationary for H (it is a state-independent random permutation action; for each fixed noise permutation, mapping uniform decks by that permutation is bijective; then mix). Alternatively `H=P;U` and the uniform pushforward/lift identity `FiberDisintegration.marginal_comp_fiber_eq_uniform` give the result. Thus TV contraction gives

```
TV(muProtocol, uniformDeck) >= TV(apply muProtocol H, uniformDeck) = TV(ideal run, uniformDeck).
```

Use `kernel_contraction` or `kernel_apply_lipschitz` with `tv_eq_tvFinsupp`. The ideal two-step TV from the segregated reference deck equals
`q2 = 12255318415559330995522631403472464258192877 / 4933350368865509640837610315994582805439728012`, which exceeds 1/1000. Existing theorem `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional` is fiber-uniform, so first use `ideal_reset_run_eq_point`/`apply_segDeck_idealKernel_eq` as for q3; relabel to other deterministic starts by `action_run_tv_noise`. The result suffices to refute a worst-case-start claim even just at segDeck. For fewer than two exchanges, ideal TV cannot be smaller because uniform is stationary for L and TV contracts. State precisely: any schedule using **at most two uniform 25-position exchanges between the same fixed piles**, with any intervening membership-preserving shuffles, fails the worst-case 0.001 target. Do not apply this lower bound to different exchange sizes, cuts changing membership, arbitrary full-deck riffles, or adversarial/nonuniform swap selection. It is a rigorous exchange-count lower bound in the stated family, not unrestricted cost optimality. Together with A2 it proves three exchanges are sufficient and necessary in that family (after B, for the specified finite binary-riffle law).

## B. Close the binary-riffle semantic bridge without rebuilding GSR

The `Gate6Corrected.lean` comment says `binary_composition_eq_ideal`, but there is no such exported declaration in this snapshot. The hard combinatorics are already in `GSR.idealShuffle_comp` and `GSR.productLabelShuffle_uniform_eq_ideal`. Transfer them along an injective encoding. This is the exact task; do not reprove rank sorting or collision bounds.

1. Define `pullLaw n a ha hn := (PermutationLaw.gsrPermutationLaw n a ha hn).map (fun p => p.symm)`. Define `encode (d : Equiv.Perm (Fin n)) := (List.finRange n).map d`. Prove `encode_injective` via `Equiv.ext` and the ith list element (the corresponding `Fin n` index of `List.finRange n`). Use `List.getElem_map` and the pinned lemma for `finRange` element, or an explicit `List.ofFn` equality then `List.getElem_ofFn`. No `Fintype (List ...)`.
2. Prove a plain list lemma, for arbitrary `f : X -> Y`, `ell : Y -> Fin a`:
   `stableBuckets a ell (xs.map f) = (stableBuckets a (ell ∘ f) xs).map f`.
   Expand `stableBuckets` (range.flatMap of filters); prove `filter p (map f xs) = map f (filter (p ∘ f) xs)` by induction on xs with `cases hp : p (f x)`. Then commute map through flatMap by list induction. No injectivity needed for this deterministic lemma.
3. For any current deck d, uniform labels on card identities `ell` induce uniform labels on positions `ell ∘ d`. Define an `Equiv` on function arrays with inverse precomposition by `d.symm` and prove inverses using `funext` and `Equiv.apply_symm_apply`. `GSR.map_bijective_uniformDist` yields uniform label reparametrization. For local reindexing of distributions use `uniform_map_eq_of_reparam` from `UniformReparamSeeds.lean`. Now `PermutationLaw.idealShuffle_canonical_eq_permPushforward` or `stableBuckets_eq_orderByNewPosition` gives

```
( (permutationActionKernel (pullLaw n a ha hn)) d ).map encode
    = GSR.idealShuffle n a ha (encode d).
```

   The output identity follows pointwise: rank maps original position to sorted rank, hence `encode (p.trans d) = (List.finRange n).map (fun i => d (p i))`, p=rank.symm. `List.map_map` is all that is needed. This is the commuting square `PAK pullLaw ; deterministic encode = deterministic encode ; idealShuffle`. Prove it for n>0 first, n=0 separately via unique permutation.
4. Compose the commuting square twice using `FiniteKernel.comp_assoc` or `GenericQuotient.apply_observation`. The RHS is precisely `GSR.idealShuffle_comp n a b ha hb` then `GSR.productLabelShuffle_uniform_eq_ideal ha hb`. On the LHS and RHS resulting deck laws, cancel their common `map encode` with the `cancel_injective_map` seed (uses `GenericQuotient.cancel_map_leftInverse`). No finite instance for lists needed. This gives `comp (PAK pullLaw_a) (PAK pullLaw_b) = PAK pullLaw_(a*b)` for every starting deck. If the coercions are difficult, state it per deck, use `funext` only at the end. Then `action_comp_eq_conv` or evaluating at identity gives the same identity for convolution of pullback noise laws.
5. Induct on t (t=0: a=1, `stableBuckets_a1_id` or constant label rank identity; handle n=0 separately). `FiniteKernel.compPow_succ`, `run_compPow`, the preceding multiplication law, `pow_succ` and proof irrelevance close `compPow (PAK pullLaw_2) t = PAK pullLaw_(2^t)`. This should be a generic theorem not a 23-step proof.
6. For the two pile embedding, show `roundEmbedMap` sends componentwise multiplication to full-deck multiplication by applying both sides to a left/right position (`FiniteDeck.embed_m_left/right`, `perm_mul_eq_trans_flip`). Independent product noise laws and the homomorphism give convolution on the product. For unequal t_L,t_R, simpler: act on left with right identity for t_L steps, then act on right with left identity for t_R. Pointwise these disjoint actions commute, and independent product sampling is `distProductFinsupp`. Use `ActionConvolution.act_composition` and `action_comp_eq_conv` to state the compiled law equality; lift to a paired local law. Combine with the swap only via `comp`, not by assuming swaps commute with local shuffles.

Acceptance: theorem connecting actual repeated independent binary stable-sort operations to the *corrected* permutation action used in `Gate6Corrected` and A. A list-level result quoted in a comment does not discharge the bridge. No need to change the existing quantitative proofs.

## C. G7 arbitrary-length changing-capacity protocols: use a time-indexed type family

`UniformTransport.lean` has a correct 895-line development and comp2/comp3, but the parked `LegalChain` attempts put the changing capacity vector into the wrong part of an inductive family. A schedule is data, not a recursive subtype of allocations. **Never make the changing capacity vector a fixed inductive parameter.** Use the generic `IndexedRunSeeds.lean`:

```
X : Nat -> Type
step : (t : Nat) -> FiniteKernel (X t) (X (t+1))
ref : (t : Nat) -> Dist (X t)
indexedRun step mu 0 = mu
indexedRun step mu (t+1) = apply (indexedRun step mu t) (step t)
```

`indexedRun_reference` proves invariance of a changing reference by ordinary Nat induction. No concrete capacities or Fintype in its proof. The optional `indexedKernel` returns a genuine heterogeneous composite `X 0 -> Dist (X t)` by running from `pointMass`. If needed, prove `apply mu (indexedKernel step t) = indexedRun step mu t` with the same induction and `FiniteKernel.apply_comp` (the row of successor is comp of earlier row with step t). This is generic; do not copy 2/3-step proofs.

### C1. Capacity schedule instance

Give `cap : Nat -> Fin p -> Nat`, `hsum : ∀ t, ∑ i, cap t i = N`. Set `X t := Allocation N p (cap t)`, `ref t := uniformAlloc (hsum t)` (explicit N,p,n arguments if required). First prove the theorem for arbitrary `step` and `hstep` above, using just `indexedRun_reference`. Then instantiate transfers with `src dst : Nat -> Fin p`, `amount : Nat -> Nat`, legality `src t ≠ dst t` and `amount t ≤ cap t (src t)` and recurrence `cap (t+1) = transferCap (cap t) (src t) (dst t) (amount t)`. Define step using `transferKernel` with explicit `(N := N) (p := p) (n := cap t)`; its result is in `Allocation N p (transferCap ...)`. Transport the result type along **only the capacity equality**, using `Eq.rec` or `cases hcap` in a small helper. Better first supply `cap` by a recursive recurrence so the successor equality is definitional, and avoid casts. Consume `hsum` proof irrelevance in a helper for the uniform reference. The one-step `hstep` is precisely `uniform_transport_transferKernel`; `transferCap_sum` proves feasibility by induction. To model a finite schedule of length T, extend by identity steps and unchanged cap after T, or provide the recurrence only on a bounded prefix via a separate `Fin (T+1)` wrapper. Identity handles p=0/1 without inventing distinct piles. No illegal transfers. The generic run accepts both homogeneous and heterogeneous actions, including deterministic or stochastic deal/discard actions on a different type family, provided each transports its indicated reference law.

Acceptance: one arbitrary-length theorem for legal changing-capacity transfer schedules, not a list of fixed length corollaries. Integrate the existing `ChangingPiles`, `DealDraw`, `DealBatch` examples as an illustration if they represent the same allocation semantics. Preserve order-information distinctions: uniform allocation does not determine the order within a pile; dealing from a fixed top position requires uniform order or the equivalent conditional subset-selection law. For adaptive actions depending on observations, the reference must be conditioned appropriately, not unconditionally uniform by default.

### C2. Conditional secrecy is just another partition fiber

Existing `HandSecrecy.handSet_uniform_law` is the marginal. Given that a set of previously observed positions P (size h) contains the known unordered set S (size h), the conditional law of a disjoint next set of t positions is uniform over the t-subsets of the **complement of S**. If the exact order of the known positions was observed, the same complement law holds. For distinct named cards, uniform deck and a positive-probability known event are essential; do not claim independence of different hands. In particular

```
Pr(next hand = T | known set S) = 1 / choose(N-h,t)
```

for T disjoint from S and |T|=t, else zero. Proof by counting: number of full decks realizing known S is h!(N-h)! (from `multiPile_card` for the partition P,complement). Number realizing known S AND next T is h! t! (N-h-t)! (three position blocks). Divide. If ordered known cards are fixed the first factor is 1 on both sides. Alternative shorter proof: within the conditional fiber, all remaining-card relabelings preserve the known event and act transitively on t-subsets, so count equal fibers and sum to one as in `HandSecrecy`. State conditional law as `fiberLaw` on the observation of the known set, then map to next hand; avoid building conditional probability from scratch. Use `Fintype.ofSurjective` on reachable observation if required. Condition h+t≤N; h=N,t=0 works. If multiple known hands or exact observations, form a partition of positions into their blocks and the unknown block. For variable number of players, the same statement uses arbitrary disjoint position blocks, not three hard-coded hands. This is useful for Cards Against Humanity-like hidden hands. Additional information (e.g., known decisions based on unobserved cards) is not covered without an explicit conditioning event.

## D. Unpark the general fixed-pair k-subset exchange (M3)

There is already a normalized `swapKernel` for two *uniform ordered card identities*, with arbitrary owner assignments. It is NOT the fixed-pair exchange of k cards from specified piles i,j. The G5capstone still needs that second kernel. The recent parked note describes a dependent-subtype/Fintype wall, not a mathematical obstruction. Avoid it entirely by sampling from a **fixed, allocation-independent choice type**.

### D1. Define the fixed source and row (no dependent product of row Fintypes)

For fixed N,p, capacities n, distinct i,j, legal k≤n i and k≤n j:

```
Pick(s,k) := {u : Finset (Fin s) // u ∈ (Finset.univ : Finset (Fin s)).powersetCard k}
Noise := Pick(n i,k) × Pick(n j,k)
```

Use the exact `Fintype.subtype` constructor and nonempty proof in `UniformTransport.TransferChoices`. Both depend only on sizes, not A. For each allocation A, form a bijection `e_i A : Fin (n i) ≃ {x : Fin N // x ∈ pileCard A i}` via `Fintype.equivOfCardEq` and `pileCard_card`; likewise for j. Consume the classical choices inside the definition. Map a selected index subset through the injection `x ↦ (e_i A x).val` (use `Finset.image` or `map` with embedding). The mapped sets U⊆A_i and V⊆A_j have size k. Define the raw owner function

```
if x ∈ U then j else if x ∈ V then i else A.val x
```

Prove it has the same capacities: output pile i is `(A_i \ U) ∪ V`, j is `(A_j \ V) ∪ U`, other piles unchanged. Prove each by `Finset.ext`, cases on x in U,V and owner, using disjointness. Cardinal equality uses `Finset.card_sdiff_of_subset`, `Finset.card_union_of_disjoint`, `U.card=V.card=k`. Use `omega` only on resulting scalar cardinality equalities. Package owner with proof in `Allocation N p n` once; do not expand this subtype in subsequent probability proofs. It is also fine to reuse `exchangePair` from `MultiPileExchange` for the two output finsets. Define `fixedPairKernel A := (GSR.uniformDist Noise).map (exchangeFromIndex A)`. Normalization automatic. k=0 yields identity even with empty piles; no requirement N>0 for this k=0 case.

### D2. Symmetry and stationarity from equal degree (no detailed factorial sum)

`exchangeFromIndex A` is injective: recover U exactly as old i minus new i, V as old j minus new j (`exchangePair_injOn` plus injectivity of the two index embeddings). The map from `Pick` to all k-subsets of the actual pile is onto by preimage under `e_i A` (construct preimage finset or use `range_iff_mem_of_card_eq` and `TransferChoices.card`; the ambient universe is only subsets of cards, not allocations). Every reachable B has uniform mass `1 / (choose(n i,k)*choose(n j,k))` by `GSR.map_injective_uniform_mass`. For the inverse transition choose V from new i and U from new j; `exchangePair_involution` proves return to A. Thus support iff is symmetric, row masses are equal in both directions, `fixedPairKernel_symmetric` follows from the injective uniform pushforward formula. Use existing `swapKernel_uniformStationary` proof as template: symmetric stochastic kernel + uniform law ⇒ stationary. Do not unfold `Fintype (Allocation ...)` to prove this. All sample domains are small symbolic Finset types.

### D3. General strong lumpability by reparametrizing the SAME noise

Let signed histograms agree for A,B. For each cell z=(i,c), `Cell A z := univ.filter (fun x => ownerCell color A x = z)`; `signedHist` counts this cell. Use `Int.ofNat.inj` to get equal cardinalities. `Cell A` is a partition indexed by `Fin p × Fin c` (unique owner from ownerCell, no cardinality proof). `Fintype.equivOfCardEq` gives a bijection for each corresponding cell. `glueBlocks` in `Partition.lean` works over a generic index type; `glueBlocks_apply_member` proves that the resulting σ has `ownerCell color B (σ x) = ownerCell color A x`. Hence `color (σ x) = color x`, `relabel σ A = B` (by `Subtype.ext`, `funext`, substitute σ.symm). This is the only transitivity lemma needed. The earlier CellRelabelSeeds guide and `MultiPileOrbit.glueBlocks_imagePile` give templates.

For each selected pile, σ restricts to a bijection of pile card subtypes. Combine
`e_i A ; restrict σ ; (e_i B).symm` to get a permutation of **fixed** `Fin (n i)`; similarly j. Lift to Pick via image, inverse via symm, cardinality via injectivity. Product gives `e : Noise ≃ Noise`. For each z, output allocation from B and e(z) is σ-relabeling of output from A and z; check raw owner update by membership in selected sets (`x ∈ image σ U ↔ σ.symm x ∈ U`). σ preserves categories, so the resulting signed histograms are equal. Apply `uniform_map_eq_of_reparam e` to the two maps from Noise to **raw signed histograms**. This is exactly the strong lumpability hypothesis; there is no dependent Fintype of histogram profile or allocation in the proof's pushforward equality. Use `GenericQuotient.quotient (signedHist color) fixedPairKernel` directly; obtain `quotient_intertwines`, `quotient_stationary`, `run_observation`, `ReversibleQuotient.reversible_quotient`, `fiberLaw_comp_eq_quotient_fiberLaw`. Mirror `histSwap_comp_square` and `histStationary_reversible`, with fixed-pair K and the SAME `histObserve` and `histStationary`, because the microscopic uniform allocation law is the same. This is the actual general G5capstone, not another scalar sum.

Fallback if the fixed index image is too cumbersome: reuse the existing row-dependent `TransferChoices A i k` and `TransferChoices A j k`, but prove the abstract uniform-reparam lemma once and instantiate it with the equivalence induced by σ, rather than rewriting one Fintype into another. The generic lemma needs the two finite types independently; their equality is NEVER needed. Use a separate lemma for image-card preservation, then a separate pointwise raw owner equation. Do not chase definitional equality of proof-bearing subtypes.

### D4. Obtain explicit profile formula as a corollary of the normalized kernel

For each category c, outgoing counts a_c from pile i, b_c from pile j with sums k, each within current cell sizes. Their probability is
`prod_c choose(X_ic,a_c)*choose(X_jc,b_c) / (choose(n_i,k)*choose(n_j,k))`.
The target is X'_ic=X_ic-a_c+b_c, X'_jc=X_jc-b_c+a_c, all other cells unchanged (use Int for arithmetic). Count each subset by the disjoint union of category pieces. The bijection is `U ↦ (U.filter color=c)_c`, inverse `Finset.biUnion`; pointwise membership and disjointness give the two inverses; each piece has size a_c. Use `Fintype.card_pi` for product counts; no multinomial induction. Push normalized kernel through profiles; to obtain mass at a target histogram sum profile masses over those producing it. If the profile carrier is inconvenient, prove only the finite indicator-sum mass equality first, bounded by existing choice domain. `histAllocSum_choose` and `lumpedTransition` are now useful cross-checks, not new kernel definitions. For two piles/two categories use x=X_00, y=X'_00, b=y-x+a as in the previous guide, or compare both kernels as pushforwards of the same allocation exchange (prefer latter). Existing `HistogramFiber.histogramTransition_eq_sum_lumpedTransition` and BL transition theorem can then serve as scalar regressions. No new specialized stationarity proof.

Acceptance: actual general normalized fixed-pair kernel, explicit physical set-swap law, symmetric uniform stationarity, actual signed histogram quotient and all-step simulation. Weighted detailed balance/uniform-fiber lift via generic results, not a false symmetric histogram matrix. Include a compiled 3-pile/2-category example with nontrivial exchange, plus two-pile BL recovery. This is the missing general gate; do not mark it complete with the transposition chain alone.

## E. General histogram probabilities using the same partition count twice (M4)

Reuse `multiPile_card` rather than proving a new multinomial recurrence. A useful proof that avoids any group-quotient library:

1. Define `ColorBlock j := univ.filter (fun x => color x = j)`, card r_j. For a reachable histogram X pick representative A0 from `GenericQuotient.representative`. Define G = `MultiFiber N c ColorBlock ColorBlock`: exactly color-preserving permutations. Its count is `prod_j r_j!` by `multiPile_card`. No group structure required.
2. Map G to the X-allocation fiber by σ ↦ `relabel σ A0`. D3 already proved surjectivity. For a given A in the fiber, the source fiber is in bijection with **the MultiFiber between cell partitions of A0 and A**. The forward map forgets the proof that σ preserves colors and proves cell-image equality. The inverse forgets cell proof and derives color preservation and relabel equality. These maps preserve the underlying permutation and are inverse by `Subtype.ext` and proof irrelevance. Cell partition index is `Fin p × Fin c`; if `multiPile_card` requires `Fin k`, reindex once using a bijection to `Fin (p*c)` (use pinned mixed-radix equivalence or explicit quotient/remainder; p*c=0 case empty). Its count is `prod_(i,j) X_ij!` by existing theorem. No new orbit-stabilizer theorem or proof that two different Fintype instances are defeq. Count this raw fiber via `Fintype.card_congr` with the equivalence, then bridge to `fiberSet.card` via `Fintype.card_coe` in a separate lemma. Use a local Fintype for a reachable carrier via `Fintype.ofSurjective` as in `histStationary_reversible`.
3. Count G by fibers: `|F_X| * prod_(i,j) X_ij! = prod_j r_j!`. Use `FiberDisintegration.sum_fiber_card` after restricting the codomain to the X-fiber, or double-count with the generic `biregular_count`. First establish the natural-number identity (if using `sum_fiber_card` cast back as done in `HandSecrecy`), then cast to Rat and divide using factorial positivity. Separately count all allocations by pushing uniform permutations through the fixed positional partition `BlockPartition.blockCap` and the multi-pile deck fiber count: `|Alloc| * prod_i n_i! = N!`. Show surjectivity using `multiPile_equivFiber` or gluing local bijections; don't rebuild global permutations by case analysis.
4. `GenericPairObservation.uniformMap_mass_card` / `ReversibleQuotient.uniformPushforward_mass` gives the actual `histStationary` mass = |F_X|/|Alloc|. Combine the two integer identities:

```
pi(X) = (prod_i n_i! * prod_j r_j!) / (N! * prod_(i,j) X_ij!) .
```

Here X has natural entries; the existing signed hist state is reachable, hence entries nonnegative, so convert via `.toNat` with `Int.toNat_of_nonneg`, not arbitrary signed factorials. This is a theorem about `histStationary`, not an independently normalized scalar function. It applies to both exchange kernels because they share the microscopic uniform equilibrium.

5. For arbitrary feasible table with given margins (not just reachable X), realize it by labeled slots. Per color j take `Σ i : Fin p, Fin (X_ij)`. Its card is r_j by column totals (`Fintype.card_sigma`), hence bijective to subtype `ColorBlock j`. Use this equivalence to assign owner i to each card from its slot. Row totals show pAlloc; for each cell the restriction of this map is a bijection with `Fin (X_ij)`. Prove once and return an allocation witness, so a histogram with correct nonnegative margins lies in ReachObs. No brute force enumeration of the full histogram space. Empty cells/piles/categories use `0! = 1`; N=0 singleton allocation if capacities sum to 0. If p=0 and N>0 feasibility fails, do not invent an allocation. The three-pile example can specialize the general formula, not calculate another separate table.

Acceptance: exported factorial mass theorem on `histStationary` plus feasible-margin realization theorem. This closes M4 even though a sharper explicit transition computation for arbitrary histograms may be deferred until D4 is needed.

## F. Arbitrary-pile local GSR comparison (M6)

The remaining generic G6 task is independent of the 99-card numerical case. Use the fixed position partition `P_i` (the block capacities are `n_i`, sum N), and choose bijections `Fin (n_i) ≃ {x // x ∈ P_i}`. A tuple of local permutations acts on positions by gluing the conjugated per-pile maps via `glueBlocks`; the output deck is `p.trans d`. The ideal uniform local law is independent uniform permutations in each block; it resets order conditionally on current allocation because `multiPile_equivFiber` is precisely the bijection from that tuple to its realized deck fiber. Prove this row theorem with `GSR.map_bijective_uniformDist` / `uniform_same_image` at generic types, not enumeration of N!.

### F1. A direct product coupling can avoid a new dependent-product TV theory

For each nonempty pile i choose independent uniform labels in `Fin (a_i)` and an independent uniform tie-breaking permutation. For the empty pile use its unique permutation (error zero). Use a common sample type whose elements are one pair `(labels, tie)` for each pile. All types depend only on fixed sizes, not the deck row. A uniform law on this finite product supplies independence. For a coordinate, pushforward uniform along evaluation is uniform: write the type as `factor_i × other_factors` using an explicit equivalence (restriction to i and to its complement) and the already existing uniform product law. The remaining factors have a witness (constant labels, identity ties), so no division by zero. Do not attempt an impossible `Fintype` on arbitrary lists or histograms.

For each sample form the finite local permutation tuple by rank inverses, and the ideal tuple by randomized tie ranks (also inverted). `Gate6TieRank.tieRankLaw_uniform` and `tieRank_eq_rankEquiv_inj` are the existing per-coordinate proofs; the common sample projects to independent uniform ideal permutations. To prove the whole ideal tuple uniform, use a product of independent pushforwards or count each tuple's fiber as the product of the per-coordinate fiber counts (the equivalence is pointwise). If all label arrays are injective, the two local tuples coincide, and hence their glued deck actions coincide. Apply `Dist.tv_maps_le_mismatch` to the common finite sample type, then union bound over pile indices. Each pile's collision probability is at most `choose(n_i,2)/a_i` by the existing collision proof. This gives

```
TV(F(d), H(d)) <= min(1, sum_i choose(n_i,2)/a_i),   for all d.
```

This method avoids a separate general n-ary product-TV subadditivity proof. Alternatively, first prove a dependent finite product of distributions by induction on the number of factors using `distProductFinsupp` and `distProductFinsupp_tv_subadditive`, plus a product encoding by `Fin.cases` (remove head, recurse on tail); if that API compiles more easily, use it instead. The key is to state the abstract product lemma before instantiating permutation types. Use pullback convention from B, not rank directly. n_i=0,1 yields unique permutations and zero error; a_i>0 needed for labels. Do not restrict arbitrary capacities by requiring every pile nonempty.

### F2. Comparison for arbitrary legal schedules

For any sequence of exchange/noise operations S_i and local finite/ideal shuffles F_i,H_i with row errors delta_i, the standard telescope gives terminal TV from ideal ≤ sum delta_i (nonexpansiveness for common kernels). `ProtocolCertificate` and `Perturbation` already establish this with `compList`; use them for a public parameterized comparison theorem. For a legal fixed-pile schedule in which every S_i factors on the allocation observation and every intermediate local operation preserves allocation, A1 improves this to **only the last local error** if the terminal ideal target has uniform internal order. Derive it by composing `S_i ; P = P ; Q_i` and `J_i ; P = P`, then `H=P;U`. This is a structural result for arbitrary numbers of piles; Commander is merely a specialization. It does not hold for local operations that change the chosen partition, or exchange rules depending on the previous internal ordering beyond the observation. When there are no exchanges, use the desired terminal reset target directly; do not claim the positive-length identity for t=0.

Acceptance: public local law on full decks, generic TV bound, and legal fixed-size schedule comparison; specialize to at least one nontrivial multi-pile example. No new copy of the two-pile proof. The exact ideal mixing residual is a separate problem of the corresponding allocation chain.

## G. M8 convergence and cost frontier: finish the core without spectral research

### G1. A shorter first implementation of the adjacent-transposition coupling

The November 25/26 guides already give the four-outcome coupling. The allocation chain now has `swapKernel_kernel`, stationary uniform law, and the histogram commuting square. **Prove the bound on the allocation chain first** if the full-deck bridge is taking time; this is independently meaningful for arbitrary multi-pile systems. Full-deck proof is the same argument with singleton position piles, or via the full permutation action. Do not confuse global uniform ordered-card-pair transpositions (with self-swaps) with fixed-pair uniform k-subset exchange.

Define `Adjacent A B := ∃ u v, u ≠ v ∧ B = swapPiles A u v` (include equality as a separate case when coupling). For A,B adjacent, couple ordered noise pairs via the involution φ on `Fin N × Fin N` swapping `(u,v)` with `(u,u)`, and `(v,u)` with `(v,v)`, fixing other pairs. This is a bijection; define it via `Equiv.swap` twice or by a four-case function and prove involution. They are four distinct outcomes, since u≠v. For those outcomes one deck performs the transposition and the other an identity; outputs agree. For all other outcomes both perform the same card transposition, and conjugation preserves adjacency. For the allocation proof use `cardTransposition_involution`, `swapPiles_swap_iff`, and `relabel_commute_owner` from `MultiExchange`. Prove equality/adjacency by extensional raw owners and the pointwise conjugation formula. It is harmless if outputs already agree in additional cases. Use `uniform_map_eq_of_reparam` for the second marginal, not an explicit sum over allocations.

Let `R_t(A) = run K t (pointMass A)`, `rho = 1 - 4/N^2`. At N≥2, 0≤rho≤1. Prove by induction on t that all adjacent A,B satisfy `TV(R_t A,R_t B) ≤ rho^t`. Base ≤1. For the step, express each run as the mixture over the first coupled noise pair of the remaining t-step run (`run_rec_eq`, `FiniteKernel.apply_pointMass`, `apply_map_kernel` from the previous `PairedMixtureSeeds`, and a generic `run_compPow` bridge). Use `pairedMixtureTV` from that seed (promote it if not yet compiled). On four distinguished pairs the contribution is zero; every other contribution ≤rho^t by IH or tv_self. The common uniform sum is bounded by `(N^2-4)/N^2 * rho^t = rho^(t+1)`. Only sum over `Fin N × Fin N`, not allocations. Use `Finset.card_sdiff_of_subset`, explicit four-pair Finset cardinality (four distinctness by simp [huv]); Rat arithmetic last. You do not need a Wasserstein metric or a max over all adjacent pairs.

### G2. Avoid a permutation-generation theorem for allocation connectivity

For A,B with the same capacities, define mismatch set `M = {x | A.owner x ≠ B.owner x}` (a Finset). If M nonempty, choose a∈M, target pile j=B.owner a. There must be b with `A.owner b=j` and `B.owner b≠j`: otherwise A_j⊆B_j, and since a∈B_j\A_j and their cards equal, contradiction by `Finset.eq_of_subset_of_card_le`. In particular b≠a and both a,b mismatched. Swap their owners: a becomes correct, b either correct or still mismatched, all other cards unchanged. Thus new mismatch set is contained in M\{a} (strict card decrease). No state can have exactly one mismatch, because the same equal-capacity argument produces another. Use induction on mismatch cardinality or `Nat.strong_induction_on`, with the statement directly about TV, avoiding a new dependent path datatype. If mismatch count is m, prove `TV(R_t A,R_t B) ≤ (m-1)*rho^t` for m>0, else zero (when the new mismatch count is zero, the step cost alone suffices since m≥2). `Nat.cast` monotonicity and TV triangle inequality give the induction. Therefore all pairs have bound `(N-1)*rho^t`. This argument also handles any number of empty piles. Singleton N=0,1 allocation cases are deterministic, no division by zero in rho; treat separately.

### G3. Finish mixing by averaging against stationarity

Uniform allocation is stationary by `swapKernel_uniformStationary`; induct on t for `run K t U = U` if a generic lemma is not already present. Average the pairwise estimate first against B~U using `pairedMixtureTV` with one constant kernel and one run kernel. This proves the bound from every deterministic allocation. Average again over A~mu (or use the same two-kernel inequality with a fixed stationary reference) to obtain

```
TV(run K t mu, uniformAlloc hsum)
  <= min(1, (N-1)*(1-4/N^2)^t).
```

Projection via `histObserve_run` and `Dist.tv_map_contraction` gives the histogram chain bound. For full decks, view them as allocations with N singleton labeled piles: `A.owner x = d.symm x` for d mapping position→card. Prove inverse `d = A.owner.symm` from every singleton fiber; owner is bijective by card=1. This is a clean `Equiv` using `Fintype.equivOfCardEq` only for local fibers, `Equiv.ofBijective` globally. With singleton capacities, `swapPiles` is exactly swapping two named card identities in the deck; when positions are sampled uniformly, mapping positions to identities by d is a uniform-pair bijection, so the physical transposition kernel has the same law. Reuse `GenericQuotient` or deterministic-map commutation and `GSR.map_bijective_uniformDist`. Transfer the bound by TV contraction/equivalence, without a second connectivity proof. This is another direct use of the general arbitrary-pile theory.

The finite-N rate is conservative (O(N² log(N/epsilon))) but rigorous and sufficient for M8; no spectral decomposition required. A small exact certificate e.g. N=4, t=30, epsilon=1/1000 reduces to `3*(3/4)^30 < 1/1000`; prove that rational inequality by `norm_num` and apply the generic theorem. For the three-exchange Commander protocol use the much stronger exact BL result in A, not the slow global transposition guarantee.

### G4. Meaningful bounded cost optimization

A provides a true lower bound on exchange count and an explicit cheaper sufficient schedule. This is a better immediate cost deliverable than another large generic optimization framework. For fixed t=3, sizes 50/49, threshold eps=1/1000, objective `rL+rR` under the *proved collision inequality* with terminal reset only, bound rL,rR by the known feasible 23+23 witness, then enumerate scalar pairs using `Finset.range` and exact Rat inequalities (or prove elementary exchange argument for diminishing gains). `check_math.py` computes the frontier. Use a `native_decide` only on a tiny scalar problem if needed, not on any deck carrier. Report collision-bound minimum separately from true physical cost optimum; distinguish mandatory uniform exchange selection cost from local riffle costs. Attach the actual physical kernel and epsilon to the certificate via `CostedKernel`/`costedProtocol_certificate` if convenient, not just a vector of arithmetic values.

General weights `w_i=choose(n_i,2)` and unit riffle cost: repeatedly choose largest marginal gain `w_i/2^(r_i+1)` minimizes summed upper bound at fixed integer budget (each pile's gains decrease; any selected gain smaller than an available next gain can be exchanged). For different costs use bounded DP or enumerate budget-feasible scalar tuples; greedy not generally optimal. For arbitrary legal exchange schedules, characterize the ideal residual via the allocation chain and use F2; do not charge intermediate local errors when those operations are provably unnecessary. Optional sharper exact GSR descent probabilities/spectral bounds can improve the certificates after G8, not block completion.

## Final acceptance checklist (morning M1–M8, updated)

| Milestone | Status at 8648036 / what must be exported |
|---|---|
| M1 | Done: `histSwapKernel`, `histSwap_comp_square`, `histStationary_stationary`, `histObserve_run`. |
| M2 | Done for M1: `histStationary_reversible`, `histStationary_uniform_fiber_lift`. |
| M3 | D: normalized arbitrary fixed-pair k-exchange, physical row law, symmetry, strong lumpability, quotient; explicit profile bridge and BL regression. |
| M4 | E: actual factorial stationary mass for arbitrary p,c; margin realization and 3-pile specialization. |
| M5 | `corrected_threeRound_headline_anyDeck` landed; B supplies repeated binary operation theorem. A is a new cheaper certificate and real cost lower bound, not a redefinition of the old theorem. |
| M6 | F: arbitrary-pile local finite/ideal law and quantitative legal schedule comparison; terminal-reset specialization for lumpable exchange. |
| M7 | Single transfer and concrete toy actions/hand-set marginal done; C arbitrary run and known-card conditional law. |
| M8 | G: arbitrary finite-N convergence, projected and full-deck guarantees, explicit costed protocol and bounded certificate optimum (with stated scope). |

Canonical build and verification required for each landed public theorem. Maintain accurate current progress in `docs/lean_plan.md` and `docs/agent_handoff.md`. Keep the review history; do not treat every prior hint as an independent task. When the required core interfaces are exported and compiled, the through-G8 campaign can be called complete; optional G9 and sharper physical models can follow. The operator will retain the same overarching goal. Read this new handoff, reconcile the resume pointer, and execute the next unfinished checkpoint rather than start over.
