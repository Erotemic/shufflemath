# Executable finite-deck finish-line handoff (2026-11-26)

Snapshot: `183eb5ee69b3`. Intended for Inkling2 or Qwen3.8:27B. This is a task-oriented guide, not a list of optional mathematical projects. Follow the numbered milestones and make the stated public theorem land before expanding the next branch. Existing hints from November 25 remain available, especially the adjacent-transposition coupling and `Gate6AssemblySeeds`. The new Lean seeds are proposed implementations, not independently compiled by the reviewer. They can be tested and adapted on the pinned Lean 4.34 toolchain. Do not introduce placeholders to make a build succeed.

## 0. Work discipline and dependency order

- Install this overlay, replace the live loop goal with the goal document, and put M1 in the current resume pointer of `docs/agent_handoff.md`. Keep the standing operational policies in AGENTS.md. Do not change existing reviews or create worktrees.
- First compile the existing `dev/inkling-hints/2026-11-25-evening/PairFactorSeeds.lean` directly (it was modified by `44de7cb`). Then compile the new `ReachableQuotientSeeds.lean` independently. Reuse exact definitions, not a second histogram carrier with no bridge. Move successful lemmas into production modules with the repository's `module`, `public import`, `@[expose] public section` convention.
- One public theorem/interface per batch. A scalar expression or a conditional theorem with the essential hypothesis unproved is not the final interface. After a small focused build, commit explicit paths, add canonical imports and update `dev/verify_next_phase.sh`. Record exact theorem names and hypotheses in the active manifest. No need to run a bulk axiom audit for every proof.
- Work at abstract `X Y : Type*` whenever possible. Do not unfold a specialized `Dist.ofFun`, `uniformDist (Equiv.Perm (Fin 99))`, allocation `Fintype`, or a full-deck TV sum. `Dist` is a finite-support simplex even on a raw infinite observation type. `FiniteKernel.apply`, `comp`, `GSR.apply_deterministic`, `GSR.comp_deterministic_left`, `Convexity.StdSimplex.map_map` and `FiniteKernel.apply_comp` are all usable without `Fintype`. A large symbolic finite type should not be evaluated.
- If a focused proof fails twice with a related elaboration error, record the exact declaration and shrink it to the generic lemma; if one check exceeds a bounded wall/memory budget (e.g. `timeout 180s` for a small new lemma, or a monitored target build with a larger explicit allowance), stop and split it. An import rebuild is not a single-lemma test; distinguish these in the log. Never use `maxHeartbeats 0` or escalating recursion depth as the plan. Keep an independent next milestone available instead of a six-hour retry.
- Do not reopen a completed result just because old prose calls it WIP. Do not convert this guide into hundreds of new checklist subtasks. The milestone checklist at the end is the finish line.

## M1. The shortest route to a genuine general histogram kernel

**Already proved:** `Shufflemath.InklingHints.signedHist_lumpable` in the evening hint file. Do not reprove it by induction on piles, group orbits, or arithmetic stationary sums.

Let `A : Allocation N p n` and `color : Fin N → Fin c`. Define `f A = signedHist color A`, a function from cells `Fin p × Fin c` to `Int`. The new theorem says that equal *natural* owner histograms give equal output pushforwards under f for `swapKernel hN`. Equal f values imply equal natural histograms: `funext z`, apply `congrFun` to the equality, unfold `signedHist` only and use injectivity of `Int.ofNat` (`exact_mod_cast` or `omega`). Thus we have strong lumpability in the exact form

```
∀ A B, f A = f B → (swapKernel hN A).map f = (swapKernel hN B).map f
```

### M1a. Use the range as the state space, not all integer matrices

Key insight: the reachable range is already a valid finite state space, and a `Dist` does not require `Fintype` to define the quotient. Do not prove every margin-feasible histogram realizable before constructing the kernel. Let

```
ReachObs f = { H // ∃ A, f A = H }
observe f A = ⟨f A, ⟨A,rfl⟩⟩
representative f H = Classical.choose H.property
Q H = (swapKernel hN (representative f H)).map (observe f)
```

The subtle bridge from the raw signed output to the subtype is easy: include the subtype into the raw type. To cancel a pushforward by the inclusion, use its left inverse. Given a default reachable value `d`, define `retract H = if h : ∃ A, f A = H then ⟨H,h⟩ else d`. On the range `retract ∘ Subtype.val = id`. Map the raw distribution equality through `retract`; `map_map` and `map_id` recover equality on the subtype. This avoids any summation, equality of dependent Fintype instances, or evaluation of histograms.

`dev/inkling-hints/2026-11-26/ReachableQuotientSeeds.lean` contains the complete proposed generic proof chain:

1. `ReachObs`, `observe`, `representative`, `observe_surjective`.
2. `retract`, `retract_val`, `cancel_map_leftInverse`, `reachable_map_eq`.
3. `quotient`, `quotient_at`, `quotient_intertwines`.
4. `apply_observation`, `quotient_stationary`, `run_observation`.

Compile in this order. If the `rw [map_map]` expression uses a lambda rather than `(r ∘ g)`, state an explicit function equality `have hi : (fun x => r (g x)) = id := funext hr` and `rw [hi]`. For `reachable_map_eq`, if the final `exact h` is not definitionally accepted, use `change μ.map f = ν.map f` after the two map rewrites; otherwise explicitly prove `Subtype.val ∘ observe f = f` by `funext; rfl`. For `quotient_at`, use `change` to expose only the representative row, then apply `reachable_map_eq` with `d := observe f x`. Do not touch the actual allocation Fintype. `run_observation` uses `run_rec_eq` (first step first) and induction generalized over μ. These generic lemmas can be compiled even on a tiny machine.

### M1b. Instantiate the generic construction (this is the next required theorem)

After promotion, create e.g. `FiniteDeck/HistogramKernel.lean`. The following is a schematic assembly with exact source identifiers; adjust namespaces after migration:

```
let f : Allocation N p n → ((Fin p × Fin c) → Int) := signedHist color
let K := swapKernel hN
have hl : ∀ A B, f A = f B → (K A).map f = (K B).map f := by
  intro A B h
  apply signedHist_lumpable hN color A B
  funext z
  have hz := congrFun h z
  change Int.ofNat (ownerHist color A z) = Int.ofNat (ownerHist color B z) at hz
  exact_mod_cast hz
have hstat : FiniteKernel.apply (uniformAlloc hsum) K = uniformAlloc hsum := by
  ext A
  exact swapKernel_uniformStationary hN hsum A
```

Define named `histObserve`, `histSwapKernel`, `histStationary` using `observe f`, `quotient f K`, `(uniformAlloc hsum).map (observe f)`. Export:

```
comp K (deterministic histObserve) = comp (deterministic histObserve) histSwapKernel
apply histStationary histSwapKernel = histStationary
∀ t μ, (run K t μ).map histObserve = run histSwapKernel t (μ.map histObserve)
```

They are direct applications of the new generic lemmas. Note that the definition returns `Dist`, so the row is normalized even before anyone proves a scalar formula. This establishes the genuine general random-transposition histogram chain. Do not substitute `HistogramFiber.histogramTransition`, which is a different, fixed-pair k process.

If the generic reachable subtype Fintype is needed for the next task, install a LOCAL instance using `Fintype.ofSurjective (observe f) (observe_surjective f)` with the existing finite `Allocation` domain; check the exact Mathlib signature. Or use a finite bounded histogram `Fin p × Fin c → Fin (N+1)` and take the `Finset.univ.image` range. Prove `ownerHist ≤ N` from `Finset.card_le_card (filter_subset ...)`. The already-proved pushforward equality carries across the injective encoding by the same retraction. Do not put Fintype requirements on the generic quotient constructor.

**Acceptance M1:** canonical imported `Dist`-valued arbitrary-pile/category transposition histogram kernel, unconditional commuting square, stationary law, and all-step projection theorem; focused build and normal verifier. The previous generic proof is already sufficient. This should be completed before any more specialized counting.

## M2. A reversible quotient also gives the backward conditional law

The general theory below applies both to the transposition quotient and the fixed-pair exchange quotient. Reuse `dev/qwen-hints/2026-11-25-morning/QuotientSeeds.lean` for `map_mass_on_fiber`, `blockMass_eq`, `reversible_quotient`. Do not produce independent stationarity proofs for each operation.

Let `K` have stationary reversible measure μ on finite X. Let `f : X → Y` be surjective and strongly lumpable, `Q` its genuine quotient. `π = μ.map f`. Consider the stationary joint edge law `J(x,x')=μ(x)K(x,x')`. Reversibility means J is symmetric. Push it forward by `(f,f)` to get

```
∑_{f(x)=y} ∑_{f(x')=z} μ(x) K(x,x') = π(y) Q(y,z).
```

Symmetry immediately gives `π(y)Q(y,z)=π(z)Q(z,y)`. The earlier `blockMass_eq` candidate implements exactly this; use it with abstract X,Y and the row equality `quotient_at`. No additional row normalization or histogram symmetry. `swapKernel_symmetric` and uniform masses discharge microscopic detailed balance.

**Stronger, useful lift theorem:** if μ is uniform on X, let `U = FiberDisintegration.fiberLaw f hf`. For any y and individual b with z=f(b), by symmetry of K,

```
(U K)(y,b) = (1/c_y) Σ_{x:f x=y} K(x,b)
           = (1/c_y) Σ_{x:f x=y} K(b,x)
           = Q(z,y)/c_y
           = Q(y,z)/c_z
           = (Q U)(y,b).
```

Here `c_y = card (fiberSet f y) > 0`. The middle equality uses the SAME forward lumpability theorem at b, with destination y. The penultimate equality is the weighted detailed-balance identity after clearing the common factor `card X`. On the RHS only the term z survives (`Finset.sum_eq_single (f b)`; all other fiber masses zero). This proves `comp U K = comp Q U`. General reversible μ with positive π works by conditional weights `μ(x)/π(f x)` instead of uniform, but do not require this generalization to finish the finite uniform project.

Lean route: first prove `uniform_map_mass` using `GSR.map_uniform_mass` or `map_mass_on_fiber` and `GSR.mass_uniformDist`. Prove separately `fiber_weight_balance : (c_y : Rat) * mass (Q y) z = (c_z : Rat) * mass (Q z) y` from `reversible_quotient`; `field_simp` only here, with positive card X. Next prove LHS mass formula with `FiniteKernel.apply_mass`, `FiberDisintegration.fiberLaw_mass`, pointwise symmetry, `Finset.mul_sum`, and the pushforward row formula. Prove RHS mass formula by one-term collapse. Finally use positive c_y,c_z and `field_simp`/`nlinarith` for the ratio identity. No concrete allocation or deck size in this proof. For the raw reachable carrier install local Fintype only at the instantiation. This also provides exact TV transfer from a uniform-fiber start via existing `FiberLifting` / `OracleRefinement` machinery; for arbitrary starts only the projection is guaranteed, not full-state TV equality.

## M3. General fixed-pair k-exchange, using the owner carrier

Keep `UniformExchange.swapKernel` as the uniform ordered-pair transposition kernel. For any distinct pile indices i,j and legal `k ≤ n i`, `k ≤ n j`, define `pile A i := univ.filter (fun x => A.val x = i)`. Its size is `Allocation.pileCard`. The two piles are disjoint. Define selection finsets `UChoices := (pile A i).powersetCard k`, `VChoices := (pile A j).powersetCard k`; their subtype product is the finite sample type E_A. Nonempty follows by `Finset.card_powersetCard`, `Nat.choose_pos`, `Finset.card_pos`. Handle k=0 as an identity operation, including empty piles. Avoid deriving a Fintype for a new nested subtype with complicated proof fields; use the actual existing finite choices. Reuse `MultiPileExchange.exchangePair` for the updated two selected piles, `exchangePair_injOn`, `pairwiseExchangeCount`, `exchangePair_involution` for local facts.

Define owner update

```
if x ∈ U then j else if x ∈ V then i else A.val x
```

and package it as `Allocation N p n`. Prove each pile accessor first: pile i becomes `(pile A i \ U) ∪ V`; pile j vice versa; every other pile unchanged. Use `Finset.ext`, `mem_filter`, `mem_sdiff`, `mem_union`, split on the membership of x in U,V, their subset facts, and i≠j. Then `card_sdiff_of_subset`, `card_union_of_disjoint`, and `omega` discharge capacity. Do not prove capacity by a large nested sum of ifs. The row is `GSR.uniformDist E_A |>.map update`. Its support has exactly `choose(n i,k)*choose(n j,k)` points because the differences of the old and new piles recover U,V. The inverse selection at B is `(V,U)`. For arbitrary A,B, the forward/reverse supports correspond; equal denominator gives microscopic symmetry. `uniformMap_mass_card` or `GSR.map_injective_uniform_mass` works on the abstract sample type. Thus uniform allocation stationarity follows from `detailedBalance_implies_stationary` just as in `UniformExchange.lean`.

### M3a. Do NOT do new category arithmetic to prove lumpability

Two safe routes, use the first unless the subtype transport becomes expensive:

* **Relabel route:** If A,B have equal owner histograms, form the partition of card identities into cells `(i,c)`. Each cell is a finset filter. Corresponding cells have equal sizes by the hypothesis. Flatten the pair index to `Fin (p*c)` using a finite product equivalence (or generalize the small `Partition` API to any finite index type). `IsPartition` is simply unique cell ownership. Obtain per-cell bijections with `Fintype.equivOfCardEq` using `Fintype.card_coe`; glue with the already-proved `glueBlocks`. The resulting σ preserves color, sends each A-pile to the corresponding B-pile, and `relabel σ A = B`. For a legal subset selection in A, map each subset through σ using `Finset.image` (or `Finset.map σ.toEmbedding`). The inverse is σ.symm. This is an equivalence E_A ≃ E_B; uniform choices transport by `GSR.map_bijective_uniformDist` (or `uniformMap_reparam`). Prove the owner update commutes pointwise with relabeling; the color-preserving relabel leaves the output histogram unchanged. Thus the pushforward equality follows by `map_map` and the uniform reparametrization theorem. Apply M1's same quotient constructor.
* **Profile route:** For k-subsets of one pile, map U to counts `u_c = #(U ∩ Cell(i,c))`. Given valid u, the fiber is in bijection with the dependent product over c of k_c-subsets of Cell(i,c). Forward = restrict/intersect; inverse = union. Prove each cardinal by `Finset.card_powersetCard`, `Fintype.card_pi`. Pair-disjointness and cover give the inverse and total k. This is a generic finite partition proof once, not induction on two colors. It establishes the actual selection mass `prod_c choose(X_ic,u_c)/choose(n_i,k)`. Independent left/right choices give product weights. The signed histogram update subtracts u from i/adds v, and subtracts v from j/adds u. Like M1, factor the row through the profile law. Use the actual pushforward to handle normalization; sums over valid destination histograms are then automatic.

The two routes complement each other: relabeling gives the exact quotient before any explicit counting, profile route gives the useful numerical formula. If you use relabeling, do not stop before the profile formula; if you use profiles, do not reprove an independent orbit theorem solely for normalization. Existing `Histograms.lumpedNum`, `lumpedTransition`, `fin_lumped_rowSum` and `prod_choose_eq_zero_iff` establish the scalar factors and zero weights. The new theorem must identify those factors with the microscopic selection pushforward, not just another scalar identity.

### M3b. Explicit formula and BL specialization

For fixed i,j, write X for initial histogram, Z for destination. The probability is

```
Q_ij,k(X,Z) = Σ_{valid u,v, Z = update(X,u,v)}
  (Π_c choose(X_ic,u_c) choose(X_jc,v_c)) /
  (choose(n_i,k) choose(n_j,k)).
```

Use only supported u,v (sum k, componentwise bounds) to avoid Nat underflow, or use Int for update and prove equality to Nat update afterwards. Each profile term is nonnegative. An invalid profile contributes zero by `lumpedTransition_eq_zero_of_exceed_left/right`; avoid summing over unbounded Nat functions. `histogramTransition_eq_sum_lumpedTransition` is the two-color scalar formula and can be identified as a specialization. It is not the actual quotient theorem.

For 2 piles, 2 colors, left capacity m and marked total r, X is determined by x=X_00; X_01=m-x, X_10=r-x, X_11=N-m-r+x with feasible margins. Build an equivalence with the existing valid `BLState`/its feasible subset (check its exact definition). Establish x' = x-u_0+v_0 on valid selections, then v_0=x'-x+u_0 in signed coordinates. Eliminate the second sum using `sum_eq_single`; zero for invalid terms, then the existing `transitionNumerator` is exactly the remaining sum. Prefer transferring already-proved BL stochasticity and stationarity to rebuilding it. For degenerate k=0, m=0,N, r=0,N, prove identity/singleton cases outside `ExchangeAdmissible` assumptions.

## M4. General histogram counts: use the existing multi-pile factorial theorem TWICE

We need arbitrary p,c, not a new extension of the 1,600-line two-color file. A direct finite slot-filling proof reuses `BlockPartition.blockCap`, `blockCap_card`, `blockIsPartition`, `MultiPileFiber.multiPile_card`, and `Partition.glueBlocks`.

Let H have nonnegative integer entries `H(i,c)` with row margins n_i and column margins r_c (r_c counts actual color-c cards). Total = N. Flatten pairs (i,c) to `Fin (p*c)` and form the *fixed canonical position partition* `S_ic` of `Fin N` using `blockCap N (p*c) Hflat`. It has cell sizes H_ic. Group these blocks by color into `S^c = ⋃_i S_ic`. Prove `card S^c = r_c` using `Finset.card_biUnion` and pair-disjointness. These unions are a partition (unique underlying cell). Let `C^c = univ.filter (color= c)` be the actual card partition. No new dependent Sigma Fintype proof is required.

1. Define F = `MultiFiber N c S^c C^c`. Its size is exactly `Π_c r_c!` by `multiPile_card`. It is nonempty by gluing per-color equivalences, since the corresponding sizes match.
2. Map each filling d∈F to `Allocation N p n`: a card's owner is the pile-coordinate of the unique slot containing `d.symm card`. Prove its pile finset equals the image under d of the union of S_ic over c; card_image_of_injective + card_biUnion gives n_i. Prove the resulting histogram equals H: `d '' S_ic` is exactly the set of pile-i cards with color c (use d injective and unique cell ownership). This also proves **all feasible histograms are realizable**.
3. For any allocation A with histogram H, let `C_ic := {card | A(card)=i ∧ color(card)=c}`. It is the fine card partition with sizes H_ic. A filling maps to A iff it sends every S_ic onto C_ic. Forward: owner matches, color matches, so subset and equal sizes imply equality. Reverse: unique membership forces the owner function to equal A. The fiber is exactly `MultiFiber N (p*c) S C` via subtype extensionality; its size is `Π_{i,c} H_ic!`, by the SAME `multiPile_card` theorem applied to the fine partition.
4. Sum cardinalities over the histogram fiber of allocations. Use finite `Finset.univ` filter / `Finset.card_biUnion` or abstract `FiberDisintegration.sum_fiber_card` with the reachable carrier. Prove the division-free identity first:

```
card {A : Allocation N p n // ownerHist color A = H} * Π_{i,c} H_ic! = Π_c r_c!
```

Use only the generic count theorem; no explicit enumeration of `Fin N` permutations. To get total allocation count, use the coarse positional partition `blockCap N p n`: the map deck → allocation is surjective by the same gluing theorem. Each fiber has `Π_i n_i!` decks. Thus `card Allocation * Π_i n_i! = N!`. This is also useful for the G6 ideal-reset TV bridge. Combine the two Nat identities in Rat (factorial positive, card Allocation positive) to get

```
π(H) = (Π_i n_i! * Π_c r_c!) / (N! * Π_{i,c} H_ic!).
```

It is exactly the mass of the stationary pushforward, not a separately normalized guessed distribution. Likewise deck fiber count = allocation histogram fiber count times `Π_i n_i!`. For invalid margins there is no allocation; no need to assign mass on a larger impossible state space. Include zero-capacity/zero-color cases (`0! = 1`); N=0 is trivial when capacities feasible, and sampling a random card requires N>0.

**Acceptance G5:** M1–M4 actual allocation/quotient kernels for the two exchange mechanisms, strong lumpability, uniform stationary allocation law, weighted detailed balance and lift intertwining, general factorial histogram formula, exact profile law, and a concrete 3-pile/2-color instance. Retain existing `ThreePileTwoColor.lean` as counting regression, add a transition example (not just another count). Do not make the whole roadmap depend on implementing an abstract group quotient in Mathlib.

## M5. Finish the existing Gate 6 certificate without a new large counting development

The restricted result is already canonical (`FiniteDeck/Gate6ThreeRound.lean`): `g6_threeRound_headline`. It is correct about its declared start and kernel, but it is not yet the all-start stable-sort theorem requested by the operator. Keep it as a regression theorem. The following proof obligation is independent of M2–M4; if M3 or M4 is blocked, finish this before returning. Do not require all multi-pile work before finishing the concrete certificate.

### M5a. Membership row independence (new concrete candidate)

Compile `dev/inkling-hints/2026-11-26/Gate6RowSeeds.lean`. It supplies the exact missing theorem `rawExchangeMembership_eq_of_membership`. The code uses the same map `choiceImage` as the real `rawExchangeMembership`, `newLeftCards_injective`, `newMembership_overlap_25`, `exchangeChoice_card_eq_transitionDenominator`, `FiniteDeck.subsetExchangeCount`, and the two compiled helpers in `Gate6K1Bridges.lean`: `range_iff_mem_of_card_eq` and `uniform_same_image`.

Detailed fallback instructions (not another counting proof):

- Commander `Membership` and `FiniteDeck.Membership 99 50` are the same underlying subtype. If their `Fintype` instances differ, a `Finset.univ` elaboration mismatch can appear. Prove membership equivalence of the resulting finite sets with `Finset.ext; simp only [FiniteDeck.ReachSet, Finset.mem_filter, Finset.mem_univ, true_and]`. Use that equality to transport the CARD theorem. Never ask Lean to reduce the instances themselves.
- For the two set differences, `Finset.card_sdiff` gives `card S - card (S∩T)`. Both card S and card T are 50; `newMembership_overlap_25` is exactly the intersection count 25. Reverse intersection by `Finset.inter_comm` for the second difference. If `rw` leaves literal arithmetic, use `omega` only there. This proves image inclusion without reconstructing inverse choices.
- `choice_card_nat`: the existing theorem is stated in Rat; cast the *symbolic* equation back to Nat after exposing `BernoulliLaplace.transitionDenominator` if necessary, and simplify `99-50=49`. Do not evaluate giant distribution terms. If the `change` in the candidate fails because the denominator uses different cast syntax, first prove a small independent denominator lemma in Nat and rewrite it in the Rat equality. The existing `CommanderA3ExchangeCard` proof already has exactly the product-of-choose calculation.
- Cardinal inclusion + injectivity + equal cardinality gives image equality by the compiled `range_iff_mem_of_card_eq`. If d,e have the same membership, their reachable set is literally the same. `uniform_same_image` concludes equality of pushforwards. This is all. Do not resume `k1b_count_split` or prove a commutation of finite local shuffles with swaps.

### M5b. Finish ideal deterministic-start smoothing using pure kernel algebra

Let `P = deterministic membership`, `U = localLift`, `E = rawExchangeMembership`. From M5a E depends only on membership; use the `rowFactor` and `rowFactor_comp` candidates in `dev/qwen-hints/2026-11-25-morning/Gate6AssemblySeeds.lean` to get `E = comp P Q` with `Q` a true membership kernel. Do not need to identify Q's scalar formula to prove reset absorption. `K1_swapFirst_eq_exchangeLift` identifies the correct-order ideal position round L with `comp E U`. By associativity L = `P ; Q ; U`. The initial local reset H = `P ; U` (`k1_idealKernel_eq_membershipLift`). `localLift_preserves_membership` says `U ; P = identity`. Apply the already compiled `reset_absorption P U Q` to show `H ; L = L`. `run_from_reset_eq_point` (candidate in same file) then gives equality of L-runs from H(d) and pointMass d for any positive number of rounds. No further deck-level distributions need to be compared term by term.

Set d0 = `Equiv.refl (Fin 99)`. Prove `membership d0` is `leftOrigSet` using `leftOrigSet_eq_image` (`CommanderFiberCount`) or `leftOrigSet_eq_L50` (`CommanderPhysicalExchange`), and the definition of `leftCards`. Show `project d = commanderSegregatedState ↔ membership d = membership d0`: `membershipFiber_iff` gives membershipCount=50. Both membership and `leftOrigSet` have size 50, so their intersection has full size iff they are equal. Specifically use `Finset.inter_subset_left/right`, `Finset.eq_of_subset_of_card_le` and `leftOrigSet_card`. This does NOT require enumeration of 99-card permutations or of macro fibers. Now `same_fiber_law` from `Gate6AssemblySeeds.lean` identifies the uniform conditional on `project=segregatedState` with the conditional on `membership=membership d0`. If `localLift` is defined by uniform pushforward instead of `fiberLaw`, use `localLift_mass` and compare its support and constant mass with `FiberDisintegration.fiberLaw_mass`, using `fiberSet_membership_card`. `ideal_batch5b` and `k1_idealKernel_eq_membershipLift` identify H(d0) with that local lift. `FiniteKernel.apply_pointMass` identifies `g6ThreeRoundStart` with the macro conditional. Use `equal_after_first_run` (compiled) to rewrite the IDEAL 3-round law from d0 to the already proved ideal residual q3. Do not assert this equality for the finite-GSR law.

### M5c. Correct the permutation orientation cheaply; certify exactly 23 binary riffles

`FiniteDeck.act p d = p.trans d`: new position i contains `d(p(i))`. `gsrPermutationLaw` maps each label vector to rank(old) = new, so the actual stable-sort pullback is `rank.symm`. This is confirmed by `PermutationLaw.idealShuffle_canonical_eq_permLaw`. Avoid changing the old theorem's semantics by an implicit rewrite. Add named `pullbackLaw = (gsrPermutationLaw ...).map (fun p => p.symm)`; use compiled `perm_inverse_tv` and `perm_inverse_uniform`. The pile embedding is conjugation through `finSplit`; inverse of `embed_m pl pr` is `embed_m pl.symm pr.symm`. Prove by `Equiv.ext` and `finSplit` cases, or `Equiv.trans_symm` and `Equiv.sumCongr` inverse law. Therefore use the local inverse laws before embedding or equivalently invert the whole `rhoRoundFinite`; the ideal embedded law is invariant by inversion. Show this by reparameterizing the pair of independent uniform local permutations (two copies of `permInverseEquiv`, product equivalence, `GSR.map_bijective_uniformDist`; use product-uniform bridge if needed). The TV bound is unchanged. Build a *new* corrected finite round S ; H_f, and use the same row discrepancy proof as `g6_threeRound_kernelDiscrepancy_le_δ1` with corrected laws. Prove it generically at abstract law arguments if concrete normalization occurs.

The `a=2^23` law needs a binary-composition bridge, not just a numeric parameter. Use the compiled `GSR.idealShuffle_comp` for stable lists, then injective encoding of a permutation by `List.finRange n |>.map p` (nth position determines p by `Equiv.ext`). For any deck d (a bijection), stable sorting by labels on positions is pushforward of the canonical ordering by d, because relabeling preserves the order-by-key comparison when the labels are attached to original positions. Show the pointwise stable sort relation using existing bucket/sorted-key lemma and `List.map_map`; reparametrize label arrays by d when labels are indexed by card identities rather than positions. Induct binary rounds via `idealShuffle_comp` and cancel the encoding with a left inverse, using `cancel_map_leftInverse` from M1. Equivalently prove the two-label product composition directly on inverse ranks using the existing mixed-radix sorting compatibility. The theorem must have the precise execution order `conv W_a W_b = W_(a*b)` under `act` (check on pointwise permutation composition, not informal notation). The n=0 or n=1 law is identity; avoid positivity assumptions by treating those cases separately. No need for a descent-based exact TV formula to close this certificate.

### M5d. Final theorem, using existing telescope (do NOT unpark powConvTV first)

The current generic `powConvTV` is parked in `Gate6K1Direct.lean` (comments explicitly say so). Do not spend time on that before the headline. We already have `compList_telescope_nstep_le_n_times_d`, which takes arbitrary starts; the existing three-round proof is the template. Keep the ideal L fixed. `action_comp_eq_conv` and `action_run_tv_noise` (compiled in `Gate6K1Bridges.lean`) transfer the ideal TV residual from the reference deterministic deck to each d via its noise law. Apply the existing telescope with start `Dist.pointMass d`, corrected finite rounds and L, δ1. Use `Eq.subst` to transport named kernel/distribution equalities if `rw` unfolds large distributions. Triangle inequality gives q3+3δ1; `gate6_headline_bound`/`gate6_headline_lt_thousandth` is already proved. The final theorem quantifies `∀ d : Deck`, and the finite law must be the stable-sort pullback with 23 binary inverse-GSR shuffles per pile after each uniform 25/25 swap. Do not substitute a constant-output kernel, a pre-reset, or a fiber-uniform start. Once this works, convexity (`mixtureTV_le` plus `run_compPow`) extends to arbitrary μ, with no new mixing proof. If useful, separately certify the longer preliminary-local-reset protocol from the November 24 handoff; label the extra 50 pile riffles and do not mark the original goal complete on that basis.

**Acceptance M5:** an exported, verified unconditional three-round stable-sort/binary-riffle theorem from every deterministic start. The already compiled restricted result is preserved. Arbitrary μ extension is useful. Do not strengthen an old docstring instead of the theorem statement.

## M6. Arbitrary pile finite-GSR comparison (the rest of G6)

Use the same block-local gluing as M4. For a fixed position partition P of capacities n, local reordering is a family of independent permutations of the subtypes `↥(P i)`. Build its distribution without `Dist.ofFun` on the full deck. Choose a bijection `Fin(n i) ≃ ↥(P i)` once per pile (equal cardinality); transport pullbackLaw to the subtype. Define a product law recursively by one pile at a time via `distProductFinsupp` and glue the family (use a fixed list enumeration of indices, or Fin recursion `Fin.cons`; do not start with complicated dependent product Fintype inference). The ideal product uniform law acts freely and transitively on each allocation's deck fiber by `multiPile_equivFiber`. Thus perfect local action = `P ; U` for P the deck-to-allocation observation. Prove uniform orbit law by mapping uniform through the fiber equivalence, `GSR.map_bijective_uniformDist`, then identifying fiber uniform distribution via masses. The reset preserves allocation and uniform deck law. All of this is independent of concrete sizes.

For one pile i, local error is at most `choose(n_i,2)/a_i`. Tensor TV subadditivity by induction (`distProductFinsupp_tv_subadditive`), then deterministic pushforward contraction (`Gate6K1Direct.supportMapTV`), yields sum over piles. A legal fixed-pair k-position swap with any deterministic pairing of the selected subsets induces the allocation kernel of M3 (pullback of card choices through the current deck is a bijection); subsequent ideal local reset gives L = allocation-read ; Q ; lift. Thus ideal state after at least one round is uniform within each resulting allocation fiber. For a schedule of arbitrary legal fixed pairs and exchange sizes, the ideal terminal allocation law is precisely the scheduled allocation chain, with deterministic-start allocation as input. Use recovery/TV equality from `FiberLifting` and `OracleRefinement` only after reset. For finite local shuffles, use the generic per-row/schedule telescope (existing `TelescopeF5` or `ProtocolCertificate`), or prove a generic list-of-noise convolution inequality by abstracting each intermediate distribution. The resulting theorem is

```
TV(finite full-deck run, uniformDeck)
 ≤ TV(ideal allocation run, uniformAlloc) + Σ_{round,i} choose(n_i,2)/a_(round,i).
```

Require at least one full ideal reset in the reference schedule before using allocation/full-deck TV equality; an empty schedule is separate. `a=1` is identity shuffle with loose bound; zero-size piles have no labels/identity and zero error. This general comparison is the G6 deliverable, not a new numeric optimized protocol for every deck size.

## M7. Changing capacities (G7): a biregular relation replaces all factorial arithmetic

**New key insight:** uniform transfer between DIFFERENT allocation carriers is not symmetry and does not require their cardinalities to match. It is an incidence relation with constant outgoing degree and constant incoming degree. Counting edges once in each direction proves the correct transport theorem without any ratios of factorials.

Given feasible capacities n, distinct i,j, and `t ≤ n i`, transfer t cards uniformly selected from pile i to j. New capacities `n' i = n i - t`, `n' j = n j + t`, other unchanged; total N. The output has a different type `Allocation N p n'`. Define `TransferChoices A = (pile A i).powersetCard t` with its subtype; nonempty as in M3. New owner `if card ∈ U then j else A.val card`; prove pile accessor identities and capacity using disjointness and card_sdiff/union. Define row as uniform choices mapped through this update. The outgoing targets are distinct (U = old pile i minus new pile i). Every row has outgoing degree `d = choose(n_i,t)`. For a fixed target B, a source A is uniquely reconstructed by choosing t cards of B's pile j to put back in i; reverse choices are in bijection with incoming sources. Incoming degree `e = choose(n_j+t,t)`. This works including t=0 and empty destination; no inverse choice on an impossible target.

Let R(A,B) mean some legal choice leads from A to B, X=old allocation type, Y=new allocation type. Count the same edges twice:

```
|X| d = |Y| e.
K(A,B) = if R(A,B) then 1/d else 0.
Σ_A K(A,B) = e/d = |X|/|Y|.
(Uniform_X K)(B) = (1/|X|) * e/d = 1/|Y|.
```

The supplied `UniformTransportSeeds.lean` contains the generic `biregular_count` and `uniform_transport_of_colsum` candidates. Compile and promote them, then the only substantive proof is the reverse-choice bijection. Derive positive d,e, positive carrier sizes from `nonemptyOfSumCapacities`, then Nat edge count -> Rat, `field_simp` once. Use the finite-filter/card form of GSR map mass, not a sum over ordered decks. You can also obtain the reverse conditional law: given B, the previous source A is uniform among e reverse choices. For a single-card transfer t=1 this is especially easy, and multiple transfers compose. A uniformly randomized draw from a uniform pile allocation, or deal to a new empty pile, preserves the correct uniform law on the new allocation carrier. A choice depending on card category generally does not; do not state uniform transport for adversarial discard selection. For ordered draws, use a perfect local reset or an already-uniform ordered deck; top-card draw from arbitrary ordering is not a uniformly sampled identity.

Show a concrete 3+ pile schedule, e.g. draw pile + hand + discard with capacities (4,0,0) on N=4; transfer two to hand then one uniformly to discard. Final capacities (2,1,1) and all `4!/(2!1!1!)=12` allocations uniform if initial law is uniform and choices uniform. If conditioning on observed dealt cards, residual cards are uniform on the restricted identity set, not all initial cards. For arbitrary initial error, TV contraction under each heterogeneous kernel applies without needing the same type for both ends. This gives practical guarantees for draw/deal/recycle operations with explicit assumptions. Generalize t transfers first; dynamic game policies can be composed from these, not a prerequisite.

**Acceptance G7:** a compiled `FiniteKernel (Allocation N p n) (Allocation N p n')`, exact capacities, normalized uniform-choice law, uniform transport theorem, plus the 3-pile example and TV contraction. If the original roadmap requires full ordered dealing, implement it by taking a uniformly ordered deck and reading successive position blocks, then applying the same fiber-counting theorem. Distinguish membership from order.

## M8. Quantitative mixing and cost (G8): a single proof for full decks and all quotients

The November 25 adjacent-transposition coupling is still useful and correct for the uniform ordered-card-pair-with-replacement kernel. The overnight agent did not implement it. There is an even more reusable way to formulate it: prove the theorem on the full permutation space (symbolic N), then project it to arbitrary allocations and histograms. This saves a separate connectivity and coupling proof for each quotient. No sharp spectral theorem is required for the core campaign.

### M8a. Uniform random position swaps, possibly interleaved with arbitrary local random permutations

Let K select `(a,b)` uniformly in `Fin N × Fin N` and apply the transposition of positions to the current deck, including a=b no-ops. It is a state-independent random position permutation, so uniform decks are stationary: every fixed permutation acts bijectively; a mixture of such actions also preserves uniform. Establish this generic theorem once using `GSR.map_bijective_uniformDist`, `FiniteKernel.apply`, and `map_map`/`join`; or use symmetry for the transposition kernel. The allocation observation after swapping positions a,b is exactly `swapPiles A (d a) (d b)` (or appropriate inverse accessor for the chosen deck convention). Since d is bijective, `(a,b)↦(d a,d b)` preserves uniform pairs. `uniformMap_reparam` from `PairFactorSeeds` gives the actual commuting square. This transfers full-deck results to the already-built allocation and histogram chains via M1, with no loss in TV. It also makes physical meaning explicit.

The coupling: two adjacent decks differ by one position transposition `(u,v)`, u≠v. Couple uniform ordered pairs z and φ(z), where φ exchanges `(u,v)` with `(u,u)` and `(v,u)` with `(v,v)`, fixes all other pairs. These are four distinct ordered pairs. On these four outcomes the two decks become equal (one applies the differing transposition and the other identity). Else both apply the same transposition; conjugation shows the resulting decks are still adjacent (possibly equal). This works whether the differing transposition acts on positions or identities provided the conjugation witness is oriented consistently. Do the proof pointwise on permutation application. `MultiExchange.conjugate_transposition`, `cardTransposition_involution`, `transposition_apply` are available. Establish `swap a a = id` and `swap a b = swap b a` as small lemmas. If the round also applies any state-independent random local permutation to both decks, use the SAME extra permutation in the coupling. Equality remains equality, and adjacency is preserved by conjugation. Thus the argument works for a fixed nonhomogeneous sequence of additional local shuffles, including finite GSR, without a collision budget for this particular unrestricted-transposition mixing theorem. Do not apply this conclusion to fixed-pair k-swaps without a new coupling.

Let rho=1-4/N² for N≥2. Use `PairedMixtureSeeds.lean` to establish the generic `pairedMixtureTV` inequality. The four coalescing outcomes contribute 0; other outcomes have adjacent-state TV after remaining t rounds at most rho^t by induction. Average exactly `(N²-4)/N² * rho^t`. Include optional extra local permutation law as another shared product random variable: sum over it using total mass one; no dependence on its distribution. The t=0 base TV≤1. Use `Finset.card` of the four-pair set, `Finset.sum_filter`, and simple rational multiplication. Avoid evaluating permutation support. This proves TV between adjacent point-start runs ≤rho^t. The induction can first be homogeneous with no extra local shuffles; extend to list of extra noise laws by induction on the list once the base theorem is compiled.

For arbitrary decks, repair the permutation using mismatches: if d(a)≠e(a), find b=d.symm(e(a)) (b≠a); b was also mismatched since e injective. Swap positions a,b, fixing a and preserving all already-correct positions. Mismatch count strictly decreases, and exactly one mismatch is impossible for bijections. Strong induction + TV triangle yields `(N-1)*rho^t` for any two initial decks. This does not need graph path or Wasserstein definitions. For a simple first proof use N rather than N-1; the exact bound with N-1 follows by the no-single-mismatch fact. Uniform is stationary; mix the second deterministic start over uniform and then the first start over arbitrary μ using the generic mixture inequality (or `mixtureTV_le` for a constant reference). Thus for every finite N≥2

```
TV(run of t uniform position transpositions from μ, uniformDeck)
 ≤ min(1, (N-1) * (1-4/N²)^t).
```

The same holds for projected allocation and histogram chains (stationary target is the corresponding pushforward) by TV contraction. N=0,1 are singleton cases. This gives an explicit finite-N bound of order N² log(N/epsilon), not the sharp random-transposition mixing time. For M8 acceptance use a concrete rational epsilon and t with an exact scalar inequality; no evaluation of N! states. E.g. N=4 gives rho=3/4, t=30 gives `3*(3/4)^30 < 1/1000`. N=99 with t sufficiently large is also certifiable by powers of rational numbers, although the bound is conservative. For fixed-pair exchange protocols, keep the stronger BL results where applicable and the generic G6 comparison theorem; do not conflate the kernels. If this full-deck formulation is harder to check, implement the allocation version from the November 25 guide first and use its already-described adjacency witness. Both are useful; do not stall G8 waiting for a sharp spectrum.

### M8b. Certified finite physical protocol and cost frontier

Use M6 for constrained schedules, M8a for the unrestricted transposition baseline, and M5 for the concrete 99-card example. A costed protocol specifies actual swap/selection operations, binary-riffle count per pile/round, and cost units. `Cost.lean`, `ProtocolCertificate.lean` already support the generic certificate. For fixed exchange schedule with ideal residual q, collision budget is `Σ w_i / 2^t_i`, where i ranges over round-pile slots and `w_i=choose(n_i,2)`. For integer cost per riffle=1, fix budget B and minimize this bound. The optimal allocation of B increments uses the largest available next marginal gain `w_i/2^(t_i+1)`, since gains are nonincreasing per slot. Prove by the exchange argument: if any selected last increment is smaller than an unselected available first increment, transfer one unit to improve; at greedy terminal state every chosen increment ≥ every unchosen one, so sum is maximal. With zero weights ties arbitrary. For unequal costs, do not claim greedy optimum; use bounded enumeration or DP on scalar budget states. A simpler FIRST certified frontier is finite enumeration of all t-vectors with total≤B for a small fixed schedule, proof via Finset.min' and witness, no full-deck enumeration. The greedy theorem is a later improvement if needed. For each feasible protocol, produce an upper-bound certificate at epsilon and attach exact cost. Lower bound on true optimality requires a separate theorem (support size or observable test); report certified-bound optimum separately from actual TV optimum. Do not claim a universal physical optimum based only on an upper bound. Keep G9 optional.

**Acceptance G8:** at least one quantified finite-N nontrivial mixing theorem for a specified physical operation, general fixed-pile finite-GSR comparison, explicit finite protocol/cost/epsilon certificate with correct initial-law assumptions, and a bounded certified cost frontier. The scope of allowed operations must be explicit. The roadmap asks for cost optimization, not resolution of an unrestricted open problem. Do not turn optional descent/eigenvalue refinements into blockers.

## Finish checklist and switching criterion

| Check | Required actual artifact |
|---|---|
| M1 | General normalized histogram transposition kernel; stationary pushforward + commuting square + run projection, imported and verified |
| M2 | Reversible quotient and uniform-fiber lift, applied to M1 |
| M3 | Legal fixed-pair k allocation kernel; profile pushforward and actual quotient, BL specialization |
| M4 | General feasible histogram realization + factorial stationary mass, 3-pile example |
| M5 | Correct pullback stable-sort binary-GSR certificate, 3 rounds, TV < 1/1000 from every deterministic 99-card deck |
| M6 | General multi-pile finite-GSR schedule comparison with stated initial-law/round assumptions |
| M7 | Changing capacities uniform transport + concrete deal/draw/discard example |
| M8 | Finite-N convergence theorem and meaningful certified cost frontier |

G0–G4 existing infrastructure should be verified and its theorem inventory reconciled, not redeveloped. Treat historical reviews as evidence and suggestions, not goals. Once each check has a real exported theorem and normal verification, the core campaign through G8 is complete; optional G9 spectral/optimality research remains separately documented.

Operator/model assessment: first compare performance on M1 (small generic theorem and short assembly), not another long combinatorial task. If Inkling repeatedly detours into two-color calculations or cannot integrate the already-supplied lemmas after bounded attempts, use Qwen on the SAME open interface with the SAME code and limits. Do not throw away compiled work or assume the change of model will solve a representation problem. Record exact failing declaration, focused build timings, and acceptance gates closed. Both models should use the mathematics above rather than rediscover the plan.
