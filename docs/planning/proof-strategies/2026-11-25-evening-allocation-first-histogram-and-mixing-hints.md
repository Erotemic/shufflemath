# Executable mathematical handoff: allocation-first histogram kernels and finite-N mixing

2026-11-25 evening; based on `3d25fc8`. Applies to Inkling2 or any successor. Companion review: `../reviews/2026-11-25-evening-inkling-proof-direction-review.md`.

## 0. Read this first: a short execution plan

Your objective is the actionable arbitrary finite-deck roadmap through G8, not a new pile of specialized scalar identities. The existing two-color histogram work is useful, but do not independently prove the same Bernoulli–Laplace mathematics twice. The existing allocation kernel is already a probability law for arbitrary capacities and any number of piles. Derive the histogram law from it. Complete one vertical slice (actual kernel + lumpability + stationary distribution + example) before growing the next abstraction.

1. If finishing the current two-color branch, do A1–A4 below (BL transport). Two bounded failed attempts on the same representation -> record the exact error and proceed to B. Do not spend a session reproving Vandermonde or stationarity. The general kernel can land independently.
2. B1–B5: normalized unrestricted-transposition histogram kernel, signed histogram update, exact pair-cell law, quotient theorem, weighted detailed balance. Compile `dev/inkling-hints/2026-11-25-evening/PairFactorSeeds.lean` and reuse `dev/qwen-hints/2026-11-25-morning/QuotientSeeds.lean`. These are candidate code, not tested Lean declarations. Integrate successful parts into canonical modules with minimal imports.
3. C1–C4: labeled-slots counting and realizability. Obtain the arbitrary-pile/category stationary law. No direct factorial summation needed.
4. D1–D4: actual pairwise k-subset exchanges, profile formula, microscopic equivalence, two-color specialization. Do not conflate this with unrestricted transpositions.
5. E: close outstanding deterministic-start and GSR orientation/iteration scope, then generic multi-pile GSR lift. F: G7 and G8, including a new elementary mixing proof. F is not a dependency of B–D.

For each numbered task: choose a declaration, state its precise hypotheses, compile a small module, integrate it and update the manifest. The proof sketches and source names below are guidance; inspect `#check` for one or two needed signatures in a scratch file, not in a default build. Use `lake build Shufflemath.FiniteDeck.<Module>` and `lake env lean <scratch>`; keep time/RSS bounded. Do not raise recursion or heartbeat limits repeatedly. If an imported concrete `Dist` causes WHNF blowup, prove the equality over abstract types, pass distributions as parameters, and specialize via an opaque theorem. Do not globally unfold `Fintype` or use a computation over `N!` or all owner functions. Do not add proof audit scans to normal builds (see AGENTS). Do not edit other agents' work or use worktrees.

## A. Salvage and close the current specialized histogram branch without re-proving BL

### A1. Exact finite-state equivalence

Source: `HistogramFiber.lean` (`Hist2 N`, `validHistSet`, `validHistPi`, `histogramTransition`), `BernoulliLaplaceGeneral.lean` (`BLState`, `blLo`, `blHi`, `transitionNumerator`, `transitionWeight`, `blExchangeKernel`, `blStationaryDist`). Use `p : BernoulliLaplaceGeneral.ExchangeAdmissible` initially: all hypotheses needed for existing laws are encoded there. Write `N=p.N`, `m=p.m`, `r=p.r`, `k=p.k` in this section.

Let `V := ↥(validHistSet N m r (N-r))`. Define

```
noncomputable def validHistEquivBL (p : ExchangeAdmissible) :
    ↥(validHistSet p.N p.m p.r (p.N - p.r)) ≃ BLState p.N p.m p.r := ...
```

Forward: `X ↦ ⟨(X.val 0).val, ...⟩`. From `Finset.mem_filter.mp X.property` extract `x0+x1=m`, `x0≤r`, `x1≤N-r`. Thus `x0≤min m r` and `m-(N-r)≤x0`. Rewrite the lower and upper bounds by `blLo_eq_tsub` (actual RHS `r-(N-m)`) and `blHi_def`; use `omega` with `m≤N`, `r≤N`. Check exact hypothesis field names in `ExchangeAdmissible` (do not invent duplicate admissibility). Inverse: `x ↦ ![⟨x.val, ...⟩, ⟨m-x.val, ...⟩]`. Bound both by N, use `omega` on extracted BL bounds and `m≤N`. For inverse proofs `Subtype.ext`, `funext i`, `fin_cases i`, `Fin.ext`, `omega`. This is exactly the two-dimensional coordinate reduction already implicit in the proof of `validHistPi_mass`, not a fresh counting theorem.

### A2. Collapse the double sum into the existing single sum

Let `x = X 0`, `y = Y 0`. In the current `histogramTransition` definition, `a,b` range over `Finset.antidiagonal k`. Replace each by `(u,k-u)` and `(v,k-v)` using `Finset.Nat.antidiagonal_eq_image` and `Finset.sum_image` with injectivity of the first component, as in the landed `validHistPi_mass`. Pull the fixed rational denominator outside both sums; prove the integer numerator identity first.

For fixed `u`, the contribution is

```
choose x u * choose (m-x) (k-u) * choose (r-x) v *
choose ((N-m)-(r-x)) (k-v)
```

if BOTH histogram coordinates of Y agree. The last population equality follows from `x≤r`, `m-x≤N-r`, `r≤N` and the row totals (`omega`). Before solving for `v`, split on `u≤x ∧ k-u≤m-x`. If false, one of the first two choose factors vanishes (`Nat.choose_eq_zero_of_lt`); both target sums contribute zero. For a candidate `v` outside `v≤r-x ∧ k-v≤(N-m)-(r-x)` the last two factors vanish likewise. This is the critical saturation guard: it is NOT valid to freely cancel Nat subtraction on inadmissible selections.

For valid profiles, the first-coordinate equation determines `v` uniquely: if `x-u≤y`, then `v=y-(x-u)`; otherwise no solution. The candidate must also satisfy `v≤k`. The second-coordinate equality then follows from the row totals (and `k-u≤m-x`) by `omega`. More explicitly `(m-x)-(k-u)+(k-v)=m-(x-u+v)=m-y`, with all subtractions supported by those hypotheses. You do not need extra inequalities for an invalid candidate: its choose product vanishes. Use `Finset.sum_eq_single` in the inner sum, and the outside-range condition when the candidate is absent. Split on `x-u≤y` and `y-(x-u)≤k`. The result matches `transitionNumerator` literally. Prove one helper `profileTerm_eq_choose` under valid row bounds; one helper `innerProfileSum_eq` for fixed `u`; then `Finset.sum_congr` for the outer sum. Only cast the resulting Nat equality and divide once.

Target:

```
-- schematic; X,Y are elements of V, e = validHistEquivBL p
histogramTransition p.N p.m p.r (p.N-p.r) p.k X.val Y.val =
  transitionWeight p.N p.m p.r p.k (e X).val (e Y).val
```

Do not use `Finset.sum_eq_single` before killing invalid profile factors. Do not prove a new Vandermonde identity. Validate the statement on N=4,m=r=2,k=1 and a boundary state where u>x. See existing `transitionNumerator` lines 182–198 for the precise condition branches.

### A3. Transfer the *actual* distribution and stationarity

Define `K_V X := (blExchangeKernel p (e X)).map e.symm`. Define `pi_V := (blStationaryDist p).map e.symm`. These are already normalized. The actual `Dist.mass (K_V X) Y` equals `histogramTransition ... X.val Y.val` by the mass theorem for a bijective pushforward (use `Finsupp.mapDomain_apply_of_injective` in a small abstract helper; avoid unfolding BL types). Read `blExchangeKernel` for the exact existing mass lemma; use `Dist.mass_ofFun` if necessary. The corresponding mass of `pi_V` equals `validHistPi`; existing `deckFiber_prob_eq_blStationary` and `mass_blStationaryDist` supply the equality, or unfold only `blStationary` and rewrite x1=m-x0. Then `blDetailedBalance` transfers immediately to `DetailedBalance pi_V K_V`. Apply `detailedBalance_implies_stationary` and distribution extensionality. The old scalar identities are corollaries. No new Fubini over the specialized histogram state space.

### A4. Be honest about coverage

The above is for `ExchangeAdmissible` (positive interior split and positive legal k). For k=0, prove identity directly or define the physical kernel from empty subset choices. For m=0 or m=N, the allocation space is a singleton and legal k=0. Do not force those into the positive-exchange BL theorem. A two-color scalar law does not close G5. If the BL bridge becomes expensive, return later after the generic physical kernel in D. Its histogram equality will give another route via the already-proved `BLRefinement` count law.

## B. General histogram kernels by factoring the random experiment (NEW, high priority)

### B1. Canonical observation and finite carrier

`Allocation N p n` is a subtype of owner functions `Fin N → Fin p`. Let `color : Fin N → Fin c`. Define

```
cell A x := (A.val x, color x)
H A z := (Finset.univ.filter (fun x => cell A x = z)).card
```

Use `Fin p × Fin c` as the cell index, not two separate dependent indices everywhere. `H A (i,j)` is the existing `lump` of `(univ.filter (fun x => A.val x=i))` and `color`; one extensionality lemma using `Finset.mem_filter` establishes the equality. This gives row/column total theorems without duplicating them. Each count ≤ N (`Finset.card_le_card` against univ). Build `boundedHist A : (Fin p × Fin c) → Fin (N+1)` by that bound. Use `ReachableHist := {h : ((Fin p × Fin c) → Fin (N+1)) // ∃ A : Allocation N p n, boundedHist A=h}` (a finite subtype, explicit `Fintype.subtype` if needed). The observation `obs A := ⟨boundedHist A, ⟨A,rfl⟩⟩` is surjective by definition. No need to prove every margin-feasible histogram is realizable until C. Avoid `Nat` as a codomain of a theorem requiring `[Fintype]`. All probability maps themselves are Fintype-free.

### B2. Elementary update in signed coordinates (the key proof)

Let `u=cell A a=(i,s)`, `v=cell A b=(j,t)`. For a swap of two named cards, use signed values in `Int`, not sequential subtraction in `Nat`:

```
H'(z) = H(z) - 1[z=u] - 1[z=v] + 1[z=(j,s)] + 1[z=(i,t)]
```

Prove `signedHist_swap_update` with the precise `hstep` signature in `PairFactorSeeds.lean`. The only work is a small finite-sum lemma, NOT a combinatorial orbit proof.

1. `signedHist color A z = ∑ x : Fin N, unitCell z (ownerCell color A x)` by `Finset.sum_filter` (card is sum of ones); orient equality of cell indices as needed. Prove generically with a `Finset` and predicate if the concrete rewrite is difficult.
2. For `a=b`, `swapOwner A a a = A.val` by `funext` and `by_cases x=a; simp [swapOwner,*]`. All four signed unit terms cancel (`ring`).
3. For `a≠b`, let `S=(Finset.univ.erase a).erase b`. Prove abstractly for any `f : Fin N → Int`, `∑ x, f x = ∑ x ∈ S, f x + f b + f a`. Use `Finset.sum_erase_add` twice with the appropriate membership proofs (`mem_univ`, `mem_erase`). Check the Mathlib signature locally. Alternatively use `univ = insert a (insert b S)` and `Finset.sum_insert`; establish the set equality by `ext x; by_cases x=a; by_cases x=b; simp [S,*]`.
4. For `x∈S`, prove `x≠a`, `x≠b` from `mem_erase`; `simp [ownerCell, swapPiles, swapOwner, *]` yields unchanged cells. At a and b, `simp [ownerCell, swapPiles, swapOwner, hab, Ne.symm hab]` gives `(j,s)` and `(i,t)`. Avoid unfolding capacity proofs: prove the owner accessor equation `((swapPiles A a b).val x) = swapOwner A a b x` by `rfl` once.
5. Rewrite both sums using step 3, cancel the equal S-sums using `Finset.sum_congr`, then `ring`. This proves the signed formula for every z; `funext z` closes. In the supplied seed the update lemma is an explicit hypothesis, NOT already proved. No Fintype on the whole allocation space participates.

If the signed sum proof fails twice, use the previous `CellRelabelSeeds.lean` and the full input equivariance in B3 (alternative): cell bijections glue into a color-preserving relabel; the equivariance transports the swap law; the observation is invariant under that relabel. Do NOT write a third standalone cell permutation construction.

### B3. The probability law of the cell pair (no orbit argument needed)

`swapKernel hN A` samples ordered pairs uniformly from `Fin N × Fin N`, with replacement. For any cells u,v, the set of pairs with these observed cells equals the Cartesian product of the two cell fibers. Its cardinality is H(u)*H(v). Therefore the law has mass H(u)H(v)/N².

`PairFactorSeeds.lean` supplies `uniformMap_mass_card`, `pairFiber_card`, `uniformPairMap_eq_of_counts`, `uniformPair_factor`, and `signedHist_lumpable_of_update`. They are proposed uncompiled code. Compile the first four independently. If the uniform-mass rewrite fails, explicitly use a filtered univ with `y=f x`, `Finset.sum_const`, and a filter equality by extensionality; never unfold `GSR.uniformDist`. If the product-fiber proof fails, prove membership in both sides iff `f a=z.1 ∧ f b=z.2` by `Prod.mk.inj`/`Prod.ext` and `Finset.mem_product`. These are small local fixes.

For A,B with equal H, the cell pair distributions are equal. B2 says the same deterministic update is applied to that pair distribution. Thus `(swapKernel hN A).map (signedHist color) = (swapKernel hN B).map (signedHist color)` by `StdSimplex.map_map`. The signed observation of `ReachableHist` (convert each bounded Fin value to Int) is injective: `Subtype.ext`, `funext z`, `Fin.ext`, injectivity of `Int.ofNat`. Transfer the equality back through this injection. An abstract `map_injective_cancel` can be proved by `Finsupp.mapDomain_apply_of_injective` or by choosing a left inverse (if the source is inhabited) and applying `congrArg (fun mu => mu.map leftInverse)`; `StdSimplex.map_map` plus `map_id` cancels it. Reuse existing bijection/injectivity lemmas where available. Do not try to equip `Int` functions with a Fintype.

The result is the exact strong lumpability equality

```
∀ A B, obs A = obs B →
    (swapKernel hN A).map obs = (swapKernel hN B).map obs
```

Alternative / independently useful: fix `swapKernel_equivariant`'s incomplete scope. `PairFactorSeeds.lean` has `swapPiles_relabel` and `swapKernel_relabel`: from `relabel_commute_owner` and `swapOwner_eq_cardTransposition`, get equality of allocations; reparametrize uniform ordered pairs via `Equiv.prodCongr σ σ`. The already-proved `GSR.map_bijective_uniformDist` does all distribution reindexing. This is a stronger, genuine equivariance statement. It also gives a short alternate proof of lumpability using cell gluing. Don't prove two routes unless the alternative solves a different downstream problem.

### B4. Construct the normalized quotient, then transport stationarity

Reuse the existing *candidate* `dev/qwen-hints/2026-11-25-morning/QuotientSeeds.lean` in the snapshot, not a fresh copy. `quotientRows`, `quotientRows_at`, `quotientRows_intertwines`, `stationary_pushforward`, and `reversible_quotient` give the interfaces. Compile and migrate the needed declarations. At `f=obs`, `K=swapKernel hN`, set `Q := quotientRows obs obs_surjective K`; no manual normalization. Prove the microscopic stationary distribution equality using extensionality and `swapKernel_uniformStationary hN hsum`. Then `stationary_pushforward` gives `Stationary ((uniformAlloc hsum).map obs) Q`. For detailed balance use `swapKernel_symmetric`, the constant uniform mass, and `reversible_quotient`. The hQ orientation in that candidate is `(K x).map f = Q (f x)`; use `(quotientRows_at ... x).symm`.

For the explicit scalar transition formula, the mass at Y is the sum over **all ordered cell pairs u,v** of `H(u)H(v)/N²` times `1[step_H(u,v)=Y]`, in signed coordinates. This works even when the signed step for an impossible pair is not a reachable histogram (zero coefficient). Do not define a partial `Q` by invalid indices. Prove the formula on a true row by pushforward and the already-established factorization. For N=0 define identity separately (only the empty allocation). N=1 also gives identity. Zero categories/piles with a nonempty deck are impossible when an actual color/owner map exists.

### B5. A general result you get nearly for free: uniform-fiber lift intertwining

Let μ be uniform on allocations, and `U = FiberDisintegration.fiberLaw obs obs_surjective`. For a reversible strongly lumpable kernel, the reverse-row argument gives for all h,z and microscopic y in F_z:

```
mass(apply (U h) K, y) = Q(z,h)/|F_h| = Q(h,z)/|F_z|.
```

Proof: `FiberDisintegration.fiberLaw_mass` -> sum over x in F_h of K(x,y)/|F_h| -> symmetry -> Q(z,h)/|F_h| by lumpability. Weighted detailed balance yields the last equality because the stationary marginal is |F_h|/|Allocation|. All denominators positive by surjectivity. For RHS `(apply (Q h) U)` only one fiber contributes. This gives the full kernel equality `comp U K = comp Q U`. It is stronger than stationarity, and yields exact full-allocation TV identity for fiber-uniform starts using existing fiber recovery and TV contraction. The proof is generic; use it for both the one-card and k-subset kernels. A nonuniform reversible microscopic law needs its conditional law, not the uniform lift; stay with uniform for the first implementation.

B done means a genuine `FiniteKernel` on reachable histograms, the actual observation intertwines, the pushforward stationary law, weighted detailed balance, and a compiled three-pile/two-category example. Not just an array of rational numbers. Do not require C's closed-form count to close B.

## C. Labeled slots: realizability and arbitrary histogram fiber counts with one equivalence

This is a more direct route than orbit-stabilizer. It does not require proving that the color-preserving permutations form a subgroup or formalizing its quotient. It also proves the missing realizability theorem.

### C1. The slot bijections that make every valid margin table realizable

Fix a table `X : Fin p × Fin c → Nat` of nonnegative counts with row sums `n i` and column sums `r j := card {x // color x=j}`. Use these types:

```
ColorSlots j := Σ i : Fin p, Fin (X (i,j))
ColorCards j := {x : Fin N // color x=j}
CellSlots i j := Fin (X (i,j))
```

By `Fintype.card_sigma`, `Fintype.card_fin`, and the column sums, `card (ColorSlots j) = card (ColorCards j) = r j`. Hence there exists a bijection `e_j : ColorSlots j ≃ ColorCards j` (`Fintype.equivOfCardEq`). This works when r_j=0: equivalences between empty types are inhabited; do not demand nonempty cells. Choose one for each j, or use an arbitrary family `e : ∀ j, ColorSlots j ≃ ColorCards j` as a parameter. Define an allocation owner by looking up the slot assigned to each card:

```
owner_e x := ((e (color x)).symm ⟨x,rfl⟩).1
```

Prove the following lemma first, at a single fixed cell: `Fin (X(i,j)) ≃ {x : Fin N // owner_e x=i ∧ color x=j}`. Forward sends s to `(e j ⟨i,s⟩).val`; its category property follows from subtype membership, owner property from `Equiv.symm_apply_apply`. Inverse is the slot index of `e j` inverse applied to `x`, after the owner equality gives the dependent pile-index cast. To avoid fragile casts, first prove a bijection between the Sigma fiber `{s : ColorSlots j // s.1=i}` and the cell; then build its equivalence with `Fin (X(i,j))` by `subst` on the first component. Keep these two small equivalences separate. Use `Subtype.ext`, `Sigma.ext` or case-splitting on the index proof; do not use large `aesop` over all cells.

Count by `Fintype.card_congr` and `Fintype.card_subtype`. Sum over j using the existing `lump_pileTotal` (or disjoint partition of each owner fiber by color). The row sums show `owner_e` satisfies `pAlloc n`. Therefore `A_e : Allocation N p n` exists and realizes X. This proves reachable = margin-valid. No network flow theorem and no induction on the entries are needed: there are no extra constraints on a card's pile assignment beyond the margins.

### C2. Count all labeled slot fillings, and then their fibers

Define `Fill := ∀ j : Fin c, ColorSlots j ≃ ColorCards j`. For any finite types S,T with equal cardinality r, the equivalences `S ≃ T` are in bijection with permutations of `S` by composing with one chosen reference equivalence. Their cardinality is r!, including r=0. Reuse the proof pattern in `MultiPileFiber.equivFiberCard`. Thus `card Fill = ∏ j, (r j)!` via `Fintype.card_pi`. Avoid enumerating fillings in a computation. If necessary state the generic theorem with explicit Fintype instances on function/equiv types and use a small separate card lemma.

The map `fillToAlloc : Fill → {A : Allocation N p n // H A=X}` is exactly C1. For a fixed A, define `CellCards A i j := {x // A.val x=i ∧ color x=j}`. The fiber of this map is equivalent to

```
∀ ij : Fin p × Fin c, Fin (X ij) ≃ CellCards A ij.1 ij.2.
```

Forward: restrict each `e_j` to its slots of pile i (the fact `fillToAlloc e=A` ensures the range lies in that cell). Inverse: combine the cell bijections into `e_j` by gluing a Sigma family; each `ColorCards j` has unique owner given by `A.val`, so its cell subtypes partition it. Use `partitionSigmaEquiv` or construct the inverse directly by reading owner. Verify the round trips at individual `j`, `⟨i,s⟩`, and individual cards, not by comparing Fintype enumeration. `funext`, `Equiv.ext`, `Subtype.ext` are the only extensionality principles needed. The known equality `H A=X` ensures every cell equivalence exists. The fiber cardinality is `∏ ij, (X ij)!`, independent of A.

Now use `Fill ≃ Σ A, {e : Fill // fillToAlloc e = A}` (general fiber partition equivalence; a direct `Equiv` is `e ↦ ⟨fillToAlloc e,⟨e,rfl⟩⟩`, inverse forgets the witness). `Fintype.card_sigma`, constant fiber size, and `Fintype.card_pi` yield the **division-free** identity

```
card {A : Allocation N p n // H A=X} * ∏ ij, (X ij)! = ∏ j, (r j)!.
```

This is the desired theorem. Positivity of factorials lets you divide in Rat after the identity, without Nat quotient/divisibility bureaucracy. Do not replace it with a claim about the number of ordered decks; the carrier here is named-card allocation, not pile ordering.

### C3. The total allocation count is a special case of the same proof

Use a single color (all N cards) and the table `X (i,0)=n i`. Then the result of C2 becomes `card Allocation * ∏ i,n_i! = N!`; the histogram fiber is the entire allocation carrier. Alternatively take a fixed positional partition from `BlockPartition` and map all full deck bijections to allocations. Every allocation fiber has cardinality `∏ n_i!` by `multiPile_card`. Both proofs are the same labeled slots idea; do only one and prove the other as a corollary if useful. `N=0` yields factorial 0 = 1. Empty products must be 1.

### C4. Stationary weights and deck-level result

The stationary distribution in B4 is the pushforward of uniform allocations. Its mass at X is the fiber cardinality divided by total allocation cardinality, by `uniformMap_mass_card`. Substitute the two Nat identities after `exact_mod_cast` and use nonzero factorials to cancel. This yields

```
π(X) = (∏ i,n_i!) * (∏ j,r_j!) / (N! * ∏ ij,X_ij!).
```

Normalization is inherited from `Dist`; weighted detailed balance inherited from the quotient. For ordered decks, each allocation carries `∏ i,n_i!` decks (existing `multiPile_card`), so its uniform marginal is uniform allocations. The same histogram probability follows. Generalize to any finite pile and category index types later if needed; `Fin p × Fin c` is sufficient for the current `FiniteDeck` modules. No Commander constants.

Concrete acceptance: prove the formula for arbitrary reachable tables and show every table satisfying margins is reachable. Cross-check `ThreePileTwoColor.lean` (N=6,p=3, capacities 2,2,2, category sizes 3,3). The table with one card of each color per pile has 36 named-card allocations out of 90; π=2/5. For an actual transition choose `X=((2,0),(1,1),(0,2))`, exchange one between pile 0 and 2 to reach all-ones Y. The fixed-pair transition is 1, reverse 1/4; π(X)=1/10, π(Y)=2/5, both flows 1/10. The unrestricted transposition row multiplies these off-diagonal entries by 2*2*2/36=2/9. This example checks that you didn't silently conflate the kernels.

## D. Fixed-pile k-subset exchanges: construct from choices and reuse the same quotient

### D1. Define the actual kernel, not a weight table

For allocation A and distinct piles i,j with `k ≤ n i` and `k ≤ n j`, let `Pile A i := univ.filter (fun x => A.val x=i)`. Let `Choices A i j k := ↥((Pile A i).powersetCard k) × ↥((Pile A j).powersetCard k)`. The cardinality is `C=choose(n i,k)*choose(n j,k)` by `Allocation.pileCard`, `Finset.card_powersetCard`, and `Fintype.card_prod`. Positivity is immediate from legality, including k=0. Construct a `Nonempty` witness once from positive card. An equivalent representation with `Fin k` ordered picks is not necessary.

For a pair `(U,V)` assign owner j to cards in U, owner i to cards in V, leave others. Because U⊆Pile i and V⊆Pile j with distinct owners, the sets are disjoint; each pile loses and gains k. Prove `pAlloc n` for the updated owner using explicit equalities for the three cases of the pile being observed: `Pile' i=(Pile i\U)∪V`, `Pile' j=(Pile j\V)∪U`, and others unchanged. Those follow directly from `Finset.ext` and owner membership. Use `exchangePair` and `exchangePair_involution` in `MultiPileExchange.lean` for the already-developed set algebra. Define `pairExchangeKernel A := (uniformDist (Choices A i j k)).map updateAllocation`. This is a true `Dist`. Even k=0 is now uniformly the identity (one choice). No summation identity is required to construct it.

### D2. Reversal and microscopic uniform stationarity

The sample space of all directed exchange experiments is a dependent sum

```
Ω := Σ A : Allocation N p n, Choices A i j k.
```

Each A has exactly C choices. The inverse experiment is `(A,U,V) ↦ (A',V,U)` (after updating, the old incoming set V is in pile i and U is in j). This is an involution, including k=0, by the set identities of D1. It is a bijection of Ω. Project each experiment to its pair of endpoints. The involution reverses those endpoints. Therefore the pushforward of the uniform law on Ω is symmetric as a joint distribution on endpoints. Its mass at `(A,B)` is `1/|Allocation| * K(A,B)`. This proves detailed balance with uniform A. Since the choice fiber size is constant, there is also a simpler row-wise proof: for fixed A,B the experiment fiber `{(U,V) // update A U V=B}` is bijective to the reverse row's fiber using `(V,U)`, and both denominators equal C. Use `uniformMap_mass_card` and `Fintype.card_congr` on those fiber equivalences; choose the row-wise route if it is shorter in Lean. No need for `exchangeTargets_symmetric` to be lifted through unrelated scalar sums.

Note this proof generalizes to uniform choices of more complex reversible moves provided the number of choices at each A is constant. If that number is not constant the natural reversible law is proportional to the number of outgoing choices, not necessarily uniform. This is a useful future graph/constraint extension; do not claim uniform stationarity without checking constant degree or other balance conditions.

### D3. Category selection law by a powerset factorization

For one pile P and a valid category profile a with `∑ c,a c=k`, `a c≤H c`, the fiber of `powersetCard k P` with profile a is equivalent to `∀ c, ↥((P.filter (fun x => color x=c)).powersetCard (a c))`. Forward maps a chosen subset S to its category filters. Inverse takes their disjoint union. Show union is inside P and has card `∑ a c=k` by `Finset.card_biUnion`; show the filters of the union recover the selections by unique category. Use the general partition interfaces, and the existing `FinsetFiberCount.sFiber_choose`/`Histograms.lumpedNum` for two-color specializations. `catAlloc` in `Histograms.lean` counts abstract `Fin (X c)`-subsets; connect the actual cell sets to these finite types by a bijection and pushforward on subsets rather than constructing a second independent enumeration.

The fiber count is `∏ c, choose(H c,a c)`. The profile law of a uniform k-subset is a distribution obtained by `.map profile`, not a manually normalized sum. Its mass is the displayed product / choose(n_i,k). Two independent choices give the product of those masses. For the output table, use simultaneous signed updates

```
X'_(i,c) = X_(i,c) - a_c + b_c
X'_(j,c) = X_(j,c) - b_c + a_c
```

and unchanged other rows. The valid profile inequalities ensure no negative values; use Int during proof to prevent accidental saturated subtraction. This is exactly the same factorization pattern as B2–B3. The distribution of the two profiles depends only on the starting histogram; hence strong lumpability. Reuse B4 and B5 to obtain weighted detailed balance and fiber-lift intertwining. Derive the existing `lumpedTransition` scalar formulas by reading the law's mass after summing profiles with the same resulting histogram. Its denominator is positive from legality, not an arbitrary definition of rational division at zero.

Alternative if the powerset equivalence stalls: use the already supplied color-preserving relabeling (`CellRelabelSeeds.lean`) to reparametrize uniform choices by applying the permutation to each chosen subset. `card_image_of_injective`, `image_sdiff`/`image_union`, and the pointwise update prove equivariance; the resulting histogram is unchanged by the relabel. This gets strong lumpability and stationarity *before* the scalar formula. Do not let the scalar formula block the actual kernel theorem.

### D4. Bridge unrestricted transpositions, fixed-pair swaps, and Bernoulli–Laplace

Under `swapKernel hN`, for i≠j the probability of choosing one card from each is `2*n i*n j/N²` (two ordered orientations), and conditional on that event the choices are uniform singleton selections. For i=j there is no change. Therefore the unrestricted allocation kernel is a mixture of identity (weight `∑ i,(n i)^2/N²`) and all unordered fixed-pair k=1 kernels with weights `2*n i*n j/N²`. Omit zero-capacity pairs or give them zero weight without constructing a nonexistent row. An even simpler implementation indexes by ordered pile pairs with weight `n_i n_j/N²` and treats i=j as identity. The choice-type Cartesian product bijection for each pair proves this, with the same `uniformMap_mass_card` helper. This makes the one-card general mixing result in F3 directly relevant to G5 while retaining the physical meaning of arbitrary k.

Specialize to p=2 and capacities m,N-m: use the first pile as membership, inverse reconstructs the owner from whether x∈S. The pairwise k kernel agrees with `FiniteDeck.subsetExchangeKernel` by the reachable-set mass or the exact image of `Choices`. Specialize to two colors and use the existing `BLRefinement` count kernel. This closes the physical/macro equivalence and supplies an independent path to A2. Avoid re-proving the already completed G3/G4 theorems.

## E. Gate 6 remains a real obligation (do not restart it)

The actual headline `g6_threeRound_headline` starts from `g6ThreeRoundStart` (fiber-uniform), not an arbitrary deterministic deck. The source still builds `rhoRoundFinite` using `PermutationLaw.gsrPermutationLaw` directly (see `GSRPermutationLaw.lean`, especially `idealShuffle_canonical_eq_permLaw`). The correct position pullback law is its map under permutation inverse; the rank maps old position to new position whereas `FiniteDeck.act p d = p.trans d` reads old positions at p(new). Inversion is a bijection and preserves uniform. `permInverseEquiv`, `perm_inverse_uniform`, and `perm_inverse_tv` are already compiled in `Gate6K1Bridges.lean`; use them directly. Transfer that estimate through the pile embedding; do not redo tie-rank probability. Use the previous November 25 hints and `dev/qwen-hints/2026-11-25/GenericClosure.lean` (already integrated in parts); also the morning `Gate6AssemblySeeds.lean` (not all integrated). Compile only the missing bridges.

Detailed reminder of the remaining short mathematical route:

* Row independence of `rawExchangeMembership`: if two decks have same membership S, each of their `exchangeChoice` maps into precisely the reachable target set (`newLeftCards_as_sdiff_union`, injective `newLeftCards_injective`, card of the reach set from `FiniteDeck.SubsetExchange`). Their injectivity and equal cardinalities to the reach set imply identical images and uniform pushforwards. Reuse the compiled `uniform_same_image` and `range_iff_mem_of_card_eq` in `Gate6K1Bridges.lean`, with `subsetExchangeCount` from `FiniteDeck/SubsetExchange.lean`. No new equal-image lemma is needed. An alternative is reparametrization of positions via the within-pile equivalence, exactly as in B3. Neither needs new inverse-choice counting or a full-deck enumeration. Establish equality of *membership rows* for all same-membership decks, not just equality of macro counts.
* Define row factor Q on memberships using `rowFactor` from morning seeds. Let P be deterministic membership projection, U=localLift, H=P;U, L=P;Q;U. `U;P=id` by `localLift_preserves_membership`, and `H;L=L` by associativity. Existing K1 and `g6_3round_idealKernel_eq_fullRound` identify L with the ideal action. `g6ThreeRoundFiniteKernel` despite its name equals L, not the finite riffle round. Use `run_from_reset_eq_point` and `same_fiber_law` from the morning seeds. For the segregated reference deck choose its marked-count endpoint fiber where the named membership is unique (check whether the convention uses 49 or 50 distinguished cards; use existing `commanderSegregatedState` and `project` definition, not an invented endpoint). Then the local reset of the reference deck equals `g6ThreeRoundStart`. The compiled `ideal_batch5b` already identifies the ideal local noise with `localLift (membership (Equiv.refl (Fin 99)))`; use it if the identity deck has the chosen segregated convention, after checking that membership/project fact. This gives the ideal q3 bound from the point mass.
* Transport the ideal q3 bound to every deterministic deck. Use the compiled `Gate6K1Bridges.lean` theorem `action_run_tv_noise` directly, together with `action_comp_eq_conv`. It already proves this for arbitrary N and any noise law. Underneath, `powConvRunEq` expresses a point-start run by pushforward of the same convolution law, and `tv_bijective_invariance` removes the starting deck. Do not reprove that result. Need no equality between finite runs from point and fiber-uniform starts. Apply the per-round discrepancy telescope to the actual point mass, independently for each d. Exact q3 + 3δ1 < 1/1000 already proved. Use the inverse local-law version of the bound; distinguish from the rank-law headline. If exact repeated binary-riffle identity is not yet established at permutation level, prove via injective encoding `p ↦ List.ofFn (fun i => p i)` (or use current canonical GSR list representation); stable sorting plus `GSR.idealShuffle_comp` gives composition with product alphabet. Check orientation with `act_composition` before the proof. State which shuffle convention is certified.
* Generalize multi-pile local noise by `Σ i, PilePosition i ≃ Fin N` and the dependent product of pile permutations. For finite alphabets a_i, tensor independent inverse-GSR laws using recursive product or a finite product of label-array types; local error ≤ min(1,∑_i choose(n_i,2)/a_i), via union bound or repeated product-TV subadditivity. Use `glueBlocks` as the embedding; uniform product maps to uniform allocation fiber. The same generic map contraction and schedule telescope apply to arbitrary legal round sequence. Empty/singleton piles have identity laws and zero collision budget; avoid importing their positivity into the generic theorem. G6 acceptance is general comparison plus concrete finite certificate, not just a 99-card numerical inequality. Prior G6 proof hints contain code for these assembly lemmas; use them, do not generate a new 500-line proof.

## F. G7 and G8: two further structural shortcuts, and a useful finite-N mixing theorem (NEW)

### F1. Drawing and changing capacities via constant preimages

Uniform allocations of capacity n, choose a uniform card from pile i (n_i>0), move to distinct pile j, produce capacity n'=n-e_i+e_j. From a fixed target A' there are exactly n'_j predecessors together with the drawn card: choose any card from target pile j and move back. The source law over experiments `(A,a∈pile_i A)` is uniform because n_i is constant. Thus every target has the same number of preimages. The output law is uniform on `Allocation n'` by the existing equal-fiber uniform pushforward lemma. This is not stationarity (the state type changes). The same proof for selecting k cards gives constant preimage count `choose(n_j+k,k)`. The capacity arithmetic is the only new type-dependent part; define the new capacity function first, prove its sum=N and the per-pile equations separately. The set identities of D1 are useful.

At histogram level the chance of drawing category c is `X_(i,c)/n_i`, the new table is `X-E_(i,c)+E_(j,c)`. This follows from the same single-cell observation as B3. Repeating draws yields hypergeometric laws. An ordered deal is a deterministic map from a uniform deck; its result is uniform allocation (or ordered hands, according to what is observed). TV contracts under the corresponding dealing kernel. If drawing depends on known category/strategy, or discarding selected undesirable cards, uniformity is not automatic. Clearly distinguish unconditional draw, conditioned observations and adaptive game decisions. Separate white/black card populations are modeled as different decks or a color constraint preventing illegal exchanges; do not shuffle them together and claim the game is modeled.

### F2. Generic transfer from ideal to finite protocols

Let K_j ideal and F_j finite rows, each with `TV(F_j(x),K_j(x))≤δ_j`. From ANY μ the terminal TV from reference π is at most `TV(ideal_run μ,π)+∑δ_j`. The generic perturbation/telescope infrastructure already exists; use the actual row laws built in D and E, not a loose `≤1` bound. In particular, if all ideal allocation fibers are uniform after the last local reset, total variation of the ideal full deck equals total variation of the allocation law from uniform. The first step erases within-pile ordering by the same P;Q;U factorization as in E. For arbitrary schedules the kernels need not be symmetric as a composite; uniform stationarity still holds by each step, and the telescope needs no reversibility of the composite. This is the bridge from finite-state allocation mixing to complete ordered decks.

### F3. New general mixing theorem using a local coalescing coupling

This gives a concrete useful theorem for the **existing** unrestricted `swapKernel`. It avoids waiting for an exact spectral gap theorem or calculating the enormous transition matrix. It is not a theorem about fixed-k pairwise-only exchange (unless you construct the mixture in D4). It is not claimed sharp.

Let N≥2, finite capacities feasible. Say A~B if B is obtained by swapping two distinct cards a,b (the actual owner assignment changes; allow equality separately). Set `ρ=1-4/N²`, a nonnegative rational <1. We will prove

```
TV(K^t(A), K^t(B)) ≤ ρ^t  for adjacent A,B
TV(K^t(A), K^t(B)) ≤ (N-1)*ρ^t  for any A,B
TV(K^t(μ), uniformAlloc) ≤ min(1,(N-1)*ρ^t)  for any μ.
```

The case N=0 or 1 is a singleton allocation carrier (when feasible); the identity law is already uniform. Treat it separately. The t=0 base case uses TV≤1, including ρ=0 when N=2 (`ρ^0=1`).

**Step F3a: a one-step coupling on the ordered-pair sample space.** Suppose B=swapPiles A a b with a≠b. Let Z be the uniform law on `(Fin N × Fin N)`. For the A-run use pair z. For the B-run use `φ z`, where φ is an involution on the pair type swapping `(a,b)` with `(a,a)` and `(b,a)` with `(b,b)`, fixing all other pairs. All four pairs are distinct. Construct φ using two disjoint `Equiv.swap`s, or explicit `if` branches and `left_inv=right_inv` from involution. Prove `φ (a,b)=(a,a)`, `φ (a,a)=(a,b)`, `φ (b,a)=(b,b)`, `φ (b,b)=(b,a)` and φ z=z for all other z. No `Fintype` proof is needed to construct the equivalence. Because φ is a bijection, its pushforward preserves Z by `GSR.map_bijective_uniformDist`.

Let `A_z=swapPiles A z.1 z.2`, `B_z=swapPiles B (φ z).1 (φ z).2`.

* On each of the four special pairs, one side applies the a,b swap and the other side applies a self-swap. The two allocations become identical, since the a,b swap is an involution. `swapPiles_involution` and the accessor `swapOwner` prove this. Prove `swapPiles A a a=A` and `swapPiles A a b=swapPiles A b a` generically if not already available.
* Off those four pairs, both apply the SAME transposition τ. Then they remain equal or adjacent: conjugation sends the old a,b swap to the swap at `(τ a,τ b)` in the new state. Use `swapPiles_relabel` from PairFactorSeeds with `σ=transposition z.1 z.2`. Show `swapPiles C z.1 z.2 = relabel τ C` because τ=τ.symm by `cardTransposition_involution`; prove this via `Subtype.ext` and the owner accessor. This gives the exact adjacency witness. No distance computation needed.

The special set has cardinality 4, so the two marginal kernels coalesce with probability at least `4/N²`; other outcomes preserve adjacency. This is a path coupling, but the following proof does not require a Wasserstein-distance formalization.

**Step F3b: prove adjacent TV bound by elementary induction.** Define `R t A := run K t (pointMass A)`. `run_succ`, `apply_pointMass`, and `apply_map_kernel` from `PairedMixtureSeeds.lean` identify `R(t+1) A` with `apply Z (fun z => R t A_z)`; similarly for B using `uniformMap_reparam φ` and `apply_map_kernel`. More explicitly, prove the generic lemma that a run from a mixture of starting states is the mixture of the point-start runs: `run K t μ = apply μ (compPow K t)` from `run_compPow`, then `compPow K t x = R t x` by `apply_pointMass`. Use `apply_map_kernel` to move the pushforward into the kernel argument. This avoids trying to rewrite every occurrence of `run` manually.

`pairedMixtureTV` states the generic inequality

```
TV(apply Z F, apply Z G) ≤ ∑ z, mass Z z * TV(F z,G z).
```

It is a sum of absolute differences: subtract the two row-mass identities, distribute the subtraction inside the finite sum, use triangle inequality and nonnegative weights, swap the finite sums. A complete proposed implementation is supplied in `PairedMixtureSeeds.lean` (uncompiled). For the four special pairs, the summand is zero (`Dist.tv_self`); all other terms bounded by `ρ^t/N²` from the induction hypothesis, allowing equal states too. Use `Finset.sum_filter` and `card` of the complement; the total is `(N²-4)/N² * ρ^t = ρ^(t+1)`. Keep rational arithmetic separate and use `Nat.cast_sub` with `4≤N*N`. This is the entire adjacent contraction proof.

**Step F3c: connect arbitrary allocations by at most N−1 transpositions.** Given A,B with same capacities, if owners disagree at card a, let j=B(a). A currently has a different owner at a. Since the number of cards with owner j is equal under A and B, there is a card b with A(b)=j and B(b)≠j. Otherwise `{x|A x=j}⊆{x|B x=j}`; equal cardinalities imply equality of these finite sets, contradicting a. Swap a and b in A. Card a is now correct, card b was already incorrect (may become correct), other cards unchanged. The mismatch-cardinality strictly decreases. There cannot be exactly one mismatch between equal-capacity allocations; same argument supplies a second mismatch. Thus a sequence with length at most N-1 exists (N≥1). Formalize this as induction on mismatch count, not on a permutation enumeration. Easiest strong induction statement: if mismatch count d>0, `TV(R t A,R t B)≤(d-1 : Nat)*ρ^t`. After one repair if new d'=0, adjacent bound ≤(d-1)ρ^t because d≥2. Otherwise triangle plus induction gives `(1 + (d'-1))*ρ^t ≤ (d-1)*ρ^t` since d'<d. The d=0 case is equality and TV=0. This directly proves the bound without storing a path or formalizing a graph distance. For an easier first theorem use N instead of N−1 (bound by d and no d≥2 arithmetic); improve later if useful.

**Step F3d: stationarity to arbitrary-start TV.** `uniformAlloc` is stationary by existing `swapKernel_uniformStationary`. The distribution after t steps from μ is `apply μ (compPow K t)` and likewise from uniform. For any A, compare its point-start run to the stationary mixture using `pairedMixtureTV` with one constant kernel and the other point-start kernel. Bound every component by `(N-1)ρ^t` and use sum_mass. Then mix over μ again using the same helper (now the reference kernel constant at uniform). Combine with `Dist.tv_le_one`. This gives the worst-case finite-N convergence theorem. For any rational epsilon>0, choose t such that `(N-1)ρ^t≤epsilon`; an effective integer stopping bound follows from geometric decay, or certify a particular t by exact Rat powers. Do not evaluate the giant state space. The 3-pile example in C checks the scope; also test N=2 where one step from each allocation with capacities (1,1) is uniform. The coupling bound is polynomial-scale O(N² log(N/epsilon)), conservative relative to sharper random-transposition mixing results, but far stronger than a minimum-positive-path bound exponentially small in N.

**Step F3e: connect to finite local shuffles.** Combine the above with F2: t rounds of unrestricted one-card swaps and ideal local reset have allocation TV as bounded, independent of initial ordering (first reset absorption). Replacing each reset by finite GSR adds at most `∑_round ∑_pile choose(n_i,2)/a_(round,i)`. The finite physical full-deck theorem is now parameterized by arbitrary capacities, pile count, and N. This gives a useful general G8 certificate even if optimal fixed-pair k schedules remain open. If a particular protocol permits only cross-pile swaps, prove the correct selection law and redo coupling for that law; don't apply this bound to it without a valid comparison.

### F4. Cost optimization and scope of optimality

For prescribed exchange schedule and collision-budget local shuffles, let t_{s,i} be the number of binary riffles assigned to pile i after step s. Its upper bound contribution is `w_{s,i}/2^t`, `w=choose(n_i,2)`. Adding one riffle reduces error by `w/2^(t+1)`; reductions are nonincreasing. If each pile riffle costs one unit, allocating a fixed budget B by repeatedly taking the largest next reduction is optimal **for this sufficient bound**, by selecting the B largest reductions among prefix-closed sequences. Prove the exchange argument: if an allocation omits a larger available next reduction than the smallest selected terminal reduction in another pile/round, moving one unit reduces error; iterate or sort marginal gains with deterministic ties. Handle zero weights and B=0. This produces a certified feasible cost frontier without claiming actual protocol TV optimality. Unequal costs need knapsack/dynamic programming or separate analysis; greedy ratio is not generally exact. A lower bound for real optimality is a separate theorem (e.g. support size, observable separation, or exact TV for a bounded protocol family).

A sharper local GSR route (not needed before G8 baseline) is in the Nov 24 hints: stable-sort pullback permutation probabilities depend only on descents; group by Eulerian numbers and compute exact TV by summing over O(n) categories rather than n! permutations. Reuse the earlier exact rational checks before formalizing. This can improve the collision certificate by many riffles and is more useful than improving a loose telescope with constants ≥1.

## G. Acceptance checklist and resumption

* G5: real allocation and histogram `Dist` kernels for unrestricted and fixed-pair k exchanges; strong lumpability; weighted balance; closed-form stationary mass; lift intertwining; BL specialization; a 3-pile concrete transition example. Separate what is proved from scalar formulas or examples.
* G6: correct stable-sort orientation, binary-riffle interpretation, all deterministic starts for the three-round certificate, then arbitrary finite piles comparison bound. Preserve the restricted existing theorem as a useful intermediate result, not the all-start claim.
* G7: legal changing-capacity kernel plus uniform transport and dealing contraction, with game-relevant assumptions and example.
* G8: quantified finite-N bound and cost certificate with explicit operations/cost; a bounded certified frontier, not a claim of unrestricted optimum. G9 optional research.
* When integrating a canonical module add it to `Shufflemath.lean` and `dev/verify_next_phase.sh` where appropriate; run the focused build then normal verification. Update the current handoff/manifest with exact declaration names and remaining blockers. Avoid new competing active goals. Do not modify this dated hint/review after landing; append a new record.

Do not require every hint to become a theorem if an alternative proves the same intended result. The important outcome is the mathematical roadmap and honest theorem scope. A change of model is not a reason to start over.
