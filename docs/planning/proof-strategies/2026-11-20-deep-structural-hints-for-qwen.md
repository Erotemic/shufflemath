# Deep structural hints for the finite-deck proof campaign — 2026-11-20

**Audience:** Qwen / the Lean proof agent. **Source base:** `shufflemath-source-2026-11-20T113201-5-58de44b84aee` (HEAD `58de44b`). This is an *additive* mathematical guide, not a rewrite of prior reviews or the previous `2026-11-20-post-g4-structural-strategies.md` overlay. It **supersedes that overlay's execution priority** where it recommends proving TV isometry before the finite-GSR bound: the coupling shortcut below can deliver the bound first. Read the accompanying [bottleneck review](../reviews/2026-11-20-proof-campaign-mathematical-bottleneck-review.md) first.

**Working contract:** Names in **backticks identifying existing declarations** have been located in the snapshot. Names introduced as `TARGET`, pseudocode, or suggested interfaces **do not claim to compile**. Lean/Lake was unavailable to the author. Do not paste all the proposed code into one enormous proof. Establish the small identities in order, using existing modules and local `lake build` on your machine. Do not create/switch Git worktrees. Do not modify dated historical reviews.

## 0. The picture that unifies the project

The fundamental object is a finite set of **distinct card identities** `C` and a finite set of **positions** `P` of equal cardinality. A complete ordered deck is a bijection

`d : P ≃ C`.

For the current generic two-pile code, both types are `Fin N`; `FiniteDeck.Deck N = Equiv.Perm (Fin N)` and **the function goes from position to card** (`FiniteDeck.TwoPile`). Separate these two kinds of permutations:

- `H ⊆ Sym(P)`: permutations of *positions* preserving every pile (right action `d ↦ d ∘ h`).
- `K ⊆ Sym(C)`: permutations of *card identities* preserving every category/color (left action `d ↦ k ∘ d`).

These actions commute. The full deck is a torsor under either full symmetric group. The quotient by the right `H` action remembers **which named cards are in which pile**, but forgets local order. The further quotient by `K` remembers only the **category count matrix**. In algebraic language, the histogram orbits are classified by double cosets `K \ Sym(P) / H` (after choosing one identification `P ≃ C`).

This is not decorative abstraction. It explains, at once:

1. Why each fixed allocation has the same number `∏_pile (pileSize)!` of ordered realizations.
2. Why the distribution conditioned on allocation is uniform over one `H`-orbit.
3. Why color-preserving relabelings are transitive on histogram fibers.
4. Why exchange selection counts depend only on category-count tables.
5. Why a reversible microscopic exchange gives detailed balance on the histogram quotient.
6. Why TV of local shuffles can be studied on the small *per-pile permutation groups* rather than on all `N!` ordered decks.

**Do not begin by formalizing Mathlib double-coset quotients.** Prove explicit equivalences and transitivity on finite subsets and subtype fibers first; the quotient vocabulary is the explanation of what those lemmas accomplish. Sections 1–7 give the shortest route to a finite physical-GSR certificate. Sections 8–11 explain how to scale to arbitrary piles and real game settings.

## 1. The exact first model gap: make a literal position-swap kernel

### 1.1 What source already supplies

- `FiniteDeck.TwoPile.leftPosition/rightPosition` embed the two local position types into `Fin N`.
- `FiniteDeck.PhysicalSwap.newLeftCards`, `literalSwapMembership`, `newLeftCards_card` characterize the post-swap **left card set**.
- `FiniteDeck.SubsetExchange.subsetExchangeKernel` and the membership kernel in `FiniteDeck.BLRefinement` give the correct uniform choice-of-card-subsets law.
- `FiniteDeck.A3KernelLaw.rawExchange` **already includes `localLift`**. It is a perfect-local *reference*, not the unrandomized swap.

### 1.2 Build an involution, not a four-case bijection proof

For `m ≤ N`, `k ≤ m`, `k ≤ N-m`, choose:

- `L : Finset (Fin m)` with `L.card = k`,
- `R : Finset (Fin (N-m))` with `R.card = k`,
- a bijection `b : {i : Fin m // i ∈ L} ≃ {j : Fin (N-m) // j ∈ R}`.

Make a permutation `τ(L,R,b) : Equiv.Perm (Fin N)` that swaps each selected pair of **global positions**, fixes all unselected positions, and satisfies `τ ∘ τ = id`. The selected left/right supports are disjoint by the two-pile decomposition. An involution is bijective automatically; do not re-prove an involved four-way injectivity/surjectivity split.

Mathematical core, for any starting deck `d`:

`membership (d ∘ τ(L,R,b)) = literalSwapMembership d L R`.

The pairing `b` changes which card lands at which *position*, but **not** the resulting *membership set*. Thus the statement is independent of `b` on its right side. If a deterministic canonical pairing is convenient for the actual protocol, choose it **after** proving the pairing-independent identity.

**Two possible Lean routes:** (A) use a disjoint pairwise-transposition product on the finite support, proving it is an involution, or (B) define an explicit function with left-selected/right-selected/unselected branches and prove `f (f x)=x`, then `Equiv.ofBijective`. In either route, keep the pairing in a small subtype `Equiv`; never encode it using arbitrary `Fin N` arithmetic where `omega` is asked to solve the whole construction.

**First compile target:** `TARGET literalSwap_membership`, with an actual `Deck N` result rather than merely `Finset` membership. Test orientation on a two-card example: `Equiv.trans f g` means apply `f` then `g`, i.e. mathematical `g ∘ f`.

### 1.3 The probability bridge is one change of variables

Let `P` be the kernel from `Deck N` that chooses `(L,R)` *uniformly and independently* and outputs `d ∘ τ(L,R,canonicalPair(L,R))`. Read back the left card set. The two image maps

`L ↦ d(image of selected left positions)` and `R ↦ d(image of selected right positions)`

are bijections between size-`k` **position** subsets and size-`k` **card** subsets of the two existing piles, because `d` is bijective. Therefore the choice-of-card-subsets law is uniform, with denominator

`choose(m,k) * choose(N-m,k)`.

Precisely the missing kernel identity is:

`TARGET: P ⊳ det(membership) = det(membership) ⊳ subsetExchangeMembershipKernel`.

Then append `localLift` and use `FiniteKernel.comp_assoc` to deduce

`P ⊳ det(membership) ⊳ localLift = A3KernelLaw.rawExchange`.

This is the correct semantics of *literal swap followed by perfect local mixing*. **Do not** define the finite physical kernel as `A3KernelLaw.rawExchange ⊳ finiteLocal`: that gives the finite scheme an illicit perfect reset.

**Proof engineering:** first show the selected-position map is a finite equivalence; prove `Dist.map` of a uniform distribution along that equivalence is uniform (`GSR.map_bijective_uniformDist` is relevant); only then combine two independent subset samplers. No new BL numerator or overlap-count theorem is required.

## 2. The first permutation-group shortcut: membership fibers are free `H`-orbits

Let `H_m = Sym(Fin m) × Sym(Fin (N-m))`. Construct

`embed_m : H_m → Sym(Fin N)`

by conjugating `Equiv.sumCongr` through the split equivalence `Fin N ≃ Fin m ⊕ Fin (N-m)`. The existing 50/49 construction `CommanderLocalGSR.pileRelabelEquiv` and `CommanderDeckGSR.pileRelabelEquiv_pairInjective` are models, but the generic proof should use the sum equivalence by construction.

Fix `d : Deck N`. The action `act_d(h) = d ∘ embed_m(h)` is **injective**: if `d ∘ h1 = d ∘ h2`, cancel the bijection `d` and restrict to each pile. Its image is **exactly** the fiber of `membership d`:

`TARGET: H_m ≃ {e : Deck N // membership e = membership d}`.

**Surjectivity argument that saves a lot of Lean code:** given such an `e`, put `h = d⁻¹ ∘ e` as a position permutation. For a left position `i`, `e(i)` belongs to the left cards of `d`; hence `d⁻¹(e(i))` is a left position. Do the same for the right positions. Thus `h ∈ H_m`, and `e=d∘h`. The proof needs no factorial calculation.

Uniform `h ∈ H_m` now pushes forward exactly to `localLift (membership d)`, because the action is a bijection onto the fiber. This is stronger than a bare `m! (N-m)!` count: it is an explicit *sampler equivalence*.

### 2.1 What TV theorem do we actually need?

For distributions `ν,η` on `H_m`, the action being injective gives

`TV(map act_d ν, map act_d η) = TV(ν,η)`.

But **only the inequality is necessary for the F4 upper bound**:

`TV(map act_d ν, map act_d η) ≤ TV(ν,η)`.

This is data processing under a deterministic map and does *not* require the action bijection. In practice, prove/use a `Finsupp`-support version of data processing first; leave the isometry as a later structural result if Lean elaboration is expensive. The existing `TotalVariation.tvFinsupp`, `distProductFinsupp_tv_subadditive`, and `kernel_apply_lipschitz` are relevant; `Dist.tv` in `TotalVariation` is a `Finset.univ` sum and can accidentally materialize a monstrous `Fintype (Deck 99)`.

**Target design:** `TARGET tvFinsupp_map_le` for any map `f` and `TARGET tvFinsupp_map_of_injective` only if useful. Their proofs should sum over **supports of the two Finsupp weights**, not `Finset.univ` of all 99-card decks.

## 3. The second permutation shortcut: replace list validity by sorted-key ranks

The last F4 wall is *not* the already-proved independent product identity `CommanderLocalGSR.gsrProductKernel_eq_distProductFinsupp`. It is turning the `GSR.idealShuffle` output list into an actual finite permutation and preserving the law.

For `n` local positions and `a>0` labels `ℓ : Fin n → Fin a`, form a **distinct key** for every original position:

`key(i) = (ℓ(i).val, i.val)`, ordered lexicographically.

These keys are always distinct, even when labels tie. Define

`rank_ℓ(i) = #{ j : Fin n | key(j) < key(i) }`.

Because the keys give a strict total order on exactly `n` elements, `rank_ℓ` takes values in `Fin n` and is a bijection. The resulting shuffled order has at output position `r` the card originally at position `rank_ℓ⁻¹(r)`. Thus the shuffle is a genuine permutation **for all label assignments**, with no invalid-list fallback.

**Hard intermediate lemma:** if `key(i) < key(j)` then `rank(i) < rank(j)`. The set of keys below `key(i)` is a proper subset of the set below `key(j)` (it misses `i`), giving strict cardinality inequality. This proves injectivity, and finite injective endomaps are bijective. Try a Mathlib order/rank equivalence before recreating this argument, but do not invent an API name without checking.

Then prove for the canonical distinct list `[0,1,...,n-1]`:

`TARGET: stableBuckets a ℓ canonicalList = orderByNewPosition (rank_ℓ.symm)`.

This is a *pointwise* sorting statement: stable buckets order by `(label(i), originalPosition(i))`. No global probability calculation is involved.

**Why this route may outperform list-to-permutation:** `GSR.stableBuckets_set` proves the **set** is preserved, but not the `Nodup`/length invariants needed to turn a list into an `Equiv`. Rank sorting builds a bijection by construction; only one list equality remains. If an existing `List.Nodup`-to-permutation library route compiles quickly, use it instead; avoid maintaining *both* bridges forever.

**Important convention:** `GSR.stableBuckets_comp` states that the *later* independent riffle label is the major lexicographic key. The `rank` implementation must match this convention exactly; a reversed pair still defines a valid permutation but proves the wrong GSR composition theorem.

Once `rank_ℓ` exists, define `ν_{n,a}` as the pushforward of existing `GSR.uniformLabels n a ha` through the sorted-key permutation map. The permutation law is a `Dist (Equiv.Perm (Fin n))`, without needing `Fintype (List (Fin n))`. For an arbitrary current pile, the labels may be indexed by cards rather than positions; the i.i.d. label law is invariant under reindexing by the current pile bijection, so the same distribution on *relative position permutations* results.

**Boundary proof probes:** `n=0` and `n=1` produce the unique permutation; `a=1` produces identity (all keys tie in label, so original positions determine order); `a<n` is allowed and sorting is still a permutation. Test two successive two-label steps on a tiny `n=3` list against the four-label order convention.

## 4. Collision coupling: the shortest quantitative GSR proof

### 4.1 The math

Let `ℓ : Fin n → Fin a` be uniform on all `a^n` label arrays (`a>0`). Let `C` be the event that **some two distinct indices have the same label**. On the complementary event `Cᶜ`, all labels are distinct and the output permutation is the relative rank ordering of independent exchangeable labels. Its conditional distribution is uniform on `Sym(Fin n)`.

Why exactly uniform? The group `Sym(Fin n)` acts on label arrays by permuting *their indices*. Uniform arrays are invariant, injective arrays are invariant as a set, and **when there are no ties** the rank permutation is equivariant under that action. Since the group acts transitively on output permutations, all output masses are equal. This avoids enumerating sorted permutations or deriving the Bayer–Diaconis probability formula.

For a fixed pair `i ≠ j`, `Pr(ℓ i = ℓ j)=1/a` by independent uniform labels. The union bound over unordered pairs gives

`Pr(C) ≤ choose(n,2) / a`.

Construct a coupling `(Q,U)` of the finite-GSR permutation and a uniform permutation as follows. Sample `ℓ`. If `Cᶜ`, set `U := Q := rankOrder(ℓ)`. If `C`, keep `Q := rankOrder(ℓ)` and sample `U` independently uniformly. The marginal of `U` is uniform in both branches (because `Q|Cᶜ` is uniform), while

`Pr(Q ≠ U) ≤ Pr(C)`.

Therefore, by the coupling inequality,

`TV(ν_{n,a}, U_n) ≤ Pr(C) ≤ min(1, choose(n,2)/a)`.

This is **not** an exact formula for TV and is conservative. It is deliberately the first general, finitely provable bound.

### 4.2 An implementation trick for `a<n`

If `a<n`, the injective-label event is empty. **Never normalize by its probability.** Prove the conditional-uniform lemma under `n≤a`; in the complementary branch use `TV≤1` and `1≤choose(n,2)/a` for `n≥2` (or take the union bound and a zero-event-safe coupling). For `n≤1` the GSR law is exactly uniform on the singleton permutation group.

The exact no-collision probability for `a≥n` is `(a)_n/a^n`, yielding a sharper `1-(a)_n/a^n` upper bound. This may be a later improvement; the pairwise union bound is significantly easier to formalize.

### 4.3 A coupling may bypass a large TV theorem entirely

A naive plan would first formalize TV isometry through `act_d`, then express the finite GSR law on `H_m`, then compare to `localLift`. The **shorter plan** is to use *the same literal swap selection and the same GSR label arrays* in two coupled worlds:

- **finite world:** swap positions, then sort each pile by finite labels;
- **perfect world:** perform the identical swap, then use the coupling above to choose a uniform within-pile permutation.

The two resulting full decks are **identical whenever both label arrays are collision-free**. The mismatch probability is bounded by the sum of the two collision probabilities. Thus for any input deck `d` and any fixed swap outcome,

`TV(finiteLocal(d), perfectLocal(d)) ≤ choose(m,2)/a_L + choose(N-m,2)/a_R`.

Averaging over the common random swap outcome does not worsen the bound. This is a *row-wise* bound for the actual physical kernel, and it does not require summing over all decks or proving `tv_map_of_injective` first. Retain the group-action proof for the more general theory, but use the coupling as the fastest route to a finite protocol certificate.

**Small Lean targets:** an abstract `TV ≤ mismatchProbability` for a finite coupling; `uniform_rank_when_no_ties`; `collision_prob_le`; `localCoupling_rowTV`. Prove the support-based/coupling versions before specializing to `Deck N`.

## 5. The telescope is simple once the row error is meaningful

Let `K_i` be actual physical swap+finite-GSR kernels and `J_i` the same swap+perfect-local kernels. Suppose for every input deck `d`, `TV(K_i(d),J_i(d)) ≤ δ_i`.

Replace the steps one at a time. Every common prefix is a distribution, and every common suffix is a Markov kernel, so total variation contracts when the suffix is applied. Triangle inequality gives the **unweighted** hybrid estimate

`TV(μ K_1 … K_t, μ J_1 … J_t) ≤ δ_1 + … + δ_t`.

No Dobrushin coefficients or full-deck maxima need be computed. (Dobrushin-weighted bounds can improve the result later.) For uniform target `U`:

`TV(μ K_1 … K_t,U) ≤ TV(μ J_1 … J_t,U) + Σ_i δ_i`.

For independent `a_i`-label local GSR on a two-pile split:

`δ_i ≤ choose(m,2)/a_i^L + choose(N-m,2)/a_i^R`.

If each pile gets `t_i^L` / `t_i^R` binary inverse riffles, `GSR.idealShuffle_comp` gives label alphabet sizes `2^(t_i^L)` and `2^(t_i^R)` respectively. Thus the entire terminal bound becomes elementary rational arithmetic **once the semantic and coupling bridges compile**.

**Lean-friendly proof:** use a `List` induction that carries two partially hybrid schedules rather than unfolding `ProtocolCertificate.errorBudget` over `Deck N`. Use source-level generic `FiniteKernel.apply_comp`, `FiniteKernel.comp_assoc`, `TotalVariation.kernel_contraction`, or the existing `TotalVariation.kernel_apply_lipschitz` machinery on support-sums. Prove the purely abstract telescope once; specialization should be a short `calc` chain. `TelescopeF5`'s `TV≤2`/`TV≤3` are not adequate substitutes for `δ_i<1`.

## 6. The missing start-state bridge is smaller than it appears

`FiniteDeck.BLDisintegration.two_physical_perfect_exchanges_uniform_deck` gives the ideal macro–deck TV identity for the initial law

`U_{x0} := (pointMass x0) ⊳ uniformCountFiberMembership ⊳ localLift`.

That is *not generally* `pointMass d0` for an ordered deck `d0`. But two facts help.

**Fact A: ideal exchange+reset depends only on membership.** If `membership d = membership e`, then their `J` rows are the same, because `J = det membership ⊳ subsetExchangeMembershipKernel ⊳ localLift` by Section 1.

**Fact B: Commander’s fully segregated macro-count fiber has one membership.** With `N=99,m=50,r=50`, count `x0=50` forces all 50 marked cards to be in the left pile. The count-fiber size is `choose(50,50)*choose(49,0)=1`. Therefore `U_{x0}` is uniform on the **orderings of that unique membership**, and Fact A implies

`(pointMass d0) ⊳ J = U_{x0} ⊳ J`

for **any ordering** `d0` of that segregated membership.

Consequently, for any number of rounds `t≥1`, applying additional `J` kernels preserves equality. This transfers the exact three-round ideal macro TV formula to a literal ordered starting deck, without pretending `pointMass d0=U_{x0}`.

**Target lemmas:** `countFiberMemb_singleton_at_segregated`, `idealRow_eq_of_sameMembership`, `idealRun_fixedStart_eq_liftedStart_of_one_round`. In Lean, using the existing membership-count bridge is preferable to proving a new factorial formula. Never infer the same equality for an interior `x0` where its membership fiber is not a singleton.

## 7. The overlooked payoff: colorblind shuffles are equivariant under *all* card relabelings

This can upgrade a certificate for one ordered deck to a **uniform guarantee over every initial deck**. It is the next theorem to prove **after** the fixed-start finite-GSR bound, not a prerequisite for the first certificate.

Let `g : Sym(C)` be any relabeling of *card identities*. It acts on decks by `g·d := g ∘ d`. A physical protocol that chooses **positions** independently of card identities and assigns i.i.d. shuffle labels is *colorblind*: for its kernel `K`,

`K(g·d, g·A) = K(d,A)`

in measure/pushforward notation, or equivalently

`K(g·d) = map (g·) (K(d))`.

The identity is immediate for a deterministic position permutation `τ` because

`(g∘d)∘τ = g∘(d∘τ)`.

For finite-GSR local sorting, sampling independent labels of cards is invariant under the reindexing induced by `g`. If the implementation samples labels of **positions** instead, equivariance is even more direct. **Do not assert this theorem for an operation whose choice depends on marked-card identities or colors.**

**Even shorter if the implementation is position-based:** after building the label-to-position-permutation encoder (Section 3), the complete round has a *single state-independent random position-permutation law* `ρ` (swap permutation followed by the two local permutations). Then `K(d) = map (fun τ => d ∘ τ) ρ`, a random walk by right multiplication on the finite permutation group. This formula makes left card-relabeling equivariance immediate, shows that uniform decks are stationary for every such round, and is a cleaner F5 implementation boundary than any card-specific case split. A list-valued GSR implementation assigning independent labels to **card identities** has this same row law only after the label-reindexing proof; do not assert the formula definitionally before that bridge.

Every pair of decks `d,d'` is related by one such relabeling: `g=d' ∘ d⁻¹`. By induction on the round count:

`run K t (pointMass d') = map (g·) (run K t (pointMass d))`.

This relabeling need **not** preserve the distinguished/marked-card category: the *physical protocol* is colorblind, and we use the macro theorem only at the original reference deck before transporting the full-deck error. Uniform deck law is invariant under bijections, and TV is invariant under a common bijective pushforward, so

`TV(run K t (pointMass d'), uniformDeck)
 = TV(run K t (pointMass d), uniformDeck)`.

**Thus the full-deck TV error of a colorblind, position-driven shuffle is identical from every deterministic starting order.** This is more general than the specially segregated membership argument of Section 6, which supplies the convenient *one starting deck* from which to evaluate the ideal reference.

Finally, if every point mass has TV at most `ε`, any initial law `μ` has TV at most `ε`: `μ K^t` is a convex mixture of point-mass outputs and TV is convex in that argument. `TotalVariation.mixtureTV_le` may help here. This is a genuine **worst-case-start mixing certificate** for all ordered `N`-card decks, subject to a proven colorblindness hypothesis.

**Suggested proof sequence:**

1. `TARGET positionAction_commutes_cardRelabel` (pointwise, almost definitional).
2. `TARGET labelsLaw_invariant_reindex` using `GSR.map_bijective_uniformDist` on label arrays.
3. `TARGET finiteRound_cardEquivariant` for the actual kernel.
4. `TARGET run_cardEquivariant` by induction.
5. `TARGET uniformDeck_relabelInvariant` and `TARGET tv_map_equiv` (support-based).
6. `TARGET tv_fixedStart_independent_of_deck`; then mixture/convexity corollary.

This is a place to use the abstract permutation-group view, **not** to unroll a finite sum over all complete decks.

## 8. Concrete theorem to aim at: 99-card, three exchange rounds, finite riffles

Choose `d0` as *any* ordered deck whose left 50 positions hold the 50 distinguished cards. Each round independently performs a uniform choice of 25 positions in each pile, swaps them by a fixed pairing, then performs **23 independent binary inverse-GSR riffles in each pile**. Define the deck-valued `finiteRound` kernel with no perfect-reset hidden inside it.

Let `J` be the literal-swap+perfect-local kernel. Sections 1 and 6 give the exact ideal reference from `d0`; Sections 4–5 give its approximation. Source has the exact three-round ideal TV constant from `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`:

```
q3 = 172379525755689183991816396516567920780192827919620440221147749
     / 6691837923759692633601708022649918108038775216019298375918637677488
   ≈ 0.00002575966837804714
```

For each round, the two-pile collision error is

`δ ≤ [choose(50,2) + choose(49,2)] / 2^23
   = (1225+1176)/8388608 = 2401/8388608`.

Three rounds give

`TV(run finiteRound 3 (pointMass d0),uniformDeck)
 ≤ q3 + 7203/8388608
 ≈ 0.0008844241810123245 < 1/1000`.

The exact inequality is a rational arithmetic goal (`norm_num` after introducing the two terms), not a stochastic proof. **For 22 riffles, the same *upper-bound method* gives about 0.00174309, but that says nothing about actual impossibility.**

If Section 7's colorblind-equivariance theorem is also proved, this exact upper bound applies to every deterministic `d0`, and then to **every initial distribution** on ordered decks. This is a substantially more useful statement than a result assuming an initially fiber-uniform deck.

**Cost note:** three exchanges plus 23 left + 23 right binary riffles per round is 141 unit-cost operations *if* each batch exchange costs one and each pile riffle costs one. Under parallel-per-pile timing, the same protocol has a different cost. Choose and name the physical cost model before claiming optimization; do not conflate arithmetic cost, time, and number of moved cards.

## 9. Multi-pile theory: the category-count table is a double orbit

### 9.1 Define the finite types so the proof can scale

Let `Pile` and `Color` be arbitrary finite types; `capacity : Pile → Nat`; `C` the finite set of *distinct* cards with `card C = ∑_p capacity p`. Use

`Position := Σ p : Pile, Fin (capacity p)`

and `Deck := Position ≃ C`. Let `color : C → Color` classify cards. (If a card has several properties, let `Color` be a finite product type; the fibers of `color` must be disjoint classes for the counting formula.)

For each ordered deck `d`, define its histogram

`X_d(p,c) = #{i : Fin (capacity p) | color (d⟨p,i⟩)=c}`.

The row totals are `capacity p`; the column totals are the total category counts `r_c := #{a:C | color a=c}`. Avoid a hard-coded `Fin 50` count-state type. An admissible histogram is a matrix of natural numbers with these exact margins.

### 9.2 Prove the double-orbit classification **constructively**

Claim: `X_d = X_e` iff `e = k ∘ d ∘ h` for a position permutation `h` preserving piles and a card permutation `k` preserving colors.

**Forward proof without quotient machinery:** For each cell `(p,c)`, the sets of *positions* having color `c` in pile `p` under `d` and under `e` have the same finite cardinality. Choose a subtype equivalence between these sets; glue these disjoint cell equivalences into a pile-preserving permutation `h` so that

`color(d(h(pos))) = color(e(pos))` for all positions.

Then `k := e ∘ (d ∘ h)⁻¹` is a card permutation, and this displayed equation shows `color(k(a))=color(a)`. Hence `e=k∘d∘h`. The reverse implication holds because `h` permutes positions inside piles and `k` preserves color. This also proves transitivity of the color-preserving-card group on every fixed histogram allocation fiber.

**Lean technique:** first define per-cell subtype sets and `Fintype.equivOfCardEq`; assemble a global equivalence using a dependent sum of cell positions. Do **not** try to prove injectivity of one huge `if` split involving arbitrary `Pile` and `Color`. Use equivalences to make bijectivity structural.

### 9.3 Count fibers by independent allocations of *categories*

For an admissible table `x_{p,c}`, write `n_p = ∑_c x_{p,c}`, `r_c = ∑_p x_{p,c}` and `N = ∑_p n_p`. The number of *named-card allocations to piles* with table `x` is

`A(x) = ∏_{c∈Color} Multinomial(r_c; (x_{p,c})_{p∈Pile})`.

For each such allocation, independent orderings within piles give exactly

`H = ∏_p (n_p)!`

ordered decks. Therefore the number of ordered decks with histogram `x` is `A(x) * H`, and under a uniformly ordered full deck,

`π(x) = [ (∏_p n_p!) (∏_c r_c!) ] /
        [ N! (∏_{p,c} x_{p,c}!) ]`.

For Lean, prove natural-cardinalities by equivalence and multiplication **before** casting to `Rat`; use divisibility rather than interpreting factorial quotients in `Nat`. `Nat.multinomial` may provide relevant counting facts, but verify its current API. This uniform stationary histogram is *not* uniform over admissible tables.

**Tiny sanity test:** three piles of sizes `(2,2,1)`, red/blue totals `(3,2)`, and histogram rows `(1,1),(1,1),(1,0)`: six allocations of red cards times two allocations of blue cards = 12 named allocations; `2!*2!*1! = 4` orders per allocation, so 48 of `5!=120` decks, probability `48/120=2/5`. Build analogous `#eval`/Python sanity checks on `N≤5` but do not use such checks as Lean proof certificates.

### 9.4 A general pair-exchange histogram transition formula

Choose two distinct piles `p,q` of capacities `n_p,n_q`, an exchange size `s≤min(n_p,n_q)`, and independently select uniform `s`-subsets of their named cards. For each color `c`, let `a_c` be the number selected from `p` and `b_c` from `q`. Then

`∑_c a_c = s`, `∑_c b_c = s`,

`x'_(p,c) = x_(p,c) - a_c + b_c`,

`x'_(q,c) = x_(q,c) - b_c + a_c`,

with all other rows unchanged. The probability of a *particular admissible profile pair* `(a,b)` is

`w_x(a,b) = [∏_c choose(x_(p,c),a_c) choose(x_(q,c),b_c)] /
            [choose(n_p,s) choose(n_q,s)]`.

If several `(a,b)` profiles yield the same `x'`, **sum their weights**. In particular, a nontrivial card exchange can leave the category histogram unchanged, so diagonal histogram mass is not merely the probability of doing nothing.

**Shortcut:** define the stochastic kernel as the pushforward of uniform legal subset choices. Row normalization is automatic; only afterwards prove the hypergeometric expression by counting selection fibers. Do not ask `ring`/`omega` to prove an enormous multinomial normalization formula from scratch.

## 10. Generic reversible quotients: one theorem instead of many balance proofs

This is the mathematical basis for G4 generalization and for the multi-pile extension. Let `X,Y` be finite, `f:X→Y` surjective, `Q` a kernel on `X`, and `π_X` a strictly positive stationary distribution **with detailed balance**:

`π_X(s) Q(s,t) = π_X(t) Q(t,s)`.

Assume **strong lumpability** along `f`: for any `x=f(s)`, the total probability to land in `F_y := {t|f(t)=y}` depends only on `x`; call it `P(x,y)`. Let

`π_Y(x) := ∑_{s∈F_x} π_X(s)` and

`U_x(s) := π_X(s)/π_Y(x)` for `s∈F_x`, zero otherwise.

The micro-to-macro double count yields

```
π_Y(x) P(x,y)
 = ∑_{s∈F_x,t∈F_y} π_X(s)Q(s,t)
 = ∑_{t∈F_y,s∈F_x} π_X(t)Q(t,s)
 = π_Y(y) P(y,x).
```

Therefore `π_Y` is stationary and reversible. More strongly, for each `t∈F_y`:

```
(U_x Q)(t)
 = (1/π_Y(x)) ∑_{s∈F_x} π_X(s)Q(s,t)
 = (π_X(t)/π_Y(x)) ∑_{s∈F_x} Q(t,s)
 = π_X(t) P(y,x)/π_Y(x)
 = P(x,y) U_y(t).
```

So the exact disintegration/intertwining theorem is

`U_x ⊳ Q = ∑_y P(x,y) U_y`.

For the symmetric uniform-micro case (`Q(s,t)=Q(t,s)` and `π_X` uniform), `U_x` is uniform on the fiber and `π_Y(x) ∝ |F_x|`. This recovers the beautiful special case from the earlier November 18 notes, **without** requiring explicit orbit bijections in the quotient proof.

**How to establish lumpability in new models:** find a group acting transitively on each `F_x` and commuting with `Q`. Then `∑_{t∈F_y} Q(s,t)` is constant across `s∈F_x` by change of variables; no transition-count formula is needed. The **color-preserving card-relabeling group on the allocation state space** in Section 9 supplies exactly such a symmetry for uniform pair exchanges between piles. Do not automatically claim full-deck right-`H` equivariance for a fixed pairing rule on *positions*: that rule can break this symmetry until local order is forgotten.

**Caveat:** a composition of individually symmetric kernels is generally **not symmetric**. A randomized mixture of symmetric kernels is symmetric, but an ordered schedule need not be. If a schedule is not reversible, use stationary composition and TV contraction rather than applying the reversible quotient theorem blindly.

## 11. Group random walks, ergodicity, and useful consequences for card games

### 11.1 Why uniform stationarity is cheap but mixing is not

If a shuffle chooses a *position permutation* `τ` independently of the current deck, the update `d↦d∘τ` is a bijection for each fixed `τ`. A mixture of such maps preserves the uniform full-deck law automatically. If the law of `τ` is invariant under inversion (e.g., a random involutive swap), the one-step deck kernel is also symmetric and reversible. **No cardinality computation over `N!` decks is needed for these stationarity results.**

But a stationary uniform law does not imply convergence. Example: `N=4,m=2,k=2`; a full exchange deterministically complements the membership, creating disconnected two-cycles on the membership space. For general connectivity, allow a positive-probability **one-card cross-pile swap**, and add laziness for aperiodicity; the resulting subset chain connects any two fixed-capacity memberships by replacing misplaced cards one at a time. Prove a positive minorization for some power before seeking spectral constants.

For multiple piles, a connected graph of allowed pairwise one-card transfers is a promising sufficient condition, but capacities, empty piles, and movement restrictions must be represented correctly. Do not claim irreducibility of every fixed-size swap chain.

### 11.2 Card games need data processing more than a theorem per deal pattern

Once a full-deck distribution is within `ε` of uniform, any deterministic/randomized *dealing* kernel `D` satisfies

`TV(μ⊳D, Udeck⊳D) ≤ TV(μ,Udeck) ≤ ε`.

This covers distributions of player hands, revealed cards, draws, etc., without a separate proof for each hand size. A later variable-pile model can describe updates after dealing; one-way draws/discards generally do **not** preserve uniform stationarity on the union of pile-capacity states. Keep those models separate from the fixed-capacity reversible theory.

## 12. From an explicit bound to a real cost certificate

For `s` exchange rounds and two piles with sizes `m, N-m`, denote by `e_s` the **proved** ideal full-deck error for the chosen starting assumption and let `t_i^L,t_i^R` be the numbers of binary riffles on each pile after round `i`. The coupling+telescope sufficient bound is

```
ε_cert = e_s + Σ_{i=1}^s
  [ choose(m,2)/2^(t_i^L) + choose(N-m,2)/2^(t_i^R) ].
```

This is an explicit `Rat` expression computable from small integers. The protocol is **certifiably feasible** for a threshold `ε` whenever `ε_cert≤ε`, with an independently named cost function. For equal `t` on both piles and all rounds, the constraint is just

`e_s + s [choose(m,2)+choose(N-m,2)]/2^t ≤ ε`.

For a fixed `s`, one can check a concrete `t` by `norm_num` without formalizing logarithms. If comparing different `t`, note that `t=22` failing this sufficient bound is *not* a lower bound on the actual mixing error.

A useful **surrogate optimization** for unequal pile sizes is budget allocation. Each extra binary riffle on pile/round `(i,p)` halves that term's error, reducing the bound by `A_(i,p)/2^(t_(i,p)+1)` where `A=choose(n_p,2)`. If every riffle has equal cost, greedily choose the next available riffle with the largest reduction; diminishing returns imply that the top successive marginal improvements respect each pile's prefix order. A finite exchange argument can certify the resulting **surrogate** minimizer within the explicitly defined action class. If costs differ, the greedy rule is not automatically optimal—use a finite dynamic program or exact enumeration over a bounded class.

Actual-TV optimality requires *lower* bounds on each competing protocol's TV (or exact evaluations), not just comparing conservative collision upper bounds. Keep **feasibility**, **surrogate-bound cost minimization**, and **actual physical optimum** separate (`CommanderCostedCertificate` already distinguishes them in prose).

## 13. Suggested proof dependency DAG, with fallbacks

```
Existing: generic subset exchange + A3/G4 + ideal macro TV
         |                                        \
         v                                         v
 literal position permutation          exact 3-step ideal rational
         |                                         |
 position swap -> membership                      |
         |                                         |
 literal swap -> perfect reset = rawExchange      |
         |                                         |
         +--------+-------------------+------------+
                  |                   |
          finite rank shuffle   collision-free -> uniform rank
                  |                   |
                  +--------+----------+
                           |
             same-swap two-world coupling
                           |
              row TV ≤ binomial collision bound
                           |
                finite hybrid telescope
                           |
          deterministic-start bridge (singleton count fiber)
                           |
              3-round TV ≤ 1/1000, t=23
                           |
         equivariance under all card relabelings
                           |
          every starting deck / every input law
                           |
               explicitly costed certificate
```

**Fallback A:** if generic free-action TV *equality* is difficult, use coupling plus TV contraction; never leave the numerical certificate blocked on isometry.

**Fallback B:** if list-to-permutation is expensive, build the label-lexicographic rank permutation directly and prove its list output matches `stableBuckets` only at the interface.

**Fallback C:** if `Dist.tv` unfolds `Fintype (Deck N)`, work at the `Finsupp`-support level or prove a universal coupling inequality; do not fight elaboration with `native_decide` on `99!` states.

**Fallback D:** if a formal generic double-coset type becomes hard, prove the cellwise finite bijections and the explicit histogram equivalence; the high-level quotient is mathematical interpretation, not required Lean infrastructure.

**Build order:** keep `FiniteDeck/` imports Commander-free; add small modules such as `FiniteDeck/LiteralSwapKernel`, `FiniteDeck/PilePermAction`, `GSRPermutation`, `GSRCoupling`, `FiniteDeck/MultiPile`, and `FiniteDeck/ReversibleQuotient` as *suggestions*, not required names. Run targeted `lake build` on each compiled bridge; only then wire the terminal F5 theorem. All existing F3/G4 results should be reused intact.

## 14. Definition of mathematical success

The campaign should ultimately prove statements for arbitrary finite `N` and finite sets of piles/categories, while retaining 99-card Commander as a **specialization and regression case**. The next meaningful success is not another valid `TV≤2` certificate. It is:

1. a literal deck-valued physical action that does not contain a hidden perfect reset;
2. a finite-GSR law on permutations (or equivalently on sorted position ranks);
3. a nonvacuous exact rational terminal TV bound for an explicitly finite protocol;
4. preferably a worst-case-start bound via card-relabeling equivariance;
5. an extensible multi-pile histogram quotient that subsumes two-color/two-pile counting; and
6. cost claims whose quantifiers clearly distinguish proven feasibility from optimized surrogate and true optimality.

The purpose of this guide is to supply the *change of representation* and the short mathematical proofs Qwen might not infer from the code alone. Prefer these lemmas over additional Commander-only numerical enumeration or another long bespoke orbit proof.
