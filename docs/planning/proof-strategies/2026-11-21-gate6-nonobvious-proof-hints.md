# November 21, 2026 — Non-obvious proof connections for Gate 6

**Read this first, then work in this order.** Assessment base: source commit `51423b0aefc8`. Companion dated assessment: `../reviews/2026-11-21-gate6-progress-mathematical-assessment.md`. These are mathematical *hints and proposed statement shapes*, **not compiled Lean code**. Existing declarations mentioned by name are source-visible; targets marked **PROPOSED** remain to be proved.

## The eight things worth recognizing immediately

1. The WHNF blocker in `collisionProb_le` is avoidable. **Define the bad event as a union of equal-label pair events** and do not touch `collision : Bool` in the new certificate. In addition, make the union-bound lemma polymorphic over **two different types**; its current signature is too narrow.
2. There is a **collision-free-free** construction of a *uniform* permutation coupled to the finite-GSR rank: introduce an independent uniform **tie-breaking permutation**. The tie-broken rank is uniform by simultaneous relabeling symmetry, whether or not labels collide. This is more robust in Lean than conditioning on the injective-label event.
3. Existing `rankEquiv` can build that tie-broken rank **without a new sorting implementation**. Conjugate the label array by the random tie-breaker, use `rankEquiv`, and compose back. The key equivariance identity is almost algebraic.
4. The pair-of-pile permutation action `WithinPileOrbit.fiberOrbit_equiv` and actual `LiteralSwapKernel.swapPerm` are already proved. **Do not rebuild them**. The distribution law should be the next layer.
5. A state-independent random **position permutation** has uniform decks stationary and is automatically equivariant under all **card relabelings**. Prove the right-convolution formula once, not state-by-state.
6. The 41-step Dobrushin theorem begins at a macro **fiber-uniform** law. For one ordered segregated deck, use the singleton extreme membership; for arbitrary ordered decks, use the colorblind right-convolution theorem. Do not conflate those steps.
7. The finite-GSR TV bound can be proved with **one source of randomness for both worlds**, then the generic inequality `TV(push f, push g) ≤ P(f≠g)`. No `max'` over `Deck 99` is required.
8. After the per-round bound, the terminal theorem is **already arithmetic**: `q3 + 3*δ1 < 1/1000` is proved. Avoid any new spectral or 99!-enumeration development on the critical path.

---

## 1. Delete the *hard step* by changing the bad-event definition

Take `n : Nat`, `a : Nat` with `0<a`. Let `Ω := Fin n → Fin a`, and for `i<j` let

\[
E_{ij}=\{\ell\in\Omega : \ell(i)=\ell(j)\},\qquad
B=\bigcup_{i<j}E_{ij}.
\]

`B` is **exactly** the set of non-injective label arrays. But to get the probability bound we do not even need that equality until we connect to sorting.

**PROPOSED definitions (Lean shape):**

```lean
noncomputable def badLabels (n a : Nat) : Finset (Fin n → Fin a) :=
  (ijPairs n).biUnion (fun p => pairEqSet n a p.1 p.2)

-- Unlike the older Bool/Nonempty definition, the following is now just
-- a sum of the cards of sets and has no nested function-valued witness.
theorem badLabels_card_le (n a : Nat) (ha : 0 < a) :
    (badLabels n a).card ≤ (n.choose 2) * a ^ (n - 1) := by
  ...
```

**Module/namespace note:** `rankEquiv`, `keyNat_lex`, and `keyBelow` are declared in namespace `Shufflemath` (source file `GSRF42.lean`), **not** a namespace `GSRF42`. The notation below assumes `namespace Shufflemath` or `open Shufflemath`; use `Shufflemath.rankEquiv` when outside it. Likewise, `ijPairs`, `pairEqSet`, and their wrapper cardinality theorems currently live in `Shufflemath._ProbeGate6Collision`, while the reusable subtype `cardPairEqSet` theorem lives directly in `Shufflemath` in `Gate6FiniteGSR.lean`. A new production file should **extract or reprove the small pair-index definitions and helper cardinality lemmas** (or move the proved material from the probe), importing the existing Gate 6 counting theorem; do not import an unresolved probe with `sorry` into production.

First fix the *type* of the already-compiled union bound. Current `_ProbeGate6Collision.biUnion_card_le_sum` uses one `X` for both the indexing `Finset` and the event elements. It **cannot** consume `ijPairs : Finset (Fin n × Fin n)` together with `pairEqSet : Finset (Fin n → Fin a)`.

Change only the binders, retaining Qwen's existing proof by induction:

```lean
-- PROPOSED signature. `I` indexes events, `X` contains event members.
theorem biUnion_card_le_sum
    {I X : Type*} [DecidableEq I] [DecidableEq X]
    (s : Finset I) (f : I → Finset X) :
    (s.biUnion f).card ≤ s.sum (fun i => (f i).card) := by
  -- Reuse the current induction proof; no union/cardinality mathematics changes.
  ...

theorem card_le_biUnion_sum
    {I X : Type*} [DecidableEq I] [DecidableEq X]
    (s : Finset I) (f : I → Finset X) (A : Finset X)
    (h : A ⊆ s.biUnion f) :
    A.card ≤ s.sum (fun i => (f i).card) := by
  exact (Finset.card_mono h).trans (biUnion_card_le_sum s f)
```

Or use a suitable generic Mathlib `card_biUnion_le` lemma if one is already in scope. The point is the **two-type** formulation, not the chosen proof.

With `badLabels` *defined as the union*, its cardinal estimate begins with

```lean
change ((ijPairs n).biUnion (fun p => pairEqSet n a p.1 p.2)).card ≤ _
calc
  _ ≤ (ijPairs n).sum (fun p => (pairEqSet n a p.1 p.2).card) :=
      biUnion_card_le_sum _ _
  _ = (n.choose 2) * a ^ (n - 1) := by
      -- sum_congr + cardPairEqSet + cardIjPairs
      ...
```

For any `p∈ijPairs`, `p.1<p.2`, so `p.1≠p.2` **and `1<n`**; use those two facts to apply `cardPairEqSet`. No separate n≥2 branch is needed for *this* finite sum, because the index set is empty if n<2. The denominator comparison splits only at `n=0`; for `n≥1`, `a^n = a*a^(n-1)`. When `n=0`, `B=∅` and the probability is zero.

**PROPOSED headline:**

```lean
theorem badLabels_uniform_bound (n a : Nat) (ha : 0 < a) :
    ((badLabels n a).card : Rat) / (a ^ n : Rat) ≤
      (n.choose 2 : Rat) / a := by
  ...
```

Proof order: `cardFnFinA` (already proved), `badLabels_card_le`, rational casting/division/cancellation. Keep the Nat cardinal bound separate from rational arithmetic. `a^n` is positive by `ha`; avoid unfolding `Finset.univ : Finset (Fin n→Fin a)` in the final arithmetic.

**Finally, not before:**

```lean
-- PROPOSED lemma for the coupling. A short pair-order argument, not Bool WHNF.
theorem not_mem_badLabels_iff_injective (ell : Fin n → Fin a) :
    ell ∉ badLabels n a ↔ Function.Injective ell := by
  ...
```

If `ell` is not injective, take `i≠j` with equal labels and sort the pair by `<` (swap it if needed); then `ell∈pairEqSet i j⊆B`. Conversely, a member of `B` gives `i<j` with equal labels. Use `Finset.mem_biUnion` and `Finset.mem_filter` **at that pair only**. No giant `Nonempty` predicate. The prior `collisionSet`/`collision` may remain for historical use, but make `badLabels` the canonical event for Gate 6.

## 2. A stronger insight: manufacture a uniform permutation by random tie-breaking

Previous guidance suggested proving that `rankEquiv ell` is uniform **conditional** on `ell` having no collisions. That is correct, but conditional distributions have difficult edge cases (`a<n` gives a zero-probability event, and renormalizing on a subtype can elaborate poorly).

There is a different construction that bypasses conditioning completely.

Let `ell : Fin n → Fin a` be uniformly random and let `σ : Equiv.Perm (Fin n)` be an **independent uniform random permutation**. Use `σ(i)` as a tie-break rank for card `i`. Sort by the lexicographic key `(ell i, σ i)` rather than `(ell i, i)`. This is a genuine permutation, since the second coordinates `σ i` are all distinct. Call its original-to-final rank `T(ell,σ)`.

**Key fact A:** `T(ell,σ)` is *exactly uniformly distributed* on `Equiv.Perm (Fin n)` **for every a≥1**. This does not assert that the finite-GSR rank is uniform; only the randomized-tie-break rank is uniform.

Why? Both the random array `ell` and the random permutation `σ` have distributions invariant under simultaneous precomposition by an arbitrary `θ∈Sym(n)`:

\[
(\ell,\sigma)\mapsto(\ell\circ\theta,\sigma\circ\theta).
\]

The sorted rank is equivariant under this operation:

\[
T(\ell\circ\theta,\sigma\circ\theta)=T(\ell,\sigma)\circ\theta.
\]

Therefore its distribution is invariant under **all right multiplications**. Those act transitively on `Sym(n)`, so its mass is constant. Total mass one forces the uniform distribution. This proof uses no count of injective arrays and no probabilities of individual permutations.

**Key fact B:** If `ell` is injective, tie-breaking is irrelevant and

\[
T(\ell,\sigma)=R(\ell),
\]

where `R(ell)` is Qwen's existing `rankEquiv` in `Shufflemath/GSRF42.lean` (original position → sorted rank). Hence the two coupled permutations disagree only if `ell∈badLabels`.

### 2.1 Reuse `rankEquiv` exactly; do not write another sorter

This is the non-obvious algebraic identity that makes the construction practical.

Define the tie-broken permutation *using the existing stable-key rank*, after reindexing the array by `σ⁻¹`:

\[
\boxed{T(\ell,\sigma)=R(\ell\circ\sigma^{-1})\circ\sigma.}
\]

In Lean's `Equiv.trans` convention (`e.trans f` applies `e` and then `f`), the statement shape is:

```lean
-- PROPOSED, for 0<n. Keep proof of all orientation facts separate.
noncomputable def tieRank (n a : Nat) (hn : 0 < n)
    (ell : Fin n → Fin a) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  σ.trans (rankEquiv n a hn (fun j => ell (σ.symm j)))
```

This formula means: temporarily rename card index `i` as `σ(i)`, stable-sort in the renamed index order, and return the rank of the original card. A card's tie key in this renamed order is `σ(i)`, as desired.

Now simultaneous precomposition becomes **almost definitional**:

\[
(\ell\circ\theta)\circ(\sigma\circ\theta)^{-1}
 =\ell\circ\sigma^{-1}.
\]

Therefore

\[
T(\ell\circ\theta,\sigma\circ\theta)=T(\ell,\sigma)\circ\theta.
\]

The new rank's complicated arithmetic does **not** need to be unfolded to prove this equivariance. In Lean, prove the reindexed label-function equality by `funext` + the inverse equivalence laws; rewrite that equality, then use `Equiv.trans_assoc` (or `Equiv.ext` and `Equiv.trans_apply`) to finish. **Fix composition orientation with two- or three-card test cases rather than guessing `σ` versus `σ.symm`.** The reference `stableBuckets_eq_orderByNewPosition` applies `rankEquiv.symm` to produce the output list, so the action law must respect that orientation.

### 2.2 Why the tie-broken permutation is uniformly distributed

Let `Ω := (Fin n → Fin a) × Equiv.Perm (Fin n)`. Use the uniform law on `Ω`, equivalently the independent product of the uniform label law and a uniform tie-breaker. For each `θ`, the map

```lean
(ell, σ) ↦ ((fun i => ell (θ i)), θ.trans σ)
```

is a bijection of `Ω`, so it preserves `GSR.uniformDist Ω` by the existing `GSR.map_bijective_uniformDist`. Under `tieRank`, this map becomes right multiplication by `θ`. Conclude right invariance of the `tieRank` pushforward.

**PROPOSED generic lemma worth isolating:** If `ν : Dist (Equiv.Perm α)` is invariant under every right multiplication and `α` is finite, then `ν = GSR.uniformDist (Equiv.Perm α)`. Proof: any `σ,τ` satisfy `τ=σ∘(σ⁻¹∘τ)`; hence point masses are all equal, and normalization determines the common value. It is a finite-group fact, independent of GSR.

A simpler but slightly less reusable route: for each output `ρ`, use a precomposition bijection of the source `Ω` to identify the fibers of `tieRank` at `ρ` and at the identity. All fibers have equal cardinality; `GSR.map_bijective_uniformDist` gives equal pushforward masses. **No `n!` numerical evaluation** is required.

### 2.3 Why `tieRank = rankEquiv` for injective labels

We need only one direct rank-compatibility lemma, and source `GSRF42` already has its ingredients:

```lean
-- Under Function.Injective ell, the flattened-key comparison reduces to
-- the pure label order; the original-index tie breaker never fires.
lemma keyBelow_eq_labelBelow (ell : Fin n → Fin a)
    (hinj : Function.Injective ell) (i : Fin n) :
    keyBelow n a ell i =
      (Finset.univ : Finset (Fin n)).filter (fun j => ell j < ell i) := by
  ...
```

Use `keyNat_lex` (in namespace `Shufflemath`): `keyNat ell j < keyNat ell i` iff `(ell j < ell i) ∨ (ell j=ell i ∧ j<i)`. Injectivity collapses the second disjunct (when j≠i), and if j=i both comparisons are false.

For any σ, the pure-label lower set for reindexed labels at `σ i` is the image under `σ` of the lower set for `ell` at `i`. An image under a permutation preserves cardinality. `rankVal` is precisely that cardinality, so

\[
\operatorname{rankVal}(\ell\circ\sigma^{-1},\sigma(i))=
\operatorname{rankVal}(\ell,i).
\]

Apply `Equiv.ext` to `tieRank` and `rankEquiv`. That proves Key fact B without any distribution algebra. For `n=0`, the permutation group is trivial and the corresponding law is already uniform; split this degenerate case outside the rank construction.

**Why this is better than the original approach:** The conditional-on-injectivity proof needs to prove the distribution of `R(ell)` on a restricted probability space and then handle the zero-event case. Random tie-breaking gives a *uniform output for free by symmetry*, with a pointwise equality under the good event. This is a stronger reusable coupling theorem and removes that whole source of dependent-subtype probability proofs.

**Sanity checks performed outside Lean:** enumerating all label arrays and tie-breaking permutations for `(n,a)=(3,2),(3,4),(4,2),(4,5)` gives equal counts for every output rank, including `a<n`; enumerating injective labels gives equal rank fibers when `a≥n`. These checks motivate the proof but are not Lean evidence.

### 2.4 The standard alternative, if tie-breaking formalization costs too much

On the injective-label set `G`, show

\[
R(\ell\circ\theta)=R(\ell)\circ\theta,
\]

and that precomposition preserves the uniform law on `G`. The rank-fiber cardinalities are all equal by transitivity, so the conditional rank law is uniform if `G` is nonempty (`n≤a`). If `n>a`, the collision probability is one and `choose(n,2)/a≥1` (for `a>0`), so `TV≤1` is sufficient. This is mathematically sound but is less clean in Lean than the independent tie-breaking coupling.

---

## 3. One generic inequality finishes the probabilistic part

Let `ρ : Dist Ω`, and let `F,G : Ω → X` be deterministic maps into a finite type. Then

\[
\boxed{\mathrm{TV}(F_*\rho,G_*\rho)\le\Pr_\rho[F\ne G].}
\]

This is a same-random-source **coupling inequality**. To avoid a `max'` over all decks, prove it once for abstract `Ω,X` (or use `TotalVariation.tvFinsupp`, which only traverses finite supports).

A source-friendly target shape is:

```lean
-- PROPOSED: actual theorem may use Dist.tv or tvFinsupp.
theorem tv_maps_le_mismatch
    {Ω X : Type*} [Fintype Ω] [Fintype X]
    (rho : Dist Ω) (F G : Ω → X) :
    Dist.tv (rho.map F) (rho.map G) ≤
      Finset.univ.sum (fun w => if F w = G w then 0 else Dist.mass rho w) := by
  ...
```

Mathematical proof from TV's event characterization: for any event `A⊆X`,

\[
|\Pr(F\in A)-\Pr(G\in A)|\le \Pr(F\ne G).
\]

Or use L1 pointwise: the difference of `F` and `G` pushforwards is the sum of signed contributions from **mismatched** samples; matched contributions cancel. Each mismatch contributes at most two units to L1; multiplying by `1/2` yields its mass. Both proofs are finite and do not depend on the cardinality of `X`. The source already has `Dist.tv` and support-based `Dist.tvFinsupp` plus `TotalVariation.mixtureTV_le`. Do the proof generically, and **do not unfold it at `X=Deck 99`**.

Apply it to the uniform joint law of `(ell,σ)`, with

- `F(ell,σ)=rankEquiv ell` (finite GSR; ignores σ),
- `G(ell,σ)=tieRank ell σ` (exactly uniform).

They agree if `ell ∉ badLabels`, so

\[
\mathrm{TV}(\nu_{n,a},U_{S_n})
 \le \Pr(\ell\in B)
 \le \binom n2/a.
\]

This theorem holds for any `n` and `a>0`, including `a<n`, **without conditioning on a zero-probability event**. For the `n=0` case, prove the trivial group-uniformity directly.

## 4. Put the rank law onto any ordered pile WITHOUT reopening list sorting

`GSRPermutationLaw.idealShuffle_canonical_eq_permLaw` currently speaks only about `List.finRange n`. The practical bridge is that a current ordered pile is a list of `n` **distinct** cards, indexed by their **positions**. Let `d : Fin n → Card` be its position-to-card bijection onto its current card set. For a label assignment `ell : Card → Fin a`, put `ellPos := ell ∘ d`.

The deterministic identity needed is

\[
\operatorname{stableBuckets}(a,\ell,[d(0),\dots,d(n-1)])
 = [d(R(\ell\circ d)^{-1}(0)),\dots,d(R(\ell\circ d)^{-1}(n-1))].
\]

**Proof shortcut:** first prove `stableBuckets` commutes with injective renaming (`List.map` distributes over `List.filter` and `List.flatMap`). Then apply the **already-proved canonical** `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition`, followed by `List.map_map`. This is much smaller than re-proving stable sorting for arbitrary lists.

Uniform card labels pulled back by a bijection `d` are uniformly distributed as position labels. Reuse `GSR.map_bijective_uniformDist` with reindexing of `Fin n→Fin a`; for a pile occupying a subset of an `N`-card deck, restrict to that pile and identify it with `Fin n` first. **The label distribution must be invariant under reindexing.** Do not silently assume label choices by card identity and by current position are definitionally equal.

If the physical implementation instead *samples labels directly by local pile positions*, the state-independent position-permutation law is its definition, and this card-label bridge is needed only for compatibility with the older `GSR` presentation.

**Twenty-three binary riffles:** For the first certificate it is acceptable to model one `2^23`-label inverse-GSR permutation; source `GSR.idealShuffle_comp` and `productLabelShuffle_uniform_eq_ideal` provide the induction that identifies it with 23 independent binary inverse riffles. Prove that equivalence as a *separate theorem* rather than interleaving it with the finite-deck TV argument. Do not silently claim the physical protocol performs 23 riffles until that bridge is part of the theorem/dependency chain.

## 5. Assemble the actual literal-swap + finite-local protocol as a law on positions

Current source already has:

- `FiniteDeck.LiteralSwapKernel.swapPerm` and `swapPerm_membership_eq`;
- `FiniteDeck.WithinPileOrbit.embed_m`, `act_d`, `fiberOrbit_equiv`;
- `GSRPermutationLaw.gsrPermutationLaw` on each `Equiv.Perm (Fin n)`.

**Do not construct another deck-space kernel by summing over `Deck 99` first.** Construct a single law `ρRound` on position permutations, then define the row from a deck `d` by pushforward:

\[
K(d)=\operatorname{Law}(d\circ\tau),\qquad \tau\sim\rho_{\mathrm{Round}}.
\]

For each round:

1. draw size-`k` position subsets `L⊆Fin m`, `R⊆Fin(N-m)` uniformly;
2. fix any bijection between the two selected *position-subtypes* (the choice is independent of card identities); let `τ_swap=swapPerm L R b`;
3. independently sample local permutation pair `(π_L,π_R)` from the finite GSR laws; let `τ_local=embed_m π_L π_R`;
4. set `τ_round = τ_swap ∘ τ_local` in **execution order** (adjust `Equiv.trans` syntax so deck becomes `d ∘ τ_swap ∘ τ_local`).

The **ideal** reference law `ρIdeal` uses the **same swap choice**, but its local permutations are independently uniform on both symmetric groups.

**Subtlety:** Qwen's `swapPerm_membership_eq` guarantees the *membership* does not depend on pairing, but the actual ordered deck does. Fix one measurable/deterministic pairing rule on every `(L,R)`, e.g. use a cardinality equivalence between their subtypes. Do not assert pairing independence of the finite-deck distribution before the subsequent local-randomization argument justifies it. For the ideal *perfect-local* kernel, any fixed pairing leads to the same row law; for finite local GSR the order after swapping can matter.

A distribution on finite positions is sufficient: `K d := rhoRound.map (fun τ => τ.trans d)` under Lean's `Equiv.trans` convention (`(τ.trans d) x = d(τ x)`). It is a **right random walk** on the permutation group. This is also the cleanest definition of a physical *colorblind* shuffling protocol.

## 6. Reuse the orbit equivalence for the local error—now it is proved

The source's `WithinPileOrbit.fiberOrbit_equiv` is an equivalence

\[
S_m\times S_{N-m}\ \simeq\ \{e : \mathrm{Deck}(N)\mid
     \mathrm{membership}(e)=\mathrm{membership}(d)\}.
\]

It is more than enough to move product permutations into a full-deck local-kernel row. For each *fixed* post-swap deck `d`, applying `(π_L,π_R)` via `act_d` is a deterministic map. TV contracts under that map; in fact it is a bijection onto the membership fiber, so an exact TV isometry is available if eventually useful.

Let `ν_L,ν_R` be finite GSR permutation laws, and `U_L,U_R` uniform. Then

\[
\begin{aligned}
\mathrm{TV}(\mathrm{localFinite}(d),\mathrm{localIdeal}(d))
&\le \mathrm{TV}(\nu_L\otimes\nu_R,U_L\otimes U_R)\\
&\le \mathrm{TV}(\nu_L,U_L)+\mathrm{TV}(\nu_R,U_R)\\
&\le \binom{m}{2}/a_L+\binom{N-m}{2}/a_R.
\end{aligned}
\]

All three steps already have generic infrastructure:

- pushforward/TV contraction (`TotalVariation.kernel_contraction` or `kernel_apply_lipschitz`),
- `TotalVariation.distProductFinsupp_tv_subadditive` (Fintype-free),
- the per-pile rank coupling from §§2–3.

The **full-deck** codomain appears only as a symbol in generic lemmas. Do not `simp [Dist.tv]` at `Deck 99` or instantiate `kernelDiscrepancy`/`dobrushinCoeff` there.

Average the fixed-post-swap bound over the *same random `L,R`* in both kernels. By convexity/`mixtureTV_le`, the result is row-wise:

\[
\boxed{\forall d,\quad\mathrm{TV}(K(d),J(d)) \le
      \delta_1=\frac{\binom{50}{2}+\binom{49}{2}}{2^{23}}
      =\frac{2401}{8388608}.}
\]

This argument is **independent of the input ordering**, even though the actual output distribution is not.

**A possible alternative:** use the *joint source* consisting of `(L,R,ell_L,σ_L,ell_R,σ_R)`, with equal swap choices and the tie-break couplings of §2. Both deck outputs agree unless a left or right label collision occurs. Apply §3 once at the full-deck level; the mismatch probability is bounded by the sum of two bad-event probabilities. This alternative avoids proving product-TV lemmas but still needs a uniform tie-broken local permutation and the common-swap model.

## 7. The starting distribution: fix the quantifier, then strengthen it

`FiniteDeck.BLDisintegration.two_physical_perfect_exchanges_uniform_deck` begins from a deck law **uniform inside one marked-count macro fiber**, not `Dist.pointMass d0`. This is an actual mathematical distinction, not a Lean nuisance.

**Seven-line conceptual bridge for the segregated reference deck** (`N=99, m=r=50`):

1. The macro count `x0=50` contains **one** membership: the set of all 50 marked cards in the left pile.
2. `U_x0` is uniform on the `50!·49!` orderings of that membership.
3. For the ideal physical round `J = swap + perfect local reset`, its output row depends only on the initial **membership** (the exchange choices are uniformly selected positions and local reset forgets the resulting order). This is exactly the kernel factorization Qwen has already proved in `FiniteDeck` / `PhysicalExchangeReduction`.
4. Thus `J(d0)=U_x0 J` for any **ordered** segregated deck `d0`.
5. Apply `J` twice more to deduce `J^3(d0)=U_x0 J^3`.
6. Use the existing three-round ideal macro/full-deck TV identity: `TV(J^3(d0),Udeck)=q3`.
7. Combine with the `3δ1` perturbation and `gate6_headline_lt_thousandth`.

**Only after that:** Prove `K` is a state-independent law on **position** permutations as in §5. For any two decks `d,d'`, put `g=d'∘d⁻¹` (a relabeling of **card identities**); then `d'=g∘d`. Because all random choices are position-based,

\[
K(g\circ d)=g_*K(d),\qquad
K^t(g\circ d)=g_*K^t(d).
\]

The uniform full-deck law is invariant under the bijection `e↦g∘e`, and TV is invariant under common bijective pushforward. Consequently

\[
\boxed{\mathrm{TV}(K^t(d),U_{\mathrm{Deck}})
      =\mathrm{TV}(K^t(d'),U_{\mathrm{Deck}})}
\]

for **every pair of deterministic ordered starting decks**. Convexity then extends the upper bound to *any initial distribution*.

**This provides the genuinely worst-case-start theorem.** The currently proved `DobrushinDecay99.physicalExchange_decay_41_lt_thousand` does not say this, because it starts from a count-fiber uniform law. No new macro spectral computation is needed for the stronger universal three-round statement once the position-permutation model and fixed-reference bound exist.

**Sanity counterexample for illicit shortcuts:** For `N=4,m=r=2,k=1`, initially left membership `{0,2}` and marked set `{0,1}`, the next count-one memberships are only `{1,2}` and `{0,3}`, while the full count-one fiber has four memberships. Hence an arbitrary ordered deck is **not** in general equivalent to a uniform macro fiber before the first swap. Do not claim the initial law is fiber-uniform by definition.

## 8. Terminal certificate: no further combinatorics

The source proves

\[
q_3=\frac{172379525755689183991816396516567920780192827919620440221147749}
 {6691837923759692633601708022649918108038775216019298375918637677488},\quad
\delta_1=\frac{2401}{8388608},\quad q_3+3\delta_1<10^{-3}.
\]

Exact rational checks (outside Lean):

- `q3 ≈ 0.0000257596683780`;
- `δ1 ≈ 0.0002862215042114`;
- `q3 + 3δ1 ≈ 0.0008844241810123`;
- slack below `0.001 ≈ 0.0001155758189877`.

Let `J` be the ideal literal-swap+perfect-local kernel and `K` the actual finite one. Prove the generic **unweighted three-step** telescope from `∀d, TV(K d,J d)≤δ1`:

\[
\mathrm{TV}(K^3(d_0),J^3(d_0))\le 3\delta_1.
\]

Use `FiniteKernel.apply` and `Dist.tv_triangle`, with TV contraction under a common suffix. Existing `TelescopeF5` contains unweighted/length-free infrastructure; avoid applying a bound of `TV≤3` (vacuous) or fully unfolding its max-over-Deck discrepancy. The end is one `calc` chain:

\[
\mathrm{TV}(K^3(d_0),U)
\le \mathrm{TV}(K^3(d_0),J^3(d_0))
       +\mathrm{TV}(J^3(d_0),U)
\le 3\delta_1+q_3<10^{-3}.
\]

**Critical theorem statement:** it must quantify the *actual concrete* `K` (chosen position pairs, pairing rule, local GSR), an ordered input deck `d0`, **uniform full-deck target**, three rounds, and the strict upper bound. The upper bound on `q3+3δ1` alone is not the certificate. Once this theorem compiles, separately prove the all-start corollary of §7 and cost it.

## 9. What comes after this is generic finite-deck mathematics

The orbit/coset viewpoint should become the reusable theory, not Commander special code. For fixed pile capacities `(n_i)` with total `N`, complete orderings within a fixed allocation have cardinality `∏_i n_i!`. For categories with populations `r_j` and count table `x_ij` (row sums `n_i`, column sums `r_j`), the number of complete **ordered decks** with that histogram is

\[
\frac{\bigl(\prod_i n_i!\bigr)\bigl(\prod_j r_j!\bigr)}
{\prod_{i,j}x_{ij}!}.
\]

This follows by first allocating named cards of each category to piles (multinomial count per category), then ordering each pile. It is a finite double-coset count in disguise. The stationary histogram distribution under any **symmetric, category-blind** fixed-capacity exchange scheme is this cardinality divided by `N!`, provided that scheme actually induces a strongly lumpable histogram quotient. Avoid claiming reversibility for ordered compositions of asymmetric elementary kernels.

For games with hands/draw/discard piles, a later dealing kernel may be modeled as a map of the ordered uniform deck; by data processing, **any full-deck TV bound propagates to every dealt hand** with no new counting proof. Drawing/discarding with changing capacities requires a different state space and should not block the finite-GSR certificate.

## 10. Short next-commit script for Qwen (not shell commands)

**First proof batch:** Generalize `biUnion_card_le_sum` to `{I X}`, add `badLabels := ijPairs.biUnion pairEqSet`, and prove `badLabels_uniform_bound` (all `n`, `a>0`) with *no* references to the old `collision : Bool` in the theorem proof. Keep all cases structural and avoid increasing global heartbeats. Compile only the new focused module.

**Second batch:** Define `tieRank` from the existing `rankEquiv` as in §2.1. Prove (i) equivariance under simultaneous precomposition and (ii) agreement with `rankEquiv` on injective labels. Show the uniform law of `tieRank` by right-translation symmetry, not by enumerating permutations. Prove the one-pile TV bound via same-source coupling.

**Third batch:** Construct the state-independent deck-position law using `swapPerm`, `embed_m`, and the now-defined GSR rank law; prove the local-product row error and the full physical-vs-perfect one-round error ≤`δ1`.

**Fourth batch:** Move the count-fiber ideal theorem to one segregated *ordered* input, telescope three rounds, use `gate6_headline_lt_thousandth`, and finally prove relabeling equivariance to upgrade to all deterministic starting decks.

**Stop conditions:** A speculative Lean declaration is *not* done until it compiles. Do not claim a theorem from a numeric Python check; do not claim the 41-step result covers every starting deck; do not replace the literal physical kernel with `localLift`. If a route fails, prefer the alternate conditional-injection rank proof or pushforward-TV method above, not another independent count of 99-card objects.
