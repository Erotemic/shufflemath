# Deep hints: convolution, subgroup orbits, and first-round smoothing

Date: 2026-11-23. Source snapshot: `1587085`. Companion assessment: `../reviews/2026-11-23-gate6-progress-and-proof-validity.md`.

**Audience:** Qwen, continuing the Lean formalization of arbitrary finite-deck shuffling. The purpose here is to do the mathematical design work in advance: identify the right invariant, the strongest already-proved bridge, and exactly which intermediate theorem will unlock the next one. All displayed Lean signatures are *proposed statement shapes*, not independently compiled declarations. Reconcile typeclass obligations and namespaces with the source before landing production code. Do not modify historical reviews.

## Executive direction

The difficult part is no longer collision counting. The repo has a single-pile GSR-to-uniform TV bound, a two-pile deck-permutation TV bound, the literal position swap, the exact ideal macro TV, and generic TV invariance. The missing object is a **probability law on physical position permutations**, with a *group action* applying that law to the current deck.

Use the following chain of maps instead of a large concrete deck kernel:

    choice of swap positions S  ------> position permutation s
    finite/ideal pile shuffles L ---> position permutation h
             independent product ----> p = h.trans s
                         n folds ----> convolution power W^*n
                   starting deck d ---> pushforward p |-> p.trans d

At no point is it necessary to enumerate all 99! decks or sum over 99! x 99! deck pairs. The only combinatorial counts are exchange-choice counts, the sizes of within-pile permutation groups, and the 50-state Bernoulli-Laplace chain.

Three themes here are easy to miss:

1. **A state-independent law of random *position permutations* is good; a state-independent law of *output decks* is wrong.** The noise distribution can be fixed and used at every round, but it must act on the input deck.
2. **Convolution gives the finite-vs-ideal telescope on the permutation laws themselves.** This bypasses the huge `kernelDiscrepancy` over the deck state space, even if a generic rowwise-TV theorem is available.
3. **Relabeling does not bridge point-start to fiber-uniform-start.** The first ideal round from a segregated deck washes out its within-pile order, and that is the missing bridge to the already-proved exact `q3` theorem.

## A. The right group action (and the composition orientation)

Define `D_N = Equiv.Perm (Fin N)` as a bijection `position -> card identity`. For a position permutation `p : D_N` and an ordered deck `d : D_N`, use

    act(p,d) := p.trans d.

Thus `act(p,d)(i)=d(p(i))` (the card at new position `i` was at old position `p(i)`). A physical swap `s` followed by a local reorder `h` produces

    act(h,act(s,d)) = h.trans (s.trans d)
                    = (h.trans s).trans d.

So the *combined* position permutation is `h.trans s` (Lean `Equiv.trans` applies its left argument first). In particular, an expression such as `g * s` is NOT an adequate specification until `Equiv.Perm.mul_apply` has been checked against this equation.

Proposed generic definitions (scheme, minor elaboration fixes may be necessary):

```lean
namespace Shufflemath

noncomputable def actionKernel (N : Nat) (W : Dist (FiniteDeck.Deck N)) :
    FiniteKernel (FiniteDeck.Deck N) (FiniteDeck.Deck N) :=
  fun d => W.map (fun p => p.trans d)

noncomputable def physicalNoise (N : Nat)
    (S L : Dist (FiniteDeck.Deck N)) : Dist (FiniteDeck.Deck N) :=
  (distProductFinsupp S L).map (fun z => z.2.trans z.1)

-- use actionKernel N (physicalNoise N swapLaw rhoFinite)
-- and actionKernel N (physicalNoise N swapLaw rhoIdeal)
```

`_ProbeGate6Fin2.lean` already contains `canonicalPairing`, `swapLaw`, and the two local deck-permutation laws. Reuse their working ingredients, but **not** its definitions `finiteRound := fun _ => fullRoundFinite` and `idealRound := fun _ => fullRoundIdeal`; those are constant-output kernels and do not model three rounds. `GSRGate6Telescope` has the same problem and explicitly calls its mixing hypothesis false.

A tiny deterministic identity is the first checkpoint:

```lean
-- schematic theorem; prove by Equiv.ext and simp [Equiv.trans_apply]
act (h.trans s) d = act h (act s d)
```

The displayed equation has the correct order: `h.trans s`, **not** `s.trans h`. Its two sides both evaluate to `d ∘ s ∘ h`. Prove this with `Equiv.ext`/`Equiv.trans_apply` before using the composition law inside the distributional proof; a concrete four-card test is also useful for catching a reversed convention.

## B. The one lemma that lets you ignore 99! pair distributions

The repository already provides all needed analytic ingredients, with finite *support* rather than global `Finset.univ`:

- `Finite.distProductFinsupp`
- `TotalVariation.tvFinsupp`
- `TotalVariation.distProductFinsupp_tv_subadditive`
- `TotalVariation.kernel_apply_lipschitz`
- `GSR.apply_deterministic`
- `TotalVariation.tv_eq_tvFinsupp` (bridge when the type is a `Fintype`)
- `GSRDeckRound.rhoRoundTransport_le_twoPile` / `oneRoundDeckTV_le_delta1`

A generic deterministic pushforward cannot increase support-TV:

    tvFinsupp(mu.map f,nu.map f) <= tvFinsupp(mu,nu).

**Proposed Lean strategy:** rewrite `mu.map f` as `FiniteKernel.apply mu (FiniteKernel.deterministic f)` using `GSR.apply_deterministic`, then use `kernel_apply_lipschitz`. This is a lemma for arbitrary types with `DecidableEq`, **not** a lemma specific to `Equiv.Perm (Fin 99)`.

A common factor cancels from the *upper bound*:

    tvFinsupp(S x F, S x I)
      <= tvFinsupp(S,S)+tvFinsupp(F,I)
       = tvFinsupp(F,I),

where `x` is `distProductFinsupp`. Apply pushforward contraction under `(s,h) |-> h.trans s`:

    tvFinsupp(physicalNoise(S,F),physicalNoise(S,I))
      <= tvFinsupp(F,I).

From the existing numerical specialization (only after the generic proof), obtain

    tvFinsupp(W_F,W_I) <= delta1 = 2401/8388608.

No new collision proof, no new sorting equality, no explicit product-mass calculation. The earlier 2026-11-22 hints already supply the support-TV rowwise route; the new suggestion is to keep `W_F` and `W_I` as laws on the **position-permutation group** throughout all rounds.

**Do not expand `Dist.tv` to `vectorTV` on `Perm(Fin 99)`**. Lift the GSR one-pile `Dist.tv` estimate into `tvFinsupp` using `tv_eq_tvFinsupp` with *symbolic* N,m,a binders. Keep this conversion as its own theorem; instantiate 99,50,2^23 only at the final numerical bound.

## C. More powerful shortcut: telescope by convolution, not by a full-deck Markov kernel

Let `G` be any finite group of position permutations (more precisely a type with decidable equality and the required composition operation), and let `mu,nu : Dist G`. Define the convolution compatible with `act` as follows:

```lean
-- schematic; first sampled p, then sampled q
noncomputable def conv (mu nu : Dist (FiniteDeck.Deck N)) :
    Dist (FiniteDeck.Deck N) :=
  (distProductFinsupp mu nu).map (fun z => z.2.trans z.1)
```

The critical one-line inequality (all types symbolic) is

    tvFinsupp(conv(mu,nu), conv(mu',nu'))
      <= tvFinsupp(mu,mu') + tvFinsupp(nu,nu').

It follows immediately from product subadditivity and pushforward contraction. In particular, convolution with an unchanged factor is nonexpansive on either side.

Define `powConv W 0 := pointMass (Equiv.refl _)`, and `powConv W (t+1) := conv (powConv W t) W`. Then induction on `t` and the preceding inequality give

    tvFinsupp(powConv W_F t, powConv W_I t)
      <= t * tvFinsupp(W_F,W_I)
      <= t * delta1.

At `t=3`, this is the entire physical-vs-ideal perturbation bound `<= 3*delta1`. The proof is the ordinary telescoping inequality in the **noise group**, never `max'` over all deck states. Prefer this over the `kernelDiscrepancy` and `compList` route in `GSRGate6Telescope.lean`.

### Show that convolution really describes sequential shuffles

Prove *one* general associativity/compatibility lemma, before induction:

    act(q,act(p,d)) = act(q.trans p,d).

Then use `Dist.map_map`, `Dist.join`, and the finite-product coupling to obtain

    run (actionKernel W) t (pointMass d)
       = (powConv W t).map (fun p => act(p,d)).

This bridge is **essential**. Without it, a theorem about `powConv W` is not automatically a theorem about the specified sequential physical process. The proof should be generic in N, not a construction of a 99! by 99! transition matrix.

### Free all-start transport, once the action kernel is correct

For fixed `d`, `p |-> p.trans d` is a bijection on the permutation group. Consequently,

    tv( (powConv W t).map (fun p => p.trans d), UniformDeck )
       = tv(powConv W t, UniformDeck).

`RelabelInvariance.tv_bijective_invariance` and `uniformDeck_relabel_invariant` (or `GSR.map_bijective_uniformDist` directly) already supply the generic principle. **All deterministic decks have exactly the same TV** to the uniform target for a state-independent position-permutation protocol. No direct proof of `idealShuffle_relabelEquiv` on arbitrary card lists is required for this *position-law* model.

But do not confuse this with the *different* assertion that this TV equals the TV from a fiber-uniform initial distribution. That needs Section E below.

## D. An important modeling bridge: card-indexed labels vs a position-indexed permutation law

`GSR.idealShuffle` assigns independent labels using the **card-identity** index `Fin n`, then applies `stableBuckets` to a list of card identities. The candidate `gsrPermutationLaw` in `GSRPermutationLaw.lean` is constructed from the canonical deck and a permutation of **positions**. These are different presentations of the same law, but equality for an *arbitrary ordered deck* must be shown.

This is a good use of a simple but easily missed change of variables. If `d : Fin n ~= Fin n` represents a deck and `ell : card -> label`, let

    ell_pos(i) := ell(d(i)).

For the ordered deck `[d(0),...,d(n-1)]`, stable grouping by `ell` has exactly the same order as stable grouping *positions* `[0,...,n-1]` by `ell_pos`, then applying `d` to the resulting positions:

    stableBuckets(a,ell, finRange.map d)
      = (stableBuckets(a,ell_pos,finRange)).map d.

This is pointwise, requiring only `List.filter_map`-style reasoning and `funext`; it does **not** require labels to be constant or invariant under relabeling. Separately, precomposition

    (ell |-> ell . d)

is a bijection on `(Fin n -> Fin a)`, with inverse precomposition by `d.symm`. By `GSR.map_bijective_uniformDist`, uniform labels pull back to uniform labels on positions. Therefore the entire law of `idealShuffle n a` on *any valid permutation deck* is the pushforward of one deck-independent rank-permutation law.

Use the existing `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition` and `GSRPermutationLaw.idealShuffle_canonical_eq_permLaw` to identify that law with `gsrPermutationLaw` (mind inverse rank: original-to-final vs final-to-original). Then an action-kernel representation follows, and colorblindness under card relabeling is automatic.

This can save an independent, long list-level relabeling proof. The currently proposed `idealShuffle_relabelEquiv` in the dated relabel batch note is mathematically reasonable, but **it is not the shortest prerequisite for Gate 6**. If it is easy to prove, retain it as a corollary of the random-position-law representation rather than making it a blocking theorem.

**Pitfall:** do not claim stable sorting of a *fixed label assignment* is card-relabeling-equivariant with *unchanged* labels. The pointwise identity reindexes the labels; its distributional consequence relies on uniform label invariance.

## E. The most consequential missing insight: one-step smoothing at an extreme membership

Here is the missing bridge between the correctly acting ideal kernel and the established `three_physical_perfect_exchanges_uniform_unconditional`.

### E1. Membership-kernel row formula, generic in N,m,k

Write `S(d)` for the left-pile set of a deck, and `T` for an arbitrary target m-card membership. Under a uniform choice of k distinct positions in each pile and fixed pairing, the target membership is `T` **iff**

    |S(d) \ T| = |T \ S(d)| = k.

For any reachable target membership, the outgoing and incoming card sets are *uniquely* `S(d) \ T` and `T \ S(d)`. Because `d` is a bijection, these have unique preimages as selected position subsets. Thus exactly **one** pair of selected-position sets `(L,R)` produces `T`. Therefore

    P(membership_after = T | d)
      = if |S(d) \ T|=k then
          1 / (choose(m,k) * choose(N-m,k))
        else 0.

This expression depends on the input deck **only through the exact membership S(d)**, not its internal ordering or the fixed swap pairing. It is the row formula of `FiniteDeck.SubsetExchange.subsetExchangeKernel`; compare `ReachSet`, `subsetExchangeKernel_rowOne`, and the source-side injectivity arguments `CommanderPhysicalExchange.newLeftCards_injective` / `FiniteDeck.LiteralSwapKernel.swapPerm_membership_eq`.

**Proposed statement shape:** for the actual uniform physical position-pair choice law `Swap N m k`, prove the deterministic-membership pushforward of `swapLaw.map (fun s => act(s,d))` equals `FiniteDeck.subsetExchangeMembershipKernel ... (membership d)`. Avoid proving merely the count-valued Bernoulli-Laplace law: it is too weak to recover uniformity among named memberships.

### E2. Local Haar action = uniform conditional deck law

Let `H = Perm(Fin m) x Perm(Fin(N-m))` be the within-pile permutation group. Its action on a fixed deck `e` is the map already called `fiberMap` / `act_d` in `FiniteDeck.WithinPileOrbit.lean`. The compiled theorem `fiberOrbit_equiv N m hm e` says

    H  ~=  {d' : Deck N // membership(d') = membership(e)}.

Push the uniform law on `H` through this equivalence, and then through `Subtype.val`. **This gives the uniform deck law on the membership fiber.** The intended equality is

    Uniform(H).map (fun h => act(embed_m(h),e))
       = FiniteDeck.localLift N m hm (membership e).

Prove a generic theorem over a finite surjection `observe : X -> Y` that `fiberLaw observe y` equals `Uniform({x // observe x=y}).map Subtype.val`. This is one small *abstract* mass calculation; the equivalence `H ~= fiber` then transports uniform measure without ever evaluating the mass of a 99-card permutation. Instantiate only after the generic lemma is compiled.

Source reuse: `FiberDisintegration.fiberLaw_mass`, `GSR.map_bijective_uniformDist`, `FiniteDeck.WithinPileOrbit.fiberOrbit_equiv`, `GSRSegHeadline.distProduct_uniform_is_uniformProd`, `GSRSegHeadline.roundEmbedMap_eq_fiberOrbit_val`.

This is a **better route than the isolated 99-card identity** `rhoRoundIdeal = localLift segMembership`: prove the uniform-orbit theorem generically and specialize it. If necessary, recover the old segregated identity as a corollary. Do not make pointwise expansion of `map_mass_eq_univ_fiber` at N=99 the next research task.

### E3. Assemble the actual ideal round from E1 and E2

Fix any current deck d. Sample an exchange choice c; let `e=act(swap(c),d)` be the literal swapped deck. Then sample uniform `h in H`, and output `act(h,e)`. By E2, conditional on c the output law is `localLift (membership e)`. By `swapPerm_membership_eq`, `membership e` is exactly the `newMembership d c` used by `CommanderPhysicalExchange.rawExchangeMembership`. Averaging over c therefore gives

    idealActionKernel(d) = rawExchange(d)

where `rawExchange = comp rawExchangeMembership localLift` in `CommanderPhysicalExchange.lean`. After this, `exchangeThenLocalReset` is the same ideal kernel because the extra `localReset` is idempotent after `rawExchange` (the latter has already resampled within membership). Prove that idempotence separately using `localLift_preserves_membership` and kernel associativity.

This is where the real physical model meets the proven mathematical model. **If this bridge is not proved, do not use the existing q3 exact-TV result for the new literal-swap process.**

### E4. Special first-step smoothing from the segregated reference deck

Let marked identities be the m cards in the left pile of a reference deck `d0` (for Commander, r=m=50), so the macro count of `d0` is `m`. Every target membership T reachable after a k-exchange has exactly `m-k` originally-left cards, and conversely **every** membership of marked-count `m-k` is reachable. E1 gives each target membership the same probability; E2 gives each ordering of each target membership the same probability.

Hence the entire one-round deck law from a *deterministic* `d0` is uniform on the macro count fiber F_(m-k):

    idealActionKernel(d0) = UniformDeckCountFiber(m-k).

The count fiber has exactly

    choose(m,k) * choose(N-m,k) * m! * (N-m)!

ordered decks, matching the product of the number of (L,R) choices with the number of internal permutations. An alternative Lean proof can build an explicit bijection

    ExchangeChoice x H  ~=  {d' // project(d') = m-k}

for the segregated start and use uniform pushforward along that bijection. The pairing choice does not affect the result because H randomizes the internal order after swapping.

**Crucial:** the macro fiber F_m contains many ordered decks but only one membership, namely the original marked set. E1/E2 show `idealActionKernel` has the same row on every member of F_m, so

    idealActionKernel(d0)
      = FiniteKernel.apply (UniformDeckCountFiber(m)) idealActionKernel.

This is the rigorous conversion from the deterministic reference start to the fiber-uniform start of the already-proved Commander exact-TV theorem. It is **not** implied by relabeling equivariance alone.

### E5. All-start theorem after the smoothing and ideal-model bridges

With E3, the physical ideal action kernel equals the already-proved perfect-local kernel. With E4, its first round from the ordered segregated deck equals the first round from the fiber-uniform segregated start. Therefore the entire t-round ideal output laws coincide for any t>=1, including t=3. Use

    CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional

for exact `q3`, without a 99! deck-TV mass expansion. Finally, because a random position-permutation protocol is colorblind under *card relabeling*, every deterministic deck is a relabeling of the reference deck and has exactly the same full-deck TV-to-uniform. The final bound then extends to **all deterministic starts**.

Do not attempt to transport the bound from a fiber-uniform law directly to a deterministic law by equivariance: see the companion assessment's exact four-card counterexample.

## F. Complete headline: which arithmetic and which theorems

Let `W_F,W_I` be the finite and ideal one-round **position-permutation** laws. After Sections B/C:

    tvFinsupp(powConv W_F 3,powConv W_I 3) <= 3*delta1.

Push both laws through `p |-> p.trans d0` and use contraction (or TV invariance under bijective pushforward):

    TV(finitePhysical^3(d0), idealPhysical^3(d0)) <= 3*delta1.

After E3-E5, the ideal three-round TV from d0 is `q3`. Therefore by the triangle inequality

    TV(finitePhysical^3(d0), UniformDeck)
      <= q3+3*delta1
       < 1/1000.

The final strict rational inequality is already `FiniteDeck.Gate6FiniteGSR.gate6_headline_bound`; do not recalculate it. Extend to all deterministic d via the action law and bijective TV invariance. The exact numerics (checked with Python `Fraction`) are

    q3             = 0.00002575966837804714...
    delta1          = 0.0002862215042114258...
    q3+3*delta1     = 0.0008844241810123245...
    margin to 0.001 = 0.0001155758189876755...

The theorem must mention the actual cost: three 25/25 exchanges and 23 independent binary inverse-GSR riffles **per pile per exchange** (138 pile-riffle actions). It is a feasible explicit certificate, not a statement of minimum practical cost.

## G. Suggested Lean implementation order (do not build a new maze of probes)

1. In a **generic, light** module, implement `actionKernel` and `physicalNoise` with `distProductFinsupp`; prove `act` composition orientation. No 99 in a theorem signature.
2. Extract `tvFinsupp_map_le` from `kernel_apply_lipschitz`; prove `tvFinsupp_conv_le` from `distProductFinsupp_tv_subadditive`; prove the n-step convolution telescope. Build this module in isolation.
3. Prove `actionKernel` repeated-run = convolution-power pushforward using monad/map/join laws. A four-card check guards against a constant-row error.
4. Obtain the generic `rhoRoundFinite/rhoRoundIdeal` support-TV bound via `tv_eq_tvFinsupp`, and instantiate the per-round 99-card delta1 **after** the generic lemmas build.
5. Prove the generic fiber-uniform law as `Uniform(Subtype fiber).map Subtype.val` and specialize via `WithinPileOrbit.fiberOrbit_equiv`. Keep that bridge independent of Commander imports.
6. Prove pointwise literal-swap-to-membership exchange E1, then ideal swap-plus-Haar equals `rawExchange` E3. Reuse `swapPerm_membership_eq` and `rawExchangeMembership`.
7. Prove the **first-round segregated-deck smoothing identity** E4 and use the existing fiber-uniform q3 theorem E5.
8. Combine steps 2-7 for `TV < 1/1000`, then transport to all ordered starts. Only after this theorem is compiled, revisit sharp costs or multi-pile exchange models.

If the first goal becomes stuck, a bounded alternative is the **rowwise support-TV route** in the 2026-11-22 hint document. Do not switch back to unbounded simplification over 99! or increase heartbeat limits. Report the smallest abstract lemma that remains unproved, not a blanket claim that the mathematics is impossible for Lean.

## H. Checks that prevent false progress

- From a small deck N=4,m=2,k=1, the correct swap-plus-ideal-local chain starting at the ordered identity has TV 1/3 after one round and 1/6 after two; a constant-row kernel remains at 1/3. Exact-fraction enumeration confirms this.
- For the same four-card system, starting at a particular deck of marked-count x=1 gives first-round TV 1/3, while starting uniformly over the x=1 macro fiber gives TV 1/6. This is a counterexample to transferring a fiber-uniform TV *upper bound* to a point start by symmetry alone.
- From an extreme (segregated) marked-count x=2, the one-round output from any ordered deck is identical to the output from the x=2 fiber-uniform law. This illustrates the correct special bridge E4.
- Verify that repeated shuffles change the output law; otherwise a `fun _ => noise` constant-row kernel has slipped back in.
- Verify the action order `h.trans s` and explicitly distinguish positions from card identities. An inverse-rank permutation is not automatically the same as a forward-rank permutation.
- The final Lean statement must mention *finite riffles*, a *deterministic starting deck*, a *three-round physical sequence*, and TV to the *uniform full-deck law*. A theorem about only local riffles, the Bernoulli-Laplace macro count, or the conditional `hq3` is not a substitute.

## I. Relevance beyond 99 cards

Sections A-D are generic finite-group/finite-deck mathematics and should be authored with arbitrary N. E1-E4 also generalize for any admissible two-pile split, especially the extreme segregated r=m reference start. The same proof architecture extends to p piles by replacing H with the product of the p within-pile permutation groups and replacing the two-pile membership with a finite allocation of named cards to piles. This is a better foundation for shuffling large collections split among hands, working piles, and discard piles than repeatedly adding Commander-specific combinatorial arguments.

Do not attempt multi-pile generalization *before* finishing the present end-to-end certificate: the generic group action, convolution and uniform-orbit lemmas developed for it are precisely the reusable foundation that a multi-pile proof will need.
