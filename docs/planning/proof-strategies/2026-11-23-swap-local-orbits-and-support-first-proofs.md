# Gate 6: swap order, uniform orbits, and support-first probability proofs

**Dated mathematical hints, 2026-11-23 evening. Source baseline `573d097`.**

This document is meant to supply the *missing mathematical connections*, not just Lean tactic suggestions. Read alongside the companion dated review. It supersedes the older K1 tactics which assume that `conv rho99Ideal swapLaw` already represents "swap, then uniform local shuffle." None of the illustrative Lean statements below have been checked in a Lean environment; adapt implicit parameters, proof names, and `DecidableEq` instances as required by this Mathlib pin.

## 0. One-page plan

The user wants a real **position-swap, followed by 23 inverse-GSR riffles per pile, repeated three times**, not an absolute resampling oracle. The goal is TV distance below `1/1000` from any deterministic starting arrangement of 99 named cards. Prefer a generic arbitrary-`N` theorem wherever it avoids a specialized 99-card proof.

The exact reusable proof chain should be:

```text
  H = Perm(Fin m) × Perm(Fin (N-m))
            | uniform H, act on a deck d
            v
  [ORBIT] uniform over membership fiber of d
            |
  [SWAP] sample independent uniform L,R, take literal swapPerm s
            v
  [K1] swapThenLocalIdeal(d)
       = apply (rawExchangeMembership d) localLift
       = exchangeThenLocalReset(d)
            |
  [CONTRACTION] left convolution common-swap factor is TV nonexpansive
            v
  [ONE ROUND] TV(Kfinite(d), Kideal(d)) ≤ δ1 for every d
            |
  [TELESCOPE] TV(Kfinite^3 δd, Kideal^3 δd) ≤ 3 δ1
            |
  [INITIAL BRIDGE] Kideal^3 δd0 = Kideal^3 U_fiber-segregated
            |
  [IDEAL TV] existing Commander three-round theorem = q3
            |
  [ARITHMETIC] q3 + 3 δ1 < 1/1000
            |
  [RELABELING] every deterministic d; [CONVEXITY] any initial law
```

**Do not** solve K1 by unrolling `Finset.univ : Finset (Equiv.Perm (Fin 99))`, or by increasing recursion limits. Every box above has a generic formulation.

## 1. The physical-order error hiding inside K1

### Actual composition convention (already proved)

`FiniteDeck.ActionConvolution` has

```lean
FiniteDeck.act (a * b) d = FiniteDeck.act b (FiniteDeck.act a d)
```

and `FiniteDeck.PositionAction` has

```lean
FiniteDeck.swap_then_local_matches_star g s d :
  g.trans (s.trans d) = (s * g).trans d
```

Thus with `s ∼ swapLaw`, `g ∼ rho99Ideal`:

- `conv swapLaw rho99Ideal` acts **swap, then local**.
- `conv rho99Ideal swapLaw` acts **local, then swap**.

`Gate6Crux.fullRoundFinite/fullRoundIdeal` currently take the **second** form. `_ProbeGate6K1` attempts to identify it directly with `exchangeThenLocalReset` (the **first** form), and the remaining goal is therefore more than an orbit-law lemma: it also implicitly asks for a commutation property of the ideal distribution.

### Why order cannot be ignored

For a deterministic local permutation `h`, the laws of `s * h` and `h * s` need not coincide. A direct check with `N=6, m=3, k=2`, canonical sorted matching, `h=(0 1)` within the left pile and uniform choices of two selected positions from each three-position pile, finds an output permutation reached by one order but not the other. The fixed-permutation check is **not** a counterexample to commutation of the *uniform* local law; it shows that no unconditional commuting rewrite is available for a finite local shuffle.

Even if one proves that `uniform_H * swapLaw = swapLaw * uniform_H` (a plausible separate theorem for this particular uniform choice law), the finite-GSR law is not uniform_H. A certificate for the wrong order does not by itself certify the requested sequence of physical actions.

### The better representation

Keep the existing crux as a correct *local-then-swap* TV result, but introduce **new**, explicitly named, correct-order laws:

```lean
-- Lean-like definitions; check namespace and implicit arguments locally.
noncomputable def swapThenLocalIdeal : Dist (FiniteDeck.Deck 99) :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal

noncomputable def swapThenLocalFinite : Dist (FiniteDeck.Deck 99) :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Finite
```

The corresponding state-dependent kernels are simply

```lean
FiniteDeck.permutationActionKernel swapThenLocalIdeal
FiniteDeck.permutationActionKernel swapThenLocalFinite
```

and, by `convPush_eq_pointMassComp` (already proved generically in `_ProbeGate6K1`), one sample of the ideal law acts as

```lean
FiniteKernel.comp
  (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
  (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)
```

**Make this generic `convPush_eq_pointMassComp` the first promoted lemma.** Do not unfold a 99-card distribution just to change the order of these kernels.

## 2. A uniform group orbit IS a fiber law

This is the main mathematical shortcut. It should replace the `GSRSegHeadline`-style attempt to expand individual 99-card masses.

Let `D_N = Equiv.Perm (Fin N)`. Let

```
H_(N,m) = Equiv.Perm (Fin m) × Equiv.Perm (Fin (N-m)).
```

For a deck `d`, write `A(d)` for the set of cards occupying its left pile, and `F_A` for all decks with the same left-card set `A`. The group `H` acts on `d` by independently reordering the positions within each pile.

**Already proved:** `FiniteDeck.fiberOrbit_equiv N m hm d` is a bijection

```
H_(N,m)  ≃  {e : D_N // leftCards e = leftCards d}.
```

Its forward map is `FiniteDeck.act_d N m hm d pl pr` (same as `act (embed_m pl pr) d`). This is much stronger than injectivity, transitivity, or counting alone.

### Abstract lemma to prove once

For *any* equivalence `e : A ≃ B` between nonempty finite types, pushing the uniform law on `A` through `e` yields the uniform law on `B`:

```
  (uniformDist A).map e = uniformDist B.
```

If `B` is a subtype `{x : X // P x}`, and `ι : B → X` forgets the proof, then

```
  (uniformDist A).map (fun a => (e a).val)
   = uniform distribution on the subset {x : X | P x}.
```

*Proof, before Lean tactics:* Every `b ∈ B` has exactly one preimage under `e`; hence each receives probability `1/|A| = 1/|B|`. Everything outside the image receives mass zero. This identifies the laws pointwise. The only cardinality step is `Fintype.card_congr e`. Avoid any enumeration of `B` and use the equivalence as an opaque term.

Now instantiate `e = fiberOrbit_equiv N m hm d`. The target is

\[
  (U_H \mathbin{\mathrm{map}} (h\mapsto h\cdot d))
  = U_{F_{A(d)}}.
\]

In project terms, the RHS is `FiberDisintegration.fiberLaw (FiniteDeck.membership N m hm) (FiniteDeck.membership_surjective N m hm) (FiniteDeck.membership N m hm d)` (check the final import; `FiniteDeck.membership_surjective` is in `FiniteDeck/Fiber.lean`).

A useful generic theorem shape:

```lean
-- PSEUDOCODE, not compiled. Keep every parameter abstract.
theorem uniformOrbitLaw (N m : Nat) (hm : m ≤ N)
    (d : FiniteDeck.Deck N) :
  ((GSR.uniformDist
        (Equiv.Perm (Fin m) × Equiv.Perm (Fin (N-m)))).map
     (fun h => FiniteDeck.act
        (FiniteDeck.embed_m N m hm h.1 h.2) d))
  = FiberDisintegration.fiberLaw
      (FiniteDeck.membership N m hm)
      (FiniteDeck.membership_surjective N m hm)
      (FiniteDeck.membership N m hm d) := by
  -- Reduce to pushforward of uniform under `fiberOrbit_equiv`.
  -- Use generic uniform-under-equivalence / subtype-inclusion law.
  -- Finish via existing leftCards_eq_iffMembership.
  ...
```

**Proof separation:** first prove `uniform_map_equiv` with generic finite types `A,B`; next prove the uniform-on-subtype inclusion lemma with an abstract predicate; finally prove `uniformOrbitLaw N m` with a single instantiation of `fiberOrbit_equiv`.

### Product-uniform identification

`rhoRoundIdeal` is built by pushing the product of two uniform permutation laws through `roundEmbedMap`. `GSRSegHeadline.distProduct_uniform_is_uniformProd` already proves the product of uniforms is uniform on `H`. Use this fact as a precompiled lemma (or factor a generic version out of that file if its imports force 99-card WHNF). `roundEmbedMap` is definitionally `embed_m` and `FiniteDeck.act_d` is `embed_m ... .trans d`. There is no need to prove `rhoRoundIdeal 99 50 = localLift segMembership` directly at the `Fin 99` level.

**Payoff:** for every input `d` and every `N,m`, the **ideal within-pile shuffle** distributes uniformly over exactly the decks with that membership. No factorial computation is required in the final theorem.

## 3. The literal swap only changes membership: pairing is irrelevant

The second reusable lemma is a law-level pushforward, not another cardinality theorem.

For a fixed deck `d`, choose `L` from the permitted left-position subsets and `R` from the permitted right-position subsets, each uniformly; use the deterministic `canonicalPairing L R`; construct the position permutation `s(L,R)` by `FiniteDeck.swapPerm`.

The relevant map is

```
  (L,R) ↦ membership (act (s(L,R)) d).
```

`FiniteDeck.LiteralSwapKernel.swapPerm_membership_eq` already proves this equals `literalSwapMembership ... d L R`. `_ProbeK1a.lean` proves the specialized equality with `CommanderPhysicalExchange.newMembership`, with no dependence on the particular `b` pairing.

Meanwhile `CommanderPhysicalExchange.rawExchangeMembership d` is **defined** by uniform choices `(L,R)` followed by `newMembership`. Thus:

\[
  (\mathrm{swapLaw}.\mathrm{map}\,(s\mapsto\mathrm{membership}(s\cdot d)))
  = \mathrm{rawExchangeMembership}(d).
\]

Prove this as a named lemma, `swapLaw_membership_map`, before introducing any local shuffle distribution.

### Lean route

1. Promote `K1a_swapPerm_membership` from `_ProbeK1a.lean` to a normal module *or* derive it from the generic `swapPerm_membership_eq` plus the existing Commander-vs-FiniteDeck membership frame bridge. Prefer the latter if it genuinely gives a shorter proof.
2. Unfold `swapLaw` and `rawExchangeMembership` only in this isolated theorem, under concrete **functions on `exchangeChoice`**, not an unbounded `Finset.univ` of permutations.
3. Use `StdSimplex.map_map` and `funext` with K1a to identify the two maps. Do **not** inspect the mass of `GSR.uniformDist (Equiv.Perm (Fin 99))`.
4. If `rw` on the 99-card law recursively elaborates, state an **abstract map-pushforward lemma** for any source distribution `C` and maps `f,g` with pointwise equality `∀c, f c = g c`; instantiate with `exact` after the expensive definitions have been hidden behind arguments.

The pairing is only a mechanism for making a position permutation. It **disappears** when projecting to membership; this is precisely why the higher-level exchange kernel has a clean subset description.

## 4. K1 as a short composition of the two structural facts

Define `K_S(d)` to be the law of the deck **after the literal swap but before any local reorder**:

```
K_S d := swapLaw.map (fun s => FiniteDeck.act s d).
```

Define `K_H(e)` as the law of `e` after an independent **ideal uniform** local reorder. By Section 2,

```
K_H e = localLift (membership e).
```

The correct ideal one-round kernel is

\[
 K_{\mathrm{ideal}}(d)=K_S(d) K_H
   = \sum_s \Pr(S=s)\,U_{F_{A(s\cdot d)}}.
\]

By Section 3, the pushforward of the swap law under `membership` is exactly `rawExchangeMembership d`. Therefore

\[
 K_{\mathrm{ideal}}(d)
   = \sum_M \mathrm{rawExchangeMembership}(d)(M)\,\mathrm{localLift}(M)
   = \mathrm{FiniteKernel.apply}(\mathrm{rawExchangeMembership}(d),\mathrm{localLift}).
\]

This is **already** the RHS normal form `k1_rhs_bookkeeping` computes. The last application equals `exchangeThenLocalReset` because `localLift_preserves_membership` makes the redundant extra reset idempotent.

### Lean assembly strategy

- Start from the generic equality for a shared **outer source** `C : Dist Choice`:

```
  (C.map (fun c => localIdeal (swap c d))).join
  = ((C.map (fun c => membership (swap c d))).map localLift).join.
```

  It follows by a pointwise equality `localIdeal e = localLift (membership e)` and `map_map`. **Do not unfold either side.**
- Pull the `localLift` through the outer map using `joinMapComm` as needed.
- Apply `swapLaw_membership_map d`.
- Close by `k1_rhs_bookkeeping` and the generic `convPush_eq_pointMassComp`, with **correct factor order** `swapLaw` then `rho99Ideal`.

The full 99-card proof should be a short `calc` with named generic lemmas and **no** `simp [membership, leftCards, uniformDist, Finset.univ]` inside it. The only support calculation is in `uniformOrbitLaw`, and there it happens with a *variable* finite type and an equivalence.

### Proposed theorem at the right level

```lean
-- PSEUDOCODE, final assembly theorem.
theorem K1_swapThenLocalIdeal_eq_exchangeThenLocalReset
    (d : Equiv.Perm (Fin 99)) :
  (FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal).map
      (fun p => FiniteDeck.act p d) =
  FiniteKernel.apply (Dist.pointMass d)
    (PhysicalExchangeReduction.exchangeThenLocalReset
       CommanderMembershipKernels.membership
       CommanderMembershipKernels.localLift
       CommanderPhysicalExchange.rawExchange) := by
  -- convPush_eq_pointMassComp, Sections 2 and 3, and
  -- _ProbeGate6K1.k1_rhs_bookkeeping.
  ...
```

This is a strictly more direct target than the *existing* `_ProbeGate6K1.K1_oneRoundLaw_eq_exchangeThenLocalReset`, because that probe asks for the opposite factor order.

## 5. Recover the collision bound for swap-THEN-local

The already-proved `Gate6Crux.convContraction` is

\[
 \operatorname{TV}(F*S,I*S)\leq\operatorname{TV}(F,I),
\]

where the **second** convolution factor `S` is common. Correct physical order requires the *mirror* inequality

\[
 \boxed{\operatorname{TV}(S*F,S*I)\leq\operatorname{TV}(F,I).}
\]

### Method A: common left-noise kernel (preferred if the Fubini bridge is easy)

For a fixed distribution `S`, define a Markov kernel on permutations:

```lean
-- PSEUDOCODE: use separate module; no concrete 99-card arguments.
noncomputable def leftNoiseKernel {N : Nat}
    (S : Dist (FiniteDeck.Deck N)) :
    FiniteKernel (FiniteDeck.Deck N) (FiniteDeck.Deck N) :=
  fun f => S.map (fun s => s * f)
```

It samples the **same** `S` for every input `f`. Show

```
conv S F = FiniteKernel.apply F (leftNoiseKernel S).
```

This is finite Fubini, not a 99-card counting theorem. For any output `p` the two sides assign mass

\[
  \sum_{f\in\operatorname{supp}F}\sum_{s\in\operatorname{supp}S}
  F(f)S(s)\,\mathbf1_{s*f=p},
\]

with the summation order reversed. The existing `joinMapComm`, `distProductFinsupp` and `distProductFinsupp_mass` are the relevant primitives. A clean intermediate lemma is

```
(distProductFinsupp S F).map Prod.swap
 = distProductFinsupp F S.
```

**Only prove this identity over generic types**, using equality of masses and finite supports. Then the `convAsApply` proof can be mirrored in a handful of `map_map` / `joinMapComm` steps.

Finally:

```lean
-- PSEUDOCODE, no enumeration of Perm(Fin 99).
theorem convLeftContraction {N : Nat}
    (S F I : Dist (FiniteDeck.Deck N)) :
  tvFinsupp (FiniteDeck.conv S F) (FiniteDeck.conv S I) ≤ tvFinsupp F I := by
  rw [convLeftAsApply S F, convLeftAsApply S I]
  exact kernel_apply_lipschitz F I (leftNoiseKernel S)
```

After this theorem compiles generically, instantiate at `S = swapLaw`, `F = rho99Finite`, `I = rho99Ideal`, then use existing `GSRDeckRound.oneRoundDeckTV_le_delta1`. The sole concrete calculation is `δ1 = 2401/8388608`, already proved.

### Method B: shared-mixture bound (more general, useful for multi-pile work)

If convolution Fubini is hard in Lean, prove an abstract Finsupp-support theorem for two different kernels applied to the *same* input law:

\[
 \operatorname{TV}(\mu K,\mu L)
   \leq \sum_{x\in\operatorname{supp}\mu}\mu(x)
                    \operatorname{TV}(K(x),L(x)).
\]

Proof: at each output `y`, subtract the two output masses; bound the absolute value of the weighted sum by the sum of absolute values; interchange the two **finite support** sums. This is closely related to `TotalVariation.mixtureTV_le`, but that existing theorem has a fixed reference law rather than a family `L(x)`. Its proof supplies the support-sum pattern; **do not pretend its current statement directly solves this goal**.

Apply it with `μ = K_S d`, `K = permutationActionKernel rho99Finite`, `L = permutationActionKernel rho99Ideal`. Each input `x` has

\[
 \operatorname{TV}(K(x),L(x)) \le \operatorname{TV}(\rho_F,\rho_I)\le\delta_1,
\]

by pushforward contraction. Thus the weighted average is at most `δ1` because `μ` has total mass one. This proof bypasses group convolution completely and is useful later when each pile has a different shuffle mechanism.

**Choose one method, not both at once.** Method A is shorter if the generic Fubini identity lands; method B is the more reusable generic kernel perturbation result. Neither needs a `Finset.univ` over full decks.

## 6. The real three-round error telescope

Use the state-dependent kernels

```
K_F = permutationActionKernel (conv swapLaw rho99Finite)
K_I = permutationActionKernel (conv swapLaw rho99Ideal)
```

and **never** the `GSRGate6Telescope.gsrRound99*` constant-output kernels in the physical theorem. The source already says their `hq3` premise is false.

Suppose Section 5 proves `∀ d, TV(K_F(d), K_I(d)) ≤ δ1`. For any distribution `μ` over deck states, the shared-mixture lemma gives `TV(μK_F, μK_I) ≤ δ1`. The generic `kernel_apply_lipschitz` gives `TV(μK_I,νK_I)≤TV(μ,ν)`. Combining them,

\[
 \begin{aligned}
 \operatorname{TV}(\mu K_F,\nu K_I)
 &\le \operatorname{TV}(\mu K_F,\mu K_I)
       +\operatorname{TV}(\mu K_I,\nu K_I)\\
 &\le \delta_1+\operatorname{TV}(\mu,\nu).
 \end{aligned}
\]

Iterate this for three rounds from the same point mass; get `≤ 3δ1`. This direct recursion avoids `kernelDiscrepancy`'s maximum over `Finset.univ` of a 99! state space.

The project's `FiniteKernel.run`, `FiniteKernel.apply_comp`, `TelescopeF5` and `FiniteDeck.powConvRunEq` implement related induction infrastructure. Check which one permits a generic theorem **without max / Fintype**, then reuse it. A compiled three-step telescope about constant-row kernels does not suffice.

## 7. The overlooked deterministic-start bridge

The existing exact theorem

```
CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional
```

starts from a distribution uniform over the segregated **macrostate fiber**, not from `Dist.pointMass d0` for a fixed ordered deck. This difference is essential. Card-relabeling invariance alone does **not** turn a fiber-uniform input into a point mass.

### Why the first ideal round erases the initial within-pile order

Fix `d0` whose original 50 distinguished cards are all in the 50-position left pile. After uniformly selecting 25 left positions and 25 right positions and swapping them, the left pile's membership contains **exactly 25** distinguished cards. Moreover, every possible target membership with this count has *exactly one* corresponding pair of selected outgoing/incoming **card sets**; because `d0` is a bijection, these card sets determine exactly one pair of selected **position sets** `(L,R)`.

Thus `rawExchangeMembership d0` is uniform on all memberships with marked count 25. Then the ideal local shuffle is uniform within each such membership fiber. Because all these fibers have equal cardinality (`50!·49!`, already proved), the output law is uniform on the *entire* `x=25` macro fiber.

Equivalently,

\[
 \boxed{K_I(\delta_{d_0})=U_{x=25}.}
\]

Exactly the same first-round law results from the *uniform* initial segregated macro fiber; in that initial macrostate the left-card membership is in fact fixed, and an ideal exchange depends only on membership, not the within-pile ordering. Hence

\[
 K_I(\delta_{d_0})=K_I(U_{x=50}).
\]

Apply the same kernel twice more:

\[
 K_I^3(\delta_{d_0})=K_I^3(U_{x=50}).
\]

Now the existing three-round exact TV theorem supplies the desired `q3` bound for the deterministic reference deck. **Prove the one-step equality, not a new three-round enumeration.**

### First-step Lean proof decomposition

1. Identify the post-swap membership measure using `swapLaw_membership_map` from Section 3.
2. Show the choice-to-new-membership map is a bijection between the legal `exchangeChoice` type and the membership subtype with marked count 25 **for the segregated input**. `CommanderPhysicalExchange.newLeftCards_injective` and its existing cardinality lemmas are useful here. Avoid constructing a huge Finset of decks.
3. Push the uniform choice distribution through that bijection to obtain uniform membership in the `x=25` fiber (reuse `uniform_map_equiv`).
4. Map each membership to `localLift`; use generic disintegration to identify the result as `U_{x=25}`. The equal-size fibers are a previously proved theorem; do not recount factorials.
5. Establish the same one-round law for a uniform `x=50` start (or show a stronger dependence-only-on-membership lemma). Compose equality with two further ideal rounds. Apply `three_physical_perfect_exchanges_uniform_unconditional`.

**Check carefully that the count is 25:** it is the count of the original 50 left-side cards remaining on the left after replacing 25 of them with cards from the original right side. The macrostate's `Fin 50` encoding may store this count offset by one; rely on the repository's `project`/state bridge lemmas, not raw numeral rewriting in `Fin 50`.

## 8. Extend one reference-deck certificate to all starts

The law of a position-only protocol does not inspect *card identities*. For any card relabeling `g`, let `R_g(d)` relabel every card in `d`. Then the state-dependent physical kernel should satisfy

\[
 K(R_g d)= (K d).\mathrm{map}\,R_g.
\]

This is a consequence of `act p (d.trans g) = (act p d).trans g` by associativity of `Equiv.trans`, and a `map_map` argument. Prove this **once generically in `N`**, or reuse `FiniteDeck.RelabelInvariance` where the precise action orientations match.

Given two deterministic decks `d,d0`, choose `g` with `d=R_g(d0)`; the action of the full card-permutation group is transitive on decks. The uniform deck law is invariant under `R_g`, so

\[
 \operatorname{TV}(K^3\delta_d,U)
 =\operatorname{TV}(K^3\delta_{d_0},U).
\]

This establishes the same bound for **every deterministic input**. Any initial distribution is a convex combination of point masses; generic mixture convexity then gives the same upper bound for every initial law. The latter is optional for the requested end condition, but mathematically cheap once the deterministic result is present.

**Warning:** This relabeling argument does **not** supply Section 7's missing first-round smoothing. You need the deterministic reference-deck certificate *before* invoking transitivity.

## 9. If Lean still expands the 99-card type

The new trace says a generic proof takes seconds but the same-looking concrete `rw` can spend minutes weak-head-normalizing a concrete permutation distribution. In this case the normalizer is being asked the wrong question. Give Qwen this debugging procedure:

- Identify the **first** lemma where abstract type variables or abstract probability laws become `Equiv.Perm (Fin 99)` and the concrete `rho99Ideal`/`swapLaw` definitions. The other generic lemmas should not mention them in their bodies.
- Inspect whether a tactic (`rw`, `simp`, `change`, `convert`, `congr`) searches or elaborates a goal containing an expanded `uniformDist`, `Fintype.card`, `Finset.univ`, or `ofFun` over those types. The correct solution is a small higher-level identity whose proof works with abstract **functions**, **equivalences**, and **finite supports**.
- Reduce a failed assembly to a named helper with parameters `(C : Dist Choice) (f g : Choice → ...)` and a hypothesis `∀ c, f c = g c`. Compile it with generic types, then invoke it using `exact` / `apply` with opaque arguments. Do not repeatedly re-increase `maxRecDepth`/heartbeats.
- Where a specialized statement is definitionally too large even for `exact`, change the *public theorem's presentation*: name the intermediate physical kernel as a definition, establish an explicit equivalence or kernel equality in a small module, and use the declaration opaquely downstream. Do not attempt to normalize two huge implementations to definitional equality.
- Verify that a successful `lake build` actually imported the **final theorem**. A probe containing `sorry` may compile and a green aggregator can omit optional probes; these are not evidence that K1 is proved.

This is not a demand for new diagnostic infrastructure or a full suite of guardrails. It is a concrete instruction to abandon proof shapes that force the kernel to enumerate astronomical finite types.

## 10. Recommended proof milestones (small and testable)

| Order | Minimal compiled target | What it unlocks |
|---|---|---|
| 1 | Generic `uniform_map_equiv` and `uniformOrbitLaw N m` | Finite-deck local reset without 99! mass sums |
| 2 | Specialized `swapLaw_membership_map d` using K1a | Literal selection law matches abstract membership exchange |
| 3 | **Correct-order K1** with no placeholder | `swapThenLocalIdeal` identified with physical perfect-local kernel |
| 4 | Generic `convLeftContraction` or shared-mixture TV | Correct-order finite-vs-ideal one-round bound |
| 5 | Generic three-round **state-dependent** telescope | `TV(K_F^3 δ_d,K_I^3 δ_d)≤3δ1` |
| 6 | Segregated reference-deck first-round smoothing | Existing exact `q3` theorem becomes applicable |
| 7 | Reference-deck certificate and relabeling | `TV(K_F^3 δ_d,U)<1/1000` for every deterministic `d` |

The prerequisite graph permits steps 1–3 and step 4 to be developed separately. **No new spectral calculations, collision proofs, or large 99-card mass sums are needed.** Once Gate 6 closes, the generic orbit and shared-mixture lemmas are natural inputs to the planned multi-pile finite-deck theory.

## 11. Existing declarations to reuse (not to recreate)

| Source module | Declarations |
|---|---|
| `FiniteDeck/ActionConvolution.lean` | `act_composition`, `joinMapComm`, `convMapEqApplyMap`, `powConvRunEq`, `conv` |
| `FiniteDeck/PositionAction.lean` | `swapThenLocalKernel`, `permutationActionKernel`, `swap_then_local_matches_star`, `perm_mul_eq_trans_flip` |
| `FiniteDeck/WithinPileOrbit.lean` | `fiberOrbit_equiv`, `fiberMap`, `act_d_preservesMembership`, `leftCards_eq_iffMembership` |
| `FiniteDeck/Fiber.lean` | `membership_surjective`, `fiberCount` |
| `FiniteDeck/LiteralSwapKernel.lean` | `swapPerm`, `swapPerm_membership_eq` |
| `GSRSegHeadline.lean` | `distProduct_uniform_is_uniformProd`, `roundEmbedMap_eq_fiberOrbit_val` |
| `GSRDeckRound.lean` | `rhoRoundIdeal`, `rhoRoundFinite`, `oneRoundDeckTV_le_delta1` |
| `Gate6Crux.lean` | `swapLaw`, `rho99Finite`, `rho99Ideal`, `convAsApply`, `convContraction`, `gate6_crux` (old orientation) |
| `_ProbeK1a.lean` | `K1a_swapPerm_membership` (probe, promote or shorten) |
| `_ProbeGate6K1.lean` | `convPush_eq_pointMassComp`, `k1_rhs_bookkeeping` (proved in probe), K1 headline (still `sorry`) |
| `CommanderPhysicalExchange.lean` | `rawExchangeMembership`, `rawExchange`, `newLeftCards_injective` |
| `CommanderMembershipKernels.lean` | `localLift`, `localLift_mass`, `localLift_preserves_membership` |
| `TotalVariation.lean` | `kernel_apply_lipschitz`, `tv_eq_tvFinsupp`, `mixtureTV_le`, `tv_map_contraction` |
| `CommanderFullDeckDisintegration.lean` | `three_physical_perfect_exchanges_uniform_unconditional` |
| `FiniteDeck/Gate6FiniteGSR.lean` | `q3`, `δ1`, `gate6_headline_bound` |
| `FiniteDeck/RelabelInvariance.lean` | Generic relabeling and uniform-TV invariance |

These are source names from the snapshot, not an instruction to import every file into one enormous module. Keep the general algebra and orbit law in light modules; specialize in a thin final module.
