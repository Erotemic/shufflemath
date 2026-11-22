# 2026-11-22 — Structural proof routes past the Gate 6 elaboration wall

**For Qwen 27B.** Read the companion review first: `../reviews/2026-11-22-gate6-proof-architecture-assessment.md`. Assessment base is commit `4ff9478`, not a future-dated filename in the working tree. These are **mathematical derivations and proposed Lean statement shapes**, not ready-to-paste compiled proofs. Names cited as existing were checked against the source; declarations labeled **PROPOSED** must be proved. The objective is still **three literal exchange + finite local GSR rounds, TV < 1/1000 from every ordered deck**. Do not substitute the already-proved 41-step fiber-uniform/perfect-local result for this goal.

## Executive direction — four connections that cut out the hard parts

1. **Random permutations are noise, not deck transitions.** A law on positions must act on the *current deck*. `fun _ => law` is a reset, not a shuffle. This semantic error currently affects the compiled `gsrRound99*` and draft `finiteRound`/`idealRound` kernels.
2. **An enormous finite type is still a finite-support distribution type.** `Dist α = Convexity.StdSimplex Rat α` already stores its weights in a `Finsupp`. The project has `tvFinsupp`, `distProductFinsupp`, and support-only kernel contraction. These are designed to avoid unfolding `Finset.univ : Finset (Equiv.Perm (Fin 99))`.
3. **A uniform subgroup action is a uniform fiber distribution.** `FiniteDeck.fiberOrbit_equiv` is precisely the bijection from within-pile permutations to decks with fixed membership. A *generic* pushforward-of-uniform-along-fiber-equivalence theorem replaces the last difficult `rhoRoundIdeal = localLift` mass expansion.
4. **Quotient first, numerical result last.** Once literal swap + uniform local action equals the ideal membership-exchange + perfect-local kernel, the three-round TV equals the known Bernoulli–Laplace `q3` without touching deck cardinalities. Combine it with three support-only per-round coupling bounds, then extend to every ordered start by relabeling.

The goal is an *abstract proof that can later be instantiated at 99*, not a 99-card-specific calculation disguised with many `simp` calls.

---

## A. Correct the physical round: state-independent noise, state-dependent action

Let `D_N := Equiv.Perm (Fin N)` denote a deck as a bijection **position → card identity**. Let `s` exchange selected physical positions and `g` permute positions *within* the two piles. The actual order is

\[
 d \xrightarrow{\text{swap }s} s.\mathrm{trans}\,d
 \xrightarrow{\text{local }g} g.\mathrm{trans}(s.\mathrm{trans}\,d).
\]

In concrete function notation the resulting card at position `i` is `d (s (g i))`. This is the source of truth for orientation; the multiplication notation `g * s` must be checked against `Equiv.Perm.mul_apply` before use.

**PROPOSED generic kernel** (namespace `Shufflemath`; needs only `Dist.map`, not `Fintype (Deck N)`):

```lean
noncomputable def permutationActionKernel {N : Nat}
    (noise : Dist (FiniteDeck.Deck N)) :
    FiniteKernel (FiniteDeck.Deck N) (FiniteDeck.Deck N) :=
  fun d => noise.map (fun p => p.trans d)

noncomputable def swapThenLocalKernel {N : Nat}
    (swapNoise localNoise : Dist (FiniteDeck.Deck N)) :
    FiniteKernel (FiniteDeck.Deck N) (FiniteDeck.Deck N) :=
  fun d =>
    (distProductFinsupp swapNoise localNoise).map
      (fun z => z.2.trans (z.1.trans d))
```

The `swapNoise` for Commander is the already-compiling `_ProbeGate6Fin2.swapLaw` (uniform choice of `L,R`, canonical pairing, then `FiniteDeck.swapPerm`). The `localNoise` laws are the existing `rhoRoundFinite 99 50 ...` and `rhoRoundIdeal ...` from `GSRDeckRound.lean`. Do *not* import the probe wholesale into production; move its proved definitions and pairing facts into a small owned module after verifying them.

**Pointwise sanity lemma:**

```lean
-- PROPOSED; the `trans` orientation is intentional.
theorem swap_then_local_apply (s g d : FiniteDeck.Deck N) (i : Fin N) :
    (g.trans (s.trans d)) i = d (s (g i)) := by
  rfl
```

The orientation proof must then match `FiniteDeck.swapPerm_membership_eq`. If the current `g * s` produces the opposite application order, change the law rather than the physical interpretation.

**Failure mode to eliminate:** the following is *not* a deck shuffle:

```lean
-- WRONG for a physical Markov chain:
fun (_d : FiniteDeck.Deck N) => noise
```

For any such constant-row `K`, `FiniteKernel.run K n (Dist.pointMass d)` is `noise` for all `n>0`. This is why `GSRGate6Telescope.gate6_headline_telescope` has a false `hq3` for its current kernels and why the corresponding definitions in `_ProbeGate6Fin2` must not be accepted as the end-to-end model. A state-independent **noise distribution** is perfectly reasonable; a state-independent **output deck distribution** is not.

**Small exact regression to catch the constant-kernel error:** for `N=4,m=2,k=1`, enumerate the four possible single-pair cross-pile swaps and the four within-pile permutations. From the identity deck, a correct ideal first round is uniform on 16 arrangements (four memberships, four orderings each), giving TV `1/3` from uniform on all 24 permutations. A correct second round has support on all 24 permutations and TV `1/6`. A constant-row kernel would instead retain the *first-round law* after two steps and report TV `1/3` again. These numbers were checked independently by exact rational enumeration, **not proved in Lean**. Turn a small version of this into a regression if it helps catch action-order mistakes without adding a costly test suite.

**Checkpoint A:** name and compile a theorem that one sample of the corrected kernel is `g.trans (s.trans d)` for any `d`; demonstrate that `K d` is the pushforward of the same noise under `p ↦ p.trans d`. No distributional TV proof yet.

---

## B. Reuse the Fintype-free TV theory Qwen has already proved

Read these existing declarations *before writing new probability algebra*:

- `Shufflemath/Finite.lean`: `distProductFinsupp` and `distProductFinsupp_mass`; `FiniteKernel.apply_mass_finsupp`.
- `Shufflemath/TotalVariation.lean`: `tvFinsupp`, `tv_eq_tvFinsupp`, `distProductFinsupp_tv_subadditive`, `kernel_apply_lipschitz`, `mixtureTV_le`, `run_nonexpansive`.
- `Shufflemath/GSR.lean`: `GSR.apply_deterministic`, proving `FiniteKernel.apply μ (deterministic f) = μ.map f` for arbitrary types.

Qwen has already developed and discussed these finite-support tools in earlier F4.3/F4.5 work. The present insight is their **composition into a complete rowwise physical-kernel bound**, not that the primitives are new. These are the tools that avoid the unexpanded `Finset.univ` of `Perm (Fin 99)`. In particular, **do not use `distProduct`** for a product with a 99-card permutation factor; its `Dist.ofFun` construction requires global `Fintype` normalization. Use `distProductFinsupp` (same mathematical product) instead.

### B1. Generic pushforward contraction without `Fintype`

**PROPOSED**, for arbitrary `A B : Type*` and decidable equalities:

```lean
theorem tvFinsupp_map_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (μ ν : Dist A) (f : A → B) :
    tvFinsupp (μ.map f) (ν.map f) ≤ tvFinsupp μ ν := by
  rw [← GSR.apply_deterministic μ f, ← GSR.apply_deterministic ν f]
  exact kernel_apply_lipschitz μ ν (FiniteKernel.deterministic f)
```

This is a **short composition of existing production lemmas**. No `Finset.univ`, no TV expansion, no `Fintype` argument, and no assumption that `f` is injective. If the `rw` does not fire due to namespace/rewrite direction, first assert both `apply = map` equalities and `simpa only` with them. The mathematical statement is independent of the syntactic proof.

### B2. Common-noise product contraction from a theorem already in the tree

**PROPOSED**, for arbitrary types `A,B`:

```lean
theorem tvFinsupp_common_product
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (P : Dist A) (F I : Dist B) :
    tvFinsupp (distProductFinsupp P F)
      (distProductFinsupp P I) ≤ tvFinsupp F I := by
  calc
    _ ≤ tvFinsupp P P + tvFinsupp F I :=
      distProductFinsupp_tv_subadditive P P F I
    _ = tvFinsupp F I := by simp [tvFinsupp]
```

The inequality is all we need, so **do not** prove the stronger equality `TV(P⊗F,P⊗I)=TV(F,I)` unless it is easier for some other reason. This bypasses the abandoned explicit `tv_product_common` proof in `_ProbeGate6Fin2`, which expanded an entire `99!×99!` product.

### B3. One-line per-round bound at an arbitrary current deck

Combine B1 and B2 with the **same** deterministic action

```lean
fun z : Deck N × Deck N => z.2.trans (z.1.trans d)
```

on both products. This proves, symbolically for every `d` and every `N`,

\[
 \mathrm{TV}_{\mathrm{supp}}(K_F(d),K_I(d))
 \le \mathrm{TV}_{\mathrm{supp}}(\rho_F,\rho_I).
\]

The random swap is *common* to the finite and ideal constructions, so its distribution does not appear in the right-hand side. This is the high-value reduction Qwen could not obtain while working with `distProduct` and `Dist.tv` at a concrete `N=99`.

Suggested proof shape:

```lean
calc
  tvFinsupp ((distProductFinsupp S F).map (act d))
      ((distProductFinsupp S I).map (act d))
      ≤ tvFinsupp (distProductFinsupp S F)
          (distProductFinsupp S I) := tvFinsupp_map_le _ _ _
  _ ≤ tvFinsupp F I := tvFinsupp_common_product S F I
```

**Important:** this route uses `tvFinsupp`, *not* `Dist.tv`, in the critical concrete full-round statement. That is a choice of equivalent metric representation, not a weakening of the TV result.

### B4. Bridge the already-proved GSR bound to support-TV symbolically

`GSRDeckRound.rhoRoundTransport_le_twoPile` already proves the exact arbitrary-`N,m` `Dist.tv` inequality for the local permutation law. `oneRoundDeckTV_le_delta1` specializes it to `(99,50,2^23)`. `tv_eq_tvFinsupp` identifies this with support TV for **any finite type**.

Do NOT apply `simp [Dist.tv, vectorTV]` to a goal at `N=99`. Prove a wrapper while `N,m` are **variables**:

```lean
-- PROPOSED theorem, schematic hypotheses abbreviated:
theorem rhoRoundTransport_support_bound (N m a : Nat) (...) :
    tvFinsupp (rhoRoundFinite N m hm hl hr a ha)
      (rhoRoundIdeal N m hm hl hr a ha) ≤
      (m.choose 2 : Rat) / a + ((N-m).choose 2 : Rat) / a := by
  rw [← tv_eq_tvFinsupp]
  exact rhoRoundTransport_le_twoPile N m hm hl hr a ha
```

Only *then* instantiate `N=99,m=50,a=2^23`. Evaluate the **rational right-hand side** with the already-proved `δ1_eq_2401_over_8388608`; never unfold either local shuffle law at 99.

**Checkpoint B:** a non-conditional, actually compiled `∀ d : Deck 99, tvFinsupp (K_F d) (K_I d) ≤ δ1` for the correctly acting kernels. This is a much more informative checkpoint than compiling a constant-row kernel or the original `Dist.tv` product crux.

---

## C. The other wall is a missing abstract uniform-fiber theorem

The 2026-11-22 handoff repeatedly tries to show

```lean
rhoRoundIdeal 99 50 ... = CommanderMembershipKernels.localLift segMembership
```

by evaluating the mass at each `d : Deck 99` and expanding `map_mass_eq_univ_fiber` on a subtype with `50!·49!` elements. This is precisely the point at which Lean times out. **Stop specializing before proving the general statement.**

### C1. Generic theorem to prove once

Let `obs : X → Y` be surjective between finite types and choose `y:Y`. Put `Fib y := {x:X // obs x = y}`. The two probability laws below are equal:

\[
  (\operatorname{Uniform}(\mathrm{Fib}\,y))_*(\mathrm{Subtype.val})
  \;=\; \operatorname{fiberLaw}(obs,y).
\]

Every `x` in that fiber receives mass `1/|Fib y|`, all other points receive zero. The denominator in `FiberDisintegration.fiberLaw_mass` is `(fiberSet obs y).card`, equal to `Fintype.card (Fib y)` by `Fintype.card_subtype`.

**PROPOSED mathematical signature** (fill class assumptions from `FiberDisintegration.lean`):

```lean
theorem uniform_subtype_val_eq_fiberLaw
    {X Y : Type*} [Fintype X] [Fintype Y] ...
    (obs : X → Y) (hs : Function.Surjective obs) (y : Y) :
    (GSR.uniformDist {x : X // obs x = y}).map Subtype.val =
      FiberDisintegration.fiberLaw obs hs y := by
  -- All types are VARIABLES here. The only fiber sum is symbolic.
  ...
```

Prove the mass formula with either `Finsupp.mapDomain_apply_of_injective` for `Subtype.val` plus support membership, or `Dist.map_mass_eq_univ_fiber` **on the type variable `X`**. The latter is okay *here*, not when `X` is the concrete 99-card permutation type. Explicitly obtain `Nonempty (Fib y)` from `hs y`.

### C2. Push uniform through an equivalence into a fiber

Given `e : A ≃ Fib y`, `GSR.map_bijective_uniformDist e` proves

\[
 (\operatorname{Uniform}(A))_*e = \operatorname{Uniform}(Fib y).
\]

Compose with `Subtype.val`; `Convexity.StdSimplex.map_map` then gives the **PROPOSED** reusable theorem:

```lean
-- Statement shape; all ambient types are variables.
theorem uniform_equiv_fiber_pushforward
    (e : A ≃ {x : X // obs x = y}) :
    (GSR.uniformDist A).map (fun a => (e a).val) =
      FiberDisintegration.fiberLaw obs hs y := by
  ... -- map_map, map_bijective_uniformDist, C1
```

**The role of `FiniteDeck.fiberOrbit_equiv`:** for any legal `N,m` and *any current deck* `d`, it gives exactly the equivalence

\[
  S_m\times S_{N-m}\;\simeq\;\{d'\mid\mathrm{leftCards}(d')=\mathrm{leftCards}(d)\}.
\]

Use this equivalence with C2 (and the known `leftCards ↔ membership` equivalence) to prove:

> Sampling independent uniform within-pile permutations, applying them to any deck `d`, gives `FiniteDeck.localLift (FiniteDeck.membership d)`.

This statement is stronger and more reusable than the segregated-only equality, and avoids another Commander case split. The product-of-uniforms law is **already proved** in `GSRSegHeadline.distProduct_uniform_is_uniformProd`; it is not a new task.

**A pairing-independence dividend:** for fixed selected left/right *sets*, any two bijections pairing those positions produce decks with the **same new membership** (already proved by `swapPerm_membership_eq`). A subsequent *uniform* within-pile permutation therefore produces exactly the same distribution in either case, by this orbit theorem. Thus a canonical pairing is perfectly adequate: **there is no need to prove that the chosen matching is uniformly random**. This independence is only guaranteed after the *ideal* uniform local shuffle; it does **not** license replacing the finite GSR kernel with a membership-only kernel.

**Checkpoint C:** a generic `N,m,d` ideal-local-action-equals-`localLift` theorem with the body using C1/C2 and `fiberOrbit_equiv`, but no expansion of `Perm (Fin 99)` masses. Specialize it to the segregated `d0` only as a corollary. If the Commander membership type causes additional elaboration trouble, finish the generic `FiniteDeck.membership` statement first, and prove a *small* `.1`-projection bridge (`GSRSegMembership.membership_iff_leftCards` and `finiteDeck_leftCards_99_50_eq_commander` already exist).

---

## D. The actual ideal three-round result is a quotient theorem, not a 99! theorem

Once C holds, the *correctly acting* full ideal kernel `J` is mathematically

\[
 J(d)=\sum_{(L,R)} \Pr(L,R)\,
       \mathrm{Uniform}\{d':\mathrm{membership}(d')=\mathrm{newMembership}(d,L,R)\}.
\]

This is precisely the membership-level exchange followed by `localLift`, provided the membership pushforward is the proved generic exchange kernel. Cite the existing results instead of counting again:

- `FiniteDeck/LiteralSwapKernel.swapPerm_membership_eq`: the literal swap and `newMembership` agree, regardless of the chosen pairing.
- `FiniteDeck/A3KernelLaw.hMembershipExchange_kernel`: the generic membership exchange kernel equality.
- `FiniteDeck/BLDisintegration.two_physical_perfect_exchanges_uniform_deck`: the macro/deck TV identity for ideal local shuffles.
- `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`: the exact existing three-step `q3` theorem.

### D1. Why a *deterministic* segregated start has the same ideal evolution

The existing exact theorem starts from a distribution uniform in the **whole count fiber** at count 50, not from a single ordered deck. This distinction cannot be dropped silently.

However, at `N=99,m=r=50`, count 50 has exactly **one possible membership** (all 50 marked cards on the left). Every deck in that count fiber has the same membership as the reference ordered deck `d0`. An exchange followed by a perfect-local reset depends only on the current membership, not on the within-pile order. Therefore **after one ideal round**, a point start `δ_{d0}` and a fiber-uniform count-50 start have *identical* laws; by kernel composition their three-round laws are identical.

Prove two general lemmas, in this order. **Do not assert row factorization for the *finite* GSR kernel:** stable sorting with finitely many labels can retain information about the old within-pile ordering. The membership-only assertion below is specifically for the **perfect-local ideal kernel**.

1. **Row factorization:** if `membership d = membership e`, then `J d = J e` for ideal swap-then-local kernel `J`. Derive this from D's abstract kernel equality; do not inspect the fibers pointwise.
2. **Constant-on-fiber averaging:** if `μ` is supported in one membership fiber and rows agree there, `FiniteKernel.apply μ J = J d0`. This follows from `FiniteKernel.apply` being a convex combination and the total mass of `μ` being 1. Prove once for abstract finite distributions.

Now the exact `three_physical_perfect_exchanges_uniform_unconditional` supplies the desired ideal `q3` for a **single** reference deck. Alternatively, prove the first step gives a uniform count-25 fiber: each valid target membership is determined by the 25 outgoing and 25 incoming card subsets, and the conditional local law is uniform on that target's full ordering fiber.

**Checkpoint D:** a compiled equality between the three-step correct `idealRound` law from the fixed reference deck and the corresponding already-proved perfect-local three-step law, or a compiled TV equality to `q3`. The equality must not refer to `gsrRound99Ideal`'s constant-row kernel.

### D2. Arbitrary starting decks come essentially for free from colorblindness

The random swap choices and local GSR labels are independent of card *names*. Let `f` relabel card identities, represented by `d.trans f`. For the correct position-action kernel,

\[
 K(d\,\mathrm{trans}\,f) = K(d).\mathrm{map}(\lambda e.\,e\,\mathrm{trans}\,f).
\]

This is pointwise associativity of `Equiv.trans` inside `Dist.map`. No new counting. The **uniform deck law** is invariant under this bijective relabeling (`GSR.map_bijective_uniformDist`).

A particularly helpful abstract TV lemma follows from B1 **twice**. If `e : A ≃ B`, then

\[
 \mathrm{TV}_{\mathrm{supp}}(\mu.\mathrm{map}\,e,\nu.\mathrm{map}\,e)
 =\mathrm{TV}_{\mathrm{supp}}(\mu,\nu).
\]

Proof: B1 gives `≤`; apply B1 again with `e.symm` to get `≥`, using `StdSimplex.map_map` and inverse equivalence identities. **Do not calculate fibers or cardinalities** to show TV invariance under a bijection.

Every `d : Deck N` is a card relabeling of the identity reference arrangement. Induct over the three correct `K` steps, using kernel equivariance to transfer the entire output law. Apply the TV bijection-isometry and invariance of the uniform target. This establishes the identical TV bound for **every deterministic input deck**, and then for any initial distribution by convexity.

**Checkpoint E:** a compiled theorem `∀ d : Deck 99, tvFinsupp (run finiteRound 3 (pointMass d)) (uniformDist (Deck 99)) ≤ q3 + 3*δ1` after D and E's generic equivalence lemmas are complete.

---

## E. The last quantitative step: telescope without `max'` over all decks

The old `Dobrushin.kernelDiscrepancy` and `errorBudget` use `Finset.max'` over deck rows. For `Perm (Fin 99)` this is not an attractive object to elaborate. We need only a **uniform pointwise bound** `∀ d, TV(K d,J d) ≤ δ1` (checkpoint B), not a computed maximum.

The support-only metric needs two small generic lemmas not visibly available in `TotalVariation.lean` as of this snapshot.

### E1. Support-only TV triangle

**PROPOSED:**

```lean
theorem tvFinsupp_triangle
    {X : Type*} [DecidableEq X] (μ ν ξ : Dist X) :
    tvFinsupp μ ξ ≤ tvFinsupp μ ν + tvFinsupp ν ξ := by
  ...
```

Let `S := supp μ ∪ supp ν ∪ supp ξ`. Enlarge each pair's support sum to `S` with the already-proved `l1OverEnlarged_eq_twoTv`. Apply `|a-c|≤|a-b|+|b-c|` pointwise; sum, then divide by two. No `Fintype X` and no global enumeration.

### E2. Mixture of pointwise-close rows stays close

**PROPOSED:**

```lean
theorem tvFinsupp_apply_same_input
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (μ : Dist X) (K J : FiniteKernel X Y) :
    tvFinsupp (FiniteKernel.apply μ K) (FiniteKernel.apply μ J) ≤
      μ.weights.support.sum
        (fun x => Dist.mass μ x * tvFinsupp (K x) (J x)) := by
  ...
```

Use `FiniteKernel.apply_mass_finsupp` for the two mixtures. Sum over the finite union of the output supports (enlarged by the finitely many row supports); pointwise use

\[
\left|\sum_x\mu(x)(K_x(y)-J_x(y))\right|
\le\sum_x\mu(x)|K_x(y)-J_x(y)|,
\]

then interchange the two finite sums. This is the **two-variable** counterpart of the already-proved `mixtureTV_le` (which compares a mixture against a single constant reference law). Read that existing proof and reuse its support-bounding machinery; do not duplicate it wholesale. If every row distance is at most `δ1`, its RHS is at most `δ1` by `μ.total`.

### E3. The three-round result by a two-term induction

For any `μ,ν`, using E1, E2, and the existing `kernel_apply_lipschitz`,

\[
\begin{aligned}
TV(\mu K,\nu J)
&\le TV(\mu K,\mu J)+TV(\mu J,\nu J)\\
&\le \delta_1+TV(\mu,\nu).
\end{aligned}
\]

Apply this recursively starting from the *same point mass*: after three steps,

\[
TV(K^3\delta_{d_0},J^3\delta_{d_0})\le3\delta_1.
\]

Use E1 once more with the known `TV(J^3δ_{d0},Uniform)=q3`, then the proved `gate6_headline_bound`. Do not invoke `kernelDiscrepancy`, `dobrushinCoeff`, `max'`, or `vectorTV` on `Deck 99`.

**Checkpoint F:** actual three-round `TV ≤ q3+3δ1<1/1000` from the reference ordered deck, followed by every-deck extension. The final theorem can be stated in `tvFinsupp` until the generic `Dist.tv = tvFinsupp` rewriting is safe; the metrics are mathematically identical.

### E4. Alternate route if E2 causes a new wall: couple the entire protocol

Rather than telescope, draw **all** random noise for three rounds jointly: exchange choices, finite GSR labels, and independent uniform tie-breaking permutations. Feed the *same* exchange choices into a finite protocol and an ideal protocol; in each pile/riffle, let the ideal shuffler use Qwen's proven `tieRank` and the finite shuffler use `rankEquiv`. Their output decks agree whenever there is no label collision in any of the six pile shuffles (left/right × three rounds). The mismatch event has probability at most

\[
3\,\frac{\binom{50}{2}+\binom{49}{2}}{2^{23}}=3\delta_1.
\]

A general **support-only** same-source coupling theorem then gives `tvFinsupp ≤ P(mismatch)` without a full-deck sum. Qwen's existing `Dist.tv_maps_le_mismatch` proves this with `[Fintype Ω] [Fintype X]`; lift its proof to `tvFinsupp` over finite *supports* rather than rerunning it at `X=Deck 99`. This approach avoids E2 and even the local-kernel TV product proof, at the expense of building a more complicated noise-source type and an induction that tracks coupling through all rounds. Use it as plan B, not as another simultaneous speculative development.

---

## F. A small backup result that diagnoses model errors early

There is an intermediate all-deterministic-start **perfect-local** bound with more rounds, separate from the three-round finite objective.

For the segregated reference deck, one physical swap plus a perfect local shuffle produces a law uniform in the count-25 fiber (reason in D1). The proved `physicalExchange_decay_41_lt_thousand` applies to that fiber-uniform law. Thus **42 perfect-local rounds** from the reference deck have TV `<1/1000` (one round to get into the uniform count fiber, then 41 to mix). By the colorblind relabeling argument, the same bound extends to any deterministic initial ordering, once the physical kernel equivalence has been proved.

This is a useful **optional** checkpoint for validating D1/D2/E, and a nontrivial strengthening of the currently documented 41-step *fiber-uniform* result. It is **not** the requested three-round finite-riffle certificate. Do not divert to improving 41 to 40 before the actual Gate 6 theorem is complete.

---

## G. Why the old 99! 'definitive wall' diagnosis is too strong

The probes establishing maximum-recursion failures are evidence that *particular terms and reductions* are impractical. They do **not** establish a mathematical unprovability, or even that Lean must change. The source already compiles generic theorems about `Dist`, `FiniteKernel`, and the local permutation TV law. The new architecture is deliberately proof-parametric:

- Work at `α`, `β` or symbolic `N,m` for TV/support and uniform-fiber theorems.
- Use `StdSimplex.map`, `join`, `Finsupp` supports, and existing generic laws, not global `Fintype` enumeration at 99.
- Keep noise laws opaque and apply their published theorems. Specialize only the **final theorem application**, never the proof's normalization steps.
- Do not make `maxHeartbeats 0`, `native_decide` over decks, or a higher recursion limit the main strategy.
- If a polymorphic theorem itself forces heavy normalization, isolate exactly which class instance or definitional equality is unfolding; rewrite via an explicit interface lemma or a small abstract equivalence. Treat that as a precise elaboration problem, not evidence the mathematics needs changing.

There is also a useful architectural reason to do this now: everything in B/C/D/E can be reused for arbitrary `N`, unequal pile sizes, several piles, and other category histograms. Commander remains a numerical specialization.

## H. Suggested small-file implementation sequence

These are *suggested new module boundaries*, not required names. Prefer small modules; do not create/switch worktrees, and do not overwrite unrelated changes. Compile each new unit and expose only established theorems.

| Step | New generic unit or existing module | Deliverable / acceptance |
|---|---|---|
| 1 | `FiniteDeck/PositionAction.lean` | `permutationActionKernel`, `swapThenLocalKernel`, orientation + relabeling lemmas; no constant rows |
| 2 | `FiniteSupportTV.lean` or `TotalVariation.lean` | `tvFinsupp_map_le`, `tvFinsupp_common_product`; symbolic type variables |
| 3 | `GSRDeckRound.lean` | Symbolic `rhoRoundTransport_support_bound`; concrete `≤ δ1` row bound via Step 2 |
| 4 | `FiniteDeck/UniformOrbitLaw.lean` | Generic uniform-subtype and fiber-equivalence pushforward theorem; ideal local group action = `localLift` |
| 5 | `FiniteDeck/IdealPhysicalRound.lean` | Actual exchange + uniform local action factors through proven membership exchange; deterministic segregated reference → `q3` |
| 6 | Support-TV module | `tvFinsupp_triangle`, `tvFinsupp_apply_same_input`; three-step rowwise telescope, no deck-row maxima |
| 7 | `FiniteDeck/Gate6Concrete.lean` | Reference-start TV <1/1000; arbitrary-start via card relabeling; optional arbitrary initial law by mixture |
| 8 | Documentation / quality | Correct handoff scope, retire misleading constant-row comments, verify production import graph and `dev/verify_next_phase.sh` |

Keep the older modules and dated reviews for historical analysis. If Step 2's support-TV lemmas compile but Step 3 fails, the failure is now in a **small wrapper between equivalent metrics**; do not retreat to the 99! distribution expansion. If Step 4 fails, prove the generic `uniformSubtype.val` lemma independently before mentioning any cards. If Step 5 fails, inspect the **action order and random-step semantics first**, not the factorial counts.

**Definition of done:** an unconditional theorem for the *literal physical* 99-card protocol containing 25 selected positions per pile per round, deterministic (but arbitrary) pairing of those selected positions, 23 independent binary inverse-GSR riffles **on each pile after each exchange**, repeated three times from **any specific ordered starting deck**, with exact rational total-variation bound `<1/1000` against uniform on all 99-card permutations. It must compile with no `sorry` or new axioms. The already-proved perfect-local 41-step theorem, one-round local GSR TV bound, conditional constant-kernel telescope, and numeric inequality are prerequisites or sanity checks—not substitutes.
