# Direct mathematical hints: close Gate 6 K1 without K1b count-split

**Date:** 2026-11-24. **Source:** Git snapshot `7d02441`. **Status:** a proof-design document, **not** compiled Lean. All suggested declaration names below are proposed names; exact Lean terms must be checked against the pinned Mathlib. Use the actual source declarations identified here rather than trying to import this Markdown as a module.

## 0. Read this first: an entire difficult proof can be deleted from the critical path

The active handoff directs you to implement a ~230-line `k1b_count_split` based on inverse witnesses and 25/25 position choices. That work is driven by a **representation mismatch**:

```
current ideal law     = conv rho99Ideal swapLaw       -- local THEN swap
physical target       = swap THEN local reset
intended ideal law    = conv swapLaw rho99Ideal       -- swap THEN local
```

The equivalence `act_composition` in `FiniteDeck/ActionConvolution.lean` proves, for arbitrary finite `N`, that

\[
\operatorname{act}(a*b,d)=\operatorname{act}(b,\operatorname{act}(a,d)).
\]

The existing `swap_then_local_matches_star` in `FiniteDeck/PositionAction.lean` confirms the `Equiv.trans` orientation. **Do not let contradictory prose comments override these proved equations.** For `s` a swap and `g` a local permutation, the intended deck is `g.trans (s.trans d)` and the combined permutation law is `s * g`.

The current code in `Gate6Crux.fullRoundIdeal` and `fullRoundFinite` uses `conv rho99* swapLaw`. The K1b counting chain is trying to show that the **uniform** local law happens to commute *distributionally* with swaps. Even if true, this does not make the **finite** GSR law commute and does not certify the physical order required in `docs/planning/goals/2026-11-23-gate6-physical-certificate-goal.md`.

**Concrete orientation regression (checked by exact enumeration):** for `N=6,m=3,k=2`, uniform 2/2 position selections with sorted pairings, and the fixed right-pile transposition `h=(4 5)`, starting at the identity deck, the swap-then-`h` law reaches `(4,5,2,3,1,0)` whereas the `h`-then-swap law does not. For *uniform* within-pile shuffles these two laws do agree in this small example, but relying on that coincidence would demand an extra theorem and does not validate swapping a finite GSR distribution past the exchange.

**Immediate action:** create a new scratch proof module for the correct order; leave existing compiled modules intact while working. Once the new chain compiles, migrate the canonical `fullRound*` definitions and their dependent theorems. Stop treating the old `k1b_swap_half` as the blocking task.

## 1. Set up two fresh, correct-order distributions

The **definitions** (not a claimed Lean proof) are:

```lean
noncomputable def physicalIdealRound : Dist (Equiv.Perm (Fin 99)) :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Ideal

noncomputable def physicalFiniteRound : Dist (Equiv.Perm (Fin 99)) :=
  FiniteDeck.conv Gate6Crux.swapLaw Gate6Crux.rho99Finite
```

For the deck-action kernels, use

```lean
FiniteDeck.permutationActionKernel physicalIdealRound
FiniteDeck.permutationActionKernel physicalFiniteRound
```

`_ProbeGate6K1.convPush_eq_pointMassComp` is **already proved generically**, so for every `d`:

\[
(\texttt{physicalIdealRound}).\operatorname{map}(p\mapsto\operatorname{act}(p,d))
=\operatorname{apply}(\delta_d,\operatorname{comp}(K_{\rm swap},K_{\rm idealLocal})).
\]

The order of `FiniteKernel.comp` is execution order: swap then local. No `99!` sum or enumeration is required. **First show this as a small theorem, using the existing generic lemma with `μ := swapLaw` and `W := rho99Ideal`.** Avoid unfolding either law in the statement or proof.

## 2. The riffle half is already stronger than you need

Existing theorem (in `_ProbeGate6K1.lean`, after the source's namespaces):

```lean
k1a_riffle_half (d : Equiv.Perm (Fin 99)) :
  FiniteKernel.apply (Dist.pointMass d)
    (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) =
  FiniteKernel.apply
    (Dist.pointMass (CommanderMembershipKernels.membership d))
    CommanderMembershipKernels.localLift
```

Use `FiniteKernel.apply_pointMass` **on both sides** to derive the row equality

\[
K_{\rm idealLocal}(d)
=\operatorname{localLift}(\operatorname{membership}(d)).
\]

By `funext d`, derive the **kernel identity**

\[
\boxed{K_{\rm idealLocal}=\operatorname{comp}(\operatorname{deterministic}(\operatorname{membership}),\operatorname{localLift}).}
\]

This is the same as `PhysicalExchangeReduction.localReset membership localLift`. Proof sketch for Qwen:

```lean
-- SKETCH, uncompiled: use the actual implicit arguments and imports.
theorem idealLocalKernel_eq_localReset :
    FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal =
      PhysicalExchangeReduction.localReset
        CommanderMembershipKernels.membership
        CommanderMembershipKernels.localLift := by
  funext d
  -- convert each side to a point-mass kernel application;
  -- rewrite with `FiniteKernel.apply_pointMass`;
  -- exact `k1a_riffle_half d`.
```

**No extra orbit theorem** is needed. `k1a_riffle_half` already supplied the uniform pushforward with its factorial normalization. Do not re-prove the orbit equivalence or expand `localLift_mass` to derive a weaker statement.

Before moving this into a production module, **extract** `k1a_riffle_half` and only its necessary dependencies from `_ProbeGate6K1.lean` so the production import graph never depends on that file's unrelated `sorry`.

## 3. The swap membership law is a pushforward, not a counting problem

Write `C` for `CommanderPhysicalExchange.exchangeChoice`, with its uniform law `U_C`. For `c : C`, let `s(c)` be the literal position permutation from `Gate6Crux.swapLaw` (using `canonicalPairing`). Then, from the definitions,

\[
K_{\rm swap}(d)=U_C.\operatorname{map}(c\mapsto \operatorname{act}(s(c),d)).
\]

Existing theorem (`_ProbeK1b.lean`):

```lean
K1a_stmt_only d L hL R hR b :
  CommanderMembershipKernels.membership
    ((FiniteDeck.swapPerm 99 50 h50le99 L R b).trans d) =
  CommanderPhysicalExchange.newMembership d L hL R hR
```

In particular it holds for `b = Gate6Crux.canonicalPairing ...`. The law of the new membership is therefore **literally the same map of the same uniform choice law**:

\[
\boxed{
K_{\rm swap}(d).\operatorname{map}(\operatorname{membership})
=\operatorname{rawExchangeMembership}(d).
}
\]

This equality is pointwise in the chosen `(L,R)`; it does not depend on the pairing or on reverse-choice counts. No 25/25 counting split is required.

**Lean recipe (target the following intermediate statements in order):**

1. A **generic Fintype-free monadic unit** lemma for `Dist`: `apply μ (deterministic f) = μ.map f`. The existing `FiniteKernel.apply_deterministic_eq_map` has `[Fintype α] [Fintype β]` assumptions and a proof over `Finset.univ`; avoid making it elaborate `Fintype (Equiv.Perm (Fin 99))`. Prove the same identity generically from `Dist.pointMass`, `Convexity.StdSimplex.map_map`, and the `map`/`join` unit law (or the Finsupp `sum` over the *support*). Keep its types abstract.
2. `Kswap_row_map`: `(FiniteDeck.permutationActionKernel swapLaw d).map membership = rawExchangeMembership d`. Expand `swapLaw` **only inside a small helper**; use `Convexity.StdSimplex.map_map` to fuse the two maps, then `funext c` and `K1a_stmt_only` with the canonical pairing. The `exchangeChoice` structure and `leftCard25`/`rightCard25` proofs are already in `CommanderPhysicalExchange.lean`.
3. `Kswap_projects_membership`: `FiniteKernel.comp (permutationActionKernel swapLaw) (FiniteKernel.deterministic membership) = rawExchangeMembership`. Use `funext d`, the generic monadic unit, then the previous row map.

The source names to consult, **not rebuild**, are `Gate6Crux.swapLaw`, `Gate6Crux.canonicalPairing`, `Gate6Crux.exchangeLCard`, `Gate6Crux.exchangeRCard`, `CommanderPhysicalExchange.rawExchangeMembership`, and `_ProbeK1b.K1a_stmt_only` (in namespace `Shufflemath`).

### Why this eliminates the hard K1b counting

The old chain attempts to identify

\[
\operatorname{apply}(U_{F_{m(d)}},K_{\rm swap})
\quad\text{and}\quad
\operatorname{apply}(\operatorname{rawExchangeMembership}(d),\operatorname{localLift}).
\]

That is a **local-then-swap vs swap-then-local** distributional equivalence. The corrected chain only needs to push `membership` through **one literal swap from the current deck**. The latter is already the content of `K1a_stmt_only`, with no invariant-subset double counting.

## 4. K1 is now kernel associativity

Use the two boxed kernel identities:

\[
K_{\rm idealLocal}=\operatorname{det}(m);\operatorname{localLift},
\qquad K_{\rm swap};\operatorname{det}(m)=\operatorname{rawExchangeMembership}.
\]

Then, by associativity of `FiniteKernel.comp`,

\[
\begin{aligned}
K_{\rm swap};K_{\rm idealLocal}
&=K_{\rm swap};\operatorname{det}(m);\operatorname{localLift}\\
&=\operatorname{rawExchangeMembership};\operatorname{localLift}\\
&=\operatorname{rawExchange}.
\end{aligned}
\]

The final equality is **the definition** of `CommanderPhysicalExchange.rawExchange`. `FiniteKernel.comp_assoc` is already proved without a 99-card sum. `PhysicalExchangeReduction.exchangeThenLocalReset` is formally `rawExchange ; (det membership ; localLift)`; because `rawExchange` *already ends in `localLift`*, `CommanderMembershipKernels.localLift_preserves_membership` shows the extra reset is idempotent. The existing `k1_rhs_bookkeeping` proves this statement at a point mass; reuse it if that is the easiest path.

**Desired K1 statement (fresh correct-order name):**

```lean
-- PSEUDOCODE: adapt namespace, definitional lemma names, and imports.
theorem physicalIdealRound_eq_exchangeThenLocalReset
    (d : CommanderPermutation.Deck) :
    physicalIdealRound.map (fun p => FiniteDeck.act p d) =
      FiniteKernel.apply (Dist.pointMass d)
        (PhysicalExchangeReduction.exchangeThenLocalReset
          CommanderMembershipKernels.membership
          CommanderMembershipKernels.localLift
          CommanderPhysicalExchange.rawExchange) := by
  -- 1. `convPush_eq_pointMassComp swapLaw rho99Ideal d`.
  -- 2. Rewrite `idealLocalKernel_eq_localReset`.
  -- 3. Associate kernels, rewrite `Kswap_projects_membership`.
  -- 4. `rawExchange` definition, `localLift_preserves_membership`.
```

There is **no reason** for this theorem to mention `k1b_beta`, `leftWitness`, `rightWitness`, `k1b_count_split`, or the 230-line `/tmp` handoff.

## 5. Reconstruct the TV bound in the correct order

The already-proved `Gate6Crux.convContraction F I S` handles

\[
\operatorname{TV}(F*S,I*S)\le\operatorname{TV}(F,I)
\]

because its common noise factor is on the **right**. The physical round needs the **mirror** inequality

\[
\boxed{\operatorname{TV}(S*F,S*I)\le\operatorname{TV}(F,I).}
\]

Do **not** rewrite `S*F = F*S`: finite GSR permutations do not generally commute with swaps. Instead use either of these two genuinely generic proofs.

### Preferred route: left-convolution as application of a common kernel

For a fixed swap distribution `S`, define a kernel **whose input is the local permutation**:

\[
L_S(g)=S.\operatorname{map}(s\mapsto s*g).
\]

Then

\[
\operatorname{conv}(S,F)=\operatorname{apply}(F,L_S),
\qquad
\operatorname{conv}(S,I)=\operatorname{apply}(I,L_S).
\]

This is a change of summation order in the finite product support (Fubini). Once the identity is proved with abstract `N` and `S,F`, the inequality is **one application** of

```lean
Shufflemath.kernel_apply_lipschitz F I L_S
```

The relevant generic building blocks already exist: `FiniteDeck.conv`, `FiniteKernel.apply`, `distProductFinsupp`, `FiniteDeck.joinMapComm`, and `Convexity.StdSimplex.map_map`.

**Proposed standalone helpers:**

```lean
-- PSEUDOCODE, not compiled.
noncomputable def leftConvolutionKernel {N : Nat}
    (S : Dist (FiniteDeck.Deck N)) :
    FiniteKernel (FiniteDeck.Deck N) (FiniteDeck.Deck N) :=
  fun g => S.map (fun s => s * g)

theorem convLeftAsApply {N : Nat} (S F : Dist (FiniteDeck.Deck N)) :
    FiniteDeck.conv S F = FiniteKernel.apply F (leftConvolutionKernel S) := by
  -- Fubini/map-join on finite supports, abstract N only.

theorem convLeftContraction {N : Nat}
    (S F I : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv S F) (FiniteDeck.conv S I) ≤
      tvFinsupp F I := by
  rw [convLeftAsApply S F, convLeftAsApply S I]
  exact kernel_apply_lipschitz F I (leftConvolutionKernel S)
```

The essential insight is that **the two distributions `F` and `I` see the same stochastic kernel `L_S`**. No explicit `Fintype (Deck 99)` is needed in the generic proof.

### Alternative route: shared-product law + deterministic-map contraction

If the kernel identity above is awkward in Lean, first prove a Fintype-free `tvFinsupp` deterministic-map contraction at abstract types `X,Y` and then combine:

\[
\begin{aligned}
\operatorname{TV}((S\otimes F).\operatorname{map}(\cdot*\cdot),
                     (S\otimes I).\operatorname{map}(\cdot*\cdot))
&\le\operatorname{TV}(S\otimes F,S\otimes I)\\
&\le\operatorname{TV}(S,S)+\operatorname{TV}(F,I)\\
&=\operatorname{TV}(F,I).
\end{aligned}
\]

`Shufflemath.distProductFinsupp_tv_subadditive` is already proved **without `Fintype`**. A deterministic `map` should be treated as kernel application and the same `kernel_apply_lipschitz` used. Don't use the existing `Dist.tv_map_contraction` proof specialized to `Fin 99` (its `[Fintype Ω]`-based universe sums are exactly the old elaboration risk).

Once the generic inequality compiles, instantiate `S := swapLaw`, `F := rho99Finite`, `I := rho99Ideal`; then use the **already-proved** `oneRoundDeckTV_le_delta1`. Do not redo collisions or the product-of-two-piles TV estimate.

## 6. Finish the real three-round theorem without a new 99! sum

Set

```
K := permutationActionKernel physicalFiniteRound
L := permutationActionKernel physicalIdealRound
δ := 2401 / 8388608
```

The correct-order one-round law inequality plus pushforward TV contraction gives, for **each** starting deck `d`,

\[
\operatorname{TV}(K(d),L(d))\le\delta.
\]

A generic mixture/triangle/telescope argument yields

\[
\operatorname{TV}(\mu K^3,\mu L^3)\le 3\delta.
\]

`Shufflemath.kernel_apply_lipschitz` and `Shufflemath.run_nonexpansive` are Fintype-free. `TelescopeF5.telescopeTV_le_idealPlusN` assumes a `Fintype` and may instantiate expensive 99-card universes; extract a generic **support-based** three-round row-bound version if that happens. The essential induction is:

\[
\operatorname{TV}(\mu K^{t+1},\mu L^{t+1})
\le \operatorname{TV}(\mu K^t K,\mu K^t L)
   +\operatorname{TV}(\mu K^t L,\mu L^t L)
\le\delta+\operatorname{TV}(\mu K^t,\mu L^t).
\]

**A final logical dependency is separate from the telescope:** `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional` starts from the **uniform segregated fiber** (see its `fiberLaw project ...` input), not a deterministic deck. Prove that from one fixed segregated reference deck, the **first ideal round** has the same distribution as from that fiber-uniform start. Why it works: the 25/25 exchange selects uniformly 25 of the marked left cards and 25 of the unmarked right cards; the *following* uniform local permutation removes all ordering information. It leaves the uniform membership/deck law on the 25-marked-card count fiber.

One way to prove the first-round lemma is through the already-general two-pile subset-exchange result and uniform-fiber disintegration, not direct `99!` counting. The required equality is **between first-round output laws**; relabeling alone does not bridge a deterministic input to a fiber-uniform input.

Then apply the existing ideal three-round `q3` result, and use the pre-proved card-relabeling invariance in `FiniteDeck/RelabelInvariance.lean`: any deterministic deck is a relabeling of the reference deck, and position-only shuffle noise commutes with relabeling. Uniform full-deck measure is relabeling invariant; hence TV to uniform is the same from all deterministic starts. (An arbitrary *distribution* of starts can then be handled by convexity/mixture contraction if desired.)

## 7. An optional general theorem explains why the old K1b identity can hold

Do **not** pursue this for the Gate 6 critical path. It is valuable mathematics for the arbitrary-`N` roadmap and may later let you salvage the K1b combinatorial work in a cleaner form.

Let `X` be a finite deck state space, `m : X → Y` its membership observation, and `P` a **symmetric** microscopic Markov kernel. Assume **strong lumpability**: for a deck with membership `a`, the probability of ending in membership `b` equals `Q(a,b)`, independently of the deck's internal ordering. For the fixed-cardinality membership space, all fibers have the same cardinality `c = m!(N-m)!`. Then for a deck `z` in membership fiber `b`,

\[
\begin{aligned}
(U_{F_a} P)(z)
 &= \frac1c \sum_{x\in F_a}P(x,z)\\
 &= \frac1c \sum_{x\in F_a}P(z,x)\\
 &= \frac1c Q(b,a).
\end{aligned}
\]

If the quotient `Q` is symmetric too (as the uniform subset-exchange law is; see `FiniteDeck.SubsetExchange.subsetExchangeKernel_symm`), this is `Q(a,b)/c`: exactly `Q(a,\cdot)` followed by the uniform fiber lift. This explains the equality behind the old `k1b_swap_half` **without the inverse-choice witness construction**.

To use this, one would still need a clean bridge from the literal position-swap kernel to the symmetric subset-exchange quotient, and a proof that the position-swap kernel itself is symmetric (uniform law on involutions suffices). All those assumptions must be explicit. It is a good *later* abstraction, not a reason to delay correct-order K1.

## 8. Acceptance gates and debugging traps

- **Gate A:** a small, separately built probe defines `physicalIdealRound` and `physicalFiniteRound` in the *correct order*. It uses only `convPush_eq_pointMassComp`, not 99-card expansion.
- **Gate B:** a placeholder-free production `idealLocalKernel_eq_localReset` from `k1a_riffle_half`, and `swapLaw_membership_pushforward` from `K1a_stmt_only`, compile independently. No new orbit or overlap counting.
- **Gate C:** the complete correct-order K1 theorem compiles, without importing any `sorry`-bearing probe into the production theorem chain.
- **Gate D:** `convLeftContraction` is proved for general `N` (or arbitrary finite-support types) and gives `TV(physicalFiniteRound, physicalIdealRound) ≤ δ` by specialization.
- **Gate E:** a state-dependent three-round telescope and deterministic-first-round bridge compile, then the actual every-deterministic-start `TV < 1/1000` theorem is imported and built.
- **Gate F:** after Gate 6, continue the finite-deck planning roadmap. Neither an unfinished K1b experiment nor a checked-in review counts toward the end-to-end certificate.

**Lean tactics to avoid at concrete 99:** `simp` on the entire `localLift`, unfolding `Fintype (Equiv.Perm (Fin 99))`, `Finsupp` construction of an all-deck `univ`, increasing `maxRecDepth`/`maxHeartbeats` to silence nontermination. `rw`/`change` against *abstract already-proved kernel equalities* is safer. If a specialized `rw` triggers WHNF, move the equality into a generic helper and instantiate with `exact` rather than reducing the concrete term.

**Source bookkeeping to remember:** `_ProbeK1k.lean` still has `sorry`; its next-proof handoff references `/tmp/k1b_count_split_handoff.md`, absent from the uploaded archive. `Gate6Crux` is imported by the main verification script; the K1 probes generally are not. The `.pi-glla` loop currently refers to the November 20 documents. Fix the loop goal separately via the provided goals file.
