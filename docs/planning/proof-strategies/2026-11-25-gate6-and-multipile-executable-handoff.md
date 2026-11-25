# 2026-11-25 — executable handoff: finish Gate 6, then build G5 by gluing

Base: `3dc079aa7d92`. This is the current action list. Earlier external evening
handoff was not delivered; do not assume its files exist. Read the companion
review for evidence. The canonical restricted-start headline already exists.
The two isolated `.lean` files in `dev/qwen-hints/2026-11-25/` are **uncompiled
candidates**, not new established lemmas. Compile each separately, correct
ordinary syntax/API errors, then migrate successful declarations to natural
library homes. No need to apply the previous undelivered overlay.

## 0. Dispatch: one small obligation at a time

- Gate 6 actual finish line: a theorem with `∀ d : Deck`, input `Dist.pointMass d`,
  three *state-dependent* rounds, each a uniform 25/25 literal position swap
  followed by a stable-sort 2^23-label local shuffle (and a theorem identifying
  that operation with 23 independent binary inverse-GSR riffles). TV < 1/1000
  against the uniform deck law. A theorem only for `g6ThreeRoundStart` does not
  meet this requirement. Preserve it as an existing result.
- A0 batch-5b is a corollary (below); do not resume its Finset subset proof.
- A1 prove uniform choice row independence. A2 absorb first ideal reset and
  derive deterministic reference start. A3 correct finite law and use existing
  telescope. A4 transport to arbitrary starts. A5 binary interpretation.
- G5 now has type definitions. Continue with B1-B4 below, then C and D. If a
  bounded Gate 6 proof attempt fails, record the exact failed declaration and
  switch to a small G5 obligation; return with a precise lemma, not hours of
  retries. Do not declare Gate 6 complete just because you switched tasks.
- No `maxHeartbeats 0`, escalating recursion limit, or broad `simp`/`decide` on
  a concrete permutation universe. Work at abstract `X Y`, distributions as
  variables, and generic `N` only if a group structure is needed. A generic
  theorem can still have expensive reducible definitions: abstract the laws
  themselves. Favor term-level `exact`, explicit `calc`, `congrArg`, `Eq.subst`
  with the predicate written out; those worked in the committed Gate 6 proof.
- Run `lake build <imported target>` before `lake env lean dev/qwen-hints/...`
  if needed. Build one seed file at a time. Split failed declarations into their
  own scratch file with narrow imports; check direct compiler diagnostics.
  Build the final real module, add it to aggregator and targeted verification.
  Do not add a WIP seed to a public import graph. Follow AGENTS.md's ordinary
  verification policy, not a new recurring axiom audit.

## A0. Batch 5b is already proved at a stronger level

`k1_bridgeA` in file `Gate6K1BridgeA.lean` is in namespace `Shufflemath` (not a
`Gate6K1BridgeA` namespace):

```
permutationActionKernel Gate6Crux.rho99Ideal =
  FiniteKernel.comp (FiniteKernel.deterministic CommanderMembershipKernels.membership)
    CommanderMembershipKernels.localLift
```

`paK_rho99Ideal_eq_localLift` (`Gate6K1Capstone.lean`) gives this equality at
any deck directly. Let `d0 := Equiv.refl (Fin 99)`. The action noise at `d0`
is the noise itself (`permutationActionKernel_eq_map`, `map_id`); hence
`rho99Ideal = localLift (membership d0)`. Use candidate `ideal_batch5b`.
`GSRSegMembership.leftCards_id_eq_segLeft` is likewise a declaration in
`Shufflemath`; use `membership_leftCards`, `segMembership_one_eq_segLeft`,
`Subtype.ext` to identify `membership d0 = segMembership`. Proofs of subtype
membership are irrelevant. Use `congrArg localLift` on that equality. Do not
compare two huge `Finset.univ` images. If concrete `Equiv.ext` on the identity
wall is an issue, prove `(fun p : FiniteDeck.Deck N => p.trans (Equiv.refl _)) = id`
with variable `N` first, then apply by name. This resolves the batch-5b request
without inspecting `_Probe5b` at all.

## A1. The missing mathematical fact: row independence, not macro independence

Let X = decks, Y = left-pile memberships. P is deterministic membership,
U = localLift, E = rawExchangeMembership : X -> Dist Y. We already have
`K1_swapFirst_eq_exchangeLift`: the ideal position round equals `E ; U`.
The new claim is:

```
∀ d e : CommanderPermutation.Deck,
  CommanderMembershipKernels.membership d = CommanderMembershipKernels.membership e →
  CommanderPhysicalExchange.rawExchangeMembership d =
    CommanderPhysicalExchange.rawExchangeMembership e
```

Do NOT claim `newMembership d L R = newMembership e L R` for each fixed
position choice. Different orderings choose different cards. It is the
**uniform law over choices** that is unchanged. Do NOT try to deduce this
from `hMembershipExchange` (that only averages over a macro fiber).

### A1.1 Define the choice map once

In a narrow Commander bridge module:

```lean
open CommanderPhysicalExchange CommanderMembershipKernels
-- Avoid opening FiniteDeck's membership as well.
def choiceOut (d : CommanderPermutation.Deck) (c : exchangeChoice) : Membership :=
  newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)
```

`E d = (GSR.uniformDist exchangeChoice).map (choiceOut d)` by rfl. Prove
`Function.Injective (choiceOut d)` with this exact proof structure:

1. `intro c c' h`; use `congrArg Subtype.val h` (annotate input type
   `Membership` if Lean guesses another subtype).
2. `change newLeftCards d c.1.1 c.2.1 = newLeftCards d c'.1.1 c'.2.1 at ...`.
3. `obtain ⟨hL,hR⟩ := newLeftCards_injective d c.1.1 c'.1.1 c.2.1 c'.2.1 ...`.
   This is the exact argument order in `CommanderPhysicalExchange.lean`.
4. `exact Prod.ext (Subtype.ext hL) (Subtype.ext hR)`.

### A1.2 Show range membership = reachable relation without building inverses

Let `S := membership d`. Define `Reach S := FiniteDeck.ReachSet 99 50 25 ... S`
(the two Membership types are definitionally the same; this is already used
by `k1_bridgeA`). `ReachSet` uses both `sdiff` cardinalities = 25.
Use `newMembership_overlap_25 d ...` to show every `choiceOut d c` lies in
`Reach S`. If needed, first prove an abstract Finset lemma:

```
S.card = m → T.card = m → (S ∩ T).card = m-k →
  (S \ T).card = k ∧ (T \ S).card = k
```

Require `k ≤ m`. Use `Finset.card_sdiff` twice, commute the intersection,
and arithmetic (`omega`). Work over abstract `Finset α`, not Deck. In code
use Lean's single backslash for finset difference. Then `simp only
[ReachSet, Finset.mem_filter, Finset.mem_univ, true_and]` closes the predicate.

**The missing surjection is a cardinality argument, not inverse counting.**
Use the supplied candidate `range_iff_mem_of_card_eq` for this generic finite-type lemma:

```
(A : Type) [Fintype A] [DecidableEq A] (f : A → B)
(R : Finset B) [DecidableEq B]
hf : Injective f; hR : ∀ a, f a ∈ R; hcard : Fintype.card A = R.card
⊢ ∀ b, (∃ a, f a = b) ↔ b ∈ R
```

Let `I := Finset.univ.image f`. `I ⊆ R` follows from `Finset.mem_image`; the
cardinality of I equals `Fintype.card A` by `Finset.card_image_of_injective`,
`Finset.card_univ`. Equal card + subset gives equality (`Finset.eq_of_subset_of_card_le`,
check its exact signature once). For reverse implication use `Finset.mem_image.mp`
with `Finset.mem_univ`. This generic proof only enumerates a symbolic domain,
never `Finset.univ : Finset Deck`. Prefer the theorem as a named declaration.

Supply card equality using **existing**
`exchangeChoice_card_eq_transitionDenominator` in `CommanderA3ExchangeCard.lean`
(Rat equality; cast back with `exact_mod_cast` after a typed RHS identity), and
`FiniteDeck.subsetExchangeCount 99 50 25 ... S` (Nat equality, `choose 50 25 * choose 49 25`).
The transition denominator is that same product. Prove its symbolic definition
once or use the proof of the existing cardinality theorem, not `native_decide`
over a type. If casting is annoying, copy its four tiny *cardinality* facts
`hProd hSubL hSubR hLc hRc` to establish a Nat version; do not enumerate choices.

This proves `∃ c, choiceOut d c = T ↔ T ∈ Reach (membership d)` for every T.
Notice the codomain here is Membership, never a deck. Prefer proving the whole
range equivalence generically and specializing with `exact`/`Eq.subst` if a
concrete `rw` forces finset normalization.

### A1.3 Finish row independence with the supplied generic lemma

`GenericClosure.lean` contains `uniform_same_image`. It applies
`GSR.map_injective_uniform_mass` twice. Feed the injectivity proofs from A1.1
and range iff from A1.2. For hmem : membership d = membership e, obtain
`Reach (membership d) = Reach (membership e)` by `congrArg Reach hmem`.
No need to construct a bijection of choices or compare finite-set membership
in a permutation universe. Conclude E d = E e. This is also the bridge to the
arbitrary-N subset exchange: specialize the same law over ReachSet, then relate
it to the concrete-pile weighted kernel in `FiniteDeck/SubsetExchange.lean`.

Fallback if the generic reach card bridge fails: reparameterize each selection
via the restriction of `d` to left and right card sets. Given `T`, outgoing
cards are `S\T`, incoming are `T\S`; pull them back via the inverse of
those restrictions. Prove image and card of each pullback using an Equiv;
then `newLeftCards_as_sdiff_union`. Do not reopen inverse-choice counting
across two independently randomized decks. The equal-card method is preferred.

## A2. Erase the initial ordering using kernel algebra

### A2.1 Factor the exchange through P

`CommanderMembershipKernels.membership_surjective` lets you choose a deck
representative `rep : Membership → Deck` with `membership (rep y) = y`
using `Classical.choose` and `Classical.choose_spec`.
Define `Q y := E (rep y)`. Then `E d = Q (membership d)` by A1.3
(row independence; orientations chosen using `membership (rep ...) = ...`).
Use `GSR.comp_deterministic_left` to get `E = comp P Q` by funext. This is a
legitimate Markov kernel: it is not a new abstract assumption. Prefer a direct
uniform ReachSet kernel later; the chosen representative is fine for closure.

Let `L := g6ThreeRoundFiniteKernel` (despite the name, ideal),
`H := permutationActionKernel Gate6Crux.rho99Ideal` (perfect local reset).
Existing facts:

- `localLift_preserves_membership`: `U ; P = id`.
- `k1_idealKernel_eq_membershipLift` (or `k1_bridgeA`): `H = P ; U`.
- `g6_3round_idealKernel_eq_fullRound`, `K1_swapFirst_eq_exchangeLift`:
  `L = E ; U = P ; (Q ; U)` by associativity.

Use `reset_absorption` from the seed with these equations to get `H ; L = L`.
Use `Eq.subst` on each kernel equality if `rw` tries to inspect definitions.
With `apply_comp`, this yields `apply (apply μ H) L = apply μ L` for ANY μ.
`equal_after_first_run` transports the equality to any positive number of
ideal rounds, including three. This is a consequence of row independence,
not of stationarity or of a constant-row finite kernel. It is false for a
finite local GSR H substituted for the perfect reset.

### A2.2 Identify the actual initial distribution

We need `apply (pointMass d0) H = g6ThreeRoundStart`, with d0 the identity.
A0 yields `localLift segMembership`. Use the F2 theorem
`membershipLift_localLift_eq_fiberLaw` and `apply_comp` to factor
`g6ThreeRoundStart` as `apply (membershipLift commanderSegregatedState) U`.
Reduce the latter membership distribution to `pointMass segMembership`.

This last step is SMALL membership-only mathematics:

- `commanderSegregatedState = ⟨49,...⟩` so `commanderLeftCount ... = 50`.
- `segMembership.val = leftOrigSet`: prove once with `Finset.ext` on `Fin 99`,
  using the definitions `segLeft`, `leftOrigSet`, `leftPositions`; or use
  `leftCards_id_eq_segLeft` and the marked-card count of identity.
- For any m, `membershipCount m = 50` iff `m = segMembership`: the intersection
  of m.val with leftOrigSet has the full cardinality of both 50-element sets.
  Use subset + equal card to conclude the intersection equals each set, then
  `Subtype.ext`. Conversely the self-intersection has card 50 (`leftOrigSet_card`).
- `membershipFiberCount 50 = 1`: use its choose formula (choose 50 50 times
  choose 49 0), not an enumeration of Membership or Deck. `norm_num` on
  *arithmetic* is okay; `norm_num` on `localLift` is not.
- Apply `membershipLift_mass` and `Dist.mass_pointMass`, `by_cases m = segMembership`,
  then `if_pos/if_neg`; `ext m` with explicit `change Dist.mass ...`. This proves
  the distribution equality at the smaller type. Transport through U via
  `congrArg (fun v => FiniteKernel.apply v U)`, then `apply_pointMass`.

Alternative if this mass proof causes a wall: use the generic uniform-fiber
of a singleton theorem with a predicate having exactly one witness; do it
at abstract types. There is no need to compare full-deck `fiberSet`s.

### A2.3 Reuse the q3 theorem

Use `g6_threeRound_compList3_eq_run` for both starts, A2.1 and A2.2 for run
congruence, then `g6_threeRound_finiteRun3_tv_le_q3` (despite its misleading
name, this is IDEAL). This proves ideal three-round TV ≤ q3 at identity point
mass. It does not assert equality of finite runs from the two starts.

## A3. Fix the GSR action convention before claiming the physical theorem

`gsrPermutationLaw` samples old->new rank `σ`. `act σ d` uses d(σ i), so the
physical stable-sort local law needs new->old `σ.symm`. Do not change the
meaning of rank throughout the codebase or redo tie-breaking. Use a common
pushforward by inversion, preferably at full within-pile noise level:

```
localPullback N ... := (rhoRoundFinite N ...).map (fun p => p.symm)
localIdealInv N ... := (rhoRoundIdeal N ...).map (fun p => p.symm)
```

1. Start from `permInverseEquiv`, `perm_inverse_uniform`, `perm_inverse_tv`
   in the seed. The generic inversion equivalence on `Equiv.Perm α` has toFun/invFun
   both `.symm` and inverse laws `Equiv.symm_symm`. Uniform is invariant by
   `GSR.map_bijective_uniformDist`; `tv_bijective_invariance` applies. This
   does not require Fintype in the construction, only the uniform-TV lemma.
2. `embed_m pl pr` is conjugation of a sum equivalence by `finSplit`.
   Its inverse equals `embed_m pl.symm pr.symm`. Prove at generic N,m with
   `Equiv.ext`, or the cleaner abstract statement `(e.symm.trans ...).symm`
   for conjugation. Use `embed_m_left/right` and `finSplit` if needed.
3. Show the ideal embedded law is invariant under inversion. Reuse
   `distProduct_uniform_is_uniformProd` and the bijection on the pair
   `(pl,pr) ↦ (pl.symm,pr.symm)`. Factor both sides with `map_map` and the
   embedding inverse identity. No need to show the ideal law uniform on all
   decks; it is uniform on the within-pile subgroup.
4. Apply the existing `rhoRoundTransport_le_twoPile` under inversion, then
   rewrite ideal-inverse = ideal. At 99/50 and a=2^23 this is still δ1.
   If direct concrete `rw` stalls, prove generic inequality and specialize
   the rational bound via `oneRoundDeckTV_le_delta1`.
5. Set `Wf := conv swapLaw localPullback`, `Wi := conv swapLaw rho99Ideal`.
   `Gate6K1Direct.convTVCommonLeft` handles their support-TV distance;
   convert with `tv_eq_tvFinsupp` at abstract N. Alternatively use the
   exact proof of `g6_threeRound_kernelDiscrepancy_le_δ1` with the finite
   local law ABSTRACTED as an argument and hTV as a hypothesis, then
   instantiate with the new bound. Do not rebuild the concrete max over 99!.
6. `action_comp_eq_conv` in the seed (from `convPush_eq_pointMassComp`) lets
   you identify the corrected round kernel `K` with `PAK Wf`. It also gives
   `L = PAK Wi` via the existing K1 bridge. The position-pairing swap law
   remains unchanged. The order is swap then local, not the reverse.

Use `compList_telescope_nstep_le_n_times_d` from `TelescopeF5.lean`, with
`mu := pointMass d0`. The complete proof of the old headline is a template:
abstract the two kernels and one-round bound, then replace the start and
ideal bound with A2.3. Or prove an n-step support-TV telescope using
`kernel_apply_lipschitz` + one-step convolution. `powConvTV` is PARKED in
`Gate6K1Direct.lean`; do not assume that theorem exists or revive the huge
WHNF attempt merely to close this proof. The current canonical telescope
works already. A separate generic induction using laws as variables can be
pursued later. `q3 + 3*δ1 < 1/1000` is `gate6_headline_lt_thousandth`.

## A4. Every deterministic deck, then every initial law

The reference-deck result is sufficient **only after A2**. The seed theorem
`action_run_tv_noise` uses `powConvRunEq` (already proved), plus
`relabel_equiv`, `uniformDeck_relabel_invariant`, `tv_bijective_invariance`.
For any noise W and any d it identifies TV(run PAK W t (pointMass d), uniform)
with TV(powConv W t, uniform). Both sides are laws on the same finite group;
the map p ↦ p.trans d is bijective. Therefore the two point-start TVs are
equal for d and d0. No need for a new permutation relabeling proof for each
operation or an actual enumeration of decks.

Use `congrArg` to transport `K = PAK Wf` through run, and the compList-run
bridge to connect A3 to the new theorem. If `rw` unfolds large terms, write
`have h : ... := ...` at the generic interface, then `exact Eq.subst ...` with
explicit predicate (the pattern that worked in the last capstone).

Optional immediate strengthening: for any law μ, run is linear in μ
(a composition of stochastic kernels). TV is convex in the first argument,
so it is at most the supremum of the point-start distances. Since all such
distances here are the same `b ≤ q3+3δ1 < 1/1000`, get the same strict bound
without a strict-max proof. Prefer a generic theorem for an arbitrary kernel
and a row bound b; use `apply_discrepancy_bound` comparing to the constant
uniform kernel, or a Finsupp triangle inequality. Do not add this as a blocker
for the deterministic theorem.

## A5. Certify 23 binary riffles, not just a 2^23-label operation

`GSR.idealShuffle_comp` followed by `GSR.productLabelShuffle_uniform_eq_ideal` proves multiplication of label alphabets on lists.
`PermutationLaw.idealShuffle_canonical_eq_permLaw` connects the rank law to
the canonical list. Prove composition for pullback laws by the following
faithfulness argument, rather than repeating stable-sort arithmetic:

- Let `encode(p) := (List.finRange n).map p`. This is injective: inspect the
  element at index i (`List.getElem_map`, finRange's element formula), then
  `Equiv.ext`. Include n=0 separately or use the vacuous ext proof.
- For an arbitrary canonical-label deck d, a stable sort with label array
  indexed by *positions* produces `encode (σ.symm.trans d)`. Lift the existing
  canonical `stableBuckets_eq_orderByNewPosition` to arbitrary values by
  proving stableBuckets commutes with mapping values (labels are unchanged),
  or reuse the existing list map lemmas in `GSRF42`/`GSRF42KeyOrder`.
- Push the convolution of two pullback laws through encode. `map_map` and
  `convPush_eq_pointMassComp` express it as two list shuffle applications.
  Existing `idealShuffle_comp n a b ha hb` and
  `productLabelShuffle_uniform_eq_ideal ha hb` together identify that law with one
  ab-label shuffle. Show the list-kernel equality pointwise on valid lists;
  use `map_join_kernels` for the bind step. The rank-law itself uses inverse
  orientation, so do not claim the convolution identity with unexamined order.
- Pushforward by injective encode reflects equality of distributions, via
  `Finsupp.mapDomain_apply_of_injective` at `encode p`; no Fintype on `List`.
  Prove this generic map-injectivity lemma once. Deduce one pullback law for
  `a*b` equals the convolution of the two pullback laws in physical order.
- Induct on t using `2^(t+1)=2^t*2`, `powConv_succ`; t=0 is 1-label stable
  sort (identity). If proving the zero-label-alphabet theorem is distracting,
  start at t=1 and prove the positive version. Lift the local product to
  the two-pile action; independent pile laws commute across disjoint piles.

If A5 is not done, the theorem can accurately advertise the independent
2^23-label shuffle. Do not label it as 23 separately executed riffles until
this bridge compiles. The mathematical result is still valuable.

## B1. G5: choose a reusable partition interface

`Piles.lean` has the correct raw definitions (`realizesAllocation`, `MultiFiber`)
but no hypotheses ensuring valid partitions. Keep them. Add `IsPartition`
for a family `P : I → Finset X` with existence and uniqueness of an owner
for each x (candidate in `PartitionSeeds.lean`). This works for arbitrary
finite index type I (later specialize Fin k), permits empty blocks, and avoids
rebuilding `Fin k` arithmetic. Equivalent presentation is a function X→I;
prove the fibers of a function form a partition and obtain an owner function
by choice from IsPartition. Prefer function-valued owner for histograms and
capacity updates; retain the current Finset interface as a compatibility
wrapper. Do not bake in positivity of every pile or `N > 0` for counting.
For `I=Fin 0`, cover is possible only when X empty; empty product = 1.

### B1.1 The central equivalence is a Sigma decomposition

`partitionSigmaEquiv` (seed) proves `Σ i, {x // x ∈ P i} ≃ X` by sending
(i,x) to x. Injectivity = unique owner + Subtype.ext; surjectivity = cover.
No cardinality or disjoint-big-union lemma needed. The `sigmaBlockEquiv`
seed maps each dependent block through a supplied equivalence. Compose:

```
X ≃ Σ i, Pos i ≃ Σ i, Card i ≃ Y
```

This produces `glueBlocks` from arbitrary block-local bijections, including
empty types. `glueBlocks_apply_member` is the crucial evaluation lemma:
if x lies in P i, the glued bijection sends it exactly to `(e i ⟨x,hx⟩).val`.
All later proofs use this pointwise theorem; no manual 4-case or k-case split.

### B1.2 Build the actual fiber equivalence by restriction and gluing

For abstract types X,Y, define
`Realizes P C d := ∀ i, (P i).image d = C i` with appropriate DecidableEq Y.
Then for partitions P,C:

```
{d : X ≃ Y // Realizes P C d} ≃
  (∀ i, {x : X // x ∈ P i} ≃ {y : Y // y ∈ C i})
```

Restrict: follow `FiniteDeck.fiberRestrictL` in `Fiber.lean`, replacing the
left-position finset by P i and A by C i. `hmem` uses `Finset.mem_image_of_mem`
and the realization equation. `Equiv.ofBijective` is injective by d.injective
and Subtype.ext; surjective by `Finset.mem_image.mp` after rewriting C i.
Gluing: seed `glueBlocks`. To show `(P i).image glue = C i`, use
`Finset.Subset.antisymm` or `Finset.ext`:
- Forward: `mem_image.mp` gives x in P i; use `glueBlocks_apply_member`, then
  `(e i ⟨x,hx⟩).property`.
- Backward: for y in C i let z := `(e i).symm ⟨y,hy⟩`; take `z.val` as
  the image witness, evaluate glue with z.property, then apply_symm_apply.
- Restrict(glue e)=e: `funext i; apply Equiv.ext; intro x; apply Subtype.ext`;
  the local formula gives equality directly.
- Glue(restrict d)=d: `apply Subtype.ext; apply Equiv.ext; intro x`;
  choose i with x∈P i via hP.1, then local formula and rfl for restriction.

Use the existing `MultiFiber` as the Fin N specialization of this result.
No need for a base deck to define this equivalence. Inhabitation follows when
all corresponding block sizes agree: for each i take `Finset.equivOfCardEq
(hsize i)` (already used by `Gate6Crux.canonicalPairing`). Conversely a
realization implies equal sizes by `card_image_of_injective`.

## B2. General fiber cardinalities; recover the two-pile theorem

Let n_i = (P i).card, assume hsize : ∀ i, (P i).card = (C i).card. Choose a
block equivalence e0_i by `Finset.equivOfCardEq`. Every other block bijection
is equivalent to a permutation of P i's subtype via `e.trans e0_i.symm`,
inverse `p.trans e0_i`. Prove this *once* for abstract equal-card types and
an e0, use `Equiv.ext` with `Equiv.trans_apply` and inverse laws. Then
`Fintype.card_congr` + `Fintype.card_perm` gives n_i!, and `Fintype.card_pi`
gives the product (already used in `Gate6F.lean`). Use `Fintype.card_subtype`
only on abstract finsets (or `Fintype.card_coe` if available). Do not invoke
`Finset.univ` of all deck permutations. Main theorem:

```
Fintype.card (MultiFiber N k posPile cardPile) =
  ∏ i : Fin k, ((posPile i).card).factorial
```

For mismatched sizes, no realization: provide a separate impossibility theorem.
For two piles, prove `realizesAllocation N 2 (twoPilePos ...) (twoPileCard ... A) d`
iff `(leftPositions ...).image d = A.val`. Forward by i=0; reverse, use
`fin_cases i`: left is h; right follows from image of complement under a
bijection (`FiniteDeck.bijection_imageCompl` in `WithinPileOrbit.lean`, or
`leftRight_cover/disjoint` + membership ext). No proof about the whole deck
set required. Then `Equiv` by identical deck value in each subtype; proof
irrelevance discharges inverses. Specialize B2 to `Fin 2`, use
`leftPositions_card`, `rightPositions_card`, finite product over two indices.
Preserve old `fiberCount` as the compatibility statement. Later consolidate
its long implementation after the generic theorem has been verified.

**G5 checkpoint:** prove the equivalence first, then cardinality, then
specialization. Also compile a 3-pile example with sizes 2,1,0 (N=3). Empty
pile yields 0!=1. Do not restrict G5 to nonempty piles to make instances easier.
Add `FiniteDeck.Piles` to the aggregator after its first verified increment;
currently only the targeted verify script includes it.

## B3. Count allocations and category histograms with the SAME theorem

This is the next non-obvious step. Do not invent a second huge multinomial
counting development. Let finite pile index I, category index J, card identities
X, category map c:X→J. Sizes n_i, category totals r_j, histogram x_ij with
sum_j x_ij=n_i and sum_i x_ij=r_j. All counts are natural. Work with typed
allocations `a : X → I` satisfying capacity constraints; finset view is fibers
of a. Every legal allocation is an image of an ordered deck for fixed position
partition, by B1 and equal sizes. Its fiber size is ∏_i n_i!.

### B3.1 Division-free total-allocation count

Let D be all decks, A be allocations of capacities n. Projection D→A is
surjective; its fibers have constant size B = ∏ n_i!. Therefore
`card A * B = N!`. Use the existing generic fiber partition principle in
`_ProbeK1uniform` (`fiberCardPartition_nat` via `Finset.card_biUnion`, if
compiled) or prove it generically as the Sigma equivalence
`X ≃ Σ a, {x // f x = a}`. The latter is B1 with fibers of a function.
If `Fintype.card_sigma` is not available in the pinned Mathlib, use the
existing `card_biUnion_pd` in `FiniteDeck/BLRefinement.lean` (or inspect the
already-built `_ProbeK1uniform` proof). Avoid depending on a guessed lemma
name. Prove once as a Nat identity; multiply before dividing. `B > 0` from
factorials. For an actual formula, cast to Rat and cancel B. This gives the
uniform allocation law as the pushforward of the uniform deck law by the
already-known equal-fiber theorem.

### B3.2 Count histograms by splitting the card universe by category

For each category j, form the type `Cj := {x : X // c x = j}`. It has r_j
cards. Allocate these cards to piles with sizes `i ↦ x i j`; denote that
allocation type by A_j. **A global allocation with histogram x is equivalent
 to `∀ j, A_j`.** Restrict the function a to Cj; glue by evaluating the chosen
component at `c x` on `⟨x,rfl⟩`. Prove both directions with funext and
Subtype.ext; the row sum ensures the glued allocation has capacities n.
No permutation group orbit proof required. If counts of a depend on Finset
fibers, first prove that a pile's category cells partition that pile, then
use the generic Sigma/card partition lemma. Avoid Nat subtraction entirely.

Apply B3.1 to each category's card type, using slots `Σ i, Fin (x i j)` as
positions if needed. It has r_j slots by the column sum. This avoids finding
an actual witness allocation with the given histogram; the slot bijection
exists by cardinality and constructs a witness. Conclude the division-free
identity

```
card(HistFiber x) * (∏ j, ∏ i, (x i j)!) = ∏ j, (r j)!
```

This is the multinomial count. Cast to Rat only after proving the Nat
identity. The probability under uniform allocations is

```
π(x) = (∏ i n_i!)(∏ j r_j!) / (N! ∏ i,j x_ij!) .
```

No need to prove a standalone multivariate Vandermonde sum for normalization:
this is the pushforward of the uniform allocation law, already normalized.
For a two-pile two-category system, histogram is determined by x00; write
x01=m-x00, x10=r-x00, x11=N-m-(r-x00) with explicit admissibility. Specialize
and simplify to `choose r x * choose (N-r) (m-x) / choose N m`. Reuse the
existing factorial/choose identities. Keep `Fin 0`, zero-size categories,
and boundary counts admissible. The denominator factorials are positive.

## B4. Pairwise exchanges on multiple piles and exact lumpability

Given allocation a, distinct piles i,j, choose k distinct cards from each
uniformly and independently (k ≤ n_i,n_j). Define kernel by pushing the
uniform choice law to the updated assignment. This establishes stochasticity
by construction. Membership/allocations remain valid: selected i-cards move
to j and selected j-cards move to i. Unselected cards unchanged, all capacities
preserved. For any fixed source-target allocation, the choices are uniquely
recoverable (moved i cards, moved j cards); there is at most one. The transition
is symmetric: reverse the two moved sets. Denominator `choose n_i k * choose n_j k`
is constant. Thus uniform allocations are stationary. Pairwise exchange on
literal ordered decks projects to this same law, because restrictions of a
deck to positions in each pile are bijections to their cards (B1); choose
subsets via image under an equivalence. This is the generic A1 argument.

For histogram transition x→y, write u_c,v_c for counts of category c removed
from piles i and j. Conditions: `sum u = sum v = k`, `u_c ≤ x_i,c`,
`v_c ≤ x_j,c`; other rows unchanged; `y_i,c = x_i,c - u_c + v_c` and
`y_j,c = x_j,c - v_c + u_c`. Probability of these selection profiles:

```
(∏ c choose (x_i,c) (u_c) * ∏ c choose (x_j,c) (v_c)) /
(choose n_i k * choose n_j k)
```

Sum over admissible profiles producing y. This uses B3-style decomposition
of a selected subset into its category cells, not a many-case arithmetic
proof. For fixed profile, equivalence between legal selections and dependent
product of subsets of category cells proves the count via `card_pi` and
`card_powersetCard`. `FinsetFiberCount` supplies two-category counting if
needed. No separate proof for each number of categories. The probability
depends only on x, establishing **strong lumpability**.

Then symmetric finite-kernel quotient theorem: if K symmetric and each
row's total mass into fiber F_y is P(x,y), then
`|F_x|P(x,y) = Σ_{s∈F_x,t∈F_y} K(s,t) = |F_y|P(y,x)`. Reverse the sum to
show starting uniformly in F_x gives mass `P(y,x)/|F_x|` at every target in
F_y; detailed balance converts to `P(x,y)/|F_y|`. This single generic
proof gives uniform-fiber intertwining and the multivariate stationary law.
For Lean, use abstract finite X,Y, use `sum_comm` on a symbolic type, keep
cardinality nonzero by surjectivity or restrict to nonempty fibers. Preserve
all existing G2-G4 theorems as specializations. This avoids reproducing
`CommanderMembershipOrbits` and `BLRefinement` for every number of piles.

## C. Subsequent general mixing and game operations (G7)

Uniform stationarity is not a convergence proof. For connected allowed
position graph, lazy random elementary transpositions generate all
permutations. Proof: any (u,v) transposition along a path can be written as
successive adjacent transpositions out and back (length 2d-1); all permutations
are generated by transpositions (use Mathlib or prove induction on number
of misplaced positions). If all edges have a positive probability and a
positive self-loop, take finite maximum path length M and minimal positive
step weight q. Then every M-step transition at least q^M, minorization
ε=|X|q^M, giving TV ≤ (1-ε)^t after Mt steps by contraction. This is crude but
arbitrary finite and worst-case. For memberships, k=1 exchanges along
connected nonempty piles give the analogous reachability. Fixed k>1 can be
reducible (N=4,m=2,k=2 simply complements). Do not assume every legal schedule
mixes; disconnected pile graph or periodic chain are counterexamples.

For variable capacity, treat allocations as maps X→I with changing capacity
vector. A uniform transfer of one card from pile i to j sends uniform source
allocations at n to uniform target allocations at n' (n_i-1,n_j+1). Reason:
for a given target there are exactly n_j+1 reverse choices, each yielding a
source and unique transferred card. Thus mass `(n_j+1)/(card A_n * n_i)`,
constant; normalization gives uniform target. Alternatively count the bijection
between `(source, chosen source card)` and `(target, chosen target card)`.
This proof does NOT require reversibility between equal state spaces. Generalize
to k using `choose n_i k` and `choose (n_j+k) k`. For draws from an ordered
pile, the top card is uniform only under appropriate within-pile uniformity.
If the initial full deck is close to uniform, any dealing/drawing/discarding
kernel applied to both real and reference states inherits the TV bound by
`supportMapTV` or `kernel_apply_lipschitz`. Do not claim strategic/biased
player discards preserve uniform allocations; model actual policy and compare
under the same kernel. Cards Against Humanity uses distinct identities even
if printed texts coincide (category observation is separate).

## D. G8: useful cost certificates and optional sharper mathematics

For a protocol with ideal TV residual b and round-specific local pile sizes
n_{s,i} and alphabets 2^{t_{s,i}}, the total error is bounded by
`b + Σ_{s,i} choose(n_{s,i},2)/2^{t_{s,i}}`. Use existing telescope with a
variable per-round bound; generalized product local shuffle via induction
on finite list of piles. First get a generic arbitrary finite-N protocol
with explicit assumptions and one numerical example. Charge actual pile
riffles, swaps, setup; different operations can have different costs.
Do not target the uniform count distribution instead of hypergeometric π.
A certificate is an upper bound, not an actual optimum.

With fixed equal unit riffle costs, optimal allocation for this **sufficient
bound** is greedy: each extra riffle on pile s,i reduces its current error
by `choose(n,2)/2^(t+1)`; marginal gains decrease geometrically. Exchange
argument: any allocated smaller marginal gain can be swapped with a larger
unallocated one, maintaining the prefix property because each list is
nonincreasing. This proves optimality for a fixed total riffle budget, or
minimal number of riffles for a target on this bound. For unequal costs use
finite search/dynamic programming; greedy ratio is not generally exact.
Actual optimum needs lower bounds or exact TV, not just this certificate.

Optional sharper GSR: for pullback permutation p with d(p) descents, the
stable sort law is `choose(a+n-1-d(p), n)/a^n` when a>d(p), zero otherwise.
Count weakly increasing label sequences along p, subtract accumulated
mandatory strict increases at descents; use stars and bars. Eulerian counts
A(n,d) satisfy `A(n,d)=(d+1)A(n-1,d)+(n-d)A(n-1,d-1)` from inserting the
largest element. Group TV by descents rather than N! permutations, and group
product laws by descent pairs. Earlier November 24 hints contain details;
this is follow-on after the collision certificate. G9 sharp spectral theory
is optional, not required before G0-G8 finish.

## Paste-ready loop goal (replace the ACTIVE goal, not just a file in docs)

Complete the actionable arbitrary-finite-deck roadmap in `docs/planning`
through G8, using `docs/planning/proof-strategies/2026-11-25-gate6-and-multipile-executable-handoff.md`
as the current implementation guide. The canonical three-round theorem is
already proved for a fiber-uniform start; finish its deterministic-start
and GSR pullback/binary-riffle bridges (A0-A5), without repeating completed
counting or increasing Lean recursion limits. Then finish G5 with the generic
partition/Sigma gluing equivalence, factorial and histogram counts, and
pairwise exchange lumping (B1-B4); proceed to G7 and generic G8 mixing/cost
certificates. Compile and integrate the supplied small candidate lemmas,
keep the targeted verification green, and record actual theorem scopes.
Historical reviews and optional G9 research are not separate completion
gates. Do not stop at the restricted 99-card result or count it as an
all-start physical certificate. On a bounded failure isolate one lemma,
change representation, or advance an independent G5 obligation and return.
