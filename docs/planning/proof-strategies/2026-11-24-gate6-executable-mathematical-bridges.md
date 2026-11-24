# Gate 6: executable mathematical bridges for Qwen (2026-11-24)

This is a follow-on to `2026-11-24-k1-direct-order-and-kernel-hints.md`, not a
replacement for that document. Read its swap-then-local plan first. The new
material here is more prescriptive: it supplies the missing mathematical
arguments, precise interface shapes, and small proof checkpoints to prevent
another long detour. Source basis: `7d024410e6d5` before the user's latest
hint commit. Do not repeat any checkpoint already implemented correctly.

The snippets below are proposed Lean code/proof templates, not independently
compiled patches. Where a library lemma's exact spelling or elaboration is
uncertain, the adjacent mathematical proof specifies what must be proved.
Use `#check` on the pinned Mathlib version; do not infer the existence of a
lemma merely from a suggested name. Use fresh namespaces for candidate
lemmas to avoid collisions with the earlier probes. Do not create a worktree.

## 0. Critical path: which result to prove next

1. Confirm the physical action uses **pullback** permutations (Section 1).
   Define the corrected finite and ideal round laws; no commutation proof.
2. Compile three small generic interfaces (Section 2): deterministic map as
   kernel application, TV map contraction, two-factor convolution bound.
3. Close K1 via **composition of the two already-proved halves** (Section 3).
   This is the priority before trying to prove new counting theorems.
4. Prove membership-only exchange via **equal cardinalities of an image and
   its target** (Section 4). Use the generic subset-exchange kernel already in
   `FiniteDeck/BLRefinement.lean`. This is the new route to the deterministic
   start (Section 5), and it also consolidates Commander with arbitrary N.
5. Assemble the power telescope, reference deck and all-start theorem
   (Section 6). Check the actual binary-riffle interpretation (Section 7).
6. Only after a compiled physical certificate, consider stronger error bounds
   and multi-pile abstractions (Section 8); then proceed through the actionable
   planning gates in dependency order.

This is a dependency list, not permission to spend days solving a single
optional abstraction. Each step should be a handful of small declarations.
The hard mathematics is explained below so that the next session need not
rediscover it. The only 99-specific proof work should be the specialization
bridges and the final exact rational comparison. Use the existing shared
working directory and preserve unrelated changes.

## 1. Fix both orientation conventions: physical order and rank versus pullback

### 1.1 Three different objects must not be confused

A deck `d : Equiv.Perm (Fin N)` is a bijection *position -> card*. The
permutation action is defined by `FiniteDeck.act p d = p.trans d`:

    act(p,d)(i) = d(p(i)).

Thus `p` is a **pullback**: given a new position, tell me which old position
its card comes from. `FiniteDeck.act_composition` already proves

    act(a*b,d) = act(b,act(a,d)).

So `conv swapLaw localLaw` is the law for doing the physical swap first and
local shuffle second. Never infer physical order from `Equiv.trans` alone.
`(act (s*g) d) i = d (s (g i))` is the regression to check. Comments in old
modules that call `conv rho99Finite swapLaw` swap-first are wrong under this
convention.

A stable inverse-GSR shuffle assigns labels to OLD positions, then orders the
positions lexicographically by `(label, old position)`. `rankEquiv n a hn ℓ`
maps old positions to **new positions**. It is the inverse of the pullback
position map needed by `act`. The source states the exact equation:

    GSR.stableBuckets a ℓ (List.finRange n)
      = (List.finRange n).map (rankEquiv n a hn ℓ).symm

(`stableBuckets_eq_orderByNewPosition` in `GSRF42KeyOrder.lean`; also
`PermutationLaw.idealShuffle_canonical_eq_permLaw`).

For example, on 4 cards with labels `[1,0,1,0]`, stable sorting gives `[1,3,0,2]`,
whereas the rank permutation is `[2,0,3,1]`. These are inverses, not equal.
Do not test only 2 or 3 cards: the distributions for some tiny configurations
happen to be inversion-invariant even though samples differ.

### 1.2 Define the corrected local law by transporting the existing rank law

In a module importing `GSRPermutationLaw`, `GSRDeckRound` and the existing TV
lemmas, generic in `n`, introduce:

```lean
-- Candidate declarations; compile at generic n.
noncomputable def gsrPullbackLaw (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    Dist (Equiv.Perm (Fin n)) :=
  (PermutationLaw.gsrPermutationLaw n a ha hn).map
    (fun p : Equiv.Perm (Fin n) => p.symm)

def permInverseEquiv (n : Nat) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun := fun p => p.symm
  invFun := fun p => p.symm
  left_inv := by intro p; simp
  right_inv := by intro p; simp
```

Prove `uniformDist.map inverse = uniformDist` using
`GSR.map_bijective_uniformDist (permInverseEquiv n)`. Its statement is generic
in the domain; do not expand `uniformDist` at n=50. Use `change` to fold the
coercion of this equivalence into `fun p => p.symm`, or `simpa only` with its
function field. Then apply `Dist.tv_map_contraction` to the rank law and
uniform law with this common map. The bound does not change:

    TV(pullbackLaw, uniform) <= TV(rankLaw, uniform).

The reverse inequality also holds by applying the same inverse map again;
`tv_bijective_invariance` proves equality directly. Use either inequality or
exact equality; the inequality is sufficient for the certificate.

The existing single-pile collision theorem in `Gate6F.lean` and
`twoPilePermutationTV_bound` have already done the hard probability work.
If the old two-pile bound does not directly match, derive the product bound
with `distProduct_tv_subadditive` or its support-based counterpart, using the
single-pile bound for both factors. Push it through the existing `roundEmbedMap`
with map contraction. This is exactly the proof structure of
`rhoRoundTransport_le_twoPile` in `GSRDeckRound.lean`, with each rank-law
factor replaced by `gsrPullbackLaw` and no new combinatorics. An equally valid
short route is to map the pair of permutations by `(p,q) -> (p.symm,q.symm)`,
prove the pair-uniform law fixed, and use the same product TV estimate.

Call the resulting local law e.g. `rhoRoundPullbackFinite N m ...`. Keep
`rhoRoundIdeal` as the ideal local law: uniforms are inverse-invariant.
Keep the old rank-law theorem intact as a valid forward-convention result if
it has downstream users; do not silently change an old theorem's meaning.
Specialize these generic definitions and theorems to `N=99, m=50, a=2^23`.
The upper bound remains `δ1 = 2401/8388608`. Section 7 supplies the separate
binary-composition bridge. At this point a single `a`-label stable-sort kernel
is already a perfectly well-defined physical random permutation operation.

## 2. The shorter TV architecture: two-variable convolution bound

**New insight:** do not prove a left-convolution Fubini theorem merely to
repair the round order. A contraction theorem for any deterministic map,
combined with the already-proved product-TV bound, is enough to prove a
stronger result. It simultaneously handles both factors and iterated powers.

### 2.1 Deterministic kernel application is `map` without Fintype

`FiniteKernel.apply_deterministic_eq_map` unnecessarily assumes `Fintype`
because its proof uses a universe sum. The same identity follows from the
monad unit law already in `Finite.lean`: `apply_id_left`.

Prove this tiny general-purpose helper first (no `[Fintype]`, no `[DecidableEq]`):

```lean
namespace Shufflemath

-- Suggested code: may need minor coercion adjustments on this Mathlib pin.
theorem applyDeterministicSupport {X Y : Type*} (u : Dist X) (f : X → Y) :
    FiniteKernel.apply u (FiniteKernel.deterministic f) = u.map f := by
  calc
    _ = FiniteKernel.apply (u.map f) FiniteKernel.identity := by
      change (u.map (fun x => Dist.pointMass (f x))).join =
        ((u.map f).map (fun y => Dist.pointMass y)).join
      rw [Convexity.StdSimplex.map_map]
    _ = u.map f := FiniteKernel.apply_id_left _
```

If `rw [map_map]` leaves function-composition syntax, use `rfl`/`change`
only at generic types. If the `change` involving the two `join`s is awkward,
write a separate equality of their outer simplex arguments, use `map_map`,
then apply `congrArg (fun w => w.join)`. There is no mathematical summation
left to prove. `FiniteKernel.apply_id_left` is the exact lemma already
proved, even though its name says "left". Do NOT expand its body.

### 2.2 Map contraction, generic over all finite-support distributions

```lean
theorem supportMapTV {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (u v : Dist X) (f : X → Y) :
    tvFinsupp (u.map f) (v.map f) ≤ tvFinsupp u v := by
  rw [← applyDeterministicSupport u f, ← applyDeterministicSupport v f]
  exact kernel_apply_lipschitz u v (FiniteKernel.deterministic f)

theorem supportTVSelf {X : Type*} [DecidableEq X] (u : Dist X) :
    tvFinsupp u u = 0 := by
  simp [tvFinsupp]
```

The definition of `tvFinsupp` is a sum on the union of supports. `supportTVSelf`
is checked with the distribution abstract; it never enumerates its support.

### 2.3 Use one convolution inequality for every order

Mathematical statement:

    TV(A*B, C*D) <= TV(A,C) + TV(B,D).

Here `*` denotes convolution, not multiplication of probabilities. Draw an
independent product, then push it through group multiplication. The existing
`distProductFinsupp_tv_subadditive A C B D` controls the product pair, and
`supportMapTV` controls its pushforward. No need to interchange summations.

```lean
-- Could be generalized further to an arbitrary binary map / group.
theorem convTVBoth {N : Nat} (A B C D : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv A B) (FiniteDeck.conv C D) ≤
      tvFinsupp A C + tvFinsupp B D := by
  calc
    _ ≤ tvFinsupp (distProductFinsupp A B) (distProductFinsupp C D) :=
      supportMapTV (distProductFinsupp A B) (distProductFinsupp C D)
        (fun z : FiniteDeck.Deck N × FiniteDeck.Deck N => z.1 * z.2)
    _ ≤ _ := distProductFinsupp_tv_subadditive A C B D

theorem convTVCommonLeft {N : Nat} (S F I : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv S F) (FiniteDeck.conv S I) ≤ tvFinsupp F I := by
  simpa only [supportTVSelf, zero_add] using convTVBoth S F S I
```

The first calc works by the definition of `conv`, at abstract N. If even
abstract `Deck N` creates a typeclass wall, prove the same theorem with
`{G : Type*} [Mul G] [DecidableEq G]` and `conv` replaced by a map of the
product using `(fun z : G × G => z.1 * z.2)`. Then instantiate the theorem.
This is a general operation on finite-support laws on any type, not a theorem
that needs a finite group. The existing `convContraction` remains valid for
common right factors; we need not rewrite it.

### 2.4 One inequality also handles all powers (no row telescope)

```lean
theorem powConvTV {N : Nat} (F I : Dist (FiniteDeck.Deck N)) (t : Nat) :
    tvFinsupp (FiniteDeck.powConv F t) (FiniteDeck.powConv I t) ≤
      (t : Rat) * tvFinsupp F I := by
  induction t with
  | zero =>
      change tvFinsupp (Dist.pointMass (Equiv.refl (Fin N)))
        (Dist.pointMass (Equiv.refl (Fin N))) ≤ (0 : Rat) * tvFinsupp F I
      rw [supportTVSelf, zero_mul]
  | succ t ih =>
      calc
        _ ≤ tvFinsupp (FiniteDeck.powConv F t) (FiniteDeck.powConv I t) +
              tvFinsupp F I :=
            convTVBoth (FiniteDeck.powConv F t) F (FiniteDeck.powConv I t) I
        _ ≤ (t : Rat) * tvFinsupp F I + tvFinsupp F I := add_le_add_right ih _
        _ = _ := by rw [Nat.cast_succ]; ring
```

If the kernel rejects definitional reductions of `powConv`, add explicit
`powConv_zero` and `powConv_succ` theorems, each checked with N, noise and t
abstract. Use `rw` on those instead of unrolling a concrete 99-card power.
Do not unfold `Dist.tv` or `tvFinsupp` in the induction. This theorem is the
whole finite-vs-ideal perturbation argument. It does not require uniform
stationarity, kernel maxima, Dobrushin coefficients or a new row-TV lemma.

Finally define `Wf := conv swapLaw rho99PullbackFinite`,
`Wi := conv swapLaw rho99Ideal`. `convTVCommonLeft` and the corrected local
bound from Section 1 give `TV(Wf,Wi) <= δ1`. Keep this result in support-TV
form and use `tv_eq_tvFinsupp` to connect it to the already established
`Dist.tv` inequality only at a named interface. If an application at 99
triggers WHNF, introduce an abstract helper whose input types, distributions,
and hypotheses are independent arguments (do not expand the specialization).

## 3. Close K1 with generic kernel algebra, not new counting

Abbreviations in this section are mathematical notation for the declarations
in the source. `K` means literal swap kernel `permutationActionKernel swapLaw`;
`H` is `permutationActionKernel rho99Ideal`; `M` is `deterministic membership`;
`L` is `localLift`; `E` is `rawExchangeMembership`. `;` means
`FiniteKernel.comp`, left-to-right execution. Types:

    K,H : Deck -> Dist Deck
    M,E : Deck -> Dist Membership
    L   : Membership -> Dist Deck

We already have (i) `H = M ; L` and (ii) `K ; M = E`, or the component facts
needed to make each equality immediate. These imply `K ; H = E ; L`.
`CommanderPhysicalExchange.rawExchange = E ; L` by definition. Its extra
perfect-local reset is redundant because `L ; M = id`. This is the full K1
proof. It has no reverse witness problem, nor any `k1b_count_split`.

### 3.1 Promote the completed probe lemmas, without importing unfinished probes

- From `_ProbeGate6K1.lean`: `convPush_eq_pointMassComp` (generic N),
  `k1a_riffle_half` (complete), `k1_rhs_bookkeeping` (complete).
- From `_ProbeK1wall.lean`: `k1wall_riffle_push_mass_factorial` and just its
  dependency lemmas, which supply `k1a_riffle_half`.
- From `_ProbeK1b.lean`: `K1a_stmt_only` plus the relevant bridge definitions.
  Its proof is pointwise for `(d,L,R,b)`; it never averages over permutations.

These probe files use repeated names such as `h50le99`. Relocate the complete
lemmas into appropriate production modules, resolving duplicate names and
import directions. Do not copy the `sorry` in the old wrong-order K1 theorem.
If a proof is already promoted in the current checkout, use it. First check
`#check`/`#print` rather than making new copies.

### 3.2 Local kernel equality from the existing point-mass theorem

The actual `k1a_riffle_half d` states

    apply (pointMass d) H = apply (pointMass (membership d)) L.

Prove the generic helper below over abstract `X,Y`, and use it to form the
kernel equality. This avoids running concrete simplification on `localLift`.

```lean
theorem kernelOfFiberRows {X Y : Type*} (H : FiniteKernel X X)
    (f : X → Y) (L : FiniteKernel Y X)
    (h : ∀ d, FiniteKernel.apply (Dist.pointMass d) H =
      FiniteKernel.apply (Dist.pointMass (f d)) L) :
    H = FiniteKernel.comp (FiniteKernel.deterministic f) L := by
  funext d
  calc
    H d = FiniteKernel.apply (Dist.pointMass d) H :=
      (FiniteKernel.apply_pointMass d H).symm
    _ = FiniteKernel.apply (Dist.pointMass (f d)) L := h d
    _ = (FiniteKernel.comp (FiniteKernel.deterministic f) L) d := rfl
```

At 99, `exact kernelOfFiberRows ... k1a_riffle_half` (not `simp` on the
statement of the whole theorem). The exact name of the specialized result can
be `idealLocal_eq_membershipLift` or use the already chosen name.

### 3.3 Literal swap kernel projection: compare two pushforwards of the SAME law

Define a single function `choicePerm : exchangeChoice -> Deck` to be the
map argument of `Gate6Crux.swapLaw`. Define `postChoice d : exchangeChoice ->
Membership` to be the map argument of `rawExchangeMembership d`:

```lean
-- Here the namespaces are important; use #check on these existing names.
-- These functions can be introduced as aliases of the existing map bodies.
noncomputable def choicePerm (c : CommanderPhysicalExchange.exchangeChoice) :
    CommanderPermutation.Deck :=
  FiniteDeck.swapPerm 99 50 (by norm_num) c.1.1 c.2.1
    (Gate6Crux.canonicalPairing c.1.1 (Gate6Crux.exchangeLCard c)
      c.2.1 (Gate6Crux.exchangeRCard c))

def postChoice (d : CommanderPermutation.Deck)
    (c : CommanderPhysicalExchange.exchangeChoice) :
    CommanderMembershipKernels.Membership :=
  CommanderPhysicalExchange.newMembership d c.1.1
    (CommanderPhysicalExchange.leftCard25 c.1.2) c.2.1
    (CommanderPhysicalExchange.rightCard25 c.2.2)
```

The proof `membership (act (choicePerm c) d) = postChoice d c` is exactly
`K1a_stmt_only d c.1.1 ... c.2.1 ... (canonicalPairing ...)`.
Proof irrelevance matches the `card = 25` and `50 <= 99` proof arguments.
If needed, first show the pointwise equality with `Equiv.trans` explicitly,
then use `FiniteDeck.act` at the small function level. **Do not** prove a
second pointwise swap theorem.

The probability proof is purely map functoriality. For an arbitrary
`u : Dist C`, `s : C -> X`, `f : X -> Y`, `g : C -> Y`, use:

```lean
theorem mapMapOfPointwise {C X Y : Type*} (u : Dist C) (s : C → X)
    (f : X → Y) (g : C → Y) (h : ∀ c, f (s c) = g c) :
    (u.map s).map f = u.map g := by
  rw [Convexity.StdSimplex.map_map]
  exact congrArg (fun v : C → Y => u.map v) (funext h)
```

Use it first to flatten `swapLaw.map (fun p => act p d)` and then to project
membership. The proof can also use one extra helper for three composed maps:
`rw [map_map, map_map]` at abstract types, followed by a `congrArg` of the
pointwise equality. The uniform choice law is unchanged throughout; **do not
unfold its `Fintype` or prove the weight formula again**.

Using `applyDeterministicSupport` from Section 2, conclude for every d:

    (K ; M) d = (K d).map membership
               = (uniformChoice.map (fun c => act (choicePerm c) d)).map membership
               = uniformChoice.map (postChoice d)
               = E d.

Apply `funext` to get `K ; M = E`. Use an isolated `rfl` for each alias of the
existing map body; if `rfl` is expensive, make the existing definition use the
same `choicePerm`/`postChoice` expression so the equality has a shared spine.
This is a source-level factoring, not an assumption that two distributions
with different definitions are defeq.

### 3.4 Combine the two equalities at abstract types

```lean
theorem fuseSwapLocal {X Y : Type*} (K H : FiniteKernel X X)
    (M E : FiniteKernel X Y) (L : FiniteKernel Y X)
    (hH : H = FiniteKernel.comp M L)
    (hK : FiniteKernel.comp K M = E) :
    FiniteKernel.comp K H = FiniteKernel.comp E L := by
  calc
    _ = FiniteKernel.comp K (FiniteKernel.comp M L) :=
      congrArg (FiniteKernel.comp K) hH
    _ = FiniteKernel.comp (FiniteKernel.comp K M) L :=
      (FiniteKernel.comp_assoc K M L).symm
    _ = _ := congrArg (fun T => FiniteKernel.comp T L) hK
```

You can now specialize to the 99-card kernels and prove a kernel equality.
Using `convPush_eq_pointMassComp swapLaw rho99Ideal d` (arguments in this
order!) and `k1_rhs_bookkeeping d`, get the desired K1 equality by a short
chain of `Eq.trans`/`congrArg` applications. For example:

    map Wi (act · d)
      = apply (pointMass d) (K ; H)         -- convPush_eq_pointMassComp
      = apply (pointMass d) (E ; L)         -- congrArg with fuseSwapLocal
      = apply (E d) L                      -- def / apply_comp + apply_pointMass
      = apply (pointMass d) oldIdeal       -- (k1_rhs_bookkeeping d).symm

Here `oldIdeal` is the exact kernel in the q3 theorem, namely
`exchangeThenLocalReset membership localLift rawExchange`. Do not accidentally
use the old `Gate6Crux.fullRoundIdeal` with the reverse order. You can wrap
the point-mass-to-row conversion in a generic lemma so no heavyweight rewrite
is required. This proves equality of actual ideal-round kernels; it is not a
hypothesis of the eventual headline.

## 4. The missing stronger statement: swap membership law depends ONLY on membership

This section is the important new combinatorial insight. It replaces direct
inverse-choice reasoning and establishes a reusable arbitrary-N bridge.

Fix a deck d. Put `S = membership d`. The map

    f_d : exchangeChoice -> Membership,  c |-> postChoice d c

has image in `R(S) = { T : |S \\ T| = |T \\ S| = k }` where `k=25` here.
The map is injective: if two choices yield the same post-exchange left set,
`newLeftCards_injective` recovers both choice sets. The number of source
choices and the number of target elements are the SAME known number:

    |exchangeChoice| = choose m k * choose (N-m) k = |R(S)|.

Thus the image is all of R(S). This proves surjectivity with no explicit
inverse, `leftWitness`, `rightWitness` or split reconstruction. In particular,
we can forget the current ordering of d. This is stronger than the count
intertwining theorem Qwen previously proved. It makes the physical-swap law
agree exactly with the preexisting generic subset-exchange kernel.

### 4.1 The generic finite-image lemma (prove at abstract types first)

A useful general result, independent of cards:

```lean
theorem imageEqOfCard {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (R : Finset B)
    (hR : ∀ a, f a ∈ R) (hc : R.card = Fintype.card A) :
    (Finset.univ : Finset A).image f = R := by
  classical
  have hsub : (Finset.univ : Finset A).image f ⊆ R := by
    intro b hb
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb
    exact ha ▸ hR a
  have hcard : ((Finset.univ : Finset A).image f).card = R.card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hc]
  -- check exact signature of Finset.eq_of_subset_of_card_le in the pinned Mathlib
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
```

If the last lemma has a different name, use the fact that a strict inclusion
of finite sets implies strictly smaller cardinality (`Finset.card_lt_card`),
contradicting hcard. Do not attempt a proof by explicit enumeration.

A second generic helper uses this image equality with the already-proved
`GSR.map_injective_uniform_mass` (not another `sum_eq_single` proof):

```lean
theorem uniformInjectionMassOn {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Nonempty A]
    (f : A → B) (hf : Function.Injective f) (R : Finset B)
    (hR : ∀ a, f a ∈ R) (hc : R.card = Fintype.card A) (b : B) :
    Dist.mass ((GSR.uniformDist A).map f) b =
      (if b ∈ R then (Fintype.card A : Rat)⁻¹ else 0) := by
  classical
  have himage := imageEqOfCard f hf R hR hc
  have hex : (∃ a, f a = b) ↔ b ∈ R := by
    constructor
    · rintro ⟨a, ha⟩; exact ha ▸ hR a
    · intro hb
      have hb' : b ∈ (Finset.univ : Finset A).image f := himage.symm ▸ hb
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb'
      exact ⟨a, ha⟩
  rw [GSR.map_injective_uniform_mass f hf b]
  -- use the iff to equate the two if conditions, or split on b ∈ R
  by_cases hb : b ∈ R
  · rw [if_pos hb, if_pos (hex.mpr hb)]
  · rw [if_neg hb, if_neg (fun h => hb (hex.mp h))]
```

Minor fixes may be needed for rewrite orientation; the two branches simply
replace the existential by the reachability predicate. `classical` can select
different `Decidable` instances than those in a statement; prove the generic
predicate/ite bridge separately if needed. This is exactly the point where
Qwen should *not* call broad `simp` at concrete 99. In the specialized proof
instantiate the already-checked theorem using `exact`.

### 4.2 Concrete ingredients: which existing declarations to call

`CommanderMembershipKernels.Membership` and `FiniteDeck.Membership 99 50`
are abbreviations of the same subtype. Work with the `.1` field; never
normalize the `Fintype` of the deck space or even the whole membership type.

Use `FiniteDeck.ReachSet 99 50 25 hm hk hkm (membership d)` (namespace in
`SubsetExchange.lean`, check its actual declaration). `ReachSet` uses its own
finite universe of membership values. If a membership `Fintype` instance from
a different module does not defeq, avoid rewriting the whole universe: compare
membership predicates using `Finset.mem_filter`, `Finset.mem_univ`, and
`Finset.ext`. The cardinality formula is already proved for this exact set.

**(a) Injectivity of f_d.**

```lean
-- Candidate shape. Reuse the postChoice definition of Section 3.
theorem postChoice_injective (d : CommanderPermutation.Deck) :
    Function.Injective (postChoice d) := by
  intro c c' heq
  have hv := congrArg Subtype.val heq
  -- change hv to the newLeftCards equality (the value of newMembership)
  -- have hparts := CommanderPhysicalExchange.newLeftCards_injective d
  --     c.1.1 c'.1.1 c.2.1 c'.2.1 hv
  -- exact Prod.ext (Subtype.ext hparts.1) (Subtype.ext hparts.2)
```

`newLeftCards_injective` has EXACT argument order `(d,L,L',R,R',h)`.
To assemble use `congrArg (fun u : Membership => u.1)` and `change` only
that value equality, then `Prod.ext` and `Subtype.ext`. Do not `cases c` or
prove injectivity of the full swap permutation; this only concerns the image
of its membership. Compile the completed injectivity theorem before advancing.

**(b) Range inclusion.** `newMembership_overlap_25 d L hL R hR` gives
`(S.1 ∩ T.1).card = 25`. `S.2 = 50` and `T.2 = 50`. Use
`Finset.card_sdiff` on each difference (and `Finset.inter_comm` as needed),
then `omega` for `50 - 25 = 25`. `Finset.mem_filter` plus
`Finset.mem_univ` puts T in `ReachSet S`. The result should be an isolated
`postChoice_mem_reach` theorem. Do not construct an inverse.

**(c) Cardinality equality.** `FiniteDeck.subsetExchangeCount` gives the
cardinality of `ReachSet`, symbolically. The existing
`CommanderA3ExchangeCard.exchangeChoice_card_eq_transitionDenominator`
returns a **Rat** equality. Obtain the Nat equality by `exact_mod_cast`
(or `Nat.cast_inj` in the appropriate form) while the two cardinalities are
named. `BernoulliLaplaceGeneral.transitionDenominator 99 50 25` is the
binomial product; unfold only `transitionDenominator` and simplify `99-50`
by a tiny arithmetic fact. Do not `norm_num` on `Fintype.card exchangeChoice`
without that bridge; the symbolic count proof already exists. Call the
result e.g. `reach_card_eq_choices (S : Membership)`.

**(d) Result.** Apply `uniformInjectionMassOn` with `f = postChoice d`,
`R = ReachSet ... (membership d)` and the three hypotheses above. The output
mass is exactly

    if T ∈ ReachSet S then (card exchangeChoice : Rat)⁻¹ else 0.

This is also exactly the mass of
`FiniteDeck.subsetExchangeMembershipKernel commanderBLParams S`, by
`FiniteDeck.subsetExchangeMembershipKernel_mass_ite` in `BLRefinement.lean`.
Note that the latter writes its predicate as **S in ReachSet T**. Use
symmetry of reachability (swap the two conjuncts) at the predicate level.
Do not rewrite a large probability term to show this equality.
The existing `commanderBLParams` abbreviation lives in
`BernoulliLaplaceCommanderBridge.lean`.

You may choose to state and prove just the equality of the two masses first;
then `StdSimplex.weights_inj` + `Finsupp.ext` gives equality of distributions.
Avoid `ext` with a large default simp set. The production theorem is:

```lean
-- Desired theorem, using the repository's actual namespaces.
theorem rawMembership_eq_subsetKernel (d : CommanderPermutation.Deck) :
    CommanderPhysicalExchange.rawExchangeMembership d =
      FiniteDeck.subsetExchangeMembershipKernel commanderBLParams
        (CommanderMembershipKernels.membership d) := by
  -- compare the two proven mass formulas; do not unfold either Dist.ofFun.
```

If importing `BernoulliLaplaceCommanderBridge` makes the dependency graph too
heavy, define the concrete parameter record locally or move the theorem to a
bridge module downstream of both constructions. Keep the generic mass proof
in the light module. Do not introduce an import cycle.

A weaker but sufficient fallback if the bridge between concrete/generic
membership instances is painful: prove `rawExchangeMembership d =
rawExchangeMembership d'` whenever `membership d = membership d'` by applying
the **same** mass formula from (d) to the two decks. It immediately follows
from their image and denominator equality; no generic `subsetExchange` kernel
instance needs to be instantiated for this last equality. This proves the
same smoothing consequence. Do not spend hours on a coercion mismatch if
this fallback already lets you finish Gate 6.

## 5. Deterministic-start smoothing is kernel algebra after Section 4

### 5.1 The general factorization theorem

In the notation of Section 3, let `Q : Membership -> Dist Membership` be the
subset-exchange kernel. The desired result of Section 4 is `E = M ; Q`.
K1 gives the ideal physical round P as `M ; Q ; L`. From the established
`CommanderMembershipKernels.localLift_preserves_membership` we know
`L ; M = identity`. Consequently

    P^t = M ; Q^t ; L,   t >= 1.

This identity is valid for any initial deck distribution, not just one
uniform on a count fiber. A useful intermediate theorem that suffices for
Gate 6 is

    (M ; L) ; P = P.

It is just associativity:

    M ; L ; M ; Q ; L = M ; id ; Q ; L = M ; Q ; L.

Prove it over abstract types `X,Y`, with kernels M, Q, L as arguments. Using
`FiniteKernel.comp_assoc`, `comp_id_left`, `comp_id_right` and a single
`L ; M = identity` hypothesis, the proof should be a calc of four equalities
or `simp only [comp_assoc, hrecover, comp_id_left]` after choosing explicit
parentheses. If `simp only` cannot locate `L ; M` in a right-associated
expression, re-associate it explicitly. Do not rewrite at concrete 99.
For example, an even smaller interface is

```lean
-- P is represented in right-associated form.
theorem resetBeforeFactoredRound {X Y : Type*}
    (M : FiniteKernel X Y) (L : FiniteKernel Y X)
    (Q : FiniteKernel Y Y)
    (hrec : FiniteKernel.comp L M = FiniteKernel.identity) :
    FiniteKernel.comp (FiniteKernel.comp M L)
      (FiniteKernel.comp M (FiniteKernel.comp Q L)) =
      FiniteKernel.comp M (FiniteKernel.comp Q L) := by
  calc
    _ = FiniteKernel.comp M
      (FiniteKernel.comp L (FiniteKernel.comp M (FiniteKernel.comp Q L))) :=
      FiniteKernel.comp_assoc M L _
    _ = FiniteKernel.comp M
      (FiniteKernel.comp (FiniteKernel.comp L M) (FiniteKernel.comp Q L)) :=
      congrArg (FiniteKernel.comp M) (FiniteKernel.comp_assoc L M _).symm
    _ = FiniteKernel.comp M
      (FiniteKernel.comp FiniteKernel.identity (FiniteKernel.comp Q L)) :=
      congrArg (fun T => FiniteKernel.comp M
        (FiniteKernel.comp T (FiniteKernel.comp Q L))) hrec
    _ = _ := congrArg (FiniteKernel.comp M) (FiniteKernel.comp_id_left _)
```

This theorem also applies if `M` is any observation kernel with a recovering
lift; it is not particular to shuffling. Use `apply_comp`, `apply_pointMass`,
`run_rec_eq` to show `run P (t+1) (pointMass d) = run P (t+1) (L (m d))`.
The first round is equal by reset absorption; the same subsequent `t` rounds
are applied to equal distributions. That is all the smoothing needed.

If only the weaker fallback (membership-only constancy) of Section 4 is
available, prove the same conclusion by a generic mixture lemma: if
`m(d)=m0` on the support of a lift, and `E d` depends only on `m(d)`, then
applying E to that lift equals the constant row `E d0`. Prove abstractly with
`FiniteKernel.apply_mass_finsupp` and `sumOverEnlarged_eq_one`, or
`StdSimplex.map_const` on support. Use `localLift_preserves_membership` or its
mass theorem to obtain support confinement. This route avoids a choice of a
representative deck for every membership.

### 5.2 The segregated count state has exactly one membership

Let `d0 = Equiv.refl (Fin 99)` and `S0 = membership d0`. The initial macrostate
`commanderSegregatedState = Fin.mk 49 ...` means count 50 (not count 49!).
All memberships are 50-sets; the marked set `leftOrigSet` also has size 50.
Therefore

    membershipCount S = 50  iff  S.1 = leftOrigSet  iff  S = S0.

Proof: `S.1 ∩ leftOrigSet` is a subset of each set. If its cardinality is 50,
equality with both sets follows from the same `eq_of_subset_of_card_le`
principle as Section 4. The reverse direction is `inter_self` and
`leftOrigSet_card`. No probability, no deck enumeration. For S0, combine
`membership_leftCards`, `leftCards_id_eq_segLeft`, `segMembership_one_eq_segLeft`
and `CommanderFiberCount.leftOrigSet_eq_image` with the definition of
`FiniteDeck.leftPositions`. Both finite sets are the same image of `Fin 50`.
Do not use `decide` on deck-valued expressions to prove this fact.

Prove the isolated theorem `membershipLift_segregated_eq_pointMass`:

    membershipLift commanderSegregatedState = pointMass S0.

Use `membershipLift_mass` (its exact conditional density) and
`membershipFiberCount 50 = choose 50 50 * choose 49 0 = 1`. This count formula
already exists as `membershipFiberCount`; unfold only this natural-number
formula, not `membershipLift`. With the iff above, the mass equals
`Dist.mass_pointMass`. If the equality's conditions are in opposite order,
use `eq_comm` at the predicate level. Conclude with `Finsupp.ext`.

Now evaluate the existing two-layer lift theorem at this particular state:

    membershipLift ; localLift = fiberLaw project project_surjective

(`CommanderMembershipKernels.membershipLift_localLift_eq_fiberLaw`).
Use `congrFun` at `commanderSegregatedState`, rewrite its first factor by the
singleton result, and `apply_pointMass`. This gives **exactly**

    apply (pointMass commanderSegregatedState) (fiberLaw project ...)
        = localLift S0.

Call this `segregatedFiber_eq_localLift`. You have now converted the precise
input law of the existing q3 theorem to the input used by reset absorption.
No need to prove an independent formula for the one-round output on the
25-count fiber. This bridge works for any positive round count. It must not
be asserted for zero rounds, where a point mass and a nontrivial local fiber
uniform law differ.

### 5.3 How to use the old exact theorem

Use K1 to identify P with the kernel in
`CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`.
Use `segregatedFiber_eq_localLift` and `resetBeforeFactoredRound` to equate
`run P 3 (pointMass d0)` with `run P 3 (old segregated fiber-law input)`.
Apply `congrArg (fun u => Dist.tv u U)` to that equality. The resulting
exact `Dist.tv (run P 3 (pointMass d0)) U = q3` is the ideal deterministic
reference theorem. This is an unconditional new result, not an assumption
on the ideal law. Use `q3` as the named constant from `Gate6FiniteGSR.lean`,
with a small rational bridge if the old theorem displays its literal fraction.

## 6. Assembly of the actual finite protocol: no concrete reductions

Now all pieces are available:

    Wf = conv swapLaw rho99PullbackFinite
    Wi = conv swapLaw rho99Ideal
    Kf = permutationActionKernel Wf
    Ki = permutationActionKernel Wi
    U  = uniformDist Deck
    d0 = identity deck
    TV(Wf,Wi) <= δ1
    TV(run Ki 3 (pointMass d0),U) = q3.

Work at the convolution level for the perturbation proof. `powConvTV Wf Wi 3`
gives `tvFinsupp (powConv Wf 3) (powConv Wi 3) <= 3 * δ1`. Apply
`supportMapTV` to the common map `fun p => act p d0`, and use `powConvRunEq`
for both sides. This produces `TV(run Kf 3 pointMass d0, run Ki 3 pointMass d0)
<= 3*δ1`. Convert between support TV and `Dist.tv` by `tv_eq_tvFinsupp`.
Keep the transport lemma generic in N, distributions and t. If needed use a
separate generic triangle wrapper at abstract `[Fintype X]`:

```lean
-- This wrapper prevents the specialization from unfolding any probability laws.
theorem tvBoundVia {X : Type*} [Fintype X] (u v target : Dist X)
    (a b : Rat) (h1 : Dist.tv u v ≤ a) (h2 : Dist.tv v target = b) :
    Dist.tv u target ≤ b + a := by
  calc
    _ ≤ Dist.tv u v + Dist.tv v target := Dist.tv_triangle u v target
    _ ≤ a + b := by rw [h2]; exact add_le_add_right h1 b
    _ = b + a := add_comm _ _
```

Specialize once; use `gate6_headline_bound : q3 + 3 * δ1 < 1/1000` from
`FiniteDeck/Gate6FiniteGSR.lean`. At concrete types, prefer explicit
`le_trans`, `.trans`, `.trans_lt`, `congrArg` and already-checked lemmas to
`calc` with underscore-inferred large terms, `simp`, `convert`, `exact?`,
or a global `rw` search. There is no new rational arithmetic to do.

### All deterministic starts via one generic identity-deck theorem

Do not prove that arbitrary deterministic starts are fiber-uniform. Instead
prove a theorem over `N`, an arbitrary law `W`, a step count `t`, and a deck `d`:

    TV(run (permutationActionKernel W) t (pointMass d), U_N)
      = TV(run (permutationActionKernel W) t (pointMass (refl _)), U_N).

Here is the complete mathematical proof. Let `ν = powConv W t`.
`powConvRunEq` says the output from d is `ν.map (fun p => p.trans d)`. From
identity, the output is simply ν, by `reflAct` / `Equiv.trans_refl` and
`StdSimplex.map_id`. The map `p -> p.trans d` is a bijection
(`relabel_equiv d`), fixes uniform measure (`uniformDeck_relabel_invariant`),
and preserves TV under common pushforward (`tv_bijective_invariance`). Thus
TV from d equals TV from identity. No comparison of macro counts for arbitrary
decks, and no new averaging assumption. This theorem is useful for ANY
state-independent position-only shuffle protocol, not just GSR.

If using the existing `tv_bijective_invariance` at generic n, note that it is
stated with `Dist.tv` and `[Fintype]`; keep those instances abstract in its
proof and apply the result once. The reference theorem is now enough to give
`∀ d : Deck 99, Dist.tv (run Kf 3 (pointMass d)) U < 1/1000`.
Optionally strengthen to every initial law with `mixtureTV_le` and the same
uniform row bound. The result is about the **actual Kf**, not about a
conditional inequality with an assumed ideal q3 premise.

## 7. Close the binary-riffle interpretation honestly and efficiently

A `2^23`-label stable-sort law is a well-defined finite shuffle. To say the
algorithm is literally 23 successive independent binary inverse-GSR riffles
on each pile, transfer the already-proved *list-level* composition to the
pullback action law. Do not derive another sorting/ranking theorem from
scratch. This is an additional representation bridge, not a new mixing bound.

Relevant exact source theorems:

- `GSR.idealShuffle_comp n a b ha hb` gives the product-label shuffle.
- `GSR.productLabelShuffle_uniform_eq_ideal ha hb` identifies that product
  label law with `idealShuffle n (a*b) (mul_pos ha hb)`.
- `PermutationLaw.idealShuffle_canonical_eq_permLaw` gives the rank-inverse
  pushforward on `List.finRange n`.
- `stableBuckets_eq_orderByNewPosition` proves the pointwise sorted order.

### 7.1 Naturality under relabeling gives the arbitrary-current-deck bridge

For any list xs of elements of X, map f:X→Y, and label function l:Y→Fin a,

    stableBuckets a l (xs.map f)
       = (stableBuckets a (fun x => l (f x)) xs).map f.

Proof by two elementary list inductions: each bucket filter commutes with
map, then the `flatMap` over `List.range a` commutes with map. This is true
without injectivity of f. Suggested helper code, at abstract X/Y:

```lean
-- Use the actual namespace GSR.
theorem stableBucketsMap {X Y : Type*} (a : Nat) (l : Y → Fin a)
    (f : X → Y) (xs : List X) :
    GSR.stableBuckets a l (xs.map f) =
      (GSR.stableBuckets a (fun x => l (f x)) xs).map f := by
  have hfilter (j : Nat) (ys : List X) :
      (ys.map f).filter (fun y => (l y).val == j) =
        (ys.filter (fun x => (l (f x)).val == j)).map f := by
    induction ys with
    | nil => rfl
    | cons x ys ih =>
        cases h : (l (f x)).val == j <;> simp [h, ih]
  unfold GSR.stableBuckets
  -- Use a local induction over an arbitrary list of bucket indices, then
  -- specialize it to List.range a. At each cons use hfilter, List.map_append.
```

For a current deck permutation d define `enc d := (List.finRange n).map d`.
Take `xs = List.finRange n` and `f = d` in this naturality theorem. The
label vector on positions is `l ∘ d`. Since d is bijective, reindexing labels
by d preserves the uniform label law (bijection of `Fin n -> Fin a`):

    ℓ |-> ℓ ∘ d, inverse ℓ' |-> ℓ' ∘ d.symm.

Implement this `Equiv` with function extensionality and
`Equiv.apply_symm_apply`/`symm_apply_apply`. `GSR.map_bijective_uniformDist`
proves uniform invariance. No independence sum or `a^n` count needed.
Combining the naturality identity, canonical stable-order theorem, and label
law invariance proves for all d:

    idealShuffle n a ha (enc d)
       = (gsrPullbackLaw n a ha hn).map (fun p => enc (act p d)).

This statement is the bridge from physical stable sorting of the *current*
deck to a state-independent pullback permutation law. Do not use only the
canonical-list theorem at later stages; tie-breaking follows current order.

### 7.2 Transfer composition through a faithful encoding

The map `enc` is injective: if two mapped `finRange` lists agree, compare the
entry at each index `i : Fin n` (or rewrite to `List.ofFn d` and use pointwise
values). Use `Equiv.ext`, and `#check` the list `getElem`/`ofFn` lemmas in the
pinned Mathlib. This is elementary and generic n. No permutation enumeration.

For any injective `enc`, equality of distributions after mapping by `enc`
implies equality of the original laws. Proof: choose a left inverse on the
image, extend it arbitrarily off the image (the permutation type is nonempty),
map both distributions through that left inverse, and use `map_map`/`map_id`.
This general lemma does not require Fintype. It is the same argument as
`map_bijection_inverse` in `RelabelInvariance.lean`, but injectivity suffices.

For transferring `apply`, use the following generic commuting-square helper.
It is just the existing `joinMapComm` applied to a family of laws:

```lean
theorem applyThroughEncoding {X Y : Type*} (u : Dist X) (enc : X → Y)
    (K : FiniteKernel X X) (J : FiniteKernel Y Y)
    (h : ∀ x, J (enc x) = (K x).map enc) :
    FiniteKernel.apply (u.map enc) J = (FiniteKernel.apply u K).map enc := by
  unfold FiniteKernel.apply
  rw [Convexity.StdSimplex.map_map]
  have hf : (fun x => J (enc x)) = (fun x => (K x).map enc) := funext h
  rw [hf, ← Convexity.StdSimplex.map_map, FiniteDeck.joinMapComm]
```

If the first `map_map` uses `Function.comp` notation, change it to the
pointwise lambda at abstract types. This is also a useful reusable refinement
lemma for multi-pile work.

Take `X=Perm(Fin n)`, `Y=List(Fin n)`, J the list-level b-label kernel,
K its pullback action kernel. Starting at the identity, use the arbitrary-deck
bridge in 7.1 and `applyThroughEncoding` to show that encoding the convolution
of the a- and b-pullback laws gives the two successive list shuffles. This
uses `Gate6Crux.convAsApply` (generic N). The already-proved list composition
identifies that law with a single a*b shuffle. The canonical pullback theorem
identifies that with the encoding of the a*b pullback law. Cancel enc using
its injectivity. Result:

    conv (gsrPullbackLaw n a ha hn) (gsrPullbackLaw n b hb hn)
      = gsrPullbackLaw n (a*b) (mul_pos ha hb) hn.

Induct on t using the `powConv` recursion: `powConv binary t = pullbackLaw (2^t)`.
For t=0 use the a=1 stable-sort identity (all labels equal; rank is identity),
which follows from stableBuckets or the canonical-list bridge plus enc
injectivity. Alternatively prove the theorem for t>=1 by starting with t=1;
then only the identity-convolution unit lemma is needed. Proofs of
`ha : 0 < 2^t` are irrelevant to the resulting law. Apply this theorem to the
49 and 50 pile factors. Independent sampling of each pile and each round is
part of the product/convolution definitions. If modeling a different temporal
interleaving of the two piles, within-pile actions commute because their
supports are disjoint (state the intended interleaving precisely).

Do not block the a-label theorem on this final interpretation: first state the
precise 2^23-label physical certificate, then prove the binary equivalence.
Do not claim the binary result before this bridge compiles.

## 8. After Gate 6: two deeper mathematical payoffs (not critical-path tasks)

### 8.1 A much sharper local-shuffle certificate via descents

The collision coupling is a useful upper bound but can substantially
overestimate TV. A more precise result for an arbitrary finite pile is
available using just descents and stars-and-bars (not a spectral calculation).
For a pullback permutation p, let `d(p)` be the number of adjacent descents
`p(i) > p(i+1)` in its output order. For uniform labels in `0,...,a-1`, the
probability of this exact stable sorted permutation is

    ν(p) = choose(a+n-1-d(p), n) / a^n.

**Proof that Qwen should follow:** for a fixed p, take the sequence of labels
along its output order. It must be weakly increasing. At every descent of p
it must be strictly increasing, because equal labels would preserve old
position order. Conversely those conditions suffice for the stable sorted
order to equal p. Let `D_i` be the number of descents strictly before index i.
Subtract `D_i` from each label in the sequence. This is a bijection to weakly
increasing sequences of n integers in `0,...,a-1-d(p)`. If `a<=d(p)`, there
are no such sequences and the binomial coefficient is zero. Otherwise count
by the standard multiset / stars-and-bars bijection (add i to transform a
weakly increasing sequence to a strictly increasing one). This yields the
binomial coefficient. Every label assignment has probability `1/a^n`.
Be explicit about Nat subtraction and the empty case, so the bijection is not
silently invalid. The permutation itself provides the label-reindexing
bijection, so no list duplicate issues arise.

Let `A(n,d)` count permutations on n positions with exactly d descents.
These are Eulerian numbers, with `A(1,0)=1` and

    A(n,d) = (d+1)*A(n-1,d) + (n-d)*A(n-1,d-1),

out-of-range terms zero. For n>=2, remove the largest element. Inserting it
into a permutation with d descents preserves the count in the final gap or
in any descent gap (d+1 positions). Inserting into a permutation with d-1
descents increases the count in all other gaps (n-d positions). This is a
bijection proof of the recurrence. Define the small integer table recursively;
prove it equals the descent-fiber cardinality using this insertion partition.
Do NOT compute `Finset.univ : Finset (Perm (Fin 50))` with `native_decide`.

Once both theorems compile, group the finite TV sum by descent counts. For
two independently shuffled piles with sizes m and n, equal alphabet a:

    TV(product,uniform product) = (1/2) sum_{i=0}^{m-1} sum_{j=0}^{n-1}
      A(m,i) A(n,j) * abs(
        choose(a+m-1-i,m)*choose(a+n-1-j,n)/a^(m+n) - 1/(m! n!)).

This is a sum of m*n rational terms, not m!*n! terms. Push it through the
already-proved injective pile embedding, or simply use map contraction.
The existing telescope from Section 2 is unchanged. An exact-arithmetic
calculation (NOT a Lean proof) gives the following for 50/49 and three rounds:

| binary riffles per pile per round | product TV | q3 + 3 product TV |
|---:|---:|---:|
| 17 | 0.0004395385341 | 0.001344375271 |
| 18 | 0.0002197692995 | 0.0006850675669 |
| 23 | 0.000006867790947 | 0.00004636304122 |

So the sharper formula could certify **18 instead of 23** riffles per pile
per round, using the same ideal q3, saving 30 pile riffles over the three-round
protocol. This does not show 18 is optimal or that 17 fails in the actual
chain; 17 only fails this sufficient bound. For a first certificate use the
proved collision bound; introduce this as a distinct post-Gate-6 project
that improves realistic cost. It is particularly valuable for arbitrary deck
sizes and optimality research. The calculation uses the Eulerian recurrence
and exact binomial arithmetic; it has also been checked against exhaustive
small-deck label enumeration. No numerical floating point claim is needed
in Lean: prove the general grouping theorem and evaluate the small table.

### 8.2 The arbitrary-multi-pile theorem behind the entire K1 story

For pile capacities `n_i` with `sum n_i = N`, let `H = product_i Sym(n_i)` be
the within-pile permutation group. Specify a movement matrix `C_ij`: how many
cards from source pile i go to destination pile j, with row and column sums
matching the capacities. Uniformly choose the disjoint subsets within each
source pile with the prescribed sizes; send them to their destinations by
any fixed legal pairing. Then perfectly shuffle each destination pile.
For each given starting ordered deck, the resulting allocation is uniform
over all allocations with that movement matrix; the final ordered deck is
uniform over the whole corresponding permutation class.

The counting proof is exactly the injection/surjection and local-fiber
argument of Sections 3-5. The number of reachable allocations is

    R = product_i (n_i! / product_j C_ij!).

A particular reachable allocation determines every source subset uniquely
by intersecting with the original source membership. Thus the choice map is
bijective, and all reachable allocations have probability 1/R. Every final
allocation has `product_j n_j!` ordered refinements. This yields the uniform
law on the `H` double coset of any permutation with that movement matrix,
whose cardinality is

    (product_i n_i!)^2 / product_(i,j) C_ij!.

Inversion transposes the movement matrix; in particular, the exchange law is
reversible for symmetric C. This is the conceptual explanation of the old
K1b commutation: for uniform 25/25 subset choices plus uniform local shuffle,
the induced double coset is symmetric, so taking inverses exchanges local-
then-swap and swap-then-local without changing its ideal law. No claim about
commutation for nonuniform finite-GSR. More generally, pile exchanges and
category histograms can use the same finite-partition ideas. Use this insight
when implementing G5 after the current certificate, rather than copying the
Commander witness proof for every number of piles.

## 9. Implementation discipline, and what to do when a proof gets stuck

- Verify exact declaration names with `#check` and actual imports; the snippets
  are intended proof routes, not a tested patch. The final theorem must compile
  without `sorry` or custom axioms. The earlier probe files and the old wrong-
  order theorem can remain historical scratch only; production imports should
  expose the compiled canonical lemmas.
- Check **one generic declaration at a time** before specializing. In a small
  temporary probe use `import` of only the necessary production modules, and
  use `lake env lean path/to/probe.lean` or the appropriate `lake build` target.
  A previous successful build is not evidence that a renamed or modified
  declaration has been checked. If a warm build skips the target, force the
  *relevant* target to recheck, not the whole project.
- On recursion/memory blowups, identify which term triggered definitional
  equality, not just which tactic was active. Move the argument into a generic
  helper with independent opaque parameters; use the proven theorem by name.
  For example, prove `imageEqOfCard` with abstract A/B and `Finset.card` data
  then apply it to exchange choices. A 99-specific equality between two
  differently-defined universe sums is exactly what we must avoid.
- If the generic helper succeeds and only its concrete instantiation fails,
  check that both sides share the same instances and the same definitions.
  `change` to a common *small* spine, use `congrArg` and proof irrelevance,
  or make both definitions use the same map function. Do not solve it with
  repeated unfolding of `Fintype`, `uniformDist`, `Dist.ofFun`, or local lift.
- Avoid `maxHeartbeats 0`/ever-growing recursion limits, and don't leave a
  multi-GB WHNF process polling for an hour. If an isolated generic helper
  compiles quickly and the specialization takes orders of magnitude longer,
  stop that specialization and inspect its representation. A generic theorem
  application does not logically require enumerating any support. Preserve
  the local default-cap success criterion reported in the handoff, and use
  a short bounded build to diagnose a failure rather than reset the budget
  repeatedly. No broad mechanical proof rewrites for unrelated modules.
- The long-term goal is still the actionable finite-deck roadmap. Once the
  unconditional physical theorem and actual binary interpretation are built,
  advance to the generic multi-pile/dealing/certification stages. Don't add a
  separate completion gate for every historical hint. The sharper descent
  result is valuable optional optimization research after the first certificate.

**Immediate instruction for the active loop:** read Sections 0-3 now. Then
Sections 4-6 in that order. Section 7 checks the binary interpretation and
Section 8 is follow-on work only. Prefer a working short proof of the actual
physical theorem to finishing the abandoned old-order K1b experiment.
