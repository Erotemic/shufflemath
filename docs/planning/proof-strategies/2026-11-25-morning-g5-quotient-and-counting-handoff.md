# 2026-11-25 morning — executable G5 quotient, histogram counting, and Gate 6 closure

**Base:** `91284abc9ec2`. Read this as the current implementation guide. The
previous 2026-11-25 handoff is largely implemented at the building-block level;
do not redo those proofs. The historical review is
`docs/planning/reviews/2026-11-25-morning-g5-quotient-and-gate6-review.md`.

The operator supplied three small, uncompiled Lean candidate modules in
`dev/qwen-hints/2026-11-25-morning/`: `QuotientSeeds.lean`,
`CellRelabelSeeds.lean`, and `Gate6AssemblySeeds.lean`. Compile one file at a
time with `lake env lean path/to/file.lean` after building its dependencies.
If a declaration fails, work on that generic declaration only; do not copy it
into the main aggregator until it passes. Their namespaces are temporary.
Use the existing verified names instead of duplicating an identical lemma.

## 0. Immediate instructions and order

You have proved `multiPile_equivFiber`, `multiPile_card`, `lump_pileTotal`,
`lump_categoryTotal`, `exchangePair_involution`, `exchangeTargets_symmetric`,
`histAllocSum_choose`, `allocPi_card`, and `twoPileTransitionStochastic`.
Do not reprove them. The last theorem is a scalar identity, NOT a kernel.
The quotient will generally NOT be symmetric. Do not seek a uniform
stationary distribution on histogram tables or prove column sums equal one.

**Main path:** A1 (carrier and actual exchange) -> A2 (cell relabel) -> A3
(lumpability and reversible quotient) -> A4 (histogram fiber counts) -> A5
(explicit transition formula) -> A6 (full uniform-fiber bridge). Work on A4
or Gate 6 while A1/A3 has a bounded compilation blockage. A3 can be completed
before A4 and A5. The generic quotient theorem should be a small independent
module, NOT imported through the Commander stack.

**Independent Gate 6 path:** B1--B4. Correct scope and GSR convention. Use
`Gate6K1Bridges` and `Gate6ThreeRound` as the source of truth. Do NOT reopen
batch 5b, K1b, or the existing three-round restricted-start certificate.

Do not raise global recursion or heartbeat limits. Large-card types must
occur only in small applications of generic opaque theorem declarations.
Use targeted build, then migrate, then full verification. If a proof takes
minutes with growing RSS, isolate the exact declaration with a bounded
external timeout; avoid running competing expensive Lean processes. A
cached successful build is not a new check of a changed declaration.

## A1. Construct a real stochastic allocation kernel

### A1.1 Carrier: fixed capacities, named cards, arbitrary number of piles

Avoid trying to encode an entire deck as a histogram or as a dependent
product of local permutation groups. The state here is the **allocation**,
not the order. Use the representation already used by `lump` and
`realizesAllocation`:

```lean
-- Proposed interface, names can be changed to fit the repository.
-- Use p for number of piles, e for exchange size, c for category count.
def Allocation (N p : Nat) (n : Fin p → Nat) :=
  {A : Fin p → Finset (Fin N) // IsPartition A ∧ ∀ i, (A i).card = n i}
```

Establish one named classical finite instance, if needed via `Finite` then
`Fintype.ofFinite`, rather than trying to synthesize a dependent product of
Fintype instances at every call. For an inhabitation proof, start with a
positional partition P and `n i = (P i).card`; the allocation P is a witness.
This proves a powerful arbitrary-capacity result already, without needing to
construct a partition from a given list of capacities. Later prove existence
for any n with sum n=N using prefix sums or a finite slot equivalence.
Do not assume positive capacities: a zero-sized pile is valid.

If the finite instance for the `Finset` family persists as a wall, a simple
alternative carrier is `{owner : Fin N → Fin p // ∀ i, (univ.filter (fun x =>
owner x = i)).card = n i}`. Its ambient function type has an ordinary
finite product instance. Translate once between owners and partitions using
`partitionSigmaEquiv` (owner x is the first component of its inverse). The
blocks of an owner function are its preimages. Prove the two round trips by
unique ownership. Do NOT create two independent mathematical developments.
The finite function carrier is a fallback, not a requirement to rewrite
`Piles.lean`/`Histograms.lean`.

### A1.2 Observe actual histograms, with bounded entries

Use `lump A.val color i j`. The histogram table of N cards has entries
in `Fin (N+1)`. Prove that each entry is at most N using `card_filter_le`
or `Finset.card_le_card (Finset.filter_subset ...)`, followed by
`Finset.card_le_univ` (or `subset_univ` and `Fintype.card_fin`).

Initially define the histogram carrier as the **image** of that observation,
not as all Nat-valued tables. E.g.

```
BoundedTable := Fin p → Fin c → Fin (N+1)
Hist := {x : BoundedTable // ∃ A : Allocation N p n, table A color = x}
observe : Allocation N p n → Hist
```

Surjectivity of `observe` is immediate from the existential witness. No
hard margin-realizability proof blocks the quotient theorem. Later show
that its image is exactly the tables with the specified row/column sums.
This representation also avoids the old `Nat` codomain issue with
`Dist.map_mass_eq_univ_fiber`. Do not choose a separate finite universe of
histograms with impossible states and then pretend `fiberLaw` is defined on
empty fibers.

### A1.3 Actual exchange operation

Fix distinct pile indices i,j and exchange size e, with e ≤ n i and e ≤ n j.
For allocation A define `Choices A` as the product of two **subtypes** of
`Finset (Fin N)`: membership in `powersetCard e (A.val i)` and
`powersetCard e (A.val j)`. This avoids the old large `Finset.product` subtype
normalization. Its cardinality is

```
D = choose (n i) e * choose (n j) e > 0.
```

Use `Finset.card_powersetCard`, `Fintype.card_coe` or `Fintype.card_subtype`,
then `Fintype.card_prod`. Provide a separate named `Nonempty (Choices A)`
lemma from the positive card. If local classical instance identities differ,
prove all cardinality/inhabitation statements generically for two finsets,
then pass them as named lemmas. Never evaluate `univ` at concrete N=99.

The update on a choice `(O,I)` is:

- `A' i = (A i \ O) ∪ I`;
- `A' j = (A j \ I) ∪ O`;
- `A' l = A l` for other l.

Reuse `exchangePair` for the first two formulas. Prove a named lemma
`update_at_i`, `update_at_j`, `update_at_other` before packaging. It is fine
to use `if l=i then ... else if l=j then ... else ...` with explicit rewrites.
Do not run broad simp over all the nested subtypes.

Partition invariant: for any card x, there is a unique old owner. If it was
in O its new owner is j; if in I its new owner is i; otherwise owner is
unchanged. O and I are disjoint because i≠j and A is a partition. This
proves both coverage and uniqueness with no counting. For a compact proof,
prove `ownerAfter` with `if x ∈ O then j else if x ∈ I then i else owner x`
and prove its preimages equal the three update cases. Reuse the existing
partition equivalence to get owner. If the owner bridge is more work than
the direct proof, use the three cases on membership in O/I. Sizes follow
from `card_sdiff_of_subset`, `card_union_of_disjoint`, and `Nat.sub_add_cancel`.
The reverse choice is `(I,O)` by `exchangePair_involution`.

Now define the actual row by pushforward:

```lean
noncomputable def allocationExchange ... : FiniteKernel Allocation Allocation :=
  fun A => (GSR.uniformDist (Choices A)).map (update A)
```

`Dist` guarantees nonnegative weights and mass one. **No row-sum proof is
needed to construct it.** `twoPileTransitionStochastic` is an independent
normalization check of a future closed formula, not a reason to delay this.

### A1.4 Symmetry from the existing reversal theorem

First prove a generic uniform-pushforward mass formula for abstract choice
and target types, using `uniformPushforward_pointMass` (in
`CommanderA3UniformPushforward.lean`) or `GSR.map_uniform_mass`. If only
finite source is needed, generalize that lemma rather than specializing a
proof on the entire allocation carrier. `GSR.map_injective_uniform_mass`
is even simpler: `update A` is injective, because the two leaving subsets
are uniquely recovered from the changed pair (`exchangePair_injOn`).

Prove the point mass equals `(exchangeTargets ...).card / D` when all other
piles agree, else zero. The finite preimage is exactly `exchangeTargets`
after unwrapping the two choice subtypes. Alternatively bypass
`exchangeTargets` count entirely: a target is reachable iff the reverse is
reachable by `exchangePair_involution`, and each reached target has mass
`1/D` by injectivity. This latter route is preferred if it avoids a messy
cardinality transport. `D` is independent of A because capacities are fixed.
Then `K(A,B)=K(B,A)` as point masses. Compile `symmetric_stationary` from
`QuotientSeeds.lean` to derive uniform stationarity. Do not prove a separate
column-sum normalization over a large allocation universe.

## A2. The non-obvious relabeling theorem: refine by (pile, category)

This is the central structural shortcut. For any fixed color map
`color : Fin N → Fin c`, define cells indexed by `Fin p × Fin c`:

```
cell A (i,j) = A i |>.filter (fun x => color x = j)
```

They are a partition, even when many cells are empty. `cells_partition` in
`CellRelabelSeeds.lean` proves this from unique pile ownership and unique
color. If A and B have the same histogram, corresponding cells have equal
cardinalities. Construct `cellEquiv A B (i,j)` with `Fintype.equivOfCardEq`
for the two member subtypes. Now glue:

```
g := glueBlocks (cell A) (cell B) hAcell hBcell cellEquiv
```

The already-compiled `glueBlocks_apply_member` implies both
`color (g x) = color x` and `g '' A i = B i` for every pile. The candidate
file supplies these proofs, with explicit names. No need to repeat the
four-block Commander construction or manually handle every color.

For a general relabeling `g : Equiv.Perm (Fin N)`, define
`relabelAllocation g A` by `A i |>.image g` (or `Finset.map g.toEmbedding`).
Prove partition and size preservation. For a color-preserving g,
`observe (relabelAllocation g A) = observe A` since g restricts to a
bijection on each color cell. Prove the image/filter lemma by membership
extensionality with `g.injective`, then `Finset.card_image_of_injective`.
This one action lemma works for all pile counts and categories.

### Transport uniform exchange choices instead of counting probabilities

Relabeling a uniform subset of A i by g is a uniform subset of g(A i).
Construct an equivalence

```
choiceRelabel g A : Choices A ≃ Choices (relabelAllocation g A)
```

by applying `Finset.image g` in each component and inverse with `g.symm`.
Image cardinalities unchanged by injectivity, membership in powersetCard
by `Finset.mem_powersetCard`. Inverses by ext: image by g and g.symm returns
original set. This is about two chosen finite sets, not full deck permutations.

Use `GSR.map_bijective_uniformDist choiceRelabel` to transport the uniform
law. Show `update (relabelAllocation g A) (choiceRelabel g A z) =
relabelAllocation g (update A z)` using `Finset.image_sdiff` (requires
injectivity) and `Finset.image_union`; inspect the exact lemmas in
`Piles.twoPile_pred_iff`. All other piles unchanged. Compose maps using
`Convexity.StdSimplex.map_map` or `Gate6K1Direct.mapMapOfPointwise`.

This yields the distribution identity

```
K (relabelAllocation g A) = (K A).map (relabelAllocation g)
```

If g preserves color, mapping again through `observe` cancels the relabel.
For A,B with `observe A = observe B`, `cellRelabel_image` supplies just
such a g with `relabelAllocation g A = B`. Thus:

```
∀ A B, observe A = observe B → (K A).map observe = (K B).map observe
```

This is **strong lumpability** from each actual allocation, not merely an
identity for a uniform mixture of allocations. It is a stronger and more
reusable result than comparing a few combinatorial formulae for counts.
No explicit histogram transition numerator is required to prove it.

## A3. Generic quotient and stationarity — stop proving the wrong symmetry

Compile `QuotientSeeds.lean` before instantiating A2. First four lemmas
are independent of any finite instance. The code uses `Classical.choose`
on the surjectivity proof to choose a representative of each histogram.
Define `Q y = (K (rep y)).map observe`. It is already a `Dist` and
independent of rep by A2. `quotientRows_intertwines` proves:

```
K ; P = P ; Q       -- P = deterministic observe, ; = FiniteKernel.comp
```

The file supplies `stationary_pushforward`: if μK=μ then
`(μP)Q = μ(PQ) = μ(KP) = (μK)P = μP`. This needs no finite sums at all.
Use μ=uniform allocation and `symmetric_stationary` from A1.4.
The stationary macro law is now defined/proved as a pushforward even before
the closed-form factorial count. Do NOT wait for the histogram fiber formula.

**Weighted detailed balance** follows from a second generic theorem in the
same file. Write F_y = {A | observe A=y}, π=μ.map observe. If μ(A)K(A,B)
=μ(B)K(B,A), then

```
π(y)Q(y,z)
  = sum_(A in F_y) sum_(B in F_z) μ(A)K(A,B)
  = sum_(B in F_z) sum_(A in F_y) μ(B)K(B,A)
  = π(z)Q(z,y).
```

Proof uses `map_mass_on_fiber`, `blockMass_eq`, and `reversible_quotient`.
The only double sum is on ABSTRACT X and Y. These are ordinary algebraic
proofs, not enumeration. Do not specialize until they compile. This also
works for nonuniform microscopic reversible laws; no equal-fiber-size
hypothesis is needed. For symmetric K and uniform μ, weighted reversibility
is immediate by `GSR.mass_uniformDist` and `hSym`. In Lean, avoid applying
`simp` globally to probability laws; rewrite the two named mass identities.

### Counterexample you must keep in mind

For N=4, pile sizes 2,2, and two red/two blue cards, swap one card from each
pile. With states x=0,1,2 red cards in pile 0, the histogram transition is

```
        [ 0    1    0   ]
Q   =   [1/4  1/2  1/4 ]
        [ 0    1    0   ]
π   =   [1/6  2/3  1/6 ]
```

This matrix is not symmetric or doubly stochastic. `π Q=π` and
`π(x) Q(x,y)=π(y) Q(y,x)`. (The column sums are 1/4, 5/2, 1/4.)
Any theorem claiming otherwise is false, not difficult to elaborate.
This is the same issue in the Bernoulli-Laplace chain; do not confuse the
uniform law on named-card allocations with a uniform law on histograms.

## A4. Count histogram fibers by a stabilizer, reusing `multiPile_card`

The following is the main new counting insight. You already know how to
count permutations respecting a partition. Do not independently formalize
multinomial partitions by complicated induction unless necessary.

Let p piles with sizes n_i; c colors with populations r_j. Let X=(x_ij)
be a realized histogram, represented by some allocation A0. Define

```
R_j       = {cards of color j}
A0_ij     = A0 i ∩ R_j
G         = {g : Deck N // ∀ j, g(R_j)=R_j}
F_X       = {A : Allocation // observe A = X}
```

The color blocks form a partition. The map G -> F_X is `g ↦ relabel g A0`.
It is surjective by A2 (cell gluing). For a target B in F_X, the preimage
of B consists of exactly the permutations carrying **each** cell A0_ij
onto B_ij. Why? A permutation preserving each color block and taking each
pile A0_i to B_i takes their intersections to intersections; conversely
mapping every cell correctly implies both unions map correctly. Prove
this via `Finset.image_inter` for injective maps and `Finset.image_biUnion`
or elementwise membership. This is an equality of predicates, so the fiber
subtype is equivalent to `MultiFiber` for the cell partition. No group
quotient API needed. In particular:

```
|G|                 = prod_j (r_j!)
|preimage of B|     = prod_(i,j) (x_ij!)
|F_X| * prod_(i,j) (x_ij!) = prod_j (r_j!) .
```

Both first two identities are **the same theorem** `multiPile_card`, once
on the category partition and once on the cell partition. Its current index
is `Fin k`. For the cell index `Fin p × Fin c`, choose one of:

1. Reindex using an equivalence `Fin (p*c) ≃ Fin p × Fin c` constructed from
   `Fintype.equivOfCardEq` and `Fintype.card_prod`, then transport the product
   by `Equiv.sum_comp`/product analogue (search exact names locally).
2. Generalize `realizesAllocation`, `MultiFiber`, `multiPile_equivFiber`, and
   `multiPile_card` to arbitrary finite index I. The existing proofs never
   use Fin-specific facts; inspect `PileEquiv`, `PileFiber`, `MultiPileFiber`.
   Keep original names as Fin-index wrappers if needed for compatibility.
   This is the natural end-state, but don't require a risky refactor before
   the theorem compiles. An intermediate generic variant is fine if later
   consolidated.

Prove the last identity by finite fiber-cardinality sum. Either generalize
`FiberDisintegration.sum_fiber_card` (already a Rat identity), or reuse
`fiberSum_eq_preimageCard` on the whole target; another route is the Sigma
bijection `g ↦ ⟨f g, ⟨g,rfl⟩⟩`. In Lean prefer the existing finite sum if
`Fintype (Sigma ...)` becomes a wall. Then `Finset.sum_const`, `nsmul_eq_mul`.
Do not first introduce Nat division; state the multiplication equality over
Nat or Rat. All factorial products are positive, including 0!=1, so division
is safe only at the final rational mass theorem.

Similarly count all allocations by the surjection from `Deck N` to allocation
with constant fiber size `prod_i n_i!` (the newly proved `multiPile_card`):

```
|Alloc| * prod_i n_i! = N!.
```

Surjectivity: for any A, gluing per-pile equal-card bijections from fixed
position partition P to A produces a deck; use `gluedRealizes` and
`equivsToMultiPile`. This also proves uniform deck pushes forward to uniform
allocation (`uniform_same_image` is for injective maps; here use the equal
fiber count and `uniformPushforward_pointMass`). All this is independent of
the choice of the positional partition as long as it has the same capacities.

The resulting mass of a histogram under stationary uniform allocation is

```
π(X) = (prod_i n_i! * prod_j r_j!) / (N! * prod_(i,j) x_ij!) .
```

Prove by multiplying the two division-free identities and canceling positive
factors in Rat. The generic `map_uniform_mass` or `uniformPushforward_pointMass`
identifies mass with `|F_X|/|Alloc|`. `multiPile_card` never needs to be
reproved. **This is the multivariate hypergeometric stationary law.** The
stationarity theorem from A3 now gives its actual physical semantics.

### Realizability of every margin-valid histogram (after image version)

For nonnegative integer table x with prescribed row and column sums, split
each actual category R_j into disjoint blocks of sizes x_ij. Construct a
bijection of R_j with `Fin r_j`; define consecutive intervals in `Fin r_j`
using the prefix sums over piles, or map the canonical disjoint block
subtypes via the bijection. Prove partition by unique interval and sizes.
Union across j within each pile. Cells disjoint across both indices; the row
sums give capacities; all columns used so union all cards is full. This
proves `Hist` (the image type) equivalent to bounded tables satisfying both
margins. Reuse a single `partition_of_card_profile` lemma later for A5.
Do not change the stationary-law definition just to force this surjectivity
proof earlier. Zero population categories and zero cells are valid.

## A5. Exact pairwise histogram transition formula: selections versus targets

The existing `allocPi_card` shows a product of category-specific subset
counts for synthetic categories `Fin (X j)`. It must be connected to actual
named card subsets. For a pile S and category profile a:Fin c→Nat with
`sum a=e`, consider

```
Sel(S,a) = {O ⊆ S | ∀ j, |O ∩ R_j| = a_j}.
```

Its members automatically have size e via `lump_pileTotal`. Map to a
family of subsets `O_j = O ∩ R_j` in `powersetCard a_j (S ∩ R_j)`; inverse
is union over j. The forward and backward maps are inverse because the
category cells partition S. Work with **actual finsets** and `Finset.pi`
if it avoids dependent Fintype; `allocPi_card` shows the precise API pattern
in this toolchain. More explicitly, construct `Finset` of functions via
`(Finset.univ : Finset (Fin c)).pi (fun j => powersetCard (a j) (S.filter
(fun x => color x=j)))`; remember `Finset.pi` uses functions on members of
univ (proof argument), so reuse the exact binder shape in `allocPi_card`.
Prove the union/intersection inverse via `Finset.mem_biUnion`, unique color,
and `Finset.mem_powersetCard`. Then `Finset.card_pi`,
`Finset.card_powersetCard` give `prod_j choose (lump S j) (a_j)`.
No need to transport each cell to `Fin (X j)` if counting actual cells is
simpler. Reuse a generic `profileChoiceCard` theorem in place of two copies.

For two active piles i,l let x_j=X_ij and y_j=X_lj. Profiles a,b select e
from each pile. Then

```
x'_j = (x_j-a_j)+b_j,   y'_j = (y_j-b_j)+a_j,
0 ≤ a_j ≤ x_j, 0 ≤ b_j ≤ y_j, sum a = sum b = e.
```

Use explicit bounds before any Nat subtraction. Prove the pointwise
histogram update by filtering the disjoint unions/differences, then taking
cards. For inactive piles X'=X is required. A profile pair has probability

```
W_X(a,b) = [prod_j choose x_j a_j * choose y_j b_j] / D.
```

**Warning:** many profile pairs can yield the same target histogram. The
transition probability Q(X,X') is the **sum** of W over all legal profile
pairs yielding X', not a single product. E.g. exchange one card of a common
color in both piles; any common color gives the same unchanged histogram.
This is a self-loop with several contributions. Use pushforward composition
and a partition into profile fibers (`fiberSum_eq_preimageCard`, or
`uniformPushforward_eventMass`) rather than assert that profile choices are
injective into target histograms. Use bounded entries `Fin (N+1)` or an
explicit finite profile type with bounds. The fact that the resulting
row sums to one comes from A3; `histAllocSum_choose` is a useful independent
check once the formula is connected to the actual row.

### Independent detailed-balance proof (fallback and valuable cross-check)

Do not prove a giant multivariate summation identity. Reverse a legal
profile pair `(a,b)` by `(b,a)`. For each category,

```
x' = x-a+b, y'=y-b+a
choose(x,a) choose(y,b) / (x! y!)
  = 1 / [a! (x-a)! b! (y-b)!]
  = choose(x',b) choose(y',a) / (x'! y'!).
```

The second equality uses `x'-b=x-a` and `y'-a=y-b`, valid by bounds.
In Lean prove the elementary factorial identity first over Nat:
`choose n k * k! * (n-k)! = n!` for k≤n. Search `Nat.choose_mul_factorial_mul_factorial`
(or the exact lemma used elsewhere in `BernoulliLaplaceGeneral`); cast to Rat
and use `field_simp` with `Nat.factorial_pos`, then `ring`. No induction on
whole tables. Multiply the per-category identity via `Finset.prod_congr`.
Other piles' factorial factors and the normalization D cancel. This proves
`π(X) W_X(a,b)=π(X') W_X'(b,a)` term by term. Reverse is an involutive
bijection between the two legal-profile target sets. Sum with
`Finset.sum_bij` or an abstract reindexing lemma. This gives the same
weighted balance as A3, and can independently validate the explicit
closed formula. Prefer A3 for actual kernel semantics; this is a fallback
if the detailed-balance sum lemma in the candidate fails, and a useful
algebraic theorem in its own right. Do NOT try to show W or Q is symmetric
without the weights.

## A6. Exact uniform-fiber intertwining and general physical resets

For uniform microscopic allocations, A3 is enough to show that a uniform
input on one histogram fiber remains conditionally uniform in every target
fiber. Let U_x be `FiberDisintegration.fiberLaw observe surj x`.
For B in F_y:

```
(U_x K)(B) = (1/|F_x|) * sum_(A in F_x) K(A,B)
           = Q(y,x)/|F_x|          (micro symmetry + strong lumpability)
           = Q(x,y)/|F_y|          (weighted detailed balance).
```

This is exactly `(Q ; U)(x)(B)`. If implementing the full equality
`U ; K = Q ; U`, first prove the two mass formulae with `FiniteKernel.apply_mass`
and `fiberLaw_mass` for abstract X,Y. Use `map_mass_on_fiber` for the
reverse row sum, and the `reversible_quotient` result with uniform μ to
get the cardinality-weighted equality. The sizes of nonempty fibers are
positive by `fiber_card_pos`. Use `field_simp` only after rewriting to
rational scalar quantities. No concrete deck type in the proof body.
Alternative stronger version: arbitrary reversible μ with positive
fiber mass; define conditional weight μ(a)/π(x) inside the fiber, and the
same proof works with the microscopic detailed-balance equality rather
than symmetry. The uniform version is sufficient now.

This generic theorem can subsume several G4/Commander-specific
uniform-fiber arguments later; don't undertake that migration before G5
is complete. `FiberLifting.run_intertwining` and `run_tv_eq_macro` are the
existing iteration/TV transfer tools. Be precise: this equality starts
from **uniform fiber inputs**, not any deterministic allocation within a
histogram unless the transition is proved to reset the whole histogram
fiber. Strong lumpability alone is only a statement about the observation.

For actual ordered decks with p piles, reuse `multiPile_equivFiber` to
show the map from pile-local permutations to a fixed allocation fiber is
bijective. For a reference deck d, local position permutations g_i act by
`glueBlocks P P ... g` followed by d. To recover g_i from another deck e
in the same allocation, use the per-pile bijections of d and e:
`g_i = e_i.trans d_i.symm` (maps positions to positions; verify composition
pointwise). No further orbit counting needed. Uniform independent pile
permutations therefore give the local allocation lift. Show uniform product
law is uniform on the product once generically; for empty/singleton piles
use point masses. Couple finite local laws with ideal ones via the existing
product-TV inequality (extend by induction over a finite list of piles).
Then each round perturbation ≤ sum_i choose(n_i,2)/a_i; cap at 1.

For pairwise exchange of physical positions, the map from selected
positions in each pile to selected card identities is a bijection because
the current deck is a bijection. Transport uniform choices through this
bijection; arbitrary fixed pairing influences order only, never allocation.
This proves the literal-swap observation bridge, not a re-sampling model.
Use K1's existing `mapMapOfPointwise` and `fuseSwapLocal` generically.

## B1. Gate 6: close row independence using the existing reachability theorem

All necessary generic helpers from the midnight overlay compiled in
`Gate6K1Bridges.lean`. Do not repeat them. `Gate6AssemblySeeds.lean` adds
small missing glue code (uncompiled): `same_fiber_law`, `rowFactor_comp`,
`run_from_reset_eq_point`, `exchangeChoiceImage_injective`.

The crucial concrete statement is:

```
∀ d d', CommanderMembershipKernels.membership d =
        CommanderMembershipKernels.membership d' →
  CommanderPhysicalExchange.rawExchangeMembership d =
  CommanderPhysicalExchange.rawExchangeMembership d'
```

1. Define the named choice map `exchangeChoiceImage d`; the supplied seed
   proves injectivity by `newLeftCards_injective` and `Prod.ext`.
2. Let S=`membership d`; use the already proved `FiniteDeck.ReachSet 99 50
   25 hm hk hkm S` (types are definitionally the same subtype). To prove
   each `exchangeChoiceImage d c` lies in ReachSet, use
   `newMembership_overlap_25`, `newMembership` and the membership size
   proofs S.2,T.2. In particular, |S∩T|=25, |S|=|T|=50 implies
   |S\T|=|T\S|=25. Use `Finset.card_sdiff` and `Finset.inter_comm`
   explicitly; inspect the orientation of `card_sdiff` in `newLeftCards_card`.
   Keep this as a separate finset arithmetic lemma if needed. `omega`
   finishes the pure Nat facts. Do not construct a choice from a target.
3. The card of ReachSet is `FiniteDeck.subsetExchangeCount 99 50 25 ... S`.
   The card of choices is `exchangeChoice_card_eq_transitionDenominator`
   (a Rat equality); get a Nat equality by `exact_mod_cast` after rewriting
   `transitionDenominator` to `choose 50 25 * choose 49 25`. Or prove the
   Nat equality directly from `Fintype.card_prod` and powersetCard cards.
   Do not use `native_decide` on the choice type.
4. Apply `range_iff_mem_of_card_eq` (compiled). Hence image of each d is
   exactly ReachSet of `membership d`. For same membership the two image
   predicates agree by rewriting only the membership equality.
5. Apply `uniform_same_image` to the two injective choice maps. Fold
   `rawExchangeMembership` with `change`, or named wrapper identity, not
   `simp [GSR.uniformDist]`. Row independence now follows.

This route proves the stronger theorem for every membership and reuses
all previously proved counting. Alternative if the huge ReachSet type
causes instance normalization: choose explicit card subsets of the left
and right membership as A1's choice type; transport the position choices
using deck-restricted equivalences and `map_bijective_uniformDist`. The
pointwise `newLeftCards` agrees with subset update by `image_sdiff`; this
is a generic two-pile corollary of the multi-pile transport proof. Do not
restart the old inverse-witness K1b proof. Both routes require a small
abstract lemma compiled before applying to 99.

## B2. Ideal reference start and all-start theorem, without finite-start transport

Let P=deterministic membership, U=localLift, H=PAK rho99Ideal,
E=rawExchangeMembership, L=swap-then-ideal local. `K1_swapFirst_eq_exchangeLift`
proves L=E;U. `k1_idealKernel_eq_membershipLift` proves H=P;U. B1 and
`rowFactor_comp` give E=P;Q for the representative row factor Q.
`CommanderMembershipKernels.localLift_preserves_membership` gives U;P=id.
Use `reset_absorption` to obtain H;L=L. With the compiled
`equal_after_first_run` or the candidate `run_from_reset_eq_point`:

```
run L 3 (Dist.pointMass d0) = run L 3 (H d0)
```

for identity deck d0. `ideal_batch5b` already identifies the ideal noise
with `localLift (membership d0)`. By `permutationActionKernel_eq_map`
and `Equiv.trans_refl`, H(d0)=rho99Ideal. **Do not redo batch 5b.**

To equate H(d0) and `g6ThreeRoundStart`, prove ONE pointwise statement:

```
∀ d, project d = commanderSegregatedState ↔ membership d = membership d0.
```

Proof: `project_count` gives leftOriginalCount=50 iff project.val=49.
`membershipCount_of_deck` relates leftOriginalCount to
`(membership d).val ∩ leftOrigSet`. `leftOrigSet` has card 50
(`leftOrigSet_card`, locate declaration); every membership has card 50.
An intersection with both card 50 must equal both sets:
`Finset.eq_of_subset_of_card_le` applied to `inter_subset_left/right`.
The identity deck's left cards are `segLeft` by
`GSRSegMembership.leftCards_id_eq_segLeft`; identify with `leftOrigSet`
by membership `x.val<50` (use `leftOrigSet_eq_L50`, `origLeft_L50`, or
`leftCards`/`leftPosition` explicitly). Reverse direction gives count 50
immediately. Do NOT enumerate all decks or use `native_decide` on a goal
with arbitrary d. Then `same_fiber_law` equates the two `fiberLaw`s;
`localLift` is that membership `fiberLaw` (or `localLift_mass` states it).
`g6ThreeRoundStart` unfolds to apply pointMass then fiberLaw;
`FiniteKernel.apply_pointMass` closes. If actual `localLift` construction
is not definitional, use `localLift_mass`, `fiberLaw_mass` generically.

Now reuse `g6_threeRound_finiteRun3_tv_le_q3` (despite the confusing name,
its kernel `g6ThreeRoundFiniteKernel` is ideal) and the compList/run bridge,
plus `g6_3round_idealKernel_eq_fullRound`. Transport the inequality through
these named equalities with `Eq.subst` if rewrite elaboration is expensive.
Get `TV(run L 3 (pointMass d0), uniform) ≤ q3`.

**New simplification of the final assembly:** transport ONLY this IDEAL
reference bound to every deterministic d, via `action_comp_eq_conv` and
`action_run_tv_noise` on `fullRoundIdealCorrect`. Both TV expressions equal
`TV(powConv idealNoise 3, uniform)`; no need to transfer the old *finite*
restricted-start bound. In particular, correcting the finite permutation
orientation does not invalidate the ideal argument. For each d use the
finite-vs-ideal telescope with μ=pointMass d and the corrected per-round
δ1. Sum q3+3δ1 and use `gate6_headline_bound`. This is simpler than trying
to equate the finite runs from pointMass and fiber-uniform starts (that
equality is generally false). State the strongest theorem for every d;
then a separate convexity/mixture proof can extend it to arbitrary μ.

## B3. GSR semantics: invert the rank permutation before acting

`GSRPermutationLaw.lean:idealShuffle_canonical_eq_permLaw` already states
`idealShuffle ... canonical = gsrPermutationLaw.map (fun σ => canonical.map
σ.symm)`. In the repository, `act p d = p.trans d`, so `act p d i=d(p i)`.
Thus a rank law (old->new) cannot be used directly in this pullback action.
Define `gsrPullbackLaw n a := (gsrPermutationLaw n a ...).map (fun p=>p.symm)`.
`perm_inverse_tv` and `perm_inverse_uniform` have compiled in the new
`Gate6K1Bridges.lean`. Apply the existing `gsrPermutationLaw_tv_bound` to
get the identical one-pile δ bound; then product-TV and `roundEmbedMap`
pushforward as in `rhoRoundTransport_le_twoPile`. Construct the corrected
finite round under a new name (do not silently invalidate old proofs).
The ideal law is unchanged. Per-round perturbation follows from the
already-compiled `convTVCommonLeft` or the common swap kernel argument,
with the new finite local law in place of `rho99Finite`. Use `tvFinsupp`
through the convolution proof; convert to `Dist.tv` only via the generic
bridge and do not unfold either at 99.

## B4. Binary interpretation, and the acceptance theorem

The existing `GSR.idealShuffle_comp` proves composition at list level.
Use the injective encoding `enc p = (List.finRange n).map p` for pullback
permutations: equality of lists gives equality of each indexed entry;
`List.getElem_map` and `List.getElem_finRange` (check names on local pin)
reduce to pointwise equality. Alternatively use `List.ofFn p` and its
get-element lemma. Push two independent pullback noise laws through
`enc`; stable sorting a deck d by labels on card identities corresponds to
stable sorting its positions by `labels ∘ d`. This function is a bijection
on label arrays, preserving the uniform law. Hence `idealShuffle` on the
encoded current deck equals the encoded position-action law. Prove it
once for any d, by stableBuckets/map commutation and the canonical theorem.
Then the composition theorem yields equality of pushed laws. Recover
actual permutation laws by applying an inverse on the range of enc (use
`Function.invFun` and injectivity); map-map, map_id, no mass sum over n!.
Iterate binary a=2 using the law and `powConvRunEq`; for 23 steps the
alphabet is `2^23`. Include n=0 separately if desired (only identity law).
Make execution orientation explicit with `act_composition` and
`swap_then_local_matches_star`, not by guessing which side of `*` applies.

Acceptance: theorem in canonical module, no placeholders or extra
hypotheses, for all d : Deck 99, TV of the **swap-first** 3 rounds of
uniform 25-position pair selections followed by 23 independent binary
stable-sort inverse-GSR riffles per pile from `Dist.pointMass d` is less
than 1/1000. It is fine to state the theorem using the equivalent 2^23-label
kernel provided the separate binary-equivalence theorem is imported and
applies. If only the rank-law certificate or fiber-uniform theorem is
compiled, label it precisely and keep the stronger goal open.

## C. After G5 and Gate 6: useful G7/G8 shortcuts, not new prerequisites

**Changing capacities (G7):** uniformly allocate a subset of e cards from
pile i to pile j, with no return. If the original allocation is uniform,
then the resulting allocation with capacities `n_i-e`, `n_j+e` is uniform.
For any target B there are exactly choose(n_j+e,e) predecessor/choice pairs:
choose which e of its target pile j cards arrived. The source choice count
is choose(n_i,e), fixed. So every target has equal probability, and since
the row law is a pushforward, the resulting mass sums to one. More general
multi-pile dealing is a re-partition of uniformly random ordered positions;
pushforward preserves uniform allocations via equal fibers. These two
proofs cover standard deals, draws and returns; deterministic card-choice
or color-dependent discard may be biased, so do not claim uniformity for
arbitrary play. TV contracts under any common dealing kernel, even a biased
one, against the corresponding pushed-forward target law.

**G8 universal mixing:** a single pairwise exchange need not be irreducible
(e.g. swapping both entire piles). For a robust baseline allow lazy
one-card swaps along a connected graph of *positive-capacity* piles. Work
with a finite graph on positions whose edges join allowed piles. It is
connected when the active pile graph is connected and there are ≥2 active
piles (one active pile is trivial on allocations, use a local uniform
shuffle for full decks). Edge transpositions generate all permutations:
for a path v0,...,v_l, transpose endpoints by adjacent swaps along path and
back, length 2l-1. Any permutation is a product of ≤N-1 transpositions
(cycle decomposition). Thus one can reach any target allocation with at
most (N-1)(2N-3) swaps for N≥2. This is conservative and avoids a hard
optimal transport argument. Pad with laziness. If each allowed elementary
move has probability ≥q>0, and self-loop ≥q, then L^T(A,B) ≥ q^T for all
A,B with that T. Uniform stationary + minorization ε=|Alloc|q^T yields
TV after tT ≤(1-ε)^t. Prove abstract minorization first. No spectrum needed
for a rigorous convergence baseline. Sharper bounds remain a separate
research task. Fixed multi-card exchanges require separate irreducibility
analysis; do not apply the one-card theorem to arbitrary k blindly.

**Cost certificates:** for t rounds and pile riffle counts b_{ri}, the
collision budget is sum_{r,i} choose(n_i,2)/2^{b_{ri}}. Under equal unit
costs, each extra riffle saves half the current term. The marginal savings
within each pile are decreasing geometric sequences; choosing the largest
available saving each time minimizes this *upper bound* at a fixed total
number of riffles, by an exchange argument selecting the largest marginal
savings subject to prefix closure. For unequal costs or additional
constraints, greedy is not guaranteed optimal; use dynamic programming or
lower bounds. Distinguish certified-bound cost optimality from actual
optimality. Complete a useful finite protocol and these generic theorem
interfaces before open-ended sharper spectral research.

## D. Compile, integrate, and document

- Candidate files are guidance only until compiled. Build the small generic
  declarations before any concrete allocation or 99-card specialization.
- Add actual `allocationExchange`, `observe`, `histogramExchange`, its
  lumpability, stationary/detailed-balance, explicit formula and uniform-
  fiber intertwining to canonical modules and aggregator. Avoid creating a
  second unrelated macro kernel just for a formula.
- The tiny worked example should compute actual transition rows, including
  an unchanged histogram with multiple legal selection profiles. The
  four-card counterexample is a regression for the intended weighted
  balance and guards against an incorrect symmetric quotient. Use the
  existing six-card/three-pile example for actual kernel reduction.
- Update the active handoff/manifest with exact theorem names and scopes.
  The last dated note about scalar stochasticity is not a G5 capstone.
- Keep the old `Gate6ThreeRound` theorem as a valid restricted certificate;
  no need to remove it after the stronger theorem is proved.
- Run `lake build` for modified modules, then the targeted verification
  and aggregator. If a generic theorem is blocked, record the exact goal
  and try the alternative path or advance an independent task. The objective
  is the whole actionable G1--G8 roadmap, not only one certificate.

### Replacement loop objective (operator must submit it)

Complete the actionable arbitrary-finite-deck roadmap through G8. Use
`docs/planning/proof-strategies/2026-11-25-morning-g5-quotient-and-counting-handoff.md`
as the current implementation guide. First construct the actual allocation
and histogram kernels and prove strong lumpability, weighted detailed
balance, uniform-fiber intertwining and factorial stationary law using
cell gluing and the supplied quotient seeds. In parallel finish the Gate 6
all-deterministic-start certificate and correct GSR pullback/binary
semantics using B1--B4 and the already integrated bridges. Continue G7/G8
with generic finite mixing and meaningful cost certificates. Compile and
integrate the small candidates; never treat a scalar normalization or
restricted-start result as the full headline. Use bounded proof attempts,
no recursion-limit escalation, and prefer reuse to specialized proof
sprawl. Historical reviews and optional G9 research are not separate goals.
