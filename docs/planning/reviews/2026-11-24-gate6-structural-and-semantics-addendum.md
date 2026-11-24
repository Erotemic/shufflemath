# Gate 6: structural and semantics addendum (2026-11-24)

Basis: snapshot `7d024410e6d5`, 2026-11-24 09:00, and the newly delivered
`2026-11-24-k1-direct-order-and-kernel-hints.md`. This is a new historical
review, not a replacement for either. The user reports pushing that last
hint overlay after the snapshot; subsequent Lean changes are not available
for inspection. Nothing here assumes that the new hints have already been
implemented. Companion execution guide:
`../proof-strategies/2026-11-24-gate6-executable-mathematical-bridges.md`.

## Executive conclusion

The remaining finite-protocol proof is predominantly a problem of mathematical
representation and integration. Do not attempt a larger concrete calculation.
There are two additional structural shortcuts and a genuine convention issue.
They are worth addressing before the all-start certificate is declared complete.

1. **The swap pushforward can be identified by injectivity and cardinality.**
   `CommanderPhysicalExchange.newLeftCards_injective` and
   `newMembership_overlap_25` show that legal position choices embed into the
   reachable-membership set. `FiniteDeck.subsetExchangeCount` counts the latter;
   `CommanderA3ExchangeCard.exchangeChoice_card_eq_transitionDenominator` counts
   the former. Both counts are the same binomial product. Surjectivity follows
   without constructing any inverse exchange choices. Combine this with
   `GSR.map_injective_uniform_mass`. This supplies a pointwise membership-only
   law and removes the need for a separate first-round smoothing calculation.
2. **The exact ideal round factors as `M ; Q ; L`.** Here `M` reads membership,
   `Q` is the subset-exchange kernel, `L` is uniform lift, and `L ; M = id`.
   Thus for any positive number of rounds `P^t = M ; Q^t ; L`.
   In particular, a deterministic deck and its local-uniform lift have the
   same output after the first round. In the segregated count state there is
   exactly one membership. The existing three-round exact TV theorem therefore
   transfers to the deterministic identity deck without additional enumeration.
3. **Check the rank/pullback convention independently of the round order.**
   `PermutationLaw.gsrPermutationLaw` is the law of `rankEquiv` (old index to
   new index). `idealShuffle_canonical_eq_permLaw` emits the list of `σ.symm`
   applied to the canonical positions. `FiniteDeck.act p d` reads `d (p i)`;
   hence it needs the inverse of the rank permutation for a stable-label
   inverse riffle. `GSRDeckRound.rhoRoundFinite` embeds rank directly, not its
   inverse. This is a second orientation issue, distinct from choosing
   `conv swapLaw localLaw` instead of `conv localLaw swapLaw`.

The remedy to (3) is small: define the pullback law as the existing rank law
mapped by inversion, prove the uniform law invariant under inversion, and
transfer the existing collision bound. Do not rebuild rank counting or the
random tie-break construction. If retaining the original rank law as a
forward-GSR convention, name it honestly and distinguish its theorem from a
stable-sort inverse-GSR theorem. Their TV distances to uniform agree but their
laws need not agree.

A four-card exact example (positions numbered 0..3, two labels): the order
`(1,3,0,2)` has one preimage among the 16 stable-sort label assignments and no
preimage in the rank law; `(2,0,3,1)` has the reverse counts. Thus this is not a
notational difference. For labels `(1,0,1,0)`, the stable sorted order is
`(1,3,0,2)` and the rank map is its inverse `(2,0,3,1)`.

## What to retain from the previous proofs

The following already exist in source, with no `sorry` in their own bodies:

| Declaration / file | Reuse |
|---|---|
| `FiniteDeck.act_composition`, `convMapEqApplyMap`, `powConvRunEq` | Physical order and repeated action |
| `Gate6Crux.convAsApply`, `convContraction` | Common right convolution |
| `kernel_apply_lipschitz`, `distProductFinsupp_tv_subadditive`, `tv_eq_tvFinsupp` | Support-based error propagation |
| `convPush_eq_pointMassComp`, `k1a_riffle_half`, `k1_rhs_bookkeeping` (`_ProbeGate6K1`) | Nearly all of K1 for the *correct* order |
| `K1a_stmt_only` (`_ProbeK1b`) | Literal swap membership equality for every legal choice and every deck |
| `GSR.map_injective_uniform_mass` | Uniform pushforward through an injection |
| `FiniteDeck.subsetExchangeCount` | Exact number of reachable memberships |
| `CommanderMembershipKernels.membershipLift_localLift_eq_fiberLaw`, `localLift_preserves_membership` | Recovery and two-layer factorization |
| `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional` | Exact ideal three-round TV from segregated fiber-uniform input |
| `tv_bijective_invariance`, `uniformDeck_relabel_invariant` | Transfer from identity to arbitrary deterministic deck |
| `GSR.idealShuffle_comp`, `GSR.productLabelShuffle_uniform_eq_ideal` | Actual composition theorem on lists |
| `gate6_headline_bound`, `δ1_eq_2401_over_8388608` | Pure rational arithmetic |

Copy/relocate complete declarations from probes into appropriate production
modules. In particular do not import a `sorry`-bearing K1 assembly to prove
an unconditional final theorem. The source has multiple probes declaring the
same `h50le99` name; importing all probes is not a viable production strategy.
Check the actual proof dependencies with `#print axioms` on the final theorem,
and check that the final module is included in the normal verification path.

## Why the remaining proof should be smaller than the current attempt

The unfinished `k1b_count_split` is an inverse-counting approach to the old
local-then-swap order. It is not needed for swap-then-local K1. It is also not
needed for the subsequent membership-only law: the latter follows from an
inclusion between two finite sets of the same size. Even the old commutation
statement can be recovered later from the symmetry of the uniform law on the
appropriate permutation double coset. Do not continue the old proof merely
because many helper lemmas are already committed.

Likewise, no new Fubini development is needed to switch the convolution
order. Prove once that deterministic kernel application equals `map` without
`Fintype`, using `apply_id_left` and `StdSimplex.map_map`. Then TV contraction
of arbitrary maps is immediate from the existing support-based kernel
contraction. Combining it with product-TV subadditivity gives a **two-variable
convolution-TV bound**, which proves both one-round contractions and the
entire power telescope. This is simpler than deriving separate left and right
convolution-as-kernel lemmas and a large row-TV perturbation argument.

## Definition of done for this milestone

- Round is literal swap followed by local pullback permutations acting on the
  current deck. No constant-output rows and no perfect reset hidden in the
  finite law. Validate the pointwise action convention before distributional
  rewrites.
- Ideal law is identified with the existing ideal exchange law by K1, and the
  swap law factors through exact membership. Prove deterministic-start transfer
  rather than applying a bound on an averaged fiber to a point mass.
- Unconditional theorem at TV < 1/1000 for every ordered deck, supported by
  actual compiled declarations. Prove the 23-binary-step interpretation (or
  first state the precise single `2^23`-label stable-sort result and then close
  that remaining bridge explicitly).
- No expensive concrete `simp`/`rfl`/instance reduction over full-deck
  distributions. The theorem should be assembled using abstract small lemmas
  whose bodies are checked at generic types. Use bounded isolated builds,
  verify the current source, and record the first failing declaration rather
  than allowing a multi-GB WHNF process to run indefinitely.

The goal after this remains the actionable arbitrary-finite-deck roadmap, not
an indefinitely expanding Commander proof. This document and the companion
hints are references, not additional independent completion requirements.

## Independent checks and limits of this review

- All 37 Python tests passed against the supplied snapshot.
- Exhaustively checked the membership image, its cardinality, and the exact
  uniform distribution after swap-then-perfect-local on every starting deck
  for `(N,m,k)=(4,2,1),(5,3,1),(5,3,2),(6,3,2)`.
- Enumerated binary/ternary labels on four cards, confirming the rank/pullback
  discrepancy and equality of their TV distances. Checked the descent-based
  counting formula on every permutation of those small decks.
- Exact rational computation gives `q3 + 3*2401/8388608 = 0.000884424181... < 1/1000`.
- No Lean/Lake toolchain is available in this review environment. Existing
  compiled status is from the repository's source and build history; the new
  suggested Lean fragments are not tested against the toolchain. The overlay
  contains only guidance. No production Lean source or active loop state is
  modified. The companion guide makes the intended proof obligations explicit.
