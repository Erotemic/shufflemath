# Mathematical bottleneck review for Qwen — 2026-11-20

**Source:** `shufflemath-source-2026-11-20T113201-5-58de44b84aee.tar.gz`, Git HEAD `58de44b` (source declarations checked, not merely roadmap status labels).

**Purpose:** a focused, *forward-looking* mathematical review. Retain the November 15 and 18 reviews as history. Read with [the accompanying deep proof guide](../proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md); the guide supplies derivations, small proof targets, and escape routes for elaboration problems. This review is not permission to abandon the finite-GSR and multi-pile goals in favor of refactoring.

**Verification boundary:** The auditor did not run Lean/Lake (toolchain absent). Declaration names and statements were inspected in source; their successful compilation is based on the repo's recorded build history. Python/arithmetic cross-checks do not certify Lean proofs. Proposed declarations in the guide are *mathematical interfaces*, not copy/paste-compiled Lean.

## 1. Retire completed assignments

The following are **already present in source**. Do not have Qwen re-prove them:

| Area | Existing declaration and source | Implication |
|---|---|---|
| Arbitrary-`N` count process | `FiniteDeck.BLRefinement.g4MacroIntertwining` | Macro–membership composition is no longer the active obstacle. |
| Generic membership exchange | `FiniteDeck.A3KernelLaw.hMembershipExchange_kernel` | Do not reconstruct the A3 event-mass proof. |
| Generic perfect-local full-deck TV | `FiniteDeck.BLDisintegration.two_physical_perfect_exchanges_uniform_deck` (parameter `n : Nat`, despite its name) | Exact ideal reference is available for all round counts under its stated lifted initial law. |
| Commander physical-perfect headlines | `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_unconditional`; `three_physical_perfect_exchanges_uniform_unconditional` | Exact 2/3-step reference certificates are available. |
| Product of list-valued GSR laws | `CommanderLocalGSR.gsrProductKernel_eq_distProductFinsupp` | This identity is **already proved**; the missing step is not the product distribution itself. |
| Pile-relabel group | `CommanderDeckGSR.pileRelabelEquiv_pairInjective`, `preservesPiles_iff_pileRelabel` | Use as evidence and a specialization test, not as the generic definition. |
| Composition of GSR label shuffles | `GSR.idealShuffle_comp`, `productLabelShuffle_uniform_eq_ideal` | `t` binary inverse riffles may be represented by a `2^t`-label shuffle after the permutation bridge. |

## 2. What is actually missing (source-grounded)

### B1 — literal physical action, not another reset kernel (critical semantic prerequisite)

`FiniteDeck.A3KernelLaw.rawExchange` is defined as `det membership ⊳ subsetExchangeMembershipKernel ⊳ localLift`. It is an idealized **exchange plus perfect order reset**. `FiniteDeck.PhysicalSwap.literalSwapMembership` computes the **card set** after selected positions move but does not construct a `Deck N → Dist (Deck N)` literal paired-position swap. A finite shuffle appended to `rawExchange` is not a model of finite physical shuffling: the perfect reset has already occurred.

**Required:** a deck-valued position permutation for selected left/right positions, a pointwise membership theorem independent of the pairing, and the kernel pushforward `literalPositionExchange ⊳ det membership = det membership ⊳ subsetExchangeMembershipKernel`. The existing perfect-local model should follow by appending `localLift`, not be redefined.

**Why this is harder than it looks:** orientation of `Equiv.trans` and right versus left group action. Prove the pointwise identity on `Fin N` before attempting any distribution calculation.

### B2 — a permutation-valued GSR law, not an arbitrary-list probability calculation

`GSR.idealShuffle` returns a `Dist (List (Fin n))`; `CommanderLocalGSR.gsrProductKernel` still lives on pairs of lists. The desired physical deck action requires a `Dist (Equiv.Perm (Fin n))` (or directly a law of reordering functions on positions). `CommanderDeckGSR` handles *fixed* pile permutations but does not furnish the random permutation produced by labels.

**Required:** encode stable label sorting of a full distinct pile into a permutation, and show that encoding agrees with `GSR.stableBuckets` on the canonical list. Consider the **rank-of-lexicographic-key** construction before committing to a large list proof. It uses only `Fin n`-indexed keys, and avoids a fictitious `Fintype` instance for all lists.

### B3 — a nonvacuous full-deck error estimate

The source has useful Finsupp-based lemmas (`TotalVariation.tvFinsupp`, `distProductFinsupp_tv_subadditive`, `kernel_apply_lipschitz`); the current `TelescopeF5` `TV ≤ 2` and `TV ≤ 3` bounds are valid but vacuous because every TV distance is at most 1. `ProtocolCertificate.errorBudget` and Dobrushin calculations on `Deck (99)` risk unfolding a finite universe of `99!` elements.

**Required:** construct a same-randomness coupling of finite and perfect local shuffles. Conditional on all labels distinct, the relative rank permutation is uniform; the failure probability is at most `choose(n,2)/a`. For a round with 50/49 piles, this gives `2401/a`; for three rounds, `7203/a`. A **contraction inequality** after a map is sufficient for the upper bound. An injective-action **TV equality** is useful mathematics but must not block the certificate.

### B4 — real deterministic initial decks versus fiber-uniform hypotheses

The generic full-deck perfect-local theorem starts from a macrostate lifted to a uniform count fiber, **not automatically** from an arbitrary fixed permutation. If the initial *membership* count fiber is a singleton, however, the ideal kernel's first row depends only on that membership, so an arbitrary fixed ordering of that membership produces the same ideal law after one step as the lifted start. This applies to the fully segregated Commander membership. Prove this small lemma explicitly before claiming a physical protocol from a fixed ordered deck.

For an interior marked count whose membership fiber contains multiple allocations, that shortcut is not valid. Do not silently replace a fixed deck by the uniform count fiber.

### B5 — wrong macro target in a legacy F5 example

`CommanderCostedCertificate.macroCountExchange_costedCertificate` compares to `GSR.uniformDist CommanderState`. The equilibrium of Bernoulli–Laplace counts is **hypergeometric**, not uniform across count labels. This example may be formally valid as a generic comparison but it is not a certificate of mixing to the correct macro equilibrium. The finite-GSR cost certificate must target uniform **decks** and use `blStationaryDist` for the count reference.

### B6 — the multi-pile mathematics is about *double cosets*

For any fixed finite pile partition and coloring of distinct cards, the full deck is a bijection from positions to cards. Pile-preserving permutations act on the **right** and category-preserving card relabelings act on the **left**. Membership/allocation fibers are right-subgroup orbits, and category-count tables classify **double orbits**. This provides the missing big picture for general finite piles and should prevent another 900-line bespoke orbit construction.

Prove it through explicit finite-partition bijections and transitivity first; call it a double-coset theorem only as a corollary if quotient types are expensive in Lean.

### B7 — reversible quotients supersede repeated detailed-balance calculations

A finite reversible kernel that is strongly lumpable along `f : X → Y` has (i) induced stationary weights, (ii) quotient detailed balance, and (iii) intertwining of **stationary-conditional fiber laws**. This extends the symmetric-uniform special case and is useful for multi-pile count matrices. The guide includes the exact double-sum derivation and hypotheses; do not assume all arbitrary schedules themselves are symmetric.

## 3. A concrete first finite-GSR target

Let `d0` be any **ordered** 99-card deck whose left pile contains exactly the 50 marked cards (the unique membership in that count fiber). Define one physical round as:

1. choose 25 left and 25 right *positions* uniformly, exchange them under any fixed pairing rule;
2. perform 23 independent **binary inverse GSR riffles in each pile**.

Repeat for three rounds, independently. The desired theorem is

`TV(law_after_3_rounds(d0), uniformDeck) ≤ 1/1000`.

**Arithmetic already checked:** the exact three-round perfect-local macro certificate in `CommanderFullDeckDisintegration` equals

`172379525755689183991816396516567920780192827919620440221147749 /
6691837923759692633601708022649918108038775216019298375918637677488`

and its sum with `7203 / 2^23` is `< 1/1000` (approximately `0.0008844241810`). For `t=22`, the same *sufficient upper bound* exceeds `1/1000`—this does **not** prove that 22 riffles are insufficient in reality.

This is a **proposed** theorem subject to B1–B4; do not label it proved until the entire Lean chain compiles. Cost is a separate, explicitly chosen metric: 3 cross-pile exchanges plus 138 individual binary pile riffles if each pile's riffle costs 1 and the two piles are counted separately. This illustrative cost convention is not a physical timing claim.

## 4. Work ordering for a 27B theorem prover

| Order | Make this theorem compile before the next | Avoid |
|---|---|---|
| 1 | `literalSwap_membership` for one deterministic pairing | Instantiating `Fintype (Deck N)` or expanding a probability kernel. |
| 2 | `literalSwapKernel_membership`; then `literalSwapThenPerfect_eq_rawExchange` | Re-proving BL transition numerators. |
| 3 | Generic `localGroup` action and `fiber≃productPermutations` (or just the row law needed in step 5) | Copying 50/49 case splits. |
| 4 | `labelsToPerm` / `stableBuckets_labelsToPerm` for arbitrary `n` | Equating arbitrary lists with permutations. |
| 5 | `finiteLocal_vs_perfectLocal ≤ choose(n,2)/a` by coupling/contraction | Making TV *equality* a prerequisite. |
| 6 | Three-round F5 ≤ `exactMacro3 + 7203/2^23` from fixed segregated deck | `TV ≤ 3`, full-deck `max'`/Dobrushin, implicit perfect reset. |
| 7 | Multi-pile allocation + histogram counting + double-orbit lemma | Building a Commander-like count-state index for every game. |
| 8 | Generic reversible quotient, multivariate exchange formula; then cost-search lower bounds | Claiming surrogate optimality implies actual optimality. |

**Parallelizable mathematics:** the generic group/fiber construction, rank permutation, and finite-label collision bound can be developed separately, then joined by the local-action kernel. A weak model should not modify the active F3/G4 modules to accomplish this.

## 5. Specific traps and failure signals

- `d : Fin N ≃ Fin N` is a **position-to-card** bijection. In Lean `e.trans f` applies `e` then `f`; check every equality direction with a two-card probe.
- `GSR.stableBuckets` sorts by `(label, original position)` with stable ties. The *later* riffle label is the more significant key in `GSR.stableBuckets_comp`. Reversing that changes the protocol.
- For `a < n`, the no-collision event is empty. Never condition by dividing by its probability. Use the trivial `TV ≤ 1` branch or a coupling valid when the event has mass zero.
- If the finite local kernel was defined using `rawExchange`, it has *already* secretly randomized perfectly. Reject any resulting too-easy exact-mixing proof.
- If a lemma creates `Finset.univ : Finset (Equiv.Perm (Fin 99))` inside a simplifier or `native_decide`, stop and use `Finsupp` support/pushforward/coupling instead.
- Do not use uniform on the macro count states as the stationary target unless an independent theorem proves it for the chosen parameters.
- An F5 theorem bounded above by 2 or 3 cannot demonstrate mixing quality. Demand an explicit `ε < 1` and a stated initial distribution.
- A finite-GSR target requires a **permutation-valued** law or a demonstrably equivalent deck-valued sorting action. A list-membership preservation lemma does not establish multiplicity or bijectivity.

## 6. Scope boundary / evidence discipline

The mathematical guide is deliberately more ambitious than a Lean-ready patch. Interfaces and proof sketches are suggestions; theorem names and exact Mathlib APIs must be checked locally. None of these new claims is certified by this review. Keep this dated review immutable after commit; update the active planning docs as new proofs land. Do not conflate the handoff's historical/future-dated session entries with independently verified compiler output for this upload.
