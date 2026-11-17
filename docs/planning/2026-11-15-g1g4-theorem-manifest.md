# G1–G4 source-to-target theorem manifest (arbitrary-finite-deck campaign)

**Date:** 2026-11-15
**Status:** active planning status (new). This does **not** edit the two dated
November 15 reviews, `docs/lean_plan.md`, or `docs/agent_handoff.md`.
**Basis:** `docs/planning/roadmaps/2026-11-15-arbitrary-finite-deck-generalization.md`
(campaign) and `docs/planning/reviews/2026-11-15-qwen-proof-quality-duplication-and-build-performance.md`
(duplication/build).

Per the roadmap's first instruction, this is a **source-to-target manifest** for
the immediate G1–G4 pivot: each existing Commander declaration, the generalized
theorem it should become, and the current open/compiled state. It is a *tracking*
document — a row marked "compiled" means the named Lean theorem builds; a row
marked "target" means the equation is a stated goal, not yet a theorem.

## Campaign framing

The foundational object is a **finite labeled card universe** (`Fin N`) and a
partition of positions into working piles. Commander (`N=99`, left `50` / right
`49`, `25`+`25` exchange) is a **specialization and regression benchmark**, not
the definition. No generic theorem may import a `Commander*` module; the proved
99-card declarations are kept as specializations.

## G1 — minimal finite deck (`FiniteDeck/TwoPile.lean`)

| Current Commander declaration | Generalized target | State |
| --- | --- | --- |
| `Deck := Equiv.Perm (Fin 99)` (`CommanderPermutation`) | `Deck N := Equiv.Perm (Fin N)` | **target** — new `FiniteDeck.TwoPile` |
| `leftCards d : Finset (Fin 99)`, `(leftCards d).card = 50` (`CommanderPermutation:49,62`) | `Membership N m := {S : Finset (Fin N) // S.card = m}`; `leftCards d` → image of the first `m` positions | **target** |
| `project d : CommanderState` (`CommanderFiberCount:114`), `project_count` (`:121`) | `count_M : Membership N m → BLState N m r` for a marked set `M` of size `r` | **target** |
| `Fin 99 ≃ Fin 50 ⊕ Fin 49` position split (implicit in `leftCards`) | `Fin N ≃ Fin m ⊕ Fin (N-m)` for `m ≤ N` | **target** |
| — | Acceptance: `N=0, m=0, m=N` compile; no `Commander*` import | **open** |

## G2 — counting & disintegration (`FiniteDeck/TwoPileFiber.lean`, `TwoColor.lean`)

| Current Commander declaration | Generalized target | State |
| --- | --- | --- |
| `CommanderFiberCount` fiber counts (`# {d // leftOriginalCount d = k}`) | T1: `# {d // allocation d = A} = m! (N-m)!`; `# {A} = choose N m` | **`choose N m` compiled** (`membershipCount`) + the four fintype-card blocks + **both restriction bijections** `fiberRestrictL : L ≃ A`, `fiberRestrictR : R ≃ B` (`FiniteDeck/Fiber`). **Next:** the count `m!(N-m)!` = glueing equiv `Fiber ≃ (L ≃ A) × (R ≃ B)` + `Fintype.card_prod` + `Fintype.card_equiv` + position-card lemmas (construction + the by_cases-opacity gotcha documented in `Fiber.lean`) |
| `membershipFiberCount k = choose 50 k * choose 49 (50-k)` (`CommanderMembershipKernels`) | T2: BL histogram fiber = `choose r (marked) * choose (N-r) (unmarked)` | **partially general** — the `choose` product is already `N,m,r`-parametric in `BernoulliLaplaceGeneral`; needs the generic `Membership N m` statement |
| `fiberLaw` / uniform-deck disintegration (`FiberDisintegration`) | uniform deck ⇒ uniform over allocation fibers | **compiled (generic)** — reuse as-is |
| `blStationary N m r`, detailed balance (`BernoulliLaplaceGeneral`) | T2 multivariate hypergeometric `π` | **compiled (two-color)** — reuse; generalize to categories in G5 |

## G3 — universal exchange (`FiniteDeck/SubsetExchange.lean`, `PhysicalSwap.lean`)

| Current Commander declaration | Generalized target | State |
| --- | --- | --- |
| `rawExchangeMembership : Deck → Membership` (25+25 position subsets, `CommanderPhysicalExchange`) | T3: `subsetExchange N m k : Membership → Membership` kernel, `K(S,T) = (choose m k · choose (N-m) k)⁻¹` iff `|S\T| = |T\S| = k` | **DONE** — `subsetExchangeCount` (count) + `subsetExchangeKernel` (weight) + `subsetExchangeKernel_symmetric`/`_rowOne`/`_colOne`/`_stationary` (all in `SubsetExchange`) |
| `newMembership` / `newLeftCards` (`CommanderPhysicalExchange`) | `literalSwap` membership pushforward, pairing-independent | **DONE** — `PhysicalSwap.lean` `newLeftCards` + `_parts_disjoint`/`_card`/`literalSwapMembership`/`_conjugate` (A2-core, generic) |
| `commanderExchange25 : FiniteKernel (Fin 50) (Fin 50)` (`BernoulliLaplace`) | T3-to-BL: `count ∘ subsetExchange = blExchange N m r k` | **target** |

## G4 — macro intertwining / physical-perfect (`FiniteDeck/BLRefinement.lean`) — **the scientific target**

| Current Commander declaration | Generalized target | State |
| --- | --- | --- |
| **A3**: `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25 membershipLift` (`CommanderMembershipExchange`) | T4: `uniform count-fiber membership ⊳ subsetExchange = blExchange ⊳ uniform count-fiber membership`, generic `N,m,r,k` | **DONE through the T4 counting core and most of the count-level transition formula.** Transitivity (`permFinsetTransitive`, `countFiber_transitive`), the count projection (`countInPile`, transparent), and the per-(a,b)/per-a move-count lemmas (`countAB`, `pieceCount`, `markedPileCards`, `filterProduct`, `filterCardProduct`, `reachMoves`, `yMoves`, `yMoves_biUnion`, `Pa`, `Pa_disjoint`, `yMoves_fiberCard`) are all in `BLRefinement`. **Remaining:** `card_biUnion_pd` (disjoint-union card = sum; induction on the Finset — see the 44th-session resume note in `agent_handoff.md` for the exact API blockers) then `yMoves_card_eq_sum` (`#yMoves = Σ_a #Pa(a)`), then summing `pieceCount` over `a` to match `transitionNumerator` (via `markedPileCards`), then the uniform-fiber intertwining, and finally **discharge Commander A3 by instantiation** at (99,50,50,25) |
| `membershipFiber_transitive` (`CommanderMembershipOrbits`, 903-line 4-part orbit) | marked-set-equivariance + transitivity on each count-fiber (generic `Equiv`-action orbit) | **equivariance DONE** (`subsetExchangeKernel_equivariant`, generic). Transitivity on the marked-count fibers: **next** (generalize the 99-orbit to the (m-pile, x-marked) level) |
| `newLeftCards_conjugate` (`CommanderPhysicalExchange`) | subset-exchange equivariance under `M`-preserving card permutations | **compiled (generic)** — `PhysicalSwap.lean` `newLeftCards_conjugate` (A2-core) + `subsetExchangeKernel_equivariant` |
| `two_physical_perfect_exchanges_uniform_of_counts` (hyp. `hMembershipExchange`, `CommanderFullDeckDisintegration`) | generic physical-perfect two-pile mixing identity | **conditional on A3** |

**Boundary caveat (T4):** the existing `generalCL_ns` assumes `k ≤ y`, so it is
not by itself an all-`(x,y)` kernel identity; the generic T4 count law must be
proved by the direct subset-kernel argument (or the low-target cases handled
separately) before claiming the full Commander kernel. `generalCL` (with `m+r≤N`)
is a *restricted* regime, not the universal statement.

## Execution order (small commits, per both docs)

1. **G1** (`FiniteDeck/TwoPile.lean`): `Deck N`, `Membership N m`, projection,
   position split/merge equivalence; `N=0/m=0/m=N` compile; no `Commander*`
   import.
2. **T1 fiber count** (G2 first lemma): `m!(N-m)!` per allocation by a finite
   equivalence (not `N!` enumeration); one small numerical specialization. **Done so far:**
   the histogram count `choose N m` and the four fintype-card blocks; the per-fiber
   count is the next concrete lemma (build `Fiber ≃ (L ≃ A) × (R ≃ B)`).
3. **G3** — `subsetExchangeCount` (the reachable count) **compiled** (`FiniteDeck/SubsetExchange`); next: the weighted `subsetExchange` kernel (symmetry/stationarity) + `literalSwap`.
4. **G4** (`BLRefinement`): generic count projection + equivariance + BL law;
   **discharge Commander A3 as an instance.**

Do **not** start the P2/P3 refactors of the quality review (module splits, orbit
rewrite) until G4 has a green build; the deduplication (Q1 fiber-count wrapper,
Q2 CL unification) is folded into the gate where the generalized theorem replaces
the specialized proof, not as a separate large refactor.
