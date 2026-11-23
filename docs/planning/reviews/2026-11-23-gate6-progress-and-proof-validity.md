# Gate 6 progress and proof-validity review - 2026-11-23

Snapshot: `shufflemath-source-2026-11-23T101834`, HEAD `1587085`.
Purpose: identify what has actually changed since the 2026-11-22 review, the logical gaps that still prevent the requested physical-shuffle theorem, and a small number of high-leverage mathematical interventions. This is a dated assessment, not a replacement handoff or a claim that the proposed proofs compile.

## Bottom line

The new substantive Lean work is `Shufflemath/FiniteDeck/RelabelInvariance.lean` (commit `e816181`): it proves generic TV invariance under bijective pushforward and invariance of uniform deck measure under card relabeling. The verification script includes this module. No end-to-end finite-riffle 99-card certificate is present. The source's own `GSRGate6Telescope.lean` explicitly states its `hq3` hypothesis is false for the current constant-row kernels. The original headline remains a target, not a proved theorem.

The next step should *not* be to develop another specialized `Fin 99` mass expansion. Use a generic random-position-permutation law and convolution, and separately show that the ideal action kernel agrees with the established membership-exchange-plus-local-reset model.

## New evidence, completed work, and outstanding work

| Item | Evidence | Assessment |
|---|---|---|
| TV under a bijection | `RelabelInvariance.map_bijection_inverse`, `tv_bijective_invariance` | Proved, generic |
| Deck relabeling preserves uniform | `RelabelInvariance.relabel_equiv`, `uniformDeck_relabel_invariant` | Proved, generic |
| Within-pile permutation-to-deck-fiber bijection | `FiniteDeck/WithinPileOrbit.fiberOrbit_equiv` | Previously proved; crucial reuse |
| Literal position swap/membership correspondence | `FiniteDeck/LiteralSwapKernel.swapPerm_membership_eq` | Previously proved |
| Finite versus ideal *within-pile* TV | `GSRDeckRound.oneRoundDeckTV_le_delta1` | Proved, 2401/8388608 |
| Pure numerical target | `FiniteDeck/Gate6FiniteGSR.gate6_headline_bound` | Proved, `q3 + 3*delta1 < 1/1000` |
| 41-step ideal count-based decay | `FiniteDeck/DobrushinDecay99.physicalExchange_decay_41_lt_thousand` | Proved for a fiber-uniform initial law, **not** for a deterministic deck |
| Three-round ideal exact TV | `CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional` | Proved from the fiber-uniform segregated macro start |
| State-dependent literal-swap plus finite-GSR full round | `_ProbeGate6Fin2` has swap and local permutation laws, but its `finiteRound`/`idealRound` ignore the input deck; `GSRGate6Telescope` has similarly constant-row kernels | Open; current kernels are not repeated physical shuffles |
| Full-row finite-vs-ideal TV <= delta1 | Generic support-TV ingredients in `TotalVariation`, but no assembled physical round | Open |
| End-to-end 3-round theorem from every ordered deck | None in current production modules | Open |
| Multiple piles, changing pile capacities, sharp cost optimality | Still beyond the two-pile Gate 6 branch | Open research |

The reported local verification (in the repository's dated notes) is green; independent verification in this review environment: 37 Python unit tests pass. Lean 4.34/Lake is not available here, so newly proposed Lean statements below are not compiler-certified.

## Critical correction: relabeling is not enough to change the *kind* of initial law

The active `docs/planning/2026-12-16-f42-relabel-batch1-done-batch2-next.md` describes this plan: prove kernel equivariance, use generic TV invariance, and then transfer `physicalExchange_decay_41_lt_thousand` from a macro-fiber-uniform start to **every deterministic deck**. The last inference is missing a premise.

An equivariant kernel makes TV-to-uniform equal for any two *point starts* related by relabeling:

    TV(K^t(delta_d), U) = TV(K^t(delta_{g*d}), U).

It does not imply that this common point-start TV is bounded by the TV of the *average* over a count fiber. Convexity gives the inequality in the other direction:

    TV(K^t(U_F), U) <= average_{d in F} TV(K^t(delta_d), U).

Even if every term on the right equals the same constant by symmetry, this does not upper-bound the constant from the fiber-average TV. Thus this is a mathematical missing step, not an `isDefEq` problem.

An exact four-card check makes the distinction concrete. Take N=4, m=2, k=1, two marked cards, and the literal exchange followed by uniform local reordering. A deterministic start with marked-count x=1 has first-round TV 1/3; starting uniformly over the x=1 count fiber gives first-round TV 1/6. Both start laws are legitimate; relabeling preserves point-start TV but does not make point-start and fiber-uniform laws equal. This was checked by exhaustive exact-fraction enumeration; it is not a Lean theorem.

### Why the original segregated start is special (and fixable)

For the reference ordered deck `d0` with all m marked identities in the left pile (r=m), the maximum count fiber contains many orderings but only *one left-pile membership*. A position-selected k-swap followed by uniform local reordering erases the original within-pile order. In fact its first-step law is uniform over **the entire new count fiber** with marked count `m-k`:

    K_ideal(delta_d0) = U_{F_{m-k}} = K_ideal(U_{F_m}).

For the 99-card example: m=r=50, k=25, so the first law is `U_{F_25}`. Establishing this equality, or the more general fact that the ideal row depends only on source *membership*, repairs the gap. After that, the established three-round fiber-uniform theorem applies to the *same* ideal process from `d0`. Relabeling then transports the result to every deterministic ordered deck.

Do not generalize this first-step identity to an arbitrary count fiber: in general many different source memberships have the same marked count, and one-round laws differ among them.

## Why the diagnosed 99-card elaboration wall need not end the campaign

Current notes repeatedly call the `99!` / `99!^2` definitional-equality failure a definitive Lean-kernel limitation. The individual failed attempts are real evidence about a particular representation and import context, not a proof that all formulations require a Lean change. The repository already provides:

- `TotalVariation.tvFinsupp`, `tv_eq_tvFinsupp`, `distProductFinsupp_tv_subadditive`, `kernel_apply_lipschitz`;
- `Finite.distProductFinsupp`, built using distribution `map`/`join` rather than global `Finset.univ`;
- `FiniteDeck.WithinPileOrbit.fiberOrbit_equiv` for each uniform local action;
- `GSR.map_bijective_uniformDist` to transport uniform probability along equivalences.

The new proposed proof works at an abstract permutation group, proves support-TV inequalities before specializing N=99, and uses the existing exact macro theorem only after a first-step bridge. The companion hints document gives the exact dependency order and the two distinct routes (convolution and state-dependent-kernel telescope).

## Suggested order of work

1. Define an **acting** random permutation kernel (do not return the noise law as the output deck). Test the orientation of `Equiv.trans`.
2. Prove a generic support-TV common-swap inequality, then a convolution telescope directly on permutation laws. This avoids `kernelDiscrepancy` maxima over 99! states.
3. Prove generic uniform-pile-orbit pushforward = uniform membership-fiber lift. Reuse the already-proved `fiberOrbit_equiv` rather than computing full-deck masses.
4. Identify ideal swap-plus-local action with the abstract `rawExchange` and prove the one-step segregated-start smoothing identity.
5. Recover the `q3` exact ideal comparison *from the deterministic reference deck*. Only then add `3*delta1` and transfer to all deterministic decks by group action.
6. Return to multi-pile generalization and cost optimization after the first correct finite physical certificate is closed.

No active source file or previous review needs to be overwritten to make progress. Keep this dated document unchanged after check-in; update normal handoff files only when corresponding theorem statements compile.

## Acceptance criteria for next progress snapshot

- The candidate `finiteRound` and `idealRound` depend on input deck by applying a sampled position permutation.
- An abstract per-round or per-noise-law TV <= delta1 theorem compiles without unfolding `Finset.univ` on `Equiv.Perm (Fin 99)`.
- The ideal random-position-permutation kernel is shown equal to the established physical perfect-local kernel, or the exact weaker special-start bridge needed for the final theorem is proved.
- A lemma explicitly converts the *deterministic segregated* start to the fiber-uniform `q3` theorem's initial law. Relabeling alone is not accepted as that conversion.
- A genuine 3-round finite physical protocol from every deterministic deck is proved to satisfy TV < 1/1000, not merely a conditional numerical inequality or a constant-row telescope.
