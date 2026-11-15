# Lean formalization roadmap (current)

Status date: **2026-11-11**. This is the **single active mathematical task list**.
For a new agent, begin with [agent_handoff.md](agent_handoff.md). Historical
phase notes are linked at the end; they do not override this plan. Read
`AGENTS.md` before modifying code.

> **Toolchain note (2026-02-10):** the library now uses Lean 4.34's `module`
> system (`module` header + `public import` + `@[expose] public section`). See
> `agent_handoff.md` §"Lean 4 module-system migration" for the exact recipe
> (dual `public import`/`public meta import` for `native_decide`, no `private`
> in `@[expose]` sections, EOF scope auto-close). The math and proof content is
> unchanged by this migration.

## Objective and model boundary

Produce a theorem for a *specified finite physical protocol* on 99 individually
identified cards: an explicit upper bound on total variation from uniform,
with an explicit physical-action cost. Eventually certify a minimum-cost
protocol in a declared finite action class. Do not confuse these statements:

1. **50-state Bernoulli--Laplace (BL) count chain:** remembers only how many
   of the original 50 left cards are in the 50-card left pile.
2. **Canonical oracle:** projects a full permutation to the count, takes a BL
   step, then resamples an arbitrary deck uniformly from the new count fiber.
3. **Physical perfect-local operation:** exchanges *selected positions* across
   piles and subsequently randomizes order *within each existing pile*.
4. **Finite-GSR physical operation:** the previous operation with finite
   independent-label riffles instead of uniform within-pile permutations.

The canonical oracle is not pointwise equal to the physical perfect-local
kernel on arbitrary ordered decks. The relevant physical theorem is an
**intertwining after a fiber-uniform input**, mediated by named-card pile
membership. See [full_deck_oracle_bridge.md](full_deck_oracle_bridge.md) and
[commander_fiber_disintegration.md](commander_fiber_disintegration.md).

## Implemented foundations (do not reimplement)

| Area | File(s) | Actual result and scope |
|---|---|---|
| Finite exact probability | `Finite`, `Matrix`, `TotalVariation` | `StdSimplex Rat`, kernels, stochastic-matrix bridge, exact TV |
| Kernel error/composition | `Perturbation`, `Dobrushin`, `ProtocolCertificate`, `Cost` | Weighted TV telescope, contraction and generic cost/error interfaces |
| BL macro chain | `BernoulliLaplace`, `BernoulliLaplaceGeneral`, `BernoulliLaplaceFiber`, `BernoulliLaplaceCommanderBridge` | General normalization, stationarity, reversibility, first centered eigenfunction and Commander specialization; exact 2-/3-step TV values |
| Array/semantic bridge | `BernoulliLaplaceSemantic` | Exact array runs and semantic `FiniteKernel` runs agree |
| Inverse GSR | `GSR` | **Complete.** `productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b)` is proved (`productLabelShuffle_uniform_eq_ideal`), from the joint-distribution bridge, the `labelReparam` pushforward, and sorting compatibility |
| Generic macro/micro TV | `FiberLifting`, `OracleRefinement` | Recoverable-lift TV isometry and canonical oracle intertwining, including schedule results |
| Physical refinement interface | `PhysicalRefinement` | Conditional full-deck physical TV bound using a perfect-local reference and weighted row error |
| Actual 99-card deck | `CommanderPermutation`, `CommanderFiberWitness` | `Equiv.Perm (Fin 99)`, count projection, explicit witness for each of the 50 fibers |
| Uniform fiber algebra | `FiberDisintegration` | Fiber law, marginal law, recovery, and generic unequal-fiber disintegration |
| Physical exchange reduction | `PhysicalExchangeReduction` | Conditional membership-level exchange implies macro-to-full intertwining |
| Commander full-deck consequences | `CommanderFullDeckDisintegration` | Exact 2-/3-step oracle-to-*uniform* theorems **assuming `HasCommanderFiberCounts`**; physical theorem has further explicit membership premises |

**Verification status, not mathematical scope:** The October 21
fiber/disintegration tranche, including the final `FiberDisintegration.lean`
v3 correction, is **compiled and verified by the user's established local
workflow**. Moving to the documentation handoff confirms completion: the
user reports build errors explicitly, rather than pasting every successful
build. Do not reopen this compilation question without concrete contrary
evidence. The 35 passing Python regression tests supplement the Lean work;
they do not establish the separate, still-open F1-F5 theorems.

`Shufflemath.lean` does **not** import every optional target, so a plain
`lake build` alone is insufficient to check the full-deck modules. The costly
`dev/BernoulliLaplacePairOptimality.lean` proof is also intentionally opt-in.

## Current entry point

**F1 is complete. Resume at F2c-iv-b** using
[`f2_fiberlaw_unblock.md`](f2_fiberlaw_unblock.md). The preceding
fiber/disintegration tranche compiles. For new Lean work, run `lake exe cache get` followed
by the affected module's `lake build`; run `./dev/verify_next_phase.sh` when
finishing a tranche. This is a regression workflow, not an extra gate on
the existing results.

## Work queue in dependency order

### F1. Prove the exact Commander fiber count -- COMPLETE

**Proved goal:** discharge
`CommanderFullDeckDisintegration.HasCommanderFiberCounts`, already defined
in `Shufflemath/CommanderFullDeckDisintegration.lean`:

```lean
forall x : BernoulliLaplace.CommanderState,
  Dist.mass BernoulliLaplace.commanderStationary x =
    ((FiberDisintegration.fiberSet CommanderPermutation.project x).card : Rat) /
      (Fintype.card CommanderPermutation.Deck : Rat)
```

This **cannot be proved solely** by `CommanderPermutation.project_surjective`: an
inhabited fiber need not have the right *cardinality*. Build a structural
counting proof, without evaluating a type containing `99!` permutations.

> **Progress (F1 complete, 2026-11):** All of F1a-F1d are proved and
> committed (`12e66df`). F1a (`decksWithLeft_card = 50! * 49!`) lives in
> `Shufflemath/CommanderFiberCount.lean`. F1b (`fiberMembershipSets_card =
> choose 50 k * choose 49 (50 - k)`), F1c, and F1d live in
> `Shufflemath/CommanderFiberMembership.lean` and
> `Shufflemath/CommanderFullDeckDisintegration.lean`:
> - **F1c:** `fiberSet_card` proves the fiber at state `x` has exactly
>   `choose 50 (x.val + 1) * choose 49 (50 - (x.val + 1)) * 50! * 49!` decks.
>   Proof shape: the macro fiber `fiberFin k` is reindexed by the section map
>   `d -> (leftCards d, d)` (injective on the fiber), which is exactly the
>   fiber-sigma `(fiberMembershipSets k).sigma leftCardsFin`; `Finset.card_sigma`
>   (Fubini) then reduces the count to the F1b sum times the F1a per-membership
>   count. The dependent-Sigma finset is stated over the Sigma type directly
>   (`Prod` and `Sigma` are distinct in Lean 4.34); the pair equality in the
>   image lemma is closed with `Sigma.ext` plus `HEq.refl`.
> - **F1d:** `commander_fiber_counts : HasCommanderFiberCounts` is unconditional.
>   The hypergeometric stationary mass equals the normalized fiber count because
>   `99! = choose 99 50 * 50! * 49!` (exact rational arithmetic, `native_decide`).
>   The two-/three-exchange uniformity corollaries and
>   `commander_uniform_disintegration_unconditional` follow.
> Verified with `./dev/verify_next_phase.sh` (35 Python tests).

Split into small compilable subresults, preferably in a new dedicated
`Shufflemath/CommanderFiberCount.lean` importing only what is needed:

1. **F1a: fixed membership:** for any valid 50-card subset of `Fin 99`,
   count complete ordered decks with exactly that left-membership set as
   `50! * 49!`. A bijection with independent left/right orderings is the
   preferred proof; avoid brute-force `native_decide` on `Deck`.
2. **F1b: count memberships:** for `x.val + 1` originally-left cards in the
   left pile, count allowed membership sets as
   `Nat.choose 50 (x.val + 1) * Nat.choose 49 (49 - x.val)`.
3. **F1c: combine and normalize:** prove
   `|fiber x| = choose(50,x+1)*choose(49,49-x)*50!*49!`, divide by `99!`,
   and rewrite into the existing exact hypergeometric `commanderStationary`.
4. **F1d: consume the theorem:** export a theorem of type
   `HasCommanderFiberCounts` with no extra premises, then use it in
   `commander_uniform_disintegration` and the existing conditional oracle
   2-/3-step results to give unconditional **ideal-oracle** results.

**Acceptance:** compile the dedicated counting module and
`CommanderFullDeckDisintegration`; check that the exported theorem has no
unproven counting assumptions. Existing `tests/test_commander_fiber_witness.py`
provides exact numeric regression evidence, not a substitute for Lean.
No need to change the already verified BL certificates.

### F2. Define the concrete membership and perfect-local kernels

**Dependency:** The compiled `CommanderPermutation` and fiber/disintegration
foundations. F2 can develop independently of F1's arithmetic, but needs F1
for uniform targets.

1. Define `Membership` as the subtype of 50-element subsets of card identities
   in `Fin 99` (or an equivalent bijective type).
2. Define `membership : Deck -> Membership`, and prove that its marked-card
   count agrees with `CommanderPermutation.project`.
3. Define `localLift : FiniteKernel Membership Deck` as uniform orderings of
   the *given membership set*, and prove
   `localLift.comp (FiniteKernel.deterministic membership) = identity`.
4. Define `membershipLift : FiniteKernel CommanderState Membership` as the
   uniform law among memberships with a specified marked count. Prove
   `membershipLift.comp localLift = FiberDisintegration.fiberLaw project
   project_surjective` (or first prove a generic version and specialize).

**Acceptance:** compile new modules and a small-deck exact reference test.
Neither `localLift` nor a physical local shuffle may change pile membership.
Do not confuse `localLift` with the canonical oracle's count-fiber reset.

> **Progress (F2, 2026-11): COMPLETE.** In `Shufflemath/CommanderMembershipKernels`:
> items 1–2 (`Membership`, `membership`, `membershipCount`, and the
> count-agreement `membershipFiber_iff`), item 3 (`localLift` +
> `localLift_preserves_membership`), and item 4 (`membershipLift` +
> `apply_mass_eq_sum` + the F2c-iv-b capstone
> `membershipLift_localLift_eq_fiberLaw`) are all proved. The F2 disintegration
> layer is done.
>
**New preferred intervention (Nov 11):** Model `localLift` as the already
proved generic `FiberDisintegration.fiberLaw membership membership_surjective`.
Its mass law and recovery theorem eliminate the blocked `Finsupp.mapDomain`
pushforward proof. Use the existing `leftCardsFin`/`decksWithLeft` cardinality
bridge from `CommanderFiberMembership.fiberFin_card`; details and proof order
are in [`f2_fiberlaw_unblock.md`](f2_fiberlaw_unblock.md). This is a proposed
route, not a theorem already in the tree.

> **COMPLETE (F2c-iv-b, the capstone, Nov 12):** the two-layer equality
> `membershipLift.comp localLift = FiberDisintegration.fiberLaw project
> project_surjective` is **proved** (commit `19d417c`), in the full
> *kernel* form — not just the point-mass form. With this, **all of F2 is
> complete**.
>
> *How the wall actually broke (revising the Nov 12 difficulty note):* the
> recursion was **not** a fundamental normalisation wall. It was the **default
> `simp` set** (and `field_simp`, which uses it) unfolding `membership` / `leftCards`
> (which depend on `d : Equiv.Perm (Fin 99)`). Once the proof is written with
> `simp only` over an *explicit* lemma list (never the default set),
> `if_pos`/`if_neg`-style `ite` reductions (`ite_eq_left`/`ite_eq_right`), and
> `by_cases` on the `Membership`/`Nat` equalities, none of the `Rat`/`Finset`
> arithmetic recurses. The kernel-level lift is then just
> `StdSimplex.weights_inj` + `Finsupp.ext` (both confirmed non-recursing over
> `Finsupp Deck`), applied to the point-mass equality.
>
> The earlier "point-mass is the deliverable / kernel form is blocked" framing
> in this file and in [`f2c_ivb_sum_collapse.md`](f2c_ivb_sum_collapse.md) is
> **superseded**: the kernel-equality form is proved. That difficulty note is
> kept as a record of the diagnosis but no longer reflects the open work.

### F3. Prove the 25-position physical-exchange membership law

> **Progress (F3, 2026-11-12):** In `Shufflemath/CommanderPhysicalExchange`:
> **(item 1, done)** the post-exchange left-pile membership `newLeftCards d L R`
> and the macro-count transition `newLeftOriginalCount_eq`.
> **(item 2, done, commits `b25d5f4`)** the deck-level `rawExchange : FiniteKernel
> Deck Deck` kernel, built as the composition of the membership-level exchange law
> `rawExchangeMembership` (pushforward of a uniform 25+25 `(L,R)` choice to its
> post-exchange membership `newLeftCards d L R`) and the uniform membership-fiber
> lift `localLift`; with the push-through lemma
> `rawExchange_membership_pushforward` (`comp rawExchange (deterministic membership)
> = rawExchangeMembership`).
> **(item 3a, done, commit `958d5f5`)** the structural reduction
> `hMembershipExchange_lhs_reduces`: the `hMembershipExchange` premise's left-hand
> side equals `comp (fiberLaw project) rawExchangeMembership` (via `comp_assoc` +
> the F2 capstone + the push-through). So the core law is
> `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25 membershipLift`.
>
> **(item 3 core, OPEN — the hard counting identity):** prove
> `comp (FiberDisintegration.fiberLaw project project_surjective) rawExchangeMembership
> = comp commanderExchange25 membershipLift`. Both sides are
> `FiniteKernel CommanderState Membership`. Mass-at-`m` (from input `x`) reduces to the
> exact counting identity
> `|{ (d,(L,R)) : project d = x, newLeftCards d L R = m }| / (|fiber project x| * choose 50 25 * choose 49 25)
>  = transitionWeight 99 50 25 (count x) (count m) / |{m' : count m' = count m}|`.
> This has two parts: (i) the new-count distribution of the physical exchange equals
> the Bernoulli--Laplace `transitionWeight` hypergeometric sum, and (ii) *given* the new
> count, the new membership is *uniform* over that count's fiber (a symmetry/group-action
> statement). Part (ii) is the harder half. This is on the critical path for item 4 and
> F4.5.
> **4th-session reduction (2026-11-12):** the underlying counting identity
> `overlap_count (n m r k) x y = transitionNumerator (n m r k) y x` now reduces to a
> single new **fiber-counting lemma (CL)** —
> `fiberSum p x y = choose(r, y) * choose(N - r, m - y) * overlap_count (N m r k) x y`
> — plus the already-proved `fiberSum_swap` and `fiberSum_eq` (the stationary `choose`
> factors cancel by pure algebra). **CL is verified on all three small decks**
> (`ExchangeOverlap.fiberCounting_{6321,7442,8431}`); the single remaining piece is the
> general (symbolic) proof of CL (reindex the 7-way `fiberSum` sum to the `(S, T)`
> double count). See `docs/qwen_unblock_nov12.md` §3.
> **6th-session progress (2026-11-14, `d55b69d`):** the **S1-side** of the CL is
> proven symbolically: `s1Fiber_choose` gives `|s1Fiber x t T1| =
> choose |T1| t * choose (|stars|-|T1|) (x-t)` for any `ExchangeAdmissible`, via
> `s1Fiber_biUnion` + `fiberA_card` (dependent `Finset.card_bij`) + `s1Fiber_card`
> (`card_biUnion` + sum-of-constant). This is the marked-side half of the 4-bin
> count for a *fixed* `T`; the remaining assembly is the mirrored plain/target
> (S2) side and the `choose(r,y)*choose(N-r,m-y)` target-choice factor, then
> `fiberSum_swap`/`fiberSum_eq` to close the full `fiberSum` identity.
> **7th-session progress (2026-11-14, `6ae278f`/`08a864b`/`19892fa`):** (a) the
> parameter-free **`Shufflemath.FinsetFiberCount`** module was extracted from
> `ExchangeOverlap.lean` (`sFiber`/`sFiberA`/`sFiber_biUnion`/`sFiberA_card`/
> `sFiber_card`/`sFiber_choose`, only `[DecidableEq α]` needed), so the marked
> and plain sides both instantiate one general lemma.  (b) Since `fiberSum_eq`
> and `fiberSum_swap` are already proven, the general CL was **sharply reduced
> to a single pure-`Nat`/`choose` identity** `transitionNumerator (N m r k) y x
> = overlap_count (N m r k) x y` (only `native_decide` small-deck versions exist
> today).  The `ExchangeOverlap.lean` section comment records the concrete
> reindexing `t = y - a` under which the four transition factors match the four
> overlap factors (two by `Nat.choose` symmetry), and characterizes the one
> remaining difficulty as the **boundary** (`if`-guards / `Nat`-saturated
> `y - a` vs `chooseSigned = 0` out of range) — a pure reindexing with no
> `Finset` API.
> **8th-session progress (2026-11-14, `0811eb6`):** the target was corrected
> to a **sum** identity (the pointwise `g(a) = h(y-a)` is *false* for `a > y`,
> where Nat-saturating `t := y-a` to `0` makes `h(0)` potentially nonzero
> while `g(a)=0`). The precise statement is
> `transitionNumerator (N m r k) y x = overlap_count (N m r k) x y` as a
> finite-sum equality; the `ExchangeOverlap.lean` comment records the exact
> factor structures of both sums and the exact common support
> `[max (0, y-k), min y (m-k)]` under `t := y-a`. This is a
> **generalized Vandermonde / hypergeometric convolution** between the two
> 4-factor decompositions (no Mathlib Vandermonde lemma exists; it must be
> proven from scratch — a combinatorial double-counting or an iterated
> Vandermonde manipulation). The S1-side counting (`FinsetFiberCount`) is
> complete; the remaining step is this one hypergeometric sum identity.
> **11th-session progress (2026-11-15, `2f93a91`/`135968c`/`b95f389`):** all
> **four** summand factor matches are now proven — `F1match`/`F2match` (9th),
> `F3match` (10th), and **`F4match`** (this session, via the new
> `intSub_eqCast`/`intSubSubAdd_eqCast` `Int`-no-saturation bridges) — plus the
> **summand assembly `tterm_eq_oterm`** (`tterm (N m r k) x y a = oterm (N m r k)
> x y (y-a)` in the admissible regime, by `rw [F1match, F2match, F3match,
> F4match]` + one `omega` base identity + `ring`) and the **definitional
> decomposition `transitionNumerator_eq_sum_tterm`** (the transition is the sum
> of `tterm` over `a ∈ [0,k]`, by `rfl`).  Combined with
> `overlap_eq_sum_oterm` (overlap = sum of `oterm` over `t ∈ [0,m-k]`), the
> general CL is reduced to the **final step: the `t = y-a` `Finset` sum
> reindexing** between the `a`-sum and the `t`-sum, aligning the supports on
> `[max (0, y-k), min y (m-k)]` where `oterm = 0` outside.  No `Finset`-API
> 2-bin products are involved.  Then (item 4) the 2-exchange TV follows from the
> CL + `fiberSum_eq`.
> **12th-session — COMPLETE (2026-11-15, `tterm_eq_oterm_all` / `oterm_sum_clip_eq`
> / `generalCL` commits):** the general CL is **proven symbolically**.
> `tterm_eq_oterm_all` gives the pointwise all-`a` equality `tterm (N m r k) x y a
> = oterm (N m r k) x y (y-a)` (three cases: both guards hold → `tterm_eq_oterm`;
> the F4 guard fails / the F2 guard fails → the corresponding `oterm` factor has a
> negative index and the product is `0`, via `chooseSigned_zero_neg` + the
> single-cast `let t := y-a` representation trick).  `transition_eq_sum_oterm_ySuba`
> reindexes the `a`-sum over `[0,k]` to the `t`-sum over `[y-k,y]` (`a ↦ y-a` is a
> bijection for `k ≤ y`, via `Finset.sum_image` + `rangeImage_ySuba_eq_Icc`).
> `oterm_sum_clip_eq` then clips *both* the transition and overlap `oterm`-sums to
> the common range `[y-k, min (y, m-k)]` (oterm is `0` outside, via
> `oterm_zero_below`/`above_mk`/`above_y` — the F3 factor `choose (m-y) (m-k-t)` and
> the F1 factor `choose y t` are off-range), so they are equal.  **`generalCL`**
> assembles these into `transitionNumerator N m r k y x = overlap_count N m r k x y`
> for the admissible regime (`k ≤ y ≤ m`, `y ≤ r`, `m+r ≤ N`, `r-y ≤ N-m`).  Also
> proved: **`fiberSum_eq_overlap`** — the fiber-level CL
> `fiberSum p x y = choose r y * choose (N-r) (m-y) * overlap_count (N m r k) x y`
> (compose `fiberSum_swap` + `fiberSum_eq` + `generalCL`).
>
> **m + r > N regime — RESOLVED this session.**  The 4th-factor base subtlety
> (`N - m - r + y` (left-saturated `Nat`) = `y` vs `(N-m) - (r-y)` = `y - 1` for
> the Commander) is fixed by using the **non-saturating** base `(N-m) - (r-y) =
> (N-r) - (m-y)` (equal, both = `N-m-r+y` as an `Int`, nonnegative for
> `y ≥ blLo = max (r-(N-m)) 0`).  The chain `baseInt_eqNatCast` → `F4match_ns` →
> `tterm_eq_oterm_ns` → `tterm_eq_oterm_all_ns` → `transition_eq_sum_oterm_ySuba_ns`
> → **`generalCL_ns`** proves the counting identity **without** `m + r ≤ N`, and
> **`generalCL_cmdr_2525`** proves the 25-25 Commander transition **symbolically**
> (no `native_decide`).  Together with `generalCL` (`m + r ≤ N`: 6321, 8431) the
> counting identity `transitionNumerator N m r k y x = overlap_count N m r k x y`
> now holds for **every valid deck**, including the Commander (99 50 50 25) and
> 7442.  **The F3 item 3 counting core is COMPLETE in both regimes.**
> **(item 4 / item 3 core, OPEN — part (ii) only):** with the counting (part (i))
> now done, the remaining half of the kernel equality
> `comp (fiberLaw project) rawExchangeMembership = comp commanderExchange25
> membershipLift` is **part (ii): given the new count `m`, the new membership is
> uniform over `{μ : membershipCount μ = m}`** — a symmetry/group-action statement
> (the physical-exchange law, averaged over the uniform `project`-fiber, treats all
> same-count memberships equally).  This is the "harder half" per the original
> F3 note; it is a member-level uniformity, distinct from the count-level CL.
> **16th-session progress (groundwork):** `Shufflemath/CommanderMembershipOrbits.lean`
> proves the well-typed range `1 ≤ membershipCount m ≤ 50` for every membership
> (`membershipCount_pos` + `membershipCount_le_50`), plus the `leftOrigSet`/
> `rightOrigSet` disjoint-cover identities the orbit construction (Spec A1) needs.
> **17th–18th-session progress (orbit primitive):** the building block
> `equiCardFinsets_bij` (`{x//x∈s} ≃ {x//x∈t}` when `#s = #t`, via
> `Fintype.card_ofFinset` + `Fintype.equivFinOfCardEq`) is committed. The core
> lemma `finsetType_perm` (a `s ≃ s` sending `A ↦ A'` and `s \ A ↦ s \ A'`, for
> `#A = #A'`) is **~90% built**: the **injective half is complete** (all four
> cases: same-piece via `Subtype.ext` + `eAB/eCD.injective`; cross-piece via the
> `A' ∩ (univ \ A') = ∅` disjointness contradiction), and the **surjective half
> has three tiny mechanical walls** documented with one-line fixes
> (`docs/agent_handoff.md`, 18th-session section: final `rfl` blocked by a `have`
> abbreviation; a `rw`-at-hypothesis motive; `rename_i` grabbing a `DecidableEq`
> typeclass). Once `finsetType_perm` closes, `membershipFiber_transitive` (two
> calls on the left/right pieces, agreeing on the disjoint cover `leftOrigSet ⊎
> rightOrigSet = univ`) is bookkeeping, and Specs A2/A3 follow.
> **(item 4, OPEN)** the unconditional physical-perfect-local 2-exchange TV theorem,
> which depends on item 3 core.

**Dependency:** F2 (satisfied: `membershipLift_localLift_eq_fiberLaw`, commit `19d417c`).

1. Specify the raw operation exactly: choose 25 distinct positions from each
   pile uniformly; swap the selected positions in a fixed bijective pairing.
   Randomness is in the chosen subsets, not an unspecified human procedure.
2. Implement `rawExchange : FiniteKernel Deck Deck` and verify the
   corresponding transition on named-card membership after a fiber-uniform
   input. Use counting/symmetry rather than enumerating permutations.
3. Discharge the `hMembershipExchange` premise of
   `CommanderFullDeckDisintegration.two_physical_perfect_exchanges_uniform_of_counts`
   through `PhysicalExchangeReduction.intertwining_of_membership_exchange`.
4. Combine with F1 to state the **unconditional physical-perfect-local**
   2-exchange TV theorem. The 3-exchange variant can follow the generic
   run/intertwining theorem; do not duplicate a giant kernel calculation.

**Acceptance:** no new abstract exchange hypothesis at the final exported
Commander theorem; exact small-deck checks in
`experiments/full_deck_oracle.py` and
`experiments/commander_fiber_witness.py` continue passing.
Do **not** try to prove pointwise equality of raw physical and canonical
oracle kernels: it is false in the documented 5-card example.

### F4. Quantify finite-GSR versus physical-perfect-local error

**Dependency:** F2 and F3 for the full 99-card statement; the standalone GSR
algebra can advance in parallel.

1. Extend `GSR.idealShuffle_comp`'s product-label theorem to the numeric
   uniform `Fin (a*b)` label alphabet via an explicit encoding and proof
   of pushed-forward uniformity. The present theorem is not this result.

   *Progress (clean dedicated pass):* the single-label core is done in
   `GSR.lean`: `encodeLabel`/`decodeLabel` give the lexicographic split of a
   `Fin (a*b)` label into a `Fin b` major and `Fin a` minor (a bijection,
   `encodeLabel_decodeLabel`/`decodeLabel_encodeLabel`); `combineLabels`/
   `splitLabels` lift this per-card to label arrays and assemble the
   `labelReparam` `Equiv`; `map_bijective_uniformDist` (a bijection carries
   the uniform law to the uniform law on the target) plus
   `productLabels_pushforward_uniform` prove the `(a*b)`-alphabet GSR label
   law equals the pushforward of the independent product of a `b`- and an
   `a`-alphabet law. The mixed-radix arithmetic is in place:
   `mixedRadix_unique` (`x*a + y = j*a + i`, with `y < a`, `i < a`, forces
   `x = j ∧ y = i`, proved via `Nat.add_mod`/`Nat.mod_eq_of_lt`/`Nat.mul_mod_right`/
   `Nat.add_right_inj`/`Nat.mul_left_cancel`) and `combinedLabel_pred`
   (per-card: `major c * a + minor c = j*a + i ↔ major c = j ∧ minor c = i`).
   *Remaining:* the **kernel equality**
   `productLabelShuffle a b (uniform) (uniform) = idealShuffle n (a*b)` — a
   joint-distribution bridge (the sorting-compatibility lemma is now DONE:
   `stableBuckets_combine_eq_lex` + the per-card `Bool`/`==`/`&&` bridge
   `combineVal_filter_eq`). **DONE:** the kernel equality
   `productLabelShuffle_uniform_eq_ideal` is proved (`GSR.lean`, `17ffab6`)
   via the joint-distribution bridge (iterated uniform `apply` = uniform
   product law, `apply_uniform_uniform_eq_product`) + the `labelReparam`
   pushforward + `stableBuckets_combine_eq_lex`. The bridge and
   `map_uniform_mass` were relaxed (codomain needs only `DecidableEq`, not
   `Fintype`, via `Finite.lean`'s `apply_mass_dom`) so they apply at the
   deck level (`α = List (Fin n)`). **F4.1 is complete.**
2. Define a permutation-preserving local-GSR kernel for the ordered cards in
   each *fixed* pile. Prove it cannot change the membership state.

   *Progress:* `CommanderLocalGSR.lean` defines the within-pile relabeling
   `pileRelabelFn pl pr` (a left position `leftPosition i` goes to
   `leftPosition (pl i)`, a right position `rightPosition j` to
   `rightPosition (pr j)`; it never moves a card between piles), with
   `pileRelabelFn_left`/`pileRelabelFn_right`. The central F4.2 fact
   `permutedLeftCards_eq` proves the left-card set of the permuted deck equals
   `leftCards d` (reindexing the 50 left positions by a bijection leaves the
   image of `univ` unchanged, `univImage_reindex`), i.e. a local shuffle
   **cannot change the membership state**. The bijection is now DONE via
   `pileRelabelEquiv` (`Fin.sumFinEquiv` + `Equiv.sumCongr` + `Equiv.trans`,
   building the `Fin 99 ≃ Fin 99` by construction) and `reorderedDeck` /
   `reorderedDeck_leftCards`. *Progress (5th session, `4e1b76f`):* **`gsrProductKernel (nL nR a b)`**
   (`CommanderLocalGSR.lean`) is now in the library — it applies the F4.1
   `GSR.idealShuffle` independently to the left and right piles (a
   `FiniteKernel` on the pile-list product), and **`gsrLocal_preserves_pile`**
   proves a within-pile GSR output holds exactly the pile's original cards
   (via `stableBuckets_set`), i.e. a local GSR cannot change the membership
   state. *Remaining:* lift the pile-list kernel to the full `Deck`
   (`Equiv.Perm (Fin 99)`) — the distributional multiset/permutation fact
   (output is a genuine rearrangement, not merely set-equal) is the sub-wall
   (`List.mem_bind`/`length_filter`/`toMultiset` absent in this build).
3. Establish the row-wise bound against *physical perfect-local* shuffling:
   for each deck, the TV discrepancy is no greater than the sum of the two
   local GSR-versus-uniform errors (49-card and 50-card working sets).
   *Progress (5th session, `87cc71f`/`104fd5e`):* the general reusable core is
   proven — `Finite.distProduct` (the independent product distribution, with
   the `distProduct_mass` simp-lemma) and
   `TotalVariation.distProduct_tv_subadditive` (`TV(μ⊗ν, μ'⊗ν') ≤ TV(μ,μ') +
   TV(ν,ν')` — the two-pile subadditivity). *Remaining:* connect the concrete
   `gsrProductKernel` to `distProduct` — `gsrProductKernel (L,R)` (a nested
   `map`/`join`) should equal
   `distProduct (GSR.idealShuffle nL a _ L) (GSR.idealShuffle nR b _ R)`, then
   `distProduct_tv_subadditive` gives the per-pile bound. **Wall:** the mass
   reduction normally uses `apply_mass_dom`, which requires a `Fintype`
   *domain*, but `idealShuffle : FiniteKernel (List (Fin n)) (List (Fin n))`
   and `List (Fin n)` is **not** a `Fintype`. Prove the point-mass equality
   directly from the `Finsupp` `map`/`join` weight definitions instead.
4. Use the existing `PhysicalRefinement.finite_local_uniform_bound` and
   `ProtocolCertificate` weighted telescope to compose these errors over a
   schedule. Use a named initial law and an explicit 99-card uniform target.

   *Progress (6th session, Fintype-free route — the `List (Fin n)` pile-list
   space is not a `Fintype`, so the `Finset.univ`-sup Dobrushin telescope has no
   direct Finsupp analog; a stochastic kernel is instead 1-Lipschitz on TV,
   which needs no finiteness):* `Finite.apply_mass_finsupp` (Fintype-free
   `apply_mass_dom` over the support), `TotalVariation.kernel_apply_lipschitz`
   (Fintype-free 1-Lipschitz kernel contraction), `TotalVariation.mixtureTV_le`
   (a mixture is no further from a reference than its component average),
   `CommanderLocalGSR.gsrOneStep_terminalTV_bound` (one two-pile GSR step keeps
   TV from the two-pile product reference within the start-weighted per-pile
   GSR-vs-reference errors — the 49+50 one-step terminal bound),
   `TotalVariation.run_nonexpansive` + `CommanderLocalGSR.gsrRunNonexpansive`
   (multi-step non-expansiveness for GSR schedules). *Remaining / blocked:* the
   fully *contractive* decay to the uniform target needs a Dobrushin coefficient
   (a `Fintype` supremum) — available only after the F4.2 Deck-level GSR lift to
   the Fintype space `Equiv.Perm (Fin 99)` (the `List.mem_bind`/`toMultiset`
   sub-wall); deferred.

**Acceptance:** a Lean-checked numeric or symbolic full-deck terminal TV
upper bound for one explicit physical finite-GSR protocol, with every model
assumption stated. Python's `experiments/oracle_gsr_budget.py` may propose a
candidate, but its output is not a Lean certificate.

### F5. Attach measured/parametric costs; certify a bounded optimizer

**Dependency:** F4 for a realistic finite-GSR protocol.

Re-use `Cost.lean`; specify the action alphabet, cost units (local riffle,
exchange, split/recombine), admissible schedules, and target TV threshold.
First prove the candidate's cost and **sufficient** TV upper bound; only then
address finite-class minimum-cost claims. A search over conservative upper
bounds is not proof that the candidate minimizes actual TV unless competing
candidates have suitable lower bounds or exact TV values.

*Progress (5th session, `e203310`/`ec68b71`):* the model-agnostic halves are
in. **`ProtocolCertificate.costed_terminalTV_le`** proves a costed schedule's
terminal TV ≤ its step kernels' weighted perturbation budget + the
ideal-reference TV (the "sufficient TV upper bound" half; reuses
`terminalTV_le_reference_add_budget`, so no F4 protocol instance is required).
**`Cost.protocolCost_nonneg`** (a schedule of nonnegative-cost actions has
nonnegative total cost) and the **`ActionKind`** action alphabet
(`localRiffle`/`exchange`/`splitRecombine`) supply the "cost" and "action
class" halves. *Remaining:* assemble these into the full F5 theorem over an
explicit finite-GSR protocol (needs the F4.2 `Deck`-level GSR product and the
F3 item 3/4 results), and state the optimization quantifiers separately.

**Acceptance:** theorem with model, action class, initial state, target,
terminal bound, and cost all explicit; separately state any optimization
quantifiers and their proof source.

### Optional / deferred tracks

- **P1: two-exchange exact optimum.** `dev/BernoulliLaplacePairOptimality.lean`
  is opt-in (`./dev/verify_next_phase.sh --pair`). Its source expresses the
  2,401-row objective. This optional certificate is independent of F1-F5.
  Prove variable-exchange-size semantics before
  presenting it as an operational schedule theorem. Do not make it a default
  library-build dependency.
- **GSR exact finite TV tables / Bayer--Diaconis permutation formula.** Useful
  for tighter F4 bounds; not a prerequisite for proving F1-F3.
- **Human bias, clumping, correlated labels, spectral higher modes.** Defer
  until a physical-perfect result and one finite-GSR bound are certified.
- **Presentation work.** The 155-scene Manim study deck is independent of
  Lean correctness. It has had LaTeX/build issues; do not count an authored
  deck or successful preflight as a completed full render without local
  evidence. See `visualizations/README.md` for build commands.

## Verification and completion rules

- Build only touched Lean targets first. **Always** run `lake exe cache get`
  before `lake build`, and run `./dev/verify_next_phase.sh` before handing
  off a tranche. That script intentionally builds modules missing from
  `Shufflemath.lean` imports. The legacy `dev/verify.sh` runs `lake update`
  and is not the preferred incremental verification path.
- Maintain current hypotheses in theorem statements until proved. Never
  silently promote a conditional theorem to an unconditional result, or
  replace proof obligations with `sorry`, `admit`, or opaque axioms.
- Exact Python tests are useful independent checks, **not** Lean proofs.
- Follow the quiet, targeted compilation policy in `AGENTS.md`; do not add
  unrelated proof-audit checks to normal build or CI workflows.
- Do not block a mathematically verified result on cosmetic linter warnings.
  Fix related warnings when editing a proof, not as an independent campaign.
- Update this file's status and `agent_handoff.md` after each completed
  tranche, recording tested targets and the next single task.

## Reference / history (not active task lists)

- [commander_fiber_disintegration.md](commander_fiber_disintegration.md):
  the concrete 99-card fiber and membership architecture.
- [full_deck_oracle_bridge.md](full_deck_oracle_bridge.md): three kernel
  models, numerical counterexample, and exact-count formula.
- [formalization_next_phase.md](formalization_next_phase.md): October 20
  source tranche and GSR/protocol rationale.
- [autonomous_lean_build.md](autonomous_lean_build.md) and
  [lean_build_history.md](lean_build_history.md): historical October 4-12
  autonomous-session record, **not current instructions**.
- [formalization_dependency_audit.md](formalization_dependency_audit.md):
  architectural background from before the `StdSimplex` migration.
