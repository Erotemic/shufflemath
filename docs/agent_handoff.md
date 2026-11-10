# Agent handoff: next Shufflemath task

**Updated:** 2026-11-09. **Source basis:** the October 21 source snapshot,
the fiber/disintegration tranche, and this session's F1 progress in
`Shufflemath/CommanderFiberCount.lean` (compiles, no `sorry`/axiom). This is
an *operational handoff*. `lean_plan.md` is the authority for overall scope and
priority; `AGENTS.md` governs repository behavior.

## Standing rules for the agent reading this document (non-negotiable)

1. **Do not stop, ask, or end the session before Thu Nov 12 22:27:06 EST 2026.**
   This is a long autonomous build. You **will be compacted multiple times**;
   compaction is normal and is not a stopping signal.
2. **After every compaction, do exactly this, in order:**
   a. Read this document top to bottom, then `AGENTS.md` and
      `docs/lean_plan.md`.
   b. Run `git log --oneline -10` and `git status --short` in
      `/home/joncrall/code/shufflemath`.
   c. Run the targeted `lake build` commands listed in `AGENTS.md` to confirm
      the tree is green (if red, fix before anything else).
   d. Resume work at the "Exactly where to resume" / "Next (F1c + F1d)" items
      in this file and the next unchecked item in `docs/lean_plan.md`.
3. **Small batches only.** One batch = 1–3 related lemmas/theorems in one
   file. Each batch must end with: targeted `lake build` green → `git add`
   + `git commit`. Never let the working tree carry more than one batch of
   uncommitted work.
4. **Commit trailer (exact):** one `Co-authored-by` trailer naming the
   **current** model only (see `AGENTS.md`; never the October session's model
   name). Subject line: short imperative, e.g.
   `Add fiber count over membership sets`.
5. **Every commit must build.** The affected modules must pass `lake build`
   before you commit. `./dev/verify_next_phase.sh` must pass at the end of
   each tranche (F1, F2, …) in `docs/lean_plan.md`. The legacy
   `./dev/verify.sh` (which runs `lake update`) is **not** the verification
   path.
6. **Keep this document updated.** After each commit, tick the item in
   "Exactly where to resume", update `docs/lean_plan.md`, and adjust the next
   action. This file is the only thing a compacted/fresh agent can trust; the
   conversation is not.
7. **Do not stop early even if the current tranche is all done.** Fall
   through to the next item in `docs/lean_plan.md` (F2, F3, F4, F5), then to
   the verification pass (re-run `./dev/verify_next_phase.sh`, audit
   docstrings, re-check regression values), until the deadline.
8. **Stuck protocol.** If a single proof resists ~2 build iterations, write a
   `-- TODO(proof): <sketch>` comment at the exact location, commit what
   builds, move to the next item, and return later. Never leave a broken
   build, never leave a `sorry` or `admit`.
9. **Taste rules:** exact `Rat` arithmetic only; no
   `set_option maxHeartbeats 0`; no floating point in proofs; docstring on
   every nontrivial theorem; no sweeping refactors of existing names.

## Lean 4 module-system migration (done this session)

Every library `.lean` file (24 `Shufflemath/*` + the `Shufflemath.lean`
aggregator) and `dev/BernoulliLaplacePairOptimality.lean` were migrated from the
old `import`-only style to Lean 4.34's **`module`** system. `lakefile.lean` was
left as-is (Lake DSL files stay plain `import Lake`). The whole graph is
atomic: a `module` file cannot `import` a non-`module` file in the same
package, so all-or-nothing was required.

The working per-file recipe (do NOT deviate):

* Header: `module` on its own line, blank line, then imports.
* **Every** `import X` → **`public import X`**. A plain `import` makes the name
  "imported privately" and it will not resolve inside an `@[expose]` section
  (the compiler says *"consider adding `public import …`"*).
* Wrap the body in `@[expose] public section … end`. `@[expose]` (not bare
  `public`) is what makes declarations **transparent across the module
  boundary** — bare `public` exports by name but leaves them **opaque**
  (consumer `rfl`/`simp`/`dsimp` cannot unfold them, which breaks this codebase's
  heavy `simp [ … ]`/`change` usage).
* **No `private` declarations inside an `@[expose]` section.** `@[expose]` +
  `private` makes the decl vanish (even to later decls in the same namespace).
  The 88 `private` decls were converted to plain `def`/`theorem`/`abbrev`/
  `instance`/`lemma` (now exposed by the section).
* Files that previously relied on Lean 4's **implicit end-of-file scope
  close** (no explicit `end`, e.g. `BernoulliLaplaceCommanderBridge`,
  `BernoulliLaplaceFiber`) must NOT get an appended bare `end` — let EOF close
  the section. Files that already had balanced explicit `end`s keep the one
  appended `end` that closes the section.
* **`native_decide` needs a dual import**: files whose `native_decide` proves a
  fact about another module's `def` (`BernoulliLaplace` → `TotalVariation`'s
  `vectorTV`; `CommanderFiberWitness` → `CommanderPermutation`'s `project`;
  `dev/BernoulliLaplacePairOptimality` → `BernoulliLaplace`) need both
  `public import M` *and* `public meta import M` for that module `M`. The
  term-level `public import` keeps `Finset.range`/`Rat.addCommMonoid`/etc.
  usable in computable defs; the `meta import` lets the generated `_native`
  code reference the target. A lone `meta import` demotes the re-exported
  Mathlib names to meta-only and breaks the computable defs.

Verified: `./dev/verify_next_phase.sh` (builds the next-phase overlay + 35
Python tests, OK) and `./dev/verify_next_phase.sh --pair` (the 2,401-pair
certificate via `lake env lean dev/…`, EXIT 0).

## Exactly where to resume

**F1a is COMPLETE and green.** `Shufflemath/CommanderFiberCount.lean` builds
(`lake build Shufflemath.CommanderFiberCount`, EXIT 0) and now proves the deck
counting theorem. The file uses **explicit `S` parameters** (no `section` /
`variable` — that pattern leaks `S` into implicit leading arguments and blocks
the deck-level equiv; see the resolved note below). All equivs target **plain
Finset-membership subtypes**, which is what `Fintype.card_of_subtype` /
`Finset.card_sddiff_of_subset` / `Fintype.card_equiv` want.

* `leftPile S := {x // x ∈ S}` and `rightPile S := {x // x ∈ (Finset.univ \ S)}`
  (abbrevs, so `Fintype.Subtype.fintype` synthesizes).
* `leftEquiv S d hd : Fin 50 ≃ leftPile S` — built via
  `Equiv.ofBijective (leftFun S d hd) ⟨inj, surj⟩`; `leftFun i = ⟨d
  (leftPosition i), leftCardInS⟩`. **Key:** build the equiv to the plain
  subtype (NOT to `(S : Set)`); the `⟨x, proof⟩` construction works once the
  target is `{x // x ∈ S}`. `leftEquiv_apply`, `leftEquiv_card = 50!`.
* `rightEquiv S d hd : Fin 49 ≃ rightPile S` — `rightFun j = ⟨d (rightPosition
  j), rightCardInS⟩`; `rightCardInS` reduces to `Finset.univ \ S` and closes
  with `simp only [Finset.mem_sdiff]` + `constructor` (membership in an sdiff
  is *not* an inductive type, so a bare `constructor` fails).
  `rightEquiv_apply`, `rightEquiv_card = 49!`.
* `deckFunSub S eL eR p` / `deckFunInvSub` — the position-wise (resp. value-wise)
  assembly, now over the subtype equivs; `left_invSub` (`deckFunSub ∘ deckFunInvSub
  = id`), `deckFunSub_left` / `deckFunSub_right`.
* `pasteDeckSub S eL eR : Deck` — `Equiv.ofBijective (deckFunSub …)`; surjectivity
  is `left_invSub`, injectivity is `Finite.injective_iff_surjective` (namespace
  **`Finite`**). `pasteDeckSub_leftCards` (left pile = `S`), `pasteDeckSub_self`
  (`pasteDeckSub (leftEquiv d) (rightEquiv d) = d`, by `apply Equiv.ext` +
  `change` + `split_ifs` — **`split_ifs` is the only tactic that splits a
  named-binder `if` inside a `def`**).
* `toLR / fromLR` and the inverse laws `fromLR_toLR`, `toLR_fromLR`; then
  `decksLR : decksWithLeft S ≃ (Fin 50 ≃ leftPile S) × (Fin 49 ≃ rightPile S)`
  via `Equiv.ofBijective (toLR S) ⟨inj, surj⟩`, where injectivity and
  surjectivity fall out of the two inverse laws (no `admit`/`sorry`).
* **`decksWithLeft_card : Fintype.card (decksWithLeft S) = 50! · 49!`** — the
  F1a deliverable: `rw [Fintype.card_congr (decksLR S), Fintype.card_prod]` +
  `simp [leftEquiv_card, rightEquiv_card]`. (`Fintype.card_congr` is the
  equiv-transport lemma; `Fintype.card_equiv` is for counting the equiv space
  itself and is *not* the right tool here.)

**F1b is COMPLETE and green.** `Shufflemath/CommanderFiberMembership.lean`
builds (`lake build Shufflemath.CommanderFiberMembership`, EXIT 0) and proves the
membership-set count. The fiber over `x` (where `k = x.val + 1` initially-left
cards remain) is determined, before resampling, by which cards end up in the
left pile. The `50`-card membership sets carrying exactly `k` initially-left
cards are counted by a bijection with left-right pairs:

* `fiberMembershipSets k := (powersetCard 50 univ).filter (S ↦ (S ∩ leftOrigSet).card = k)`;
  `leftRightPairs k := powersetCard k leftOrigSet ×ˢ powersetCard (50 - k) rightOrigSet`.
* `S_decomp` (`S = (S ∩ left) ∪ (S ∩ right)`, via the union partition) and
  `S_decomp_disjoint` (the two parts are disjoint).
* `unionMap_mem_fiber` (forward: a `(k, 50-k)` pair unions to a fiber member) and
  `fiberMem_to_pairs` (backward: a fiber member splits as `(S ∩ left, S ∩ right)`);
  `leftPart_of_union` / `rightPart_of_union` (a part is recovered by intersecting the
  union with the corresponding pile); `unionMap_injective` (disjointness forces a
  unique split).
* `fiberMembershipSets_eq_image` (the fiber membership sets are exactly the image of
  the pairs under `unionMap`) and the F1b deliverable
  **`fiberMembershipSets_card : #(fiberMembershipSets k) = choose 50 k * choose 49 (50 - k)`**
  (via `card_image_of_injOn` + `card_product` + `card_powersetCard` + the pile sizes).

Set-theory notes: use `Finset.subset_empty.mp` for `s ⊆ ∅ → s = ∅`,
`Finset.inter_subset_inter` + `Finset.Subset.rfl` for the disjoint-intersection
proofs, `Finset.union_inter_distrib_right` for `(a ∪ b) ∩ c`, and `omega` (with
a `k ≤ 50` side-lemma) for the truncated-Nat arithmetic `k + (50 - k) = 50`
(`ring` cannot do truncated subtraction). `Finset` has no `subset_univ` and no
`mem_empty`; `s ⊆ univ` is trivial (`Finset.mem_univ`).

**F1 bridge is COMPLETE and green.** `leftOriginalCount_eq_leftCardsInter (d : Deck) :
leftOriginalCount d = (leftCards d ∩ leftOrigSet).card` is now in
`Shufflemath/CommanderFiberCount.lean`. It is the key link: the macro count
`leftOriginalCount d` equals the number of originally-left cards *in the left
pile*, i.e. the size of `leftCards d ∩ leftOrigSet`, where `leftCards d` is the
left-pile membership (a 50-subset of card identities). Proof: `unfold` the three
defs, show the left pile `∩ leftOrigSet` equals the *image of the selected
left positions* (an `ext` on `Fin 99` with `rcases` on the existential/`And`
forms — `Finset` has no `subset_univ`/`mem_empty`; use `mem_inter`/`mem_image`/
`mem_filter`/`mem_univ` + `and_true`/`true_and` + `leftOrigSet` in the `simp`),
then `Finset.card_image_of_injective` on the injective left-position map
(`d.injective` ⊢ `leftPosition_injective`).

**Next (F1c + F1d) — the final F1 assembly.** Two facts remain, then F1d:

1. **Full fiber count** `#(fiberType k) = #(fiberMembershipSets k) * 50! * 49!`.
   Define `fiberType (k) := {d : Deck // leftOriginalCount d = k}` (a `Fintype`
   subtype). The fiber decomposes over the membership sets: each `d` has a unique
   `leftCards d ∈ fiberMembershipSets k` (by the bridge, since
   `leftOriginalCount d = k ↔ leftCards d ∈ fiberMembershipSets k`), and the decks
   over a fixed membership `S` are `decksWithLeft S` (card `50! * 49!` by
   `decksWithLeft_card`). The natural statement is a `Fintype` bijection
   `fiberType k ≃ fiberSigma k` where
   `fiberSigma k := Σ S : {S // S ∈ fiberMembershipSets k}, decksWithLeft S.val`,
   then `Fintype.card_sigma` + `Finset.sum_const` + `Fintype.card_of_subtype`
   gives `#fiberSigma k = #(fiberMembershipSets k) * 50! * 49!`.

   **Obstacle found (do not re-derive):** the dependent-`Sigma` route hits a
   *maximum recursion depth* in the Lean kernel when `decksWithLeft S.val` is
   indexed by the *subtype* variable `S : {S // S ∈ fiberMembershipSets k}` (the
   concrete-S form `decksWithLeft leftOrigSet` builds fine in isolation —
   `test_dwl`). The `Equiv`-level `ext` on the Sigma equality also resists
   `⟨Subtype.ext ?_, Subtype.ext ?_⟩`. **Recommended path:** prove the fiber
   count at the *Finset* level instead of via a dependent `Fintype` — take
   `fiberFin (k) := (Finset.univ : Finset Deck).filter (fun d => leftOriginalCount d = k)`
   and show `#fiberFin k = Finset.sum (fiberMembershipSets k) (fun S =>
   Fintype.card (decksWithLeft S))` via `Finset.biUnion` with the pairwise-
   disjointness given by the bridge (`leftCards d` is a unique membership, so the
   filters are disjoint), where each term is `decksWithLeft_card` and the sum is
   `#(fiberMembershipSets k) * 50! * 49!` (constant summand).
   `#(fiberFin k) = #fiberType k` (Fintype vs. Finset filter) closes the loop.

2. **Normalization + F1d.** With `#(fiberType k) = choose 50 k * choose 49 (50-k)
   * 50! * 49!` (F1b × F1a) and `#Deck = 99!`, the stationary mass for a state
   `x` (with `k = commanderLeftCount x = x.val + 1`) is
   `#(fiberSet project x) / #Deck = choose 50 k * choose 49 (50-k) * 50! * 49! / 99!`
   `= choose 50 k * choose 49 (50-k) / choose 99 50` (using
   `choose 99 50 * 50! * 49! = 99!`, i.e. `Nat.choose_mul_factorial` /
   `Nat.factorial_choose`). This equals `commanderStationaryVector x` by its
definition (`choose 50 (commanderLeftCount x) * choose 49 (50 - commanderLeftCount x)
   / choose 99 50`). F1d then exports `HasCommanderFiberCounts` by connecting
   `fiberSet project x` to `fiberType (commanderLeftCount x)` (via
   `project_val_eq`-style: `project d = x ↔ leftOriginalCount d = x.val + 1`),
   then `change Dist.mass (Dist.ofFun _ _ _) x = _` + `rw [Dist.mass_ofFun _]`
   (**never `simp`/`dsimp` on `commanderStationary` directly — it is a
   `noncomputable` `Dist.ofFun` and the projection stalls**).

**`#Deck = 99!`:** `Fintype.card (Equiv.Perm (Fin 99))` — use
`Fintype.card_perm` / `Fintype.card_equivFin` (`#(Perm (Fin n)) = n!`).

**Resolved blocker (for the record):** the section-`variable (S)` pattern is
**abandoned** in this file. Every def/theorem takes an explicit `(S : Finset
(Fin 99))` argument. The old Set-form `deckFun` / `pasteDeck` /
`decksWithLeft` (using `Equiv (Fin 50) (S : Set)`) have been *removed*; the
new subtype-form `deckFunSub` / `pasteDeckSub` / `decksLR` replace them.
`decksWithLeft` itself (the `abbrev`) is unchanged and is the subtype the deck
count is stated over.

### Hard-won API notes for this step

* `rightEquiv`'s codomain is the *Set* form `((Finset.univ \ S) : Set)`; the
  counting `rightPile S` is the *Finset*-membership subtype. They are the same
  elements; their `Fintype`s coincide (both reduce to `Finset.card_compl` = 49).
  The remaining friction is only the `Equiv`-level cast between the two
  representations when assembling the product.
* `Fintype.card_coe` does **not** auto-fire on the double coercion
  `Fintype.card ↑↑S`; use `Fintype.card_coe` with an explicit `simp`/`rw`, or
  bridge through a single-coercion subtype.
* `Set.mem_sdiff` (top-level `mem_sdiff` inside `namespace Set`) is `Iff.rfl`
  and its `.mp`/`.mpr` projections do **not** resolve by name; destructure a
  `x ∈ a \ b` goal directly with `⟨...⟩` / `rcases` (Set sdiff is definitionally
  `∧`).
* Do **not** define `rightPosition` inside the `section` — a section
  `variable (S)` leaks into a `def` as an implicit leading parameter, so
  `rightPosition j` then expects `j : Finset (Fin 99)`. Keep `rightPosition`
  (and `rightPile`) at namespace level; they don't use the section variables.
* `Finset.compl` / `Sᶜ` (the Finset complement) triggers a kernel `whnf`
  **timeout**; use `Finset.univ \ S` (sdiff) and, where a Set is needed,
  `((Finset.univ \ S) : Set)`. `Finset.compl_eq_univ_sdiff` bridges sdiff
  back to `Sᶜ` for `Finset.card_compl`.

At the end of the new tranche, run `./dev/verify_next_phase.sh`. Do not
rerun established modules solely to resolve an invented verification doubt.
The legacy `./dev/verify.sh` uses `lake update` and is not the incremental
default.

## What is already there

| Capability | Where | Status to carry forward |
|---|---|---|
| General finite kernel, TV, Dobrushin, BL and first eigenfunction | `Shufflemath/{Finite,TotalVariation,Perturbation,Dobrushin,BernoulliLaplaceGeneral,BernoulliLaplaceCommanderBridge}.lean` | Previously compiled and reported verified |
| Exact macro 2-/3-exchange TV certificates and semantic transport | `BernoulliLaplace.lean`, `BernoulliLaplaceSemantic.lean` | Earlier tranche compiled |
| GSR product-label shuffle; TV/protocol refinement | `GSR.lean`, `FiberLifting.lean`, `OracleRefinement.lean`, `PhysicalRefinement.lean`, `ProtocolCertificate.lean` | Earlier tranche compiled; numeric alphabet bridge not done |
| Actual 99-card permutation count projection | `CommanderPermutation.lean` | User expressly confirmed successful compilation after its fix |
| Constructive witness of all 50 macro fibers | `CommanderFiberWitness.lean` | Implemented and compiled |
| Uniform fiber disintegration and membership reduction | `FiberDisintegration.lean`, `PhysicalExchangeReduction.lean` | Implemented and compiled, including the v3 correction |
| Conditional full-uniform oracle and physical-perfect results | `CommanderFullDeckDisintegration.lean` | Compiles; **counting and membership hypotheses still open** |
| Left/right action bijections + exact 50!/49! counts (F1) | `CommanderFiberCount.lean` | **This session: compiles; deck-level assembly + HasCommanderFiberCounts remain** |
| Optional 2,401-pair exact TV minimum | `dev/BernoulliLaplacePairOptimality.lean` | Separate opt-in target; not a prerequisite for F1-F5 |

Last observed local warnings from `CommanderPermutation.lean` (`simpa`
versus `simp`, and `haveI` versus `have`) are not build blockers.
The 35 Python tests were passing at the time of the fiber tranche.

## The next deliverable, strictly scoped

Implement a count proof for
`CommanderFullDeckDisintegration.HasCommanderFiberCounts` without evaluating
all `99!` permutations. Good checkpoints:

- A proof of `50! * 49!` ordered decks over one fixed 50-card membership.
- A proof of the number of eligible memberships:
  `choose 50 (x.val + 1) * choose 49 (49 - x.val)`.
- Their product as the cardinality of `fiberSet project x`.
- Rational normalization to the *existing* `commanderStationary` mass.
- An exported theorem of the already-declared `HasCommanderFiberCounts` type,
  removing the counting premise from the *ideal-oracle* uniform theorem.

These are distinct subtasks. Do **not** try to solve F1-F5 in a single patch.
If the whole count theorem resists, deliver the independently proved first
sublemma, note the exact next obligation, and keep the build green.

### Non-goals for this patch

- Do not redefine `Dist`, `FiniteKernel`, or the 50-state BL kernel.
- Do not assert that the physical perfect-local kernel equals the canonical
  oracle on arbitrary deck states (the documented five-card counterexample
  rules that out).
- Do not use `native_decide` over a 99-card permutation type or enumerate
  `99!` states. A 50-state finite decision (as in the existing fiber witness)
  is different.
- Do not replace counting or exchange hypotheses with assumptions called
  "obvious", or weaken theorem statements to make them compile.
- Use targeted compilation as the routine proof check (see `AGENTS.md`).
- Do not change the Manim presentation, documentation history, or other
  independent projects as part of the counting proof.

## After F1: exact dependency chain

1. **F2:** `Membership` for a 50-element subset of named cards, the map
   `Deck -> Membership`, and uniform within-membership `localLift`; prove
   recovery and the factorization through `membershipLift`.
2. **F3:** uniform 25-position cross-pile exchange and named-membership
   transition identity; discharge `hMembershipExchange`; prove physical
   perfect-local 2-exchange uniform TV using F1 and F2.
3. **F4:** numeric product-label GSR law; permutation-preserving local-GSR
   kernels; per-row TV discrepancy against physical perfect-local; combine
   via `PhysicalRefinement.finite_local_uniform_bound`.
4. **F5:** give explicit operation costs and a protocol satisfying an
   explicit terminal TV target; optional bounded optimality later.

A weaker agent can work on F1a, F1b, F2a, or the GSR numeric-encoding
lemma independently. Every contribution should name its prerequisite,
exact output theorem, and the compiler command used to verify it.

## Work and handoff protocol

1. Check `git status --short`; do not discard unrelated changes or create
   worktrees. Work in place in the user's existing checkout.
2. Run `lake exe cache get`, then `lake build` on *only affected modules*.
   Run the full targeted script when the tranche is complete.
3. Keep changes small and directly buildable. Report actual compiler errors
   with filename/line number. Use the current mathlib API rather than
   guessing lemma names; inspect existing source signatures.
4. Preserve the actual theorem obligations and keep builds focused;
   follow `AGENTS.md` for proof-checking and audit policy.
5. Once the new work is tested, update `docs/lean_plan.md` and the
   **first action** of this handoff. Treat user-confirmed compilation as
   established; don't invent pending-verification status.
6. Stage only changed files and commit with a single trailer using the
   current model, e.g.
   `Co-authored-by: GPT-6 <noreply@openai.com>`.

The active mathematical specification is in [lean_plan.md](lean_plan.md).
The detailed model distinction is in
[full_deck_oracle_bridge.md](full_deck_oracle_bridge.md) and
[commander_fiber_disintegration.md](commander_fiber_disintegration.md).
