# G4 kernel equality — complete proof blueprint (verified against disk, 56th session)

## Context / why this is the right target

`BLRefinement`'s module header names the G4 goal:
  `uniform count-fiber ⊳ subsetExchange = blExchange ⊳ uniform count-fiber`
The *concrete* (99,50,50,25) route is **blocked** by a Fintype↔Finset wall:
`FiberLifting`'s `uniformPullback` / `fiberDisintegration` are stated over a
`Fintype`'s `Finset.univ`, but `uniformCountFiberMembership` is built from a
`countFiberMemb` **Finset**, and no committed equiv `Fintype.univ ≃ countFiberMemb`
exists (the `countFiberMemb_equiv` is only a *Type* equiv, not a Finset one).
The *generic* (arbitrary N,m,r,k) route is the honest discharger and it is
**nearly entirely already proved**. This note pins the exact target + the ONE
new lemma + the composition of existing lemmas.

## Target theorem (EXACT — note the composition argument order)

```lean
theorem uniformCount_intertwines_subsetExchange (p : ExchangeAdmissible) :
    comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p) =
      comp (blExchangeKernel p) (uniformCountFiberMembership p) := by ...
```

**CRITICAL (do NOT copy the WIP-note-47k statement, it has the args reversed):**
`comp (K)(L) x = ((K x).map L).join` is **K-then-L** (`Shufflemath/Finite.lean:111`).
So the two valid `BLState → Membership` compositions are:
  LHS = `comp (UCFM : BLState→Membership) (SE : Membership→Membership)`  [middle = Membership ✓]
  RHS = `comp (BL  : BLState→BLState)   (UCFM : BLState→Membership)`      [middle = BLState ✓]
`comp (SE)(UCFM)` does NOT typecheck (SE's output = Membership ≠ UCFM's input = BLState).
Both sides are `FiniteKernel (BLState N m r) (Membership N m)` — the goal typechecks.

## Pointwise-mass reduction (the math)

Mass of a composition (existing: `apply_mass_finsupp`, Finite.lean:191):
  `(comp K L x).mass y = ∑_j mass(K x j) · mass(L j y)`.

Notation: `x : BLState` (val = x.val), `S : Membership` with `c := countInPileVal S`,
`D := transitionDenominator = choose m k · choose (N-m) k`,
`#fiber z := (countFiberMemb z).card`, `kxch(S,T) := S≠T ∧ (S\T).card=k ∧ (T\S).card=k`.

Existing mass formulas (all committed):
  - `mass(UCFM x T) = if countInPileVal T = x.val then 1/#fiber x else 0`  (uniformCountFiberMembership body, BLRefinement:1484)
  - `mass(SE S T)   = if kxch(S.1,T.1) then 1/D else 0`  (subsetExchangeKernel, SubsetExchange:182)
  - `mass(BL x y)   = transitionWeight x.val y.val`     (blExchangeKernel body, BernoulliLaplaceGeneral:1043)

  **LHS at S** = ∑_{T} [count T = x ? 1/#fiber x : 0]·[kxch(T,S) ? 1/D : 0]
               = (1/#fiber x)·(1/D)·#{ T ∈ fiber x : kxch(T,S) }.
  **RHS at S** = ∑_{y : BLState} transitionWeight(x.val, y.val)·[c = y.val ? 1/#fiber y : 0].
               Only the unique `y` with `y.val = c` contributes (one BLState per count,
               `Fintype.ofFinset (Icc blLo blHi)`); for `S : Membership` the count `c` is
               ALWAYS admissible (`blLo = max(r-(N-m),0) ≤ c ≤ min(m,r) = blHi`), so
               **RHS at S = transitionWeight(x.val, c)/#fiber c**.

Reduce LHS = RHS  ⟺  `#{T ∈ fiber x : kxch(T,S)}/(#fiber x · D) = transitionNumerator(x,c)/(#fiber c · D)`
            ⟺  `#{T ∈ fiber x : kxch(T,S)}/#fiber x  =  transitionNumerator(x,c)/#fiber c`   ... (∗)

Two more bridges (both EXISTING):
  - `#{T ∈ fiber x : kxch(T,S)} = #yMoves N m r k hr S c x.val  =  transitionNumerator N m r k c x.val`
      (via NEW Lemma A below + `yMoves_card_eq_transitionNumerator` BLRefinement:908,
       applied with source count `c = count S`).
  - (∗) then becomes  `transitionNumerator(c,x)/#fiber x = transitionNumerator(x,c)/#fiber c`,
      which is EXACTLY `detailedBalance` (BernoulliLaplaceFiber:909) restated:
      `blStationary z = #fiber z / choose N m` (countFiber_blStationary, BLRefinement:232) and
      `transitionWeight(x,c) = transitionNumerator(x,c)/D` ⇒
      `detailedBalance p x y`  ⇔  `#fiber x·transitionNumerator(x,c) = #fiber c·transitionNumerator(c,x)`.
      Take `y` = the BLState with `.val = c`.

## THE ONE new lemma needed — "move↔target, fiber-restricted"

```lean
/- T4/G4 bridge: the k-exchange targets of S that carry count `y` are in bijection
   with the moves from S that land at `y`, so their cardinality is `#yMoves S c y`
   (hence `transitionNumerator c y` by yMoves_card_eq_transitionNumerator). -/
theorem reachSetFiberCard_eq_yMoves (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (hk : k ≤ m) (hkm : k ≤ N - m) (S : Membership N m) (c y : Nat)
    (hc : c = (S.1 ∩ markedSet N r hr).card)
    (x : BernoulliLaplaceGeneral.BLState N m r) (hx : x.val = y) :
    ((ReachSet N m k hm hk hkm S) ∩ (countFiberMemb N m r hr x)).card =
      (yMoves N m r k hr S c y).card := by ...
```
Proof sketch (self-contained Finset work, NO native_decide):
  - `ReachSet S` = univ.filter (T => (S\T).card=k ∧ (T\S).card=k)  (SubsetExchange:38).
  - `countFiberMemb x` = univ.filter (T => (T.1∩M).card = x.val)   (BLRefinement:1200).
  - Their intersection = univ.filter (T => kxch(S,T) ∧ count T = y).
  - `reachMoves S = (powersetCard k S.1) ×ˢ (powersetCard k (univ\S.1))`  (BLRefinement:535);
    `yMoves S c y = reachMoves S .filter (c - #(removed∩M) + #(added∩M) = y)`.
  - Define `target : reachMoves S → Membership` by `(A,B) ↦ ⟨(S.1\A)∪B, by⟩`.
    The existing bijection `subsetExchangeCount` (SubsetExchange:132, `ReachSet S ≃ Lset S ×ˢ Rset S`)
    already establishes each target has exactly one move (`hInject` there). Reuse it.
  - Show: `target` maps `yMoves S c y` bijectively onto `ReachSet S ∩ fiber y`, because
    `count(target (A,B)) = c - #(A∩M) + #(B∩M)` (marked-count bookkeeping: `A⊆S`, `B⊆comp S`,
    so the removed marked are exactly `A∩M` and added marked `B∩M`), which is precisely the
    yMoves filter, and the target's k-exchange-from-S is the ReachSet condition.
  - Card equality follows by `Finset.card_bijection` / `Finset.card_image` with that bijection.
    (Alternative: `Finset.card_bijOn` on the filtered finsets.)

If `subsetExchangeCount`'s inverse is awkward to reuse, a direct `Finset.card_bijection`
between `{p ∈ yMoves S c y}` and `{T ∈ ReachSet S : count T = y}` with
  fwd  `p ↦ ⟨(S.1\p.1)∪p.2, ...⟩`
  inv  `T ↦ ⟨(S.1\T.1, T.1\S.1)⟩`
  works standalone (injectivity: given the target T, A = S\T and B = T\S are forced).

## Assembly of the theorem (order of work)

```lean
theorem uniformCount_intertwines_subsetExchange (p : ExchangeAdmissible) :
    comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p) =
      comp (blExchangeKernel p) (uniformCountFiberMembership p) := by
  let {N, m, r, k} := p
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  let hk := p.hkm
  let hkm := p.hknm
  let D  := (transitionDenominator N m k : Rat)
  refine fun x S => ?_
  let c := countInPileVal N m r hm hr S
  let yc := ⟨c, countInPile_admissible N m r hm hr S⟩  -- : BLState, .val = c
  -- LHS mass:
  have hLHS : mass (comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p) x) S
      = (transitionNumerator N m r k c x.val : Rat) / ((countFiberMemb N m r hr x).card * D : Rat) := by
    rw [apply_mass_finsupp, ...]          -- mass of comp = Σ_T mass(UCFM x T)*mass(SE T S)
    -- collapse the sum to the fiber-x T's, use subsetExchangeKernel mass,
    -- reachSetFiberCard_eq_yMoves + yMoves_card_eq_transitionNumerator, countInPile_val.
  -- RHS mass:
  have hRHS : mass (comp (blExchangeKernel p) (uniformCountFiberMembership p) x) S
      = (transitionNumerator N m r k x.val c : Rat) / ((countFiberMemb N m r hr yc).card * D : Rat) := by
    rw [apply_mass_finsupp, ...]          -- Σ_y transitionWeight(x,y)*mass(UCFM y S)
    -- only y with y.val=c contributes (unique BLState per count); UCFM mass 1/#fiber c.
  -- Close with detailed balance:
  have hDB : #fiber x * (transitionNumerator N m r k x.val c : Rat)
      = #fiber c * (transitionNumerator N m r k c x.val : Rat) := by
    -- restatement of detailedBalance p x yc (blStationary z = #fiber z / choose N m,
    --   transitionWeight = numerator/D): cross-multiply by (choose N m * D).
  -- hLHS = hDB → = hRHS.
```

Existing lemmas to lean on (all committed, no native_decide):
  - `apply_mass_finsupp` (Finite.lean:191)  — comp-mass = Σ_j mass(K x j)·mass(L j y).
  - `uniformCountFiberMembership` / `subsetExchangeKernel` / `blExchangeKernel` bodies (above).
  - `countInPile_val` (BLRefinement:432), `countInPile_admissible` (BLRefinement).
  - `countFiberMemb_nonempty` (BLRefinement:1200-adj) — #fiber > 0 (for the division).
  - `yMoves_card_eq_transitionNumerator` (BLRefinement:908).
  - `detailedBalance` (BernoulliLaplaceFiber.lean:909) + `countFiber_blStationary` (BLRefinement:232)
    + `blStationary`/`transitionWeight`/`transitionDenominator` defs (BernoulliLaplaceGeneral:117/825/862).
  - `ReachSet`/`Lset`/`Rset`/`subsetExchangeCount` (SubsetExchange:38/44/46/132),
    `reachMoves`/`yMoves` (BLRefinement:535/682).
  - `transitionDenominator_pos` (BernoulliLaplaceGeneral:896) for D ≠ 0.

## Import note (RESOLVED)
CONFIRMED: BLRefinement is a **leaf** — imported by NOTHING (`grep -rl` for its import path
returns empty). BernoulliLaplaceFiber imports only {BernoulliLaplaceGeneral, Markov} (+Mathlib),
neither of which can import BLRefinement (it's a leaf). So adding
`public import Shufflemath.BernoulliLaplaceFiber` to BLRefinement's header is **cycle-safe**
and the G4 theorem + bridge lemma both live in **BLRefinement** (its module header already
names the G4 macro-intertwining as the module's purpose).
Current BLRefinement imports: TwoPile, BernoulliLaplaceGeneral, FiberDisintegration, SubsetExchange + Mathlib.
Add exactly one line: `public import Shufflemath.BernoulliLaplaceFiber` after the SubsetExchange import.

## Execution plan (next session)
1. Add `public import Shufflemath.BernoulliLaplaceFiber` to BLRefinement (cycle-safe, confirmed above).
2. Probe `/home/joncrall/code/shufflemath/Shufflemath/_ProbeG4.lean` with
   `public import Shufflemath.FiniteDeck.BLRefinement` + the **new lemma**
   `reachSetFiberCard_eq_yMoves` first (build it standalone — it's the riskiest).
3. Once the bridge lemma compiles, add the capstone `uniformCount_intertwines_subsetExchange`.
4. Build the probe → fix → `lake build Shufflemath.FiniteDeck.BLRefinement` →
   splice both into BLRefinement (use Python splice, NOT the `edit` tool — it chokes on `⊳`/`×ˢ`).
5. Full library build (AGENTS.md list) + `./dev/verify_next_phase.sh`.
6. Commit (one commit, both the bridge lemma + capstone; `Co-authored-by: the current model`).
7. Update `docs/lean_plan.md` G4 status + `docs/agent_handoff.md` resume point +
   `.pi-glla/47k_kernel_wip.lean` (mark this route DONE, note the concrete route is superseded).
8. Re-publish LLM tally.

## Gotchas (learned this session)
- **edit tool** fails on content containing `⊳` (and likely `×ˢ`): use a Python splice
  (write file + `python3 -c` read/replace/write) to insert into BLRefinement.
- **Fintype↔Finset wall** is avoided entirely by this route: we only ever use Finset
  cardinalities (`countFiberMemb`, `ReachSet`, `yMoves`) and the `detailedBalance`
  *Rat* identity — no `FiberLifting` uniformPullback needed.
- The RHS sum collapses to ONE term because `BLState` is `Fintype.ofFinset (Icc blLo blHi)`
  (one element per admissible count). For `S : Membership`, `c` is always in `[blLo, blHi]`,
  so the term exists and no "else 0" branch is needed — but prove the `c` admissibility
  (`countInPile_admissible`) explicitly.
- `transitionNumerator` is NOT symmetric in (x,c); only the *weighted* form
  `#fiber x · transitionNumerator(x,c) = #fiber c · transitionNumerator(c,x)` holds (detailedBalance).
  This is why the fiber-size factors are essential — do NOT try to claim bare symmetry.

## Resume state (session 55/56, 2026-11-18) — CONCRETE next steps
- **Confirmed in the probe (`Shufflemath/_ProbeG4.lean`, a WIP scratch file, NOT
  committed):** the module must be `namespace Shufflemath / namespace FiniteDeck` with
  `open FiniteKernel` and `open BernoulliLaplaceGeneral` **inside** the namespace
  (`comp` is `Shufflemath.FiniteKernel.comp`; `BLState`/`blExchangeKernel`/`ExchangeAdmissible`
  are `Shufflemath.BernoulliLaplaceGeneral`). Top-level `open` of those fails.
- **`markedCountChange` is ~85% proved** in the probe. The disjointness
  `hInt : ((S.1\p.1)∩M)∩(p.2∩M) = ∅` compiles via `ext x; simp only
  [Finset.mem_inter, Finset.mem_sdiff]; constructor; <contradiction via hsubB>`,
  exactly the `CommanderFiberCount.lean:425` pattern. Three remaining Finset-tactic
  nits, all mechanical:
  1. `hInt` dir-1: `have hxS : x ∈ S.1 := hx.1.1` fails (coercion `x∈↑S` vs `x∈S.1`);
     use `exact absurd hx.1.1 hxBc` instead (drop the `hxS` have).
  2. `hIntCard`: `exact hu` reports "No goals to be solved" — the
     `rw [hZero, Nat.zero_add] at hu` is closing the goal; drop the `exact hu` or
     replace with a clean `calc`/`gcongr` on `#(L∪R) = #L + #R` using
     `Finset.card_union_add_card_inter` + `hZero`.
  3. `hLcard`: `rw [hInter]` fails because `hInter : p.1∩(S.1∩M) = p.1∩M` has the
     operands in a different order than the goal's `(S.1∩M)∩p.1`; add
     `rw [Finset.inter_comm]` first (or state `hInter` as `(S.1∩M)∩p.1 = p.1∩M`).
- **After `markedCountChange` compiles:** prove `reachSetFiberCard_eq_yMoves`
  (`Finset.card_bij'` of `i : T ↦ (S.1\T.1, T.1\S.1)` / `j : p ↦ ⟨(S.1\p.1)∪p.2,
  newpile_card …⟩`; the landing proofs call `markedCountChange` in each direction
  and use `hsubA`/`hsubB` to get the `p.1∩M`/`p.2∩M` cards), then `newpile_reach` +
  `inv_first`/`inv_second` give the two inverses — all present in `subsetExchangeCount`.
- **Capstone:** `uniformCount_intertwines_subsetExchange` = `finKernels_eq` +
  `comp_unfold` + `pushforward_unfold` + `sum_eq_sum_if` + the two lemmas +
  `yMoves_card_eq_transitionNumerator` + `transitionNumerator_eq_transitionDenom_mul_card`.
- Once `_ProbeG4.lean` builds, **port the three theorems into `BLRefinement.lean`**
  (append inside `namespace Shufflemath.FiniteDeck`, before the trailing `end`s —
  use `sed`/heredoc, NOT the `edit` tool, for the Unicode-heavy content) and run
  `dev/verify_next_phase.sh` (which builds `Shufflemath.FiniteDeck.BLRefinement`).

## Session 57 progress (2026-11-18) — markedCountChange DONE + in BLRefinement
- **`markedCountChange` is PROVEN and committed into `Shufflemath/FiniteDeck/BLRefinement.lean`**
  (after `countFiberMemb_equiv`, before `end FiniteDeck`). It builds clean in BLRefinement and
  the whole `dev/verify_next_phase.sh` tranche (37 tests OK).
  Final proof shape: `hInt` (disjointness via `ext; simp [mem_inter,mem_sdiff]; constructor;
  <absurd hx.1.1.1 hxBc>`), `hDistrib` (`ext; simp; tauto`), `hIntCard`
  (`card_union_add_card_inter` + `hZero : #(L∩R)=0` + `Nat.add_zero` + `exact hu`),
  `hLrewrite` (`ext; simp; tauto`), `hLcard` (`card_sdiff` + `hInter : (S.1∩M)∩p.1 = p.1∩M`
  via `simp [inter_comm, hInter]`). The key projection gotcha: after `simp [mem_inter,mem_sdiff]`
  a premise `x ∈ (A∩B)∩(C∩D)` expands to `((x∈A∧x∈B)∧(x∈C∧x∈D))` — a **doubly** nested
  conjunction, so `x∈A` is `hx.1.1.1`, not `hx.1.1`.
- **`reachSetFiberCard_eq_yMoves` (in `_ProbeG4.lean`, untracked) is ~70% written.** Two precise
  helpers it needs (discovered this session), both easy:
  1. **`ymReach`**: from `hp : p ∈ yMoves`, get `p ∈ reachMoves`. `yMoves = (reachMoves).filter f`,
     so `have h : p ∈ (reachMoves N m k S).filter _ := by simpa [yMoves] using hp;
     exact (Finset.mem_filter.mp h).1`. (A bare `simpa [yMoves,reachMoves] using hp` does NOT
     work — it yields the conjunction `p∈reachMoves ∧ f p`, not `p∈reachMoves`.)
  2. **`ymFilter`**: from the same `h`, `(Finset.mem_filter.mp h).2` gives
     `c - (p.1 ∩ M).card + (p.2 ∩ M).card = y` — exactly the yMoves filter.
  3. **`hTarget` bridge**: to apply `markedCountChange` to a target `T`, its conclusion is
     written with target `(S.1\(S.1\T.1))∪(T.1\S.1)`, which Lean auto-simplifies to
     `((S.1∩T.1)∪(T.1\S.1))`; bridge it to `T.1` with
     `have hTarget : ((S.1 \ (S.1 \ T.1)) ∪ (T.1 \ S.1)) = T.1 := by rw
     [Finset.sddiff_sdiff_self_left, Finset.inter_comm, Finset.union_comm,
      Finset.sdiff_union_inter]` (the same rw as `subsetExchangeCount`'s left-inverse), then
     `rw [hTarget] at hraw`.
  Then `Finset.card_bij' i j` with the 4 directions (dir 1: `i T` → move in reachMoves [reuse
  `subsetExchangeCount` dir-1] + y-filter [markedCountChange + hTarget + hCountT=(T.1∩M).card=x.val=y];
  dir 2: `j p` → newpile_reach + target-in-fiber [markedCountChange + ymFilter]; dirs 3-4:
  verbatim from `subsetExchangeCount`).
- **Capstone `uniformCount_intertwines_subsetExchange`**: `finKernels_eq` on `x,S`; reduce both
  `comp` sides to their single-`x` / single-`S` fiber contributions (the uniform mass formula
  `1/#fiber x` on the fiber, `0` off it — `uniformCountFiberMembership`'s body); LHS becomes
  `(1/#fiber x)(1/D)#(ReachSet∩fiber x∩kxch→S)` = `(1/#fiber x)(1/D)#yMoves(c,x)` (via
  `reachSetFiberCard_eq_yMoves` + `yMoves_card_eq_transitionNumerator`); RHS =
  `transitionWeight(x,c)/#fiber c`; close with `transitionNumerator_eq_transitionDenom_mul_card`
  (detailed balance) + `#fiber x = #fiber c`. See the "The proof (calc)" section above.
- **Port when done**: move `reachSetFiberCard_eq_yMoves` + `uniformCount_intertwines_subsetExchange`
  from `_ProbeG4.lean` into BLRefinement (python/sed, not the `edit` tool — Unicode `⊳`/`∩`/`∪`
  break the edit tool); both need `open BernoulliLaplaceGeneral` + `open FiniteKernel` (already in
  scope via BLRefinement's imports? `comp`/`FiniteKernel` — BLRefinement does NOT `open FiniteKernel`,
  so the capstone must write `FiniteKernel.comp` fully-qualified, OR add the open). Then build + verify.

## Session 58 progress (2026-11-18) — reachSetFiberCard_eq_yMoves DONE + in BLRefinement
- **`reachSetFiberCard_eq_yMoves` is PROVEN and committed into
  `Shufflemath/FiniteDeck/BLRefinement.lean`** (after `markedCountChange`, before
  `end FiniteDeck`, ~line 1623). It builds clean in BLRefinement and the whole
  `dev/verify_next_phase.sh` tranche (37 tests OK).
- **Final proof shape** (the 4 directions of `Finset.card_bij' i j`):
  1. *i lands in yMoves* — `hMove : (S.1\T.1, T.1\S.1) ∈ Lset ×ˢ Rset` (from
     `hInR : T ∈ ReachSet` via `rw [mem_product, Lset, Rset, mem_powersetCard, ...];
     rcases hInR with ⟨hA,hB⟩; ⟨⟨sdiff_subset,hA⟩,⟨hsub2,hB⟩⟩` where
     `hsub2 : T.1\S.1 ⊆ univ\S.1`), then `hmc` (markedCountChange, with
     `hT : (S.1∩T.1)∪(T.1\S.1) = T.1` via `ext; simp [mem_union,mem_inter,mem_sdiff]; tauto`),
     then `hmc2 : c - #((S.1\T.1)∩M) + #((T.1\S.1)∩M) = (T.1∩M).card` (`rw [hc, hmc.symm]`),
     then `hfilter : ... = y` (`rw [hmc2, hCountT]; exact hx`), then
     `rw [yMoves]; exact (Finset.mem_filter.mpr ⟨by dsimp [i]; simpa [reachMoves, mem_product,
     Lset, Rset, mem_powersetCard] using hMove, by simpa using hfilter⟩)`.
     **Gotcha**: the `mem_filter.mpr` first arg needs `i T hT ∈ reachMoves` — `i` is a `let`,
     so `dsimp [i]` first, THEN `simpa` with `reachMoves/mem_product/Lset/Rset/mem_powersetCard`
     in the set to unfold the goal to match `hMove`'s `↑S\↑T ∈ Lset ∧ ↑T\↑S ∈ Rset` form.
  2. *j lands back in ReachSet ∩ fiber* — `hpL` (p ∈ Lset×Rset), `hraw :=
     markedCountChange ... p hpL`, `rw [← hc, hFilter] at hraw` (reduces the count-change RHS to
     `y`), then `Finset.mem_inter.mpr ⟨by simpa using newpile_reach ... hpL,
     by simpa [countFiberMemb, hx] using hraw⟩`. **Gotcha**: the second `mem_inter` arg's goal is
     still the MEMBERSHIP `j p hp ∈ countFiberMemb x`; `simpa [countFiberMemb, hx]` unfolds it to
     the `((S.1\p.1)∪p.2)∩M = y` equality that `hraw` supplies.
  3. *left inverse* `j (i T) = T` — `dsimp only [i,j]; refine Subtype.ext ?_; change
     (S.1\(S.1\T.1))∪(T.1\S.1) = T.1; rw [Finset.sdiff_sdiff_self_left, inter_comm, union_comm,
     sdiff_union_inter]` (verbatim from `subsetExchangeCount`).
  4. *right inverse* `i (j p) = p` — `dsimp only [i,j]; have hpL := simpa [reachMoves,Lset,Rset]
     using (ymReach p hp); ext; rw [inv_first ... hpL] / rw [inv_second ... hpL]`.
     **Gotcha**: use `rw [inv_first/inv_second]` (NOT `exact`) — matches `subsetExchangeCount`.
- **`_ProbeG4.lean` is now capstone-only** (27 lines): it keeps
  `uniformFiber_intertwines` (the kernel-equality capstone, still `sorry`) as the next unit,
  importing BLRefinement for the bridge lemma.
- **NEXT (session 59+): the G4 kernel-equality CAPSTONE.** IMPORTANT: the name
  `uniformFiber_intertwines` is ALREADY taken (BLRefinement:1420, a proven
  macrostate-kernel = pushforward result) — the capstone is a DIFFERENT theorem,
  the `comp`-equality of the two kernel defs, staged in `_ProbeG4.lean` as
  `g4MacroIntertwining` (elaborates, body `sorry`):
    `FiniteKernel.comp (uniformCountFiberMembership p) (subsetExchangeMembershipKernel p)
     = FiniteKernel.comp (blExchangeKernel p) (uniformCountFiberMembership p)`
  Both sides are `FiniteKernel (BLState p.N p.m p.r) (Membership p.N p.m)`; this is the doc's
  `uniform count-fiber >> subsetExchange = blExchange >> uniform count-fiber` (BLRefinement:1453).
  - `uniformCountFiberMembership` (BLRefinement:1484) and `subsetExchangeMembershipKernel`
    (BLRefinement:1531) are the two halves; `blExchangeKernel` is BernoulliLaplaceGeneral:1043.
  - Proof sketch (pointwise in (x, T)): LHS = (1/#fiber x)(1/D)#(fiber-x targets kxch-ing to T)
    = (1/#fiber x)(1/D)#yMoves(S,T.count)  [reachSetFiberCard_eq_yMoves +
    yMoves_card_eq_transitionNumerator]; RHS = transitionWeight(x, T.count)/#fiber(T.count),
    closed by detailed balance (transitionNumerator_eq_transitionDenom_mul_card) + the
    fiber-card symmetry. BLRefinement does NOT `open FiniteKernel` / `open
    BernoulliLaplaceGeneral`, so the body must qualify `FiniteKernel.comp`,
    `blExchangeKernel`, and (for `Membership`/`BLState` projections) as needed.
  - **Port when done**: move `g4MacroIntertwining` from `_ProbeG4.lean` into BLRefinement
    (python/sed, not the `edit` tool), after `reachSetFiberCard_eq_yMoves`.


## Session 59 (2026-11-18): capstone skeleton; next sub-lemma = hLHS

The one **new** G4 lemma, **`reachSetFiberCard_eq_yMoves`** (ReachSet∩fiber ↔ `yMoves`),
is **DONE and committed** (moved into `BLRefinement.lean` after `markedCountChange`,
`public import Shufflemath.FiniteDeck.SubsetExchange`; 3223-job build green; all 37 tests pass).

The **capstone** `g4MacroIntertwining` (the full G4 kernel-equality) now has a
**compiling WIP skeleton** in `Shufflemath/_ProbeG4.lean`:
`funext x; unfold FiniteKernel.comp; ext S; change <pointwise-mass goal>; sorry`.
The **ext path is confirmed** (`FiniteKernel = alpha -> Dist beta`; `comp K L x = (K x).map L ⋅ join`;
`ext S` drills `StdSimplex -> .weights (Finsupp) -> pointwise`). `import Shufflemath.Finite`
brings in `FiniteKernel.apply_mass_finsupp`.

**Remaining (three sub-lemmas + close), in `Shufflemath/_ProbeG4.lean`:**
- **`hLHS`** (NEXT): `mass (apply (UCFM x) (SE)) S = transitionNumerator c x.val / (#fiber x * D)`.
  Via `apply_mass_finsupp` → dsimp the UCFM/SE mass bodies → collapse the support-sum to
  `(1/#fiber x)·D⁻¹·#{j∈fiber x : kxch(j,S)}` → `reachSetFiberCard_eq_yMoves` +
  `yMoves_card_eq_transitionNumerator`. (`countInPileVal` unfolds via `dsimp`, not `simp`.)
- **`hRHS`**: `mass (apply (blExchangeKernel x) (UCFM)) S = transitionNumerator x.val c / (#fiber yc * D)`,
  where `yc = ⟨c, countInPile_admissible ...⟩`. Via `apply_mass_finsupp` + `mass_blExchangeKernel`
  + the UCFM mass at `S`; only `y` with `y.val = c` contributes (BLState Fintype = `Icc blLo blHi`,
  one element per count; use the `Finset.univ`/`Icc` bridge as at BLRefinement:1217).
- **`hDB`**: `#fiber x * tn(x.val,c) = #fiber yc * tn(c,x.val)` via `detailedBalance`
  (BernoulliLaplaceFiber:909) + `countFiber_blStationary` + `transitionWeight = tn/D`.
  **Reconcile** `#countFiber` (raw `Finset (Fin N)`, used by those lemmas) with
  `#countFiberMemb` (Membership, used by the mass formulas) — the `.1` projection is a bijection;
  add a `countFiberMemb_card_eq_countFiber` helper if needed.
- **close**: `change` to the two mass forms; `rw [hLHS, hRHS, ← hDB]; ring_nf`.

After proven, move `g4MacroIntertwining` into BLRefinement (after the bridge lemma). Then **G4
kernel equality is complete**. Full sub-lemma tactics: `/tmp/note_g4_capstone.md`.

Session-58 correction stands: `uniformFiber_intertwines` (BLRefinement:1420) is **already complete**;
the G4 remainder is `reachSetFiberCard_eq_yMoves` (done) + the capstone `g4MacroIntertwining`
(hLHS/hRHS/hDB, this session's target).
