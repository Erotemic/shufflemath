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
