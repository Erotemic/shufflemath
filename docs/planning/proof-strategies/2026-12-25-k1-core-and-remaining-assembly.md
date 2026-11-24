# Gate 6, K1 — committed state and the two remaining halves (2026-12-25)

## What is committed and builds (verified `lake build`)

**`Shufflemath/Gate6K1Direct.lean`** (namespace `Shufflemath.Gate6K1Direct`)
holds the *generic, Fintype-free kernel algebra* that **closes K1 by
composition** — no 99, no deck-space `Fintype`, no `native_decide`:

- **`fuseSwapLocal`** — the core composition closure. From the two halves
  `hH : H = comp M L` and `hK : comp K M = E`, it proves
  `comp K H = comp E L` in three `calc` lines (`comp_assoc` + two congruences).
  This is K1's `K ; H = E ; L`, stated at abstract types.
- **`kernelOfFiberRows`** — turns a *point-mass* (fiber-row) identity
  `∀ d, apply (pointMass d) H = apply (pointMass (f d)) L` into the *kernel*
  equality `H = comp (deterministic f) L`.  This is how a point-mass ideal half
  becomes the kernel half `H = deterministic membership ; localLift` (§3.2).
- **`mapMapOfPointwise`** — `(u.map s).map f = u.map g` from
  `∀ c, f (s c) = g c`; the map-fusion used to build the swap/membership half.
- §2.2/§2.3 (`supportMapTV`, `convTVBoth`, `convTVCommonLeft`) — Fintype-free
  TV contraction for deterministic maps and the two-variable convolution-TV
  bound.  (§2.4 `powConvTV` is parked — its induction step blows a bounded
  heartbeat on the `Nat.rec`-of-`conv` shape.)

**`Shufflemath/_ProbeK1wall.lean`** (untracked, sorry-free):
`k1wall_riffle_push_mass_factorial` — the 49!/19! push-mass identity, the
`newLeftCount = leftCard25` bookkeeping, and the 25/74-swap membership
preservation.  The counting core the K1 halves feed on.

**`Shufflemath/_ProbeGate6K1.lean`** (untracked, sorry-free):
`k1a_riffle_half` — the **ideal half** in *point-mass* form:
`rho99Ideal.map (act · d) = uniformMembershipFiber (membership d)`.
Through `kernelOfFiberRows` this *is* the kernel half `H =
deterministic membership ; localLift` (§3.2).

**`Shufflemath/_ProbeK1b.lean`** (untracked): `K1a_stmt_only` — the **core
pointwise** identity `membership ((L l) (R r) c).trans d = newMembership d l r c`
(the 25/74 swap of the exchange choice, then the 99/1 riffle, preserves the
50/49 membership exactly).

## What remains to close K1 in production form

`fuseSwapLocal` needs its two halves as **production** theorems, then K1 is one
`apply` away:

1. **Ideal half (§3.2):** `k1_idealKernel_eq_membershipLift :
   PAK rho99Ideal = comp (deterministic membership) localLift`.  The point-mass
   form is proven (`k1a_riffle_half`); the kernel form is `kernelOfFiberRows`
   + `apply_pointMass`.  The only friction this session was the `rw [comp]`
   step (Lean refused the equation theorem once probe imports were present);
   `unfold comp` / a direct `ext1` mass proof from `hFiberCard` bypasses it.

2. **Swap/membership half (§3.3): DONE (2026-12-25).**
   `k1_swapMembership_eq_exchangeMembership :
   comp (PAK swapLaw) (deterministic membership) = rawExchangeMembership`.
   Promoted to production **`Shufflemath/Gate6K1Swap.lean`** (Fintype-free, sorry-free).
   Closed exactly as predicted: `map_det_join_eq_map` (now committed in
   `Finite.lean`, `f6296eb`) collapses the join; `permutationActionKernel_eq_map`
   unfolds the PAK (definitional, to `.map (fun p => p.trans d)`); two
   `StdSimplex.map_map` pushes reduce both sides to
   `(uniformDist exchangeChoice).map (fun c => …)`; `congrArg` + `funext c`
   lands on `K1a_stmt_only`.  The 99! deck universe never enters a sum.

3. **K1:** the capstone is `comp (PAK rho99Ideal) (PAK swapLaw) =
   comp rawExchangeMembership localLift`.  Substituting the §3.2 ideal half
   (`PAK rho99Ideal = comp (deterministic membership) localLift`) and the §3.3
   swap half, this reduces (by `comp_assoc`) to the **deck-level fiber-
   uniformity commutation**:

   ```
   comp (deterministic membership) (comp localLift (PAK swapLaw))
     = comp (comp (PAK swapLaw) (deterministic membership)) localLift
   ```

   i.e. "read membership, lift uniformly into the fiber, then swap" = "swap,
   read the exchanged membership, then lift uniformly".  **This is the batch-5b
   within-pile-orbit = uniform-fiber bridge — the genuinely hard counting step,**
   NOT a mechanical `rfl`/`fuseSwapLocal` finish: `fuseSwapLocal` closes
   `comp (PAK swapLaw) (PAK rho99Ideal) = comp rawExchangeMembership localLift`
   (swap-then-riffle order), which is the *opposite* order from the K1 LHS
   `comp (PAK rho99Ideal) (PAK swapLaw)` (riffle-then-swap, per the committed
   `k1_lhs_bookkeeping`).  Do not conflate the two orders, and do not claim the
   capstone is "one `apply` away" on the strength of the two membership-level
   halves alone.  The deck-level statement needs the fiber-law uniformity (that
   the swap push of a fiber-uniform law is fiber-uniform at the exchanged
   membership), which the membership-level §3.3 does not by itself give.

## Composition order (settled)

Riffle-first: `comp (PAK swapLaw) (PAK rho99Ideal)`, i.e. `apply (apply
(pointMass d) H) K`.  Reference:
`docs/planning/proof-strategies/2026-11-24-k1-direct-order-hints-and-kernel-hints.md`.

## This session's notes (2026-12-25)

- **Three wins landed.**  `map_det_join_eq_map` (the Fintype-free Giry-mondad
  unit) is committed in `Shufflemath/Finite.lean` (`f6296eb`).  The §3.3
  swap/membership half is committed as production `Shufflemath/Gate6K1Swap.lean`
  (promoted from the `_ProbeK1swap` probe, which was deleted; `74c7333`).
  The §3.2 *ideal-half kernel form* is now proven (sorry-free) in
  **`Shufflemath/_ProbeK1ideal.lean`** — `k1_idealKernel_eq_membershipLift :
  PAK rho99Ideal = comp (deterministic membership) localLift`, a single `exact`
  of `Gate6K1Direct.kernelOfFiberRows` applied to the committed `k1a_riffle_half`
  point-mass form.  So **both halves of K1 are now in kernel form.**  Promotion
  of the ideal half to a production module is deferred until the whole K1 (incl.
  the deck-level bridge) lands, so `_ProbeK1half` (`k1a_riffle_half`) and its
  `_ProbeK1wall` counting dependency stay together in one promotion.
- **Corrected the "mechanical" claim.**  The two membership-level halves
  (ideal §3.2 + swap §3.3) do NOT by themselves close the K1 capstone; the
  capstone needs the deck-level fiber-uniformity commutation (item 3 above),
  which is the batch-5b counting bridge.  The §3.2 *kernel* form
  (`PAK rho99Ideal = comp (deterministic membership) localLift`) is still to be
  promoted to production (it is `kernelOfFiberRows` + the committed
  `k1a_riffle_half` point-mass form); it is the mechanical of the three and is
  the next small win before the deck-level bridge.
- No `sorry`/`admit` in `Finite.lean`, `Gate6K1Swap.lean`, `_ProbeK1ideal.lean`,
  or the other `_ProbeK1*` files; `lake build` of `Gate6K1Swap` + `Gate6K1Direct`
  + `_ProbeK1half` + `_ProbeGate6K1` + `_ProbeK1ideal` is green.

## The single remaining proof — a finite 25-swap counting target (derived 2026-12-25)

Working the deck-level fiber-uniformity pointwise in the target deck `X` reduces
the K1 capstone to an explicit finite count, isolating the *one* new combinatorial
claim.  With `F := 50!·49!` (`fiberSet_membership_card`): the capstone
`apply (localLift (membership d)) (PAK swapLaw) = apply (rawExchangeMembership d)
localLift` is, after `apply_mass_finsupp` (`Finite.lean`) + `localLift_mass` +
`fiberSet_membership_card` on **both** sides, exactly equivalent to

```
Σ_{s ∈ swapLaw.support} swapLaw s · 𝟏{ membership (s.symm·X) = membership d }
  = Dist.mass (rawExchangeMembership d) (membership X)          (∗)   for all d, X
```

- **LHS** of (∗): the total `swapLaw` weight of the swaps `s` whose inverse image
  `s.symm·X` lies in the source fiber (`membership d`).  Each `s` is a bijection,
  so at most one source deck maps to `X` per `s` — no `99!` sum.
- **RHS** of (∗): the exchanged-membership law at `membership X`; by the §3.3 swap
  half `= (swapLaw).map (fun s => membership (s.trans d))` at `membership X`.
- Total mass of each side is `25/74` (= `swapLaw`'s mass, a sub-probability law),
  so (∗) is mass-consistent and not trivially false.

**Next action.**  Prove (∗) as `k1_swap_fiber_count : ∀ d X, …` in a fresh
`Shufflemath/_ProbeK1b*.lean`.  Route: `swapLaw` has exactly 25 point masses
(25 `swapCard` permutations, each weight `1/74`), so both sides are sums over
`Finset.range 25`; expand both and match the `membership (swapCard_l · (·))` bookkeeping
against `newMembership d` (the exchange-choice law).  The 25-card structure of
`swapCard (Finset.range 25) l (Finset.range 74) (l+25)` and `newMembership` are
the concrete objects to compute on — this is the batch-5b within-pile-orbit =
uniform-fiber counting.  Do **not** introduce a `Fintype (Equiv.Perm (Fin 99))`.
After (∗), the K1 capstone is `apply_mass_finsupp` + `localLift_mass` +
`fiberSet_membership_card` in both directions, and the whole one-round law
`K1_oneRoundLaw_eq_exchangeThenLocalReset` follows by the already-committed
`k1_lhs_bookkeeping` / `k1_rhs_bookkeeping`.

**Refinement (why the naive per-choice equivalence fails).**  `newLeftCards d L R
= image (fun l => d (leftPosition l)) (univ \ L) ∪ image (fun r => d (rightPosition
r)) R` — the second union term reads specific **right-pile cards** `d (rightPosition
r)` for `r ∈ R`, so `newMembership d L R` is *not* a function of the left-pile
membership `membership d` alone; it also depends on the right-pile card
assignment.  Consequently the naive per-choice statement
`membership ((swapPerm c)⁻¹·X) = membership d ↔ newMembership d c = membership X`
for a fixed `c` is **not** the right lemma (the RHS carries full-deck information
the LHS bare-membership side does not).  The genuine core is the **right-pile-
dependent fiber bijection**: for each choice `c`, `swapPerm c` maps the source
fiber `fiber (membership d)` bijectively onto the target fiber `fiber (newMembership
d c)`, where the target membership tracks the right-pile assignment.  This is the
batch-5b within-pile-orbit = uniform-fiber bridge, and it is the single remaining
proof — not a `Finset.filter` count of a membership-only predicate.  Proving it
requires working with the right-pile card sets (`d ∘ rightPosition`), the
`swapPerm`/`canonicalPairing` construction, and the `50!·49!` fiber cardinality;
a `Fintype (Equiv.Perm (Fin 99))` must not be introduced.
