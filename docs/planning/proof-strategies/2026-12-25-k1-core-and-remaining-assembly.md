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

2. **Swap/membership half (§3.3):** `k1_swapMembership_eq_exchangeMembership :
   comp (PAK swapLaw) (deterministic membership) = rawExchangeMembership`.
   Wall: after `funext d; simp only [comp, apply, deterministic]` the goal
   still carries a `deterministic` kernel + `.join`.  Next action: a Giry
   unit lemma
   ```
   map_det_join_eq_map {α β γ} (ν : Dist α) (g : α → γ) (f : γ → β) :
     (ν.map (fun x => deterministic f (g x))).join = (ν.map g).map f
   ```
   (a corollary of `FiniteKernel.apply_deterministic_eq_map` + the
   `apply`/`join` defs, Fintype-free).  Then §3.3 closes by
   `rw [map_det_join_eq_map, permutationActionKernel_eq_map]; unfold swapLaw,
   rawExchangeMembership; rw [map_map]; refine congrArg (fun f => uniformDist.map f)
   ?_; funext c; simpa using K1a_stmt_only …`.

3. **K1:** `funext d; rw [hH, ← comp_assoc, hK, apply_pointMass]; rfl`, with
   `hH`/`hK` the two halves above — or directly `fuseSwapLocal`'s `calc`.

## Composition order (settled)

Riffle-first: `comp (PAK swapLaw) (PAK rho99Ideal)`, i.e. `apply (apply
(pointMass d) H) K`.  Reference:
`docs/planning/proof-strategies/2026-11-24-k1-direct-order-hints-and-kernel-hints.md`.

## This session's notes

- The earlier `Gate6K1.lean` production file was removed (its §3.2/§3.4a/§3.5
  drafts are captured here and in the `_ProbeK1*` files).
- The `map_det_join_eq_map` unit lemma is the single clean next proof; after
  it, both halves and the K1 capstone are mechanical.
- No `sorry`/`admit` in any file above; `lake build` of `Gate6K1Direct` + the
  AGENTS.md target module list is green.
