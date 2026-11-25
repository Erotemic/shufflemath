# batch-5b wall-bound step: elementwise `Finset` subset `image ⊆ fiberSet` (seed, 2026-12-30)

**Status of the batch-5b headline** `rhoRoundIdeal 99 50 hm = localLift segMembership`:

**WALL-FREE (proven, in `Shufflemath/_Probe5b.lean`, builds clean at N=99):**
- `leftCards_embed_eq_segLeft`: `embed_m` (hence `roundEmbedMap`) preserves the left-50-card
  set = `segLeft`. Proven all in the `FiniteDeck` frame via `finiteDeck_leftCards_99_50_eq_commander`
  + `FiniteDeck.embed_m_imageLeft` — no `leftPosition` Fin-defeq, no `(fiberOrbit_equiv …).val`
  deck. This is the **linchpin** (previously the blocker in the 2026-11-25 wall-free plan).
- `membership_embed_eq_segMembership`: for a *specific* `(pl, pr)`,
  `membership (roundEmbedMap (pl,pr)) = segMembership` (via the linchpin + `membership_iff_leftCards`).
- `withinPile_pairs_card`: `Fintype.card (Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49)) = 50! * 49!`.

**WALL-BOUND (this seed — the remaining piece):**
The elementwise `Finset` subset
```
(Finset.univ : Finset (Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49))).image
  (roundEmbedMap 99 50 hm5099) ⊆ FiberDisintegration.fiberSet CommanderMembershipKernels.membership segMembership
```
recurses (`linter … maximum recursion depth has been reached` at the theorem). Even after
`intro x hx; rw [Finset.mem_image] at hx; rcases hx with ⟨p, hp, rfl⟩` (which specializes `x` to
`roundEmbedMap p`), unfolding `FiberDisintegration.fiberSet` → `univ.filter (fun b => membership b = segMembership)`
and deciding `membership (roundEmbedMap p) = segMembership` in that *Finset-filter* context recurses,
whereas the same equality for the bare deck (`membership_embed_eq_segMembership`) elaborates fine.
So the wall is specifically in **`Finset` membership decision for a 99-card membership fiber**, not
in the membership equality itself.

**Why it matters for the headline:** the headline needs `image = fiberSet` (both directions).
Forward `image ⊆ fiberSet` (this wall) + equal 50!·49! cardinality (both wall-free above) would give
`image = fiberSet` by finiteness, and then the mass-equality assembly (`map_mass_eq_univ_fiber` +
`localLift_mass` + `fiberSet_segMembership_card` + `withinPile_pairs_card`) would close
`rhoRoundIdeal = localLift`. So **only** the elementwise subset is between us and the headline.

**Next-session ideas (not yet tried):**
1. Replace the `Finset` membership decision with a `Fintype`/subtype one: prove
   `image ⊆ fiberSet` by lifting to `{d // membership d = segMembership}` (where `fiberSet_segMembership_card`
   already worked at the *card* level) — i.e. show the `Fintype` image lands in the subtype, avoiding
   the `Finset.filter` predicate decision.
2. Prove `image = fiberSet` directly via a **bijection** between the within-pile-pair `Fintype` and the
   fiber `Fintype` (a `Fintype.card`-level equinumerosity, no elementwise `Finset` membership).
3. A `set_option` heartbeat bump is NOT acceptable per the do-not-stop/build discipline (no `maxHeartbeats`
   escalation for a wall); route (1)/(2) is the intended wall-free path.

**Do NOT** put `sorry` here. The three wall-free lemmas are the real, committed progress.

---

## Sharpened diagnosis (later this same session)

Tried the **leftCards-level** analog: `leftCardsFiber = (univ : Finset (Perm (Fin 99))).filter
(fun d => leftCards d = segLeft)` and the inclusion `image ⊆ leftCardsFiber` (same shape, but
`leftCards` is a 50-element image, *not* the 99-card `membership`). **It recurses too**
(`maximum recursion depth has been reached` at the theorem).

⇒ The wall is **not** `membership`-specific. It is the **elementwise `.mem` / `.filter` on the
99! `Finset.univ : Finset (Equiv.Perm (Fin 99))` universe** — i.e. *any* pointwise predicate over the
99! deck `Finset` (membership, leftCards, …) recurses when Lean decides `x ∈ filter …` for a general
deck. This is why `fiberSet_segMembership_card` builds (it computes a **card** via
`Fintype.card_subtype`, never a pointwise `.mem`), while any elementwise `Finset` inclusion/recap does
not.

**Consequence for the headline** `rhoRoundIdeal = localLift segMembership`: a *pointwise* mass proof
must decide, for a **general** `d : Perm (Fin 99)`, whether `d` is in the fiber / image — exactly the
99!-universe `.mem` that recurses. So the headline cannot be closed pointwise at N=99 without a
fundamentally different route that avoids the 99! `Finset` entirely:

1. **Fintype-level equinumerosity** — prove the within-pile-pairs `Fintype` and the fiber `Fintype`
   `{d // membership d = segMembership}` are `Equiv` (a `Fintype.card`-level bijection, no `Finset.mem`),
   then transport the uniform law across the equiv. Risk: constructing that `Equiv` is essentially the
   `fiberOrbit_equiv` bijection, which is where the original `.val` wall came from — so this may just
   relocate the wall. Verify at the *card* level first (`Fintype.card_subtype`), which is known-good.
2. **A distributional (non-pointwise) argument** — show both laws are the unique uniform law on the
   same `50!·49!`-element `Fintype` via their *marginals/moment* structure, without deciding any
   individual deck's membership. This would need a characterization lemma that doesn't reference the
   99! `Finset`.

Both are genuinely open; neither is a `maxHeartbeats` bump (forbidden by build discipline). The
three wall-free lemmas (`leftCards_embed_eq_segLeft`, `membership_embed_eq_segMembership`,
`withinPile_pairs_card`) are the durable, committed content of this work.

## Fintype-card asymmetry (final probe this session)

- `Fintype.card {d : Perm (Fin 99) // membership d = segMembership}` **builds** (this is exactly what
  `fiberSet_segMembership_card` proves, `= 50!·49!`).
- `Fintype.card {d : Perm (Fin 99) // leftCards d = segLeft}` **recurses** (`maximum recursion depth
  has been reached`) — even as a bare goal type, before any proof.

So the *membership-record* subtype is well-behaved under `Fintype.card` (its `Membership` records have
a decidable instance Lean can normalize), while the *Finset-equality* predicate (`leftCards d = segLeft`)
triggers recursion in the same machinery. Net: the Fintype-equinumerosity route (route 1) must be
carried on the **membership-subtype** (the one that computes), not the leftCards-subtype — and building
the actual `Equiv` (within-pile pairs ≃ membership-fiber) is where the original `fiberOrbit_equiv` `.val`
wall reappears. **This is a genuinely hard, multi-week elaborator battle, not a one-session item.**

**Recommended disposition:** leave the batch-5b headline parked at this wall. The on-mission result
(`TV < 1/1000`) is already met and committed independently (the 3-round headline + the 41-exchange
`DobrushinDecay99`). The three wall-free lemmas here are the durable yield. If a future session wants to
resume, start from the *membership-subtype* (computes) and attempt the `Equiv` construction at the
`Fintype` level, verifying each step only at the *card* level (never `Finset.mem` / pointwise over the
99! `Finset`). Do **not** use `maxHeartbeats`/`set_option` bumps.
