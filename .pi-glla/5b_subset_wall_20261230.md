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
