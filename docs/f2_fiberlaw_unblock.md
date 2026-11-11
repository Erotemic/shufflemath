# F2c-iv-b: use the generic fiber law to bypass permutation pushforward normalization

**Context:** Nov 11 snapshot `9786c4b`. **Status:** a proposed route for the
next Lean proof, not a completed theorem. F1's cardinality lemmas and
`FiberDisintegration.fiberLaw` are already proved; the F2 capstone is open.

## Diagnosis

The stalled argument computes `Dist.mass ((GSR.uniformDist
(decksWithLeft m.1)).map Subtype.val) d` by opening `Finsupp.mapDomain` and
simplifying a `DecidableEq (Equiv.Perm (Fin 99))` or `Finset` equality. That
pulls the proof into huge concrete finite instances. More attempts at deep
`simp`, `whnf`, or hand-constructing permutation equality are lower priority.

**The main simplification is architectural:** `localLift` is, by definition of
its mathematical behavior, the conditional uniform law on the fiber of
`membership : Deck -> Membership`. The library already contains exactly that
construction, its pointwise mass theorem, and its recovery theorem.

## Short proof sequence

1. **Prove `membership_surjective`.** For each `m : Membership`, take a deck
   from `Nonempty (decksWithLeft m.1)`, which is already established for
   50-card sets. The deck has the requested membership by `Subtype.ext`.
   This only requires the existence proof, never enumeration of `Equiv.Perm`.
   A schematic proof shape is:

   ```lean
   theorem membership_surjective : Function.Surjective membership := by
     intro m
     obtain ⟨d⟩ : Nonempty (decksWithLeft m.1) := inferInstance
     refine ⟨d.val, ?_⟩
     apply Subtype.ext
     exact d.property
   ```

   Add `classical` only locally if instance inference needs it. Compile this
   theorem alone before changing `localLift`.

2. **Implement `localLift` using the existing generic fiber law.** Replace its
   representation through `uniformDist.map Subtype.val` by:

   ```lean
   noncomputable def localLift : FiniteKernel Membership Deck := by
     classical
     exact FiberDisintegration.fiberLaw membership membership_surjective
   ```

   This preserves the intended stochastic semantics: it selects uniformly
   among *precisely* the decks having the specified named-card left-pile
   membership. It does change the internal definition; re-prove the existing
   API theorem `localLift_preserves_membership` with
   `FiberDisintegration.fiberLaw_recovers membership membership_surjective`
   rather than retaining the old `map_const` proof. Keep the statement.
   `localLift` is not the canonical count-fiber reset.

3. **Use the existing mass theorem.** The generic
   `FiberDisintegration.fiberLaw_mass` yields directly

   ```lean
   Dist.mass (localLift m) d =
     if membership d = m then
       ((FiberDisintegration.fiberSet membership m).card : Rat)⁻¹
     else 0
   ```

   First keep this exact expression; do not rewrite the 99-card equality
   predicate under `simp` just to replace it with `leftCards d = m.1`.
   This avoids `Finsupp.mapDomain`, `Subtype.val` image-support tactics,
   and all deep pushforward normalization.

4. **Prove the constant fiber size once.** Establish a named lemma

   ```lean
   (FiberDisintegration.fiberSet membership m).card =
     Nat.factorial 50 * Nat.factorial 49
   ```

   by showing `fiberSet membership m = leftCardsFin m.1` with `Finset.ext`.
   Membership equality and left-pile-set equality are logically equivalent
   by `Subtype.ext`, without evaluating any permutation.

   Then reuse the *already compiling* finset/subtype cardinality bridge
   literally from `CommanderFiberMembership.lean`, theorem `fiberFin_card`,
   local proof `hbridge` (around lines 383–395 in this snapshot):
   `Set.toFinset_ofPred` plus `Fintype.card_of_subtype` proves
   `(leftCardsFin S).card = Fintype.card (decksWithLeft S)` without unfolding
   the `Fintype` instance. Apply `decksWithLeft_card S m.2` for the factorial
   value. Prefer extracting that existing `hbridge` into a named lemma near
   `leftCardsFin` if it helps avoid duplication, provided the downstream
   F1 proof continues to compile.

5. **Complete the two-layer mass identity.** Use the existing
   `FiniteKernel.apply_mass` (or the local `apply_mass_eq_sum`) and the new
   `fiberLaw_mass`. The membership sum is supported only at
   `m = membership d`. Use `Finset.sum_eq_single (membership d)` and explicit
   `if_pos` / `if_neg` case proofs. Do not `simp` the defining `leftCards`
   image or the `Fintype Deck` instance.

   The surviving coefficient equals the project-fiber weight because
   `fiberSet_card` (F1c) states

   ```text
   #(project fiber at x)
     = membershipFiberCount (commanderLeftCount x) * 50! * 49!
   ```

   Use `membershipFiber_iff` for support and `membershipLift`'s `ofFun`
   mass for its weight. For the nonzero denominators use the existing
   factorial/choose positivity facts; finish rational inverses only after
   the combinatorial equality has been rewritten.

6. **Build and verify.** After each small step, build
   `Shufflemath.CommanderMembershipKernels`. After the final F2 theorem,
   run `./dev/verify_next_phase.sh`; its target list includes both the
   F2 and F3 working modules. Only then return to F3's actual `rawExchange`
   kernel or F4's sorting compatibility.

## Two useful cautions

- `FiberDisintegration.fiberLaw membership membership_surjective` is a
  theorem-backed replacement *in mathematical behavior*, but the source
  implementation change has not been compiled in this overlay. Do not claim
  the F2 capstone is complete until the revised file and resulting equality
  compile under Lean 4.34.
- The exact permutation equality typeclass can be synthesized; the failure
  is caused by forcing its computational representation during large proof
  reductions. Avoiding those reductions is preferable to replacing it with
  a bespoke global instance.

## Verification gap corrected by this overlay

Previously `dev/verify_next_phase.sh` did not list
`Shufflemath.CommanderMembershipKernels` or
`Shufflemath.CommanderPhysicalExchange`, even though they contain the latest
F2/F3 changes. Both are now explicit targets. A successful Python-only test
run does not validate Lean builds; target compilation remains mandatory.
