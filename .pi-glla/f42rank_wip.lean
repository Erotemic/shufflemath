/-!
F4.2 last-wall WIP — the sorted-key rank as a *genuine* finite permutation.
==========================================================================
The "last F4 wall" (Section 3 of `docs/planning/proof-strategies/
2026-11-20-deep-structural-hints-for-qwen.md`): turn `GSR.idealShuffle`'s output
into a real finite permutation of the deck positions and preserve the law.

Root blocker (this session): this Mathlib has **no `DecidableRel` instance for
the lexicographic `<` on a product type** — probed both `Nat × Nat` and
`Fin a × Fin n`, and `Finset.filter` fails on both.  The fix is to **flatten the
lex key to a single `Nat`**:

    keyNat i = (ℓ i).val * n + i.val

whose `<` *is* the lexicographic order on `(ℓ i).val, i.val` (for `i,j < n`,
`keyNat i < keyNat j ↔ (ℓ i).val < (ℓ j).val ∨ (ℓ i).val = (ℓ j).val ∧ i < j`),
and whose `<` is decidable.  Everything below is built on that.

Progress:
  * `keyNat`, `keyBelow`, `rankVal` — defs (build clean).
  * **`keyNat_injective` — PROVEN** (this session): two equal flattened keys are
    congruent mod `n` (`Nat.mul_modulus_add_modEq_iff`), which forces equal
    indices (both `< n`, via `Nat.mod_eq_of_lt`).
  * **`rank_orderPreserve` — next resumption point** (`sorry`): smaller key
    ⇒ smaller rank, by the disjoint-union proper-subset decomposition
    (documented in its docstring).
Then the next layer: `rankEquiv` (`Equiv.ofBijective` +
`Finite.surjective_of_injective`), then `stableBuckets a ℓ (List.range n) =
orderByNewPosition (rank_ℓ.symm)`, then `ν_{n,a}` as the pushforward of
`GSR.uniformLabels`, then the deck-level law via `CommanderDeckGSR.pileRelabelEquiv`.
-/

module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq

@[expose]
public section F42RankWip

open Finset

/- The flattened lex key: `(ℓ i).val * n + i.val`.  For `i,j < n`,
   `keyNat i < keyNat j ↔ (ℓ i).val < (ℓ j).val ∨ (ℓ i).val = (ℓ j).val ∧ i < j`,
   i.e. it is exactly the lexicographic order, and `<` is decidable. -/
def keyNat (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (ℓ i).val * n + i.val

/- The set of elements whose key is strictly below `i`'s (the "initial segment
   before `i`" in the sorted order). -/
def keyBelow (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => keyNat n a ℓ k < keyNat n a ℓ i)

/- The rank: how many keys are strictly below `i`'s.  This is the order-
   preserving map the permutation is built from. -/
def rankVal (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (keyBelow n a ℓ i).card

/- **Sub-goal 1 — PROVEN** (`keyNat` is an injection for `0 < n`). Two equal
   flattened keys are congruent mod `n`, which forces equal indices: both
   `i.val` and `j.val` are `< n`, so equal mod `n` ⇒ equal. -/
theorem keyNat_injective (n a : Nat) (_hn : 0 < n) (ℓ : Fin n → Fin a) :
    Function.Injective (keyNat n a ℓ) := by
  intro i j h
  have hL : keyNat n a ℓ i ≡ i.val [MOD n] := by
    rw [keyNat]
    exact Nat.mul_modulus_add_modEq_iff.mpr (Nat.ModEq.rfl)
  have hR : keyNat n a ℓ j ≡ j.val [MOD n] := by
    rw [keyNat]
    exact Nat.mul_modulus_add_modEq_iff.mpr (Nat.ModEq.rfl)
  have hmid : keyNat n a ℓ i ≡ keyNat n a ℓ j [MOD n] := by
    simpa [h] using (Nat.ModEq.rfl : keyNat n a ℓ i ≡ keyNat n a ℓ i [MOD n])
  have hval : i.val ≡ j.val [MOD n] := (hL.symm).trans hmid |>.trans hR
  have heq : i.val = j.val := by
    rw [Nat.ModEq] at hval
    simpa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hval
  exact Fin.ext heq

/- **Sub-goal 3 — NEXT RESUMPTION POINT** (order-preservation: smaller key ⇒
   smaller rank).  `keyBelow i` is a PROPER subset of `keyBelow j`: it is
   contained (transitivity of the key-order) and it *misses* `i`, which itself
   lies in `keyBelow j` (since `keyNat i < keyNat j`).  The strict-cardinality
   inequality then follows from the disjoint-union decomposition

       keyBelow j = keyBelow i ∪ (keyBelow j \ keyBelow i)

   with `(keyBelow j \ keyBelow i).Nonempty` (it contains `i`), giving
   `|keyBelow j| = |keyBelow i| + |keyBelow j \ keyBelow i| > |keyBelow i|`.

   The one fiddly bit (worked in an earlier probe): the `let`-bound
   `Si`/`Sj` must be unfolded with `dsimp` (not `dsimp only`) so the
   set-membership goals reduce; the `⟨…⟩` for `Finset.mem_sdiff` is a plain
   conjunction. -/
theorem rank_orderPreserve (n a : Nat) (ℓ : Fin n → Fin a) (i j : Fin n)
    (hk : keyNat n a ℓ i < keyNat n a ℓ j) :
    rankVal n a ℓ i < rankVal n a ℓ j := by
  sorry

end F42RankWip
end Shufflemath
