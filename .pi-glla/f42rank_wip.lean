module
public import Shufflemath.GSR
public import Shufflemath.Finite
public import Mathlib
@[expose] public section

namespace Shufflemath
namespace F42RankWip

/-! # F4.2 last-wall — WIP starting point (rank construction)

Session WIP: the sorted-key **rank as a genuine permutation**, the first step of
Section 3 of `docs/planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md`
(the "second permutation shortcut: replace list validity by sorted-key ranks").

## The one root blocker (and its fix)
`Finset.filter (fun k => (ℓ k, k) < (ℓ i, i))` does NOT elaborate: this Mathlib
has **no `DecidableRel` instance for the lexicographic `<` on a product type**
(neither `Nat × Nat` nor `Fin a × Fin n`; both probed). The fix is to **flatten
the lex key into a single `Nat`**: `keyNat i = (ℓ i).val * n + i.val`, whose `<`
*is* the lex order (label major, index minor) and `Nat.<` is decidable.

## Sub-goals, in order
1. `keyNat_injective` — `keyNat` is an injection for `0 < n`.  Route: reduce
   `keyNat i = keyNat j` modulo `n`.  `add_modulus_mul_modEq_iff`
   (`a + n*b ≡ c [MOD n] ↔ a ≡ c [MOD n]`) gives `keyNat i ≡ i.val [MOD n]`;
   hence `i.val ≡ j.val [MOD n]`, and since `i.val, j.val < n` and `0 < n`,
   `i.val % n = i.val` / `j.val % n = j.val` force `i.val = j.val`.  (Find the
   exact `mod_eq_of_lt`-style lemma; the inequality route keeps a `*` of two
   unknowns, which `omega`/`nlinarith` refuse.)
2. `rank_lt_iff` — `rank i < rank j ↔ rankVal i < rankVal j` (`simp [rank, rankVal]`).
3. `rank_orderPreserve` — `keyNat i < keyNat j → rank i < rank j`.  `keyBelow i`
   is a proper subset of `keyBelow j` (it misses `i`, which has `keyNat i < keyNat j`);
   prove the strict card inequality by the disjoint-union decomposition
   `keyBelow j = keyBelow i ∪ (keyBelow j \ keyBelow i)` + `card_union_of_disjoint`
   + `(Sj \ Si).Nonempty` (contains `i`).  This pattern is already written and
   checked in the earlier `keyBelow`-product version — port it to `keyNat`.
4. `rankEquiv` — `Equiv.ofBijective (fun i => rank n a ℓ i) ⟨hinj,
   Finite.surjective_of_injective hinj⟩`; injectivity = distinct positions have
   distinct, totally-ordered keys (`lt_or_gt_of_ne`) + `rank_orderPreserve`.

## Then (later layers, not yet started)
- `stableBuckets_eq_orderByNewPosition` (the pointwise sort statement:
  `stableBuckets a ℓ (List.range n) = orderByNewPosition (rank_ℓ.symm)`).
- `ν_{n,a}` = pushforward of `GSR.uniformLabels n a ha` through the
  sorted-key permutation map → `Dist (Equiv.Perm (Fin n))`.
- Deck-level: lift to `Deck` via `CommanderDeckGSR.pileRelabelEquiv` (already
  built) and match the `gsrProductKernel_eq_distProductFinsupp` identity.

NOTE: this file is a WIP record (lives in `.pi-glla/`, not a build target).  The
defs below build; the four theorems are left as marked `sorry` resumption points.
-/

/-- The flattened sorting key of position `i` under `ℓ` (see header). -/
def keyNat (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (ℓ i).val * n + i.val

/-- The set of positions with a strictly smaller key than `i`. -/
noncomputable def keyBelow (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => keyNat n a ℓ k < keyNat n a ℓ i)

/-- The rank value of `i`. -/
noncomputable def rankVal (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (keyBelow n a ℓ i).card

/-- **Sub-goal 1** (`keyNat` is an injection for `0 < n`). -/
theorem keyNat_injective (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    Function.Injective (keyNat n a ℓ) := by
  -- WIP: reduce `keyNat i = keyNat j` mod n via `add_modulus_mul_modEq_iff`,
  -- then `i.val ≡ j.val [MOD n]` + `i.val, j.val < n` → `i.val = j.val`.
  sorry

/-- **Sub-goal 3** (order-preservation: smaller key ⇒ smaller rank). -/
theorem rank_orderPreserve (n a : Nat) (ℓ : Fin n → Fin a) (i j : Fin n)
    (hk : keyNat n a ℓ i < keyNat n a ℓ j) :
    rankVal n a ℓ i < rankVal n a ℓ j := by
  -- WIP: proper-subset disjoint-union decomposition (see header).
  sorry

end F42RankWip
end Shufflemath
