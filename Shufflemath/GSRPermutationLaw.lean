module

public import Shufflemath.GSR
public import Shufflemath.GSRF42
public import Shufflemath.GSRF42KeyOrder
public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open GSR

namespace PermutationLaw

/-!

## F4.2 — "preserve the law": the GSR as a permutation action

Section 3 of `docs/planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md`
says the last F4 wall has two halves:

1. **Turn the `idealShuffle` output into a genuine permutation** — the
   `rankEquiv` construction and the pointwise capstone
   `stableBuckets a ℓ (finRange n) = (finRange n).map (rankEquiv ℓ).symm`
   (proved in `GSRF42KeyOrder.stableBuckets_eq_orderByNewPosition`); and
2. **Preserve the law** — the GSR is a random-permutation *action*, not a
   list-validity fallback.

This module is the second half: it names the GSR's law as a distribution on
`Equiv.Perm (Fin n)` (`gsrPermutationLaw`, the `ν_{n,a}` of Section 3) and
proves the GSR on the canonical deck is that law pushed through "apply the
permutation to the deck".

-/

/-- The **permutation law**: the GSR `a`-shuffle applied to the canonical deck
    `finRange n` equals the pushforward of the uniform label law through the
    sorted-key permutation map. Each label assignment `ℓ` produces the deck
    reordered by `rankEquiv ℓ .symm`, so the GSR is a genuine
    random-permutation action on the canonical deck (no invalid-list fallback).
    Direct consequence of `stableBuckets_eq_orderByNewPosition`. -/
theorem idealShuffle_canonical_eq_permPushforward (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    idealShuffle n a ha (List.finRange n) =
    (uniformLabels n a ha).map (fun ℓ : Fin n → Fin a => (List.finRange n).map (rankEquiv n a hn ℓ).symm) := by
  dsimp only [idealShuffle, labelShuffle]
  congr 1
  funext ℓ
  exact stableBuckets_eq_orderByNewPosition n a ha hn ℓ

/-- The GSR `a`-shuffle viewed as a **law on permutations**: the pushforward of the
    uniform label law through the sorted-key permutation `rankEquiv`. This is the
    object `ν_{n,a}` of Section 3 — a `Dist` on `Equiv.Perm (Fin n)`, so the GSR is a
    genuine random-permutation action (no `Fintype (List (Fin n))` needed). -/
noncomputable def gsrPermutationLaw (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    Dist (Equiv.Perm (Fin n)) :=
  (uniformLabels n a ha).map (fun ℓ => rankEquiv n a hn ℓ)

/-- Factored form of the permutation law: the GSR on the canonical deck is the
    `gsrPermutationLaw` pushed forward through "apply the permutation to the
    canonical deck". -/
theorem idealShuffle_canonical_eq_permLaw (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    idealShuffle n a ha (List.finRange n) =
    (gsrPermutationLaw n a ha hn).map (fun (σ : Equiv.Perm (Fin n)) => (List.finRange n).map σ.symm) := by
  rw [idealShuffle_canonical_eq_permPushforward n a ha hn]
  -- LHS is now `uniformLabels.map (fun ℓ => (finRange n).map (rankEquiv n a hn ℓ).symm)`;
  -- unfold the RHS and collapse the two maps into one.
  unfold gsrPermutationLaw
  rw [Convexity.StdSimplex.map_map]
  -- both sides collapse to `uniformLabels.map (fun x => (finRange n).map (rankEquiv n a hn x).symm)`

end PermutationLaw
end Shufflemath
