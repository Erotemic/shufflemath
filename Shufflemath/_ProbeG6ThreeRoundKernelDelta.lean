module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.Perturbation
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.Gate6FiniteGSR
public import Shufflemath.Gate6Crux
public import Shufflemath.GSRDeckRound

@[expose]
public section

namespace Shufflemath

open CommanderPermutation

/-!
## Gate 6 (3-round headline) — sub-lemma A: the A3 per-round bound on the
swap-composed 3-round finite kernel.

The 3-round finite round is `comp (PAK swapLaw) (PAK rho99Finite)`: the left
physical shuffle (swap) first, then the A3 perfect-shuffle round (resample +
exchange). This file proves that its per-round kernel discrepancy against the
swap-composed ideal round `comp (PAK swapLaw) (PAK rho99Ideal)` is at most the
per-round collision budget `δ1`.

The proof decomposes each row through the swap law's action law: both the
finite and ideal rows are the `PAK` action of `swapLaw` on `x` post-composed
with the A3 finite/ideal kernel, so the per-row discrepancy is exactly
`apply_discrepancy_bound` (the A1 mixture bound) between the A3 finite and
ideal kernels. That A3 bound is then `≤ TV(rho99Finite, rho99Ideal)` by the
`tv_map_contraction` row bound and `≤ δ1` by the already-proved
`oneRoundDeckTV_le_delta1`.

`convContraction` cannot be used here: it contracts on the *right* side of a
composition, but the two kernels that differ (finite vs ideal A3) are the
*inner* (right) factor while the shared `PAK swapLaw` is the *left* (outer)
factor — so the row decomposition through the `PAK` action law is the
right route. No oracle, no `native_decide`, no `native_defeq`/`WHNF` wall. -/

-- The one-card commander deck state, as a full deck permutation.
abbrev g6ThreeRoundDeck := Equiv.Perm (Fin 99)

/-- The finite 3-round round kernel: swap (left shuffle) first, then the A3
    physical perfect-shuffle round (resample + exchange). -/
noncomputable def g6ThreeRoundFiniteRound : FiniteKernel Deck Deck :=
  FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
    (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)

/-- Sub-lemma A: the per-round kernel discrepancy between the finite round
    `comp (PAK swapLaw) (PAK rho99Finite)` and the ideal round
    `comp (PAK swapLaw) (PAK rho99Ideal)` is at most the per-round collision
    budget `δ1`. -/
theorem g6_threeRound_kernelDiscrepancy_le_δ1 :
    kernelDiscrepancy g6ThreeRoundFiniteRound
      (FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)) ≤ δ1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  set νx := (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw) x with hνx
  have hK : g6ThreeRoundFiniteRound x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite) := by
    simp only [g6ThreeRoundFiniteRound, FiniteKernel.comp, FiniteKernel.apply, hνx]
  have hL : (FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
          (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal)) x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
    simp only [FiniteKernel.comp, FiniteKernel.apply, hνx]
  rw [hK, hL]
  have hA1 := apply_discrepancy_bound
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) νx
  calc
    _ ≤ kernelDiscrepancy (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := hA1
    _ ≤ Dist.tv Gate6Crux.rho99Finite Gate6Crux.rho99Ideal := by
        unfold kernelDiscrepancy
        apply Finset.max'_le
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨y, _, rfl⟩
        simpa only [FiniteDeck.permutationActionKernel_eq_map]
          using Dist.tv_map_contraction Gate6Crux.rho99Finite Gate6Crux.rho99Ideal (·.trans y)
    _ ≤ δ1 := by
        rw [δ1_eq_2401_over_8388608]
        simpa only [Gate6Crux.rho99Finite, Gate6Crux.rho99Ideal] using oneRoundDeckTV_le_delta1

end Shufflemath
