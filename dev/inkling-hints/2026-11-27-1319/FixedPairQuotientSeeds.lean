import Shufflemath.FiniteDeck.FixedPairExchange
import Shufflemath.ReversibleQuotient

/-! Candidates against 06fd99f. The reverse witness and microscopic
stationarity are already compiled in FixedPairExchange. Do not re-prove them.
This file only packages the existing results into the remaining interfaces.
Compile before promoting; no claims of independent Lean verification. -/
namespace Shufflemath.FiniteDeck.Nov27At1319
open Classical
variable {N p c : Nat} {n : Fin p → Nat}

-- Extract the local hsym from fixedPairKernel_uniformStationary as an export.
-- This is state symmetry, NOT fixedPairKernel_swap (i/j symmetry).
theorem state_symmetric (A B : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) :
    Dist.mass (fixedPairKernel A i j k hij hki hkj) B =
      Dist.mass (fixedPairKernel B i j k hij hki hkj) A := by
  classical
  rw [fixedPairKernel_mass A i j k hij hki hkj B,
      fixedPairKernel_mass B i j k hij hki hkj A]
  have hiff := fixedPairAlloc_swap_iff A B i j k hij
  by_cases h : ∃ z, fixedPairAlloc A i j k hij z = B
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h2 => h (hiff.mpr h2))]

noncomputable def K (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) : FiniteKernel (Allocation N p n) (Allocation N p n) :=
  fun A => fixedPairKernel A i j k hij hki hkj

abbrev HistState (color : Fin N → Fin c) :=
  @GenericQuotient.ReachObs (Allocation N p n) (Fin p × Fin c → Int) (signedHist color)

noncomputable def Q (color : Fin N → Fin c) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) :
    FiniteKernel (HistState (n := n) color) (HistState (n := n) color) :=
  GenericQuotient.quotient (signedHist color) (K (N := N) i j k hij hki hkj)

theorem row (color : Fin N → Fin c) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) (A : Allocation N p n) :
    ((K i j k hij hki hkj) A).map (histObserve N p c n color) =
      (Q color i j k hij hki hkj) (histObserve N p c n color A) := by
  exact (GenericQuotient.quotient_at (signedHist color) (K (N := N) i j k hij hki hkj)
    (fun A B h => fixedPairKernel_strong_lumpable color A B h i j k hij hki hkj) A).symm

theorem square (color : Fin N → Fin c) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) :
    FiniteKernel.comp (K (N := N) i j k hij hki hkj)
      (FiniteKernel.deterministic (histObserve N p c n color)) =
    FiniteKernel.comp (FiniteKernel.deterministic (histObserve N p c n color))
      (Q color i j k hij hki hkj) := by
  exact GenericQuotient.quotient_intertwines (signedHist color) (K (N := N) i j k hij hki hkj)
    (fun A B h => fixedPairKernel_strong_lumpable color A B h i j k hij hki hkj)

-- Direct corollary of the latest commit; no new detailed-balance sum.
theorem stationary (hsum : (∑ i, n i) = N) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) :
    Stationary (uniformAlloc hsum) (K (N := N) i j k hij hki hkj) := by
  ext A
  exact fixedPairKernel_uniformStationary hsum i j k hij hki hkj A

theorem quotient_stationary (hsum : (∑ i, n i) = N) (color : Fin N → Fin c)
    (i j : Fin p) (k : Nat) (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) :
    Stationary (histStationary N p c n hsum color) (Q color i j k hij hki hkj) := by
  exact GenericQuotient.quotient_stationary (signedHist color) (K (N := N) i j k hij hki hkj)
    (fun A B h => fixedPairKernel_strong_lumpable color A B h i j k hij hki hkj)
    (uniformAlloc hsum) (stationary hsum i j k hij hki hkj)

theorem run_observe (color : Fin N → Fin c) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) (t : Nat) (μ : Dist (Allocation N p n)) :
    (FiniteKernel.run (K i j k hij hki hkj) t μ).map (histObserve N p c n color) =
      FiniteKernel.run (Q color i j k hij hki hkj) t (μ.map (histObserve N p c n color)) := by
  exact GenericQuotient.run_observation (histObserve N p c n color)
    (K (N := N) i j k hij hki hkj) (Q color i j k hij hki hkj)
    (square color i j k hij hki hkj) t μ

-- Reuse the same uniform mass and the exported symmetry. Do not infer
-- reversibility merely from the (weaker) stationary law.
theorem detailed_balance (hsum : (∑ i, n i) = N) (i j : Fin p) (k : Nat) (hij : i ≠ j)
    (hki : k ≤ n i) (hkj : k ≤ n j) :
    DetailedBalance (uniformAlloc hsum) (K (N := N) i j k hij hki hkj) := by
  classical
  letI : Nonempty (Allocation N p n) := nonemptyOfSumCapacities N p n hsum
  intro A B
  have hmx : Dist.mass (uniformAlloc hsum) A = (Fintype.card (Allocation N p n) : Rat)⁻¹ := by
    change Dist.mass (GSR.uniformDist (Allocation N p n)) A = _
    exact GSR.mass_uniformDist A
  have hmy : Dist.mass (uniformAlloc hsum) B = (Fintype.card (Allocation N p n) : Rat)⁻¹ := by
    change Dist.mass (GSR.uniformDist (Allocation N p n)) B = _
    exact GSR.mass_uniformDist B
  change Dist.mass (uniformAlloc hsum) A * Dist.mass (fixedPairKernel A i j k hij hki hkj) B =
    Dist.mass (uniformAlloc hsum) B * Dist.mass (fixedPairKernel B i j k hij hki hkj) A
  rw [hmx, hmy, state_symmetric A B i j k hij hki hkj]

theorem quotient_reversible (hsum : (∑ i, n i) = N) (color : Fin N → Fin c)
    (i j : Fin p) (k : Nat) (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) :
    DetailedBalance (histStationary N p c n hsum color) (Q color i j k hij hki hkj) := by
  classical
  letI : Fintype (HistState (n := n) color) :=
    Fintype.ofSurjective (histObserve N p c n color) (GenericQuotient.observe_surjective (signedHist color))
  intro y z
  exact ReversibleQuotient.reversible_quotient (uniformAlloc hsum) (K (N := N) i j k hij hki hkj)
    (histObserve N p c n color) (Q color i j k hij hki hkj)
    (row color i j k hij hki hkj) (detailed_balance hsum i j k hij hki hkj) y z

-- Same explicit instance interface as histStationary_uniform_fiber_lift.
-- The macro type is the reachable subtype, not the full Int-function type.
theorem quotient_fiber_lift (color : Fin N → Fin c)
    (i j : Fin p) (k : Nat) (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j)
    [FI : Fintype (HistState (n := n) color)]
    [DEQ : DecidableEq (HistState (n := n) color)]
    [DL : DecidableEq (Allocation N p n)] [NE : Nonempty (Allocation N p n)] :
    FiniteKernel.comp
      (FiberDisintegration.fiberLaw (histObserve N p c n color) (GenericQuotient.observe_surjective (signedHist color)))
      (K (N := N) i j k hij hki hkj) =
    FiniteKernel.comp (Q color i j k hij hki hkj)
      (FiberDisintegration.fiberLaw (histObserve N p c n color) (GenericQuotient.observe_surjective (signedHist color))) := by
  exact ReversibleQuotient.fiberLaw_comp_eq_quotient_fiberLaw
    (histObserve N p c n color) (GenericQuotient.observe_surjective (signedHist color))
    (K (N := N) i j k hij hki hkj) (Q color i j k hij hki hkj)
    (row color i j k hij hki hkj) (fun x t => state_symmetric x t i j k hij hki hkj)

end Shufflemath.FiniteDeck.Nov27At1319
