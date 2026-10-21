import Shufflemath.BernoulliLaplace
import Shufflemath.Matrix

namespace Shufflemath
namespace BernoulliLaplace

/-!
# Relating materialized Commander certificates to `Dist` / `FiniteKernel`

The existing 50-entry arrays make rational computations tractable for
`native_decide`; they are not a second probability model. This file proves
that each array update agrees pointwise with application of the semantic
Markov kernel, and that array iteration agrees with `FiniteKernel.run`.
Therefore the existing exact rational certificates are also statements
about the authoritative `StdSimplex` distributions.
-/

private theorem arrayGet_ofFn (f : CommanderState → Rat) (x : CommanderState) :
    commanderArrayGet (Array.ofFn f) x = f x := by
  simp [commanderArrayGet, x.isLt]

private theorem tableGet_eq_matrix (x y : CommanderState) :
    commanderTableGet commanderExchange25Table x y =
      commanderExchange25Matrix x y := by
  simp [commanderTableGet, commanderExchange25Table, x.isLt, y.isLt]

/-- The computational transition table is exactly the matrix of the
semantic quarter-deck exchange kernel. -/
theorem commanderTableGet_eq_mass (x y : CommanderState) :
    commanderTableGet commanderExchange25Table x y =
      Dist.mass (commanderExchange25 x) y := by
  rw [tableGet_eq_matrix]
  have h := FiniteKernel.toMatrix_ofRowStochastic
    commanderExchange25Matrix commanderExchange25Matrix_rowStochastic
  have hxy := congrFun (congrFun h x) y
  simpa only [FiniteKernel.toMatrix, commanderExchange25] using hxy.symm

/-- One array update agrees pointwise with the semantic kernel application,
for **any** array representing the input distribution. -/
theorem stepCommanderArray_eq_apply (p : CommanderArray) (mu : Dist CommanderState)
    (h : ∀ x, commanderArrayGet p x = Dist.mass mu x)
    (y : CommanderState) :
    commanderArrayGet (stepCommanderArray p commanderExchange25Table) y =
      Dist.mass (FiniteKernel.apply mu commanderExchange25) y := by
  calc
    _ = ∑ x : CommanderState,
          commanderArrayGet p x * commanderTableGet commanderExchange25Table x y :=
      arrayGet_ofFn _ y
    _ = ∑ x : CommanderState,
          Dist.mass mu x * Dist.mass (commanderExchange25 x) y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h x, commanderTableGet_eq_mass]
    _ = Dist.mass (FiniteKernel.apply mu commanderExchange25) y :=
      (FiniteKernel.apply_mass mu commanderExchange25 y).symm

/-- The same semantic bridge after an arbitrary number of array steps.
The induction is generalized over the initial array/distribution; this
matches the array implementation's `run n (step p P)` recursion. -/
theorem runCommanderArray_eq_run (n : Nat) (p : CommanderArray)
    (mu : Dist CommanderState)
    (h : ∀ x, commanderArrayGet p x = Dist.mass mu x)
    (y : CommanderState) :
    commanderArrayGet (runCommanderArray commanderExchange25Table n p) y =
      Dist.mass (FiniteKernel.run commanderExchange25 n mu) y := by
  induction n generalizing p mu with
  | zero => exact h y
  | succ n ih =>
      change commanderArrayGet
          (runCommanderArray commanderExchange25Table n
            (stepCommanderArray p commanderExchange25Table)) y =
        Dist.mass (FiniteKernel.run commanderExchange25 n
          (FiniteKernel.apply mu commanderExchange25)) y
      exact ih _ _ (stepCommanderArray_eq_apply p mu h)

private theorem initialArray_eq_mass (x : CommanderState) :
    commanderArrayGet commanderInitialArray x =
      Dist.mass (Dist.pointMass commanderSegregatedState) x := by
  rw [show commanderArrayGet commanderInitialArray x = commanderInitialVector x from
    arrayGet_ofFn commanderInitialVector x]
  simp [commanderInitialVector, Dist.mass_pointMass]

private theorem stationaryArray_eq_mass (x : CommanderState) :
    commanderStationaryVector x = Dist.mass commanderStationary x := by
  exact (Dist.mass_ofFun commanderStationaryVector
    commanderStationaryVector_nonneg commanderStationaryVector_total x).symm

/-- Array-based `n`-step evolution agrees with the semantic `run` law. -/
theorem commanderRun25_eq_mass (n : Nat) (x : CommanderState) :
    commanderArrayAsVector (commanderRun25 n) x =
      Dist.mass (FiniteKernel.run commanderExchange25 n
        (Dist.pointMass commanderSegregatedState)) x := by
  change commanderArrayGet
      (runCommanderArray commanderExchange25Table n commanderInitialArray) x = _
  exact runCommanderArray_eq_run n commanderInitialArray
    (Dist.pointMass commanderSegregatedState) initialArray_eq_mass x

/-- A universal bridge: for any step count, exact TV of the materialized
vectors equals TV of the semantic distributions. The large rational
calculations stay in the original `native_decide` certificates. -/
theorem commander_run25_tv_semantic (n : Nat) :
    Dist.tv (FiniteKernel.run commanderExchange25 n
      (Dist.pointMass commanderSegregatedState)) commanderStationary =
      vectorTV (commanderArrayAsVector (commanderRun25 n))
        commanderStationaryVector := by
  unfold Dist.tv
  refine congrArg₂ (vectorTV (alpha := CommanderState)) ?_ ?_
  · funext x
    exact (commanderRun25_eq_mass n x).symm
  · funext x
    exact (stationaryArray_eq_mass x).symm

/-- The exact two-exchange result, now expressed directly in `Dist.tv` and
`FiniteKernel.run`. This is a corollary of the existing computational
certificate, not a second calculation. -/
theorem commander_tv_after_two_semantic :
    Dist.tv (FiniteKernel.run commanderExchange25 2
      (Dist.pointMass commanderSegregatedState)) commanderStationary =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  rw [commander_run25_tv_semantic]
  exact commander_tv_after_two_exchange25

/-- Same bridge for the three-exchange exact rational certificate. -/
theorem commander_tv_after_three_semantic :
    Dist.tv (FiniteKernel.run commanderExchange25 3
      (Dist.pointMass commanderSegregatedState)) commanderStationary =
      (172379525755689183991816396516567920780192827919620440221147749 /
        6691837923759692633601708022649918108038775216019298375918637677488 : Rat) := by
  rw [commander_run25_tv_semantic]
  exact commander_tv_after_three_exchange25

end BernoulliLaplace
end Shufflemath
