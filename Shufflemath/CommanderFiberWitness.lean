import Shufflemath.CommanderPermutation
import Mathlib.Tactic

namespace Shufflemath
namespace CommanderPermutation

/-!
# An explicit deck in every Commander macrostate fiber

The original `uniformFiber` construction required a proof that each of the
50 possible marked-card counts was represented by an actual 99-card deck.
Here that proof is supplied constructively, without enumerating the 99!
possible permutations.

For macrostate `x : Fin 50`, rotate the canonical deck by `49 - x.val` card
identities. The first 50 positions then contain exactly `x.val + 1` of the
50 marked cards. The permutation is a genuine equivalence of `Fin 99`.
The final finite check has only 50 states and at most 50 membership tests
per state, not a computation over the permutation group.
-/

/-- Cyclic addition of a shift to a card identity. -/
private def addShift (s i : Fin 99) : Fin 99 :=
  ⟨(i.val + s.val) % 99, Nat.mod_lt _ (by decide)⟩

/-- Cyclic subtraction of the same shift. -/
private def subShift (s i : Fin 99) : Fin 99 :=
  ⟨(i.val + 99 - s.val) % 99, Nat.mod_lt _ (by decide)⟩

private theorem subShift_addShift (s i : Fin 99) :
    subShift s (addShift s i) = i := by
  apply Fin.ext
  dsimp [subShift, addShift]
  have hs := s.isLt
  have hi := i.isLt
  omega

private theorem addShift_subShift (s i : Fin 99) :
    addShift s (subShift s i) = i := by
  apply Fin.ext
  dsimp [subShift, addShift]
  have hs := s.isLt
  have hi := i.isLt
  omega

/-- A concrete 99-card cyclic permutation, with inverse and both inverse
laws proved (not asserted). -/
def rotation (s : Fin 99) : Deck where
  toFun := addShift s
  invFun := subShift s
  left_inv := subShift_addShift s
  right_inv := addShift_subShift s

/-- A canonical full deck realizing macrostate `x`. -/
def deckForCount (x : BernoulliLaplace.CommanderState) : Deck :=
  rotation ⟨49 - x.val, by have hx := x.isLt; omega⟩

/-- There are only 50 concrete count witnesses to check. The computation
uses the actual `CommanderPermutation.project`, including its proven
pigeonhole lower bound, and the genuine permutation above. -/
theorem deckForCount_projects_all :
    ∀ x : BernoulliLaplace.CommanderState, project (deckForCount x) = x := by
  native_decide

/-- Every Bernoulli--Laplace Commander macrostate is realizable by a
permutation of all 99 individually named cards. -/
theorem project_surjective : Function.Surjective project := by
  intro x
  exact ⟨deckForCount x, deckForCount_projects_all x⟩

/-- The conditional full-deck oracle no longer needs a surjectivity
hypothesis from its callers. -/
noncomputable def commanderFiberLift :
    FiniteKernel BernoulliLaplace.CommanderState Deck :=
  uniformFiber project_surjective

/-- The constructed conditional oracle really recovers its macrostate. -/
theorem commanderFiberLift_recovers :
    FiniteKernel.comp commanderFiberLift
      (FiniteKernel.deterministic project) = FiniteKernel.identity :=
  uniformFiber_recovers project_surjective

/-- The exact two-exchange distance now has *no fiber existence premise*.
The target is the lifted stationary law; identifying it with the uniform
law on all 99! permutations is a separate counting theorem. -/
theorem two_oracle_exchanges_exact_without_surjectivity_premise :
    Dist.tv
      (FiniteKernel.run (idealExchange25 project_surjective) 2
        (FiniteKernel.apply
          (Dist.pointMass BernoulliLaplace.commanderSegregatedState)
          commanderFiberLift))
      (FiniteKernel.apply BernoulliLaplace.commanderStationary
        commanderFiberLift) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  exact two_oracle_exchanges_exact project_surjective

/-- The analogous three-exchange exact rational certificate. -/
theorem three_oracle_exchanges_exact_without_surjectivity_premise :
    Dist.tv
      (FiniteKernel.run (idealExchange25 project_surjective) 3
        (FiniteKernel.apply
          (Dist.pointMass BernoulliLaplace.commanderSegregatedState)
          commanderFiberLift))
      (FiniteKernel.apply BernoulliLaplace.commanderStationary
        commanderFiberLift) =
      (172379525755689183991816396516567920780192827919620440221147749 /
        6691837923759692633601708022649918108038775216019298375918637677488 : Rat) := by
  exact OracleRefinement.commander_oracle_three_exact project
    commanderFiberLift commanderFiberLift_recovers

end CommanderPermutation
end Shufflemath
