module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderFiberCount
public import Shufflemath.FinsetCombinatorics
public import Shufflemath._Probe47p
public import Shufflemath._Probe47s
public import Shufflemath._Probe47t
public import Shufflemath._Probe47v
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace
open CommanderMarkedRightCount
open Finset

namespace _Probe47u

/-!
# perDeckBridge

Connects the physical A3 count
`# { (L, R) : (newLeftCards d L R ∩ leftOrigSet).card = n }`
to the Bernoulli-Laplace numerator `transitionNumerator 99 50 25 (leftOriginalCount d) n`.

Two-step composition:
(1) `newLeftOriginalCount_eq` makes the physical count equal to the marked
    const-sub count `# { (L,R) : (leftOriginalCount d - markedInLeft d L) + markedInRight d R = n }`;
(2) `_Probe47v.transitionNumerator_eq_fiberProduct` (the proved F3 A3 kernel) makes that
    marked const-sub count equal to the transition numerator.
-/

variable {d : Deck}

abbrev s50 : Finset (Finset (Fin 50)) := (Finset.univ : Finset (Fin 50)).powersetCard 25
abbrev t49 : Finset (Finset (Fin 49)) := (Finset.univ : Finset (Fin 49)).powersetCard 25

-- The per-deck bridge: the physical count equals the Bernoulli-Laplace numerator.
theorem perDeckBridge (n : Nat) :
    ((s50 ×ˢ t49).filter
      (fun p : Finset (Fin 50) × Finset (Fin 49) =>
        (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
    transitionNumerator 99 50 25 (leftOriginalCount d) n := by
  -- (1) newLeftCards-count filter  =  marked const-sub filter  (pointwise, via newLeftOriginalCount_eq).
  have hfilt :
      (s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n) =
      (s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, newLeftOriginalCount_eq d p.1 p.2]
  -- (2) count the filter, then apply 47v's proved kernel (marked const-sub count = transition numerator).
  have hcount :
      ((s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
      ((s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n)).card := by
    simp [hfilt]
  exact hcount.trans (_Probe47v.transitionNumerator_eq_fiberProduct d n).symm

end _Probe47u
end Shufflemath
