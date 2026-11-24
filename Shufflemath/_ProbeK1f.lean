module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.CommanderPermutation

@[expose]
public section

namespace ShufflemathProbe2

open Finset
open Fin
open Shufflemath.FiniteDeck
open Shufflemath.CommanderPermutation

theorem h50le99 : 50 ≤ 99 := by
  norm_num

theorem K1f_appEquiv
    (d : Deck)
    (L : Finset (Fin 50)) (R : Finset (Fin 49))
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R})
    (i : Fin 50) (hi : i ∈ L) :
    (swapPerm 99 50 h50le99 L R b) (leftPosition 99 50 h50le99 i) =
      (swapFn 99 50 h50le99 L R b) (leftPosition 99 50 h50le99 i) := by
  change (swapFn 99 50 h50le99 L R b) (leftPosition 99 50 h50le99 i) =
      (swapFn 99 50 h50le99 L R b) (leftPosition 99 50 h50le99 i)
  rfl

end ShufflemathProbe2
