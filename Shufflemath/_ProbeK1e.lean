module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile

@[expose]
public section

namespace ShufflemathProbe

open Finset
open Fin
open Shufflemath.FiniteDeck

theorem h50le99 : 50 ≤ 99 := by
  norm_num

theorem K1e_bridge (i : Fin 50) (hxl : (leftPosition 99 50 h50le99 i).val < 50) :
    (⟨(leftPosition 99 50 h50le99 i).val, hxl⟩ : Fin 50) = i := by
  apply Fin.ext
  dsimp only [leftPosition, castLE]

end ShufflemathProbe
