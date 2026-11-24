module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

theorem h50le99 : 50 ≤ 99 := by
  norm_num

theorem K1c_probe
    (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    True := by
  let hm := h50le99
  set S := FiniteDeck.swapPerm 99 50 hm L R b with hS
  -- (a) shallow theorem application
  have hT : (S.trans d) (FiniteDeck.leftPosition 99 50 hm 0) =
      d (S (FiniteDeck.leftPosition 99 50 hm 0)) := Equiv.trans_apply S d (FiniteDeck.leftPosition 99 50 hm 0)
  -- (b) unfold the let only
  have hU : (FiniteDeck.swapPerm 99 50 hm L R b).trans d = S.trans d := by
    dsimp only [S]
  -- (c) force normalization of the application
  have hC : (S.trans d) (FiniteDeck.leftPosition 99 50 hm 0) =
      (FiniteDeck.swapPerm 99 50 hm L R b).trans d (FiniteDeck.leftPosition 99 50 hm 0) := by
    simp only [S]
  -- (d) membership normalization
  have hM : 0 ∈ ((Finset.univ : Finset (Fin 50)).image (fun i => (S.trans d) (FiniteDeck.leftPosition 99 50 hm i))) ↔
      ∃ i, i ∈ (Finset.univ : Finset (Fin 50)) ∧ (S.trans d) (FiniteDeck.leftPosition 99 50 hm i) = 0 := by
    rw [Finset.mem_image]
  -- (e) rcases the existential
  -- (e) rcases/use the image-membership existential (true instance: fixed point value)
  have hE : ∃ i, i ∈ (Finset.univ : Finset (Fin 50)) ∧
        (S.trans d) (FiniteDeck.leftPosition 99 50 hm i) =
          (S.trans d) (FiniteDeck.leftPosition 99 50 hm 0) := by
    use 0
    trivial
  -- (the haves above are the probe: they must elaborate; the conclusion is trivial)
  trivial

end Shufflemath
