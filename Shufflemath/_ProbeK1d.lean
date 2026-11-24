module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.CommanderPermutation

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

theorem h50le99 : 50 ≤ 99 := by
  norm_num

theorem K1d_bridge (i : Fin 50) :
    (⟨(FiniteDeck.leftPosition 99 50 h50le99 i).val, by
      dsimp only [FiniteDeck.leftPosition]
      exact i.isLt⟩ : Fin 50) = i := by
  -- probe: does the kernel delta-reduce (castLE hm i).val back to i.val?
  rfl

theorem K1d_memrcases (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    True := by
  let hm := h50le99
  set S := FiniteDeck.swapPerm 99 50 hm L R b with hS
  let f := fun i => (S.trans d) (FiniteDeck.leftPosition 99 50 hm i)
  -- DIAGNOSTIC RESULT (this session): the image-membership form builds, and
  -- `rcases` over it elaborates — PROVIDED the witness equation is `f 0 = f 0`
  -- (reflexive, no reduction). The original probe asserted `f 0 = 0`, whose
  -- `whnf` of `(swapPerm 99 50 ·).trans d (leftPosition ·)` TIMED OUT at
  -- 200,000 heartbeats — the K1b wall: a single transport application must
  -- never be `whnf`/`simp`-normalized (use `have`/`simpa`, as in K1a).
  -- SAFE pattern: prove the image membership directly (no existential form).
  have hx : f 0 ∈ (Finset.univ : Finset (Fin 50)).image f := by
    apply Finset.mem_image_of_mem
    trivial
  -- WALL (this session, bisected): after `rw [Finset.mem_image]`, closing the
  -- existential by `use 0` / `rcases` TIMES OUT at 200,000 heartbeats — the
  -- whnf of the existential motive `(S.trans d) (leftPosition 99 50 hm i)` with
  -- `i` OPEN does not terminate (concrete `f 0 = f 0` is fine; cf. K1c, which
  -- builds). So in K1b the transport must never be pushed through
  -- `use`/`rcases`/`simp` on image-membership existentials — carry it as a
  -- `have` and use `simpa`/`exact`.
  trivial

end Shufflemath
