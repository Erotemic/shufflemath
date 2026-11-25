module

public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.GSR
public import Shufflemath.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

variable {N p : Nat} {n : Fin p → Nat}

/-- The **uniform-transposition exchange kernel** on the allocation carrier: from a
    state `A`, pick two card indices `(a, b)` uniformly at random from
    `Fin N × Fin N` (all `N^2` pairs, the `a = b` pair being the no-op) and move
    to the swapped state `swapPiles A a b`.  A pushforward of a distribution, so
    each row is a genuine `Dist` (row-mass sums to 1 by construction).  The
    `0 < N` argument exists only to name the uniform law on the (nonempty) pair
    type; a positive deck is the natural domain of the exchange. -/
noncomputable def swapKernel (hN : 0 < N) (A : Allocation N p n) : Dist (Allocation N p n) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  exact (GSR.uniformDist (Fin N × Fin N)).map (fun ab => swapPiles A ab.1 ab.2)

/-- Swapping the piles of `a` and `b` and then swapping them again restores the
    original allocation owner function: `swapOwner ∘ swapOwner = A.val`.  Uses
    only `swapOwner_eq_cardTransposition` + the involution of `cardTransposition`. -/
theorem swapOwner_involutive (A : Allocation N p n) (a b x : Fin N) :
    swapOwner (swapPiles A a b) a b x = A.val x := by
  have h1 : swapOwner (swapPiles A a b) a b x =
      (swapPiles A a b).val (cardTransposition a b x) :=
    swapOwner_eq_cardTransposition (swapPiles A a b) a b x
  have h2 : (swapPiles A a b).val (cardTransposition a b x) =
      swapOwner A a b (cardTransposition a b x) := by
    simp [swapPiles]
  have h3 : swapOwner A a b (cardTransposition a b x) =
      A.val (cardTransposition a b (cardTransposition a b x)) :=
    swapOwner_eq_cardTransposition A a b (cardTransposition a b x)
  rw [h1, h2, h3]
  rw [cardTransposition_involution]

/-- The exchange operation is an **involution** on the allocation carrier:
    `swapPiles (swapPiles A a b) a b = A`. -/
theorem swapPiles_involution (A : Allocation N p n) (a b : Fin N) :
    swapPiles (swapPiles A a b) a b = A := by
  apply Subtype.ext
  funext x
  simpa [swapPiles] using swapOwner_involutive A a b x

/-- Swapping `a` and `b` sends `A` to `A'` iff it sends `A'` back to `A`: the
    involution, stated as an `iff` on the outcome.  This is the fiber-symmetry
    fact that makes the uniform-transposition kernel **symmetric**. -/
theorem swapPiles_swap_iff (A A' : Allocation N p n) (a b : Fin N) :
    (swapPiles A a b = A') ↔ (swapPiles A' a b = A) := by
  constructor
  · intro h
    rw [← h]
    exact swapPiles_involution A a b
  · intro h
    rw [← h]
    exact swapPiles_involution A' a b

/-- Explicit mass of the swap kernel at `A'`: the sum, over all `N^2` card pairs,
    of the uniform pair-mass `(N^2)⁻¹` times the indicator that the pair's swap
    lands exactly on `A'`.  Follows directly from `GSR.map_uniform_mass`. -/
theorem swapKernel_mass (hN : 0 < N) (A A' : Allocation N p n) :
    Dist.mass (swapKernel hN A) A' =
      (Finset.univ : Finset (Fin N × Fin N)).sum
        (fun s => (N * N : Rat)⁻¹ * if A' = swapPiles A s.1 s.2 then 1 else 0) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  show Dist.mass ((GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => swapPiles A ab.1 ab.2)) A' =
      (Finset.univ : Finset (Fin N × Fin N)).sum
        (fun s => (N * N : Rat)⁻¹ * if A' = swapPiles A s.1 s.2 then 1 else 0)
  have hcard : Fintype.card (Fin N × Fin N) = N * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [GSR.map_uniform_mass]
  simp [hcard]

/-- The uniform-transposition kernel is **symmetric** (doubly stochastic):
    `mass (swapKernel A) A' = mass (swapKernel A') A`.  The two fiber indicators
    are pointwise equivalent by `swapPiles_swap_iff` (the involution). -/
theorem swapKernel_symmetric (hN : 0 < N) (A A' : Allocation N p n) :
    Dist.mass (swapKernel hN A) A' = Dist.mass (swapKernel hN A') A := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  rw [swapKernel_mass hN A A', swapKernel_mass hN A' A]
  refine Finset.sum_congr rfl fun s _ => by
    by_cases h : A' = swapPiles A s.1 s.2
    · have h2 : A = swapPiles A' s.1 s.2 :=
        ((swapPiles_swap_iff A A' s.1 s.2).1 h.symm).symm
      rw [ite_eq_left h, ite_eq_left h2]
    · have h2 : A ≠ swapPiles A' s.1 s.2 := by
        intro hc
        exact h ((swapPiles_swap_iff A A' s.1 s.2).2 hc.symm).symm
      rw [ite_eq_right h, ite_eq_right h2]

end FiniteDeck
end Shufflemath
