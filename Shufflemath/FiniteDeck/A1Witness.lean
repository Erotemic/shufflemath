module

public import Shufflemath.FiniteDeck.UniformExchange
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

/-! A1 sanity witness: a concrete `N = 2`, `p = 2`, capacities `(1, 1)` instantiation
    of the allocation carrier, the two-card-pile exchange, and the relabel-invariance
    headline.  This is the "do not accept a claim" small-`N` check the A1 program
    required: every abstract statement is checked against a two-card deck a reader can
    enumerate by hand.  There are exactly two ways to put one card in each of two piles
    (the identity owner `A0` and the swap owner `A1`); the exchange (swap the two named
    cards) carries `A0` to `A1` and back; and the uniform-transposition kernel is
    invariant under relabeling. -/

/-- The two-card, two-pile, one-card-per-pile capacities. -/
def n2 : Fin 2 → Nat := fun _ => 1

/-- The allocation with card `x` in pile `x` (card 0 in pile 0, card 1 in pile 1):
    a valid one-card-per-pile allocation.  Pile `i` is the singleton `{i}`. -/
def A0 : Allocation 2 2 n2 :=
  ⟨fun x => x, fun i => by
    have hfiber : (Finset.univ.filter (fun x : Fin 2 => x = i)) = {i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and, iff_self]
    simp only [n2, hfiber]
    exact Finset.card_singleton i
  ⟩

/-- The **swapped** allocation, defined as the concrete exchange applied to `A0`
    (swap the two named cards): card 0 ends up in pile 1 and card 1 in pile 0.  Its
    validity as a one-card-per-pile allocation is inherited from `swapPiles`
    (`swapOwner_capacity`). -/
noncomputable def A1 : Allocation 2 2 n2 := swapPiles A0 0 1

/-- The concrete allocations really put the cards where we expect: `A0` puts card
    `x` in pile `x`, and its exchanged image `A1` swaps them (card 0 in pile 1, card
    1 in pile 0). -/
theorem A0_owner : A0.val 0 = 0 ∧ A0.val 1 = 1 := ⟨rfl, rfl⟩

theorem A1_owner : A1.val 0 = 1 ∧ A1.val 1 = 0 := by
  constructor
  · simp only [A1, swapPiles, swapOwner, A0, Subtype.val]
    rfl
  · simp only [A1, swapPiles, swapOwner, A0, Subtype.val]
    rfl

/-- The two concrete allocations are distinct: the exchange has a nontrivial target
    (`A0` puts card 0 in pile 0, `A1` puts it in pile 1). -/
theorem A0_ne_A1 : A0 ≠ A1 := by
  intro h
  have hc : A0.val 0 = A1.val 0 := congrArg (fun (A : Allocation 2 2 n2) => A.val 0) h
  have h0 : (0 : Fin 2) = 1 := by simpa [A0, A1_owner, Subtype.val] using hc
  exact absurd h0 (by decide)

/-- **The concrete exchange:** swapping the two named cards carries `A0` to `A1`
    (definitionally, since `A1` is that exchange).  This is the multi-pile exchange
    on the smallest nontrivial deck, the finite-deck analogue of the two-pile
    `PileEquiv.swap`. -/
theorem swapPiles_A0_eq_A1 : swapPiles A0 0 1 = A1 := rfl

/-- The exchange is an **involution** on the concrete deck: swapping the two cards of
    `A1` restores `A0`. -/
theorem swapPiles_A1_eq_A0 : swapPiles A1 0 1 = A0 := by
  rw [← swapPiles_A0_eq_A1]
  exact swapPiles_involution A0 0 1

/-- Concrete instance of the A1.4 relabel-invariance headline (`swapKernel_equivariant`)
    at `N = 2`: relabeling the two cards by any permutation preserves the swap-kernel
    mass, so the kernel is invariant on the concrete deck. -/
theorem swapKernel_equivariant_at2 (σ : Equiv.Perm (Fin 2)) (B : Allocation 2 2 n2) :
    Dist.mass (swapRelabel (by norm_num) σ A0) (relabel σ B) =
      Dist.mass (swapKernel (by norm_num) A0) B :=
  swapKernel_equivariant (by norm_num) σ A0 B

end FiniteDeck
end Shufflemath
