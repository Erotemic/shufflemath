module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PhysicalSwap
public import Shufflemath.GSRSegHeadline

@[expose]
public section

namespace Shufflemath

open Finset
open CommanderPermutation

theorem h50le99 : 50 ≤ 99 := by
  norm_num

/-- **B5 finset bridge (99/50 specialisation).**  The parameterized
    `FiniteDeck.newLeftCards` at `N = 99, m = 50` is the commander's:  both are
    `image (fun l => d (leftPosition l)) (univ \ L) ∪ image (fun r => d (rightPosition r)) R`,
    and `leftPosition 99 50 hm` is `Fin.castLE hm` (i.e. `⟨i.val, ·⟩`) just like the
    commander's `leftPosition`, and `rightPosition 99 50 hm i = ⟨50 + i.val, ·⟩` just
    like the commander's — the two are definitionally equal (proof irrelevance on
    the `Fin`-bound proofs). -/
theorem newLeftCards_99_50_eq_commander (d : Deck) (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    FiniteDeck.newLeftCards 99 50 h50le99 d L R = CommanderPhysicalExchange.newLeftCards d L R := by
  dsimp only [FiniteDeck.newLeftCards, CommanderPhysicalExchange.newLeftCards,
      FiniteDeck.leftPosition, leftPosition,
      FiniteDeck.rightPosition, rightPosition, Fin.castLE]

theorem K1a_stmt_only
    (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    CommanderMembershipKernels.membership ((FiniteDeck.swapPerm 99 50 h50le99 L R b).trans d) =
      CommanderPhysicalExchange.newMembership d L hL R hR := by
  -- Membership is a Subtype carrying the 50-card set, so prove that set.
  apply Subtype.ext
  rw [CommanderMembershipKernels.membership_leftCards _,
      ← finiteDeck_leftCards_99_50_eq_commander _]
  -- Re-read the LHS as the `.1` of the parameterized membership, so the B1
  -- headline (`swapPerm_membership_eq`) applies.
  change (FiniteDeck.membership 99 50 h50le99
      ((FiniteDeck.swapPerm 99 50 h50le99 L R b).trans d)).1 =
    (CommanderPhysicalExchange.newMembership d L hL R hR).1
  have hsw := FiniteDeck.swapPerm_membership_eq 99 50 25 h50le99
      (by norm_num) (by norm_num) d L hL R hR b
  rw [hsw]
  -- `.1` of each membership: the parameterized `newLeftCards` (left) and the
  -- commander's (right);  the B5 bridge closes the 99/50 specialisation.
  dsimp only [FiniteDeck.literalSwapMembership, CommanderPhysicalExchange.newMembership]
  exact newLeftCards_99_50_eq_commander d L R

end Shufflemath
