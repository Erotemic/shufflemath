module

public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G2: counting fibers of the two-pile projection

The counting results of the generalization, proved by explicit finite
equivalences and `choose`-counting of `Finset.powersetCard` — never by
enumerating `N!` permutations or by `native_decide`.

- The number of `m`-element left piles (memberhips) of an `N`-card deck is the
  binomial coefficient `choose N m` (`membershipCount`).
-/

/-- The number of `m`-element left piles of an `N`-card deck is `choose N m`. -/
theorem membershipCount (N m : Nat) (_hm : m ≤ N) :
    Fintype.card (Membership N m) = Nat.choose N m := by
  classical
  change Fintype.card {S : Finset (Fin N) // S.card = m} = Nat.choose N m
  rw [Fintype.card_subtype]
  have hE : ({S : Finset (Fin N) | S.card = m} : Finset (Finset (Fin N))) =
      Finset.powersetCard m (Finset.univ : Finset (Fin N)) := by
    apply Finset.ext
    intro S
    simp
  rw [hE, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
end FiniteDeck
end Shufflemath
