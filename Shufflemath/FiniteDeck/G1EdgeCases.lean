module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.TwoPileFiber
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
## G1 edge cases: `N = 0`, `m = 0`, `m = N` (no `Commander*` imports)

The G1 acceptance item that the core `FiniteDeck` types stay well-formed and
non-degenerate at the boundary parameter values, using only the generic G1
modules (no `Shufflemath.Commander*` import).  The core type is
`Membership (N m) := {S : Finset (Fin N) // S.card = m}` and
`Deck N := Equiv.Perm (Fin N)`, each parameterized only by the constraint
`m ≤ N`, which all three edge values satisfy:
- `N = 0` forces `m = 0` (a 0-card deck);
- `m = 0` (the empty left pile);
- `m = N` (the full deck is the left pile).
For each, the relevant state space has exactly one element, as these lemmas
record.
-/

/-- `N = 0` edge: a 0-card deck has exactly one permutation (`0! = 1`). -/
theorem deckCard_zero : Fintype.card (Deck 0) = 1 := by
  dsimp only [Deck]
  rw [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero]

/-- `m = 0` edge: there is exactly one 0-subset of `Fin N` — the empty set.
  `#(Membership N 0) = choose N 0 = 1`. -/
theorem membershipCard_zero (N : Nat) : Fintype.card (Membership N 0) = 1 := by
  rw [membershipCount N 0 (Nat.zero_le N)]
  exact Nat.choose_zero_right N

/-- `m = N` edge: there is exactly one `N`-subset of `Fin N` — the full set.
  `#(Membership N N) = choose N N = 1`. -/
theorem membershipCard_top (N : Nat) : Fintype.card (Membership N N) = 1 := by
  rw [membershipCount N N (Nat.le_refl N)]
  exact Nat.choose_self N

/-- `N = 0`, `m = 0` edge (both empty): exactly one membership state. -/
theorem membershipCard_zero_zero : Fintype.card (Membership 0 0) = 1 := by
  rw [membershipCount 0 0 (Nat.zero_le 0)]
  exact Nat.choose_zero_right 0

end FiniteDeck
end Shufflemath
