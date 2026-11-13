module

/-
Four-bin overlap count for the membership-exchange fiber (F3 item 3).

For a target membership `T` of size `m` containing `y` of the `r` marked
identities, the number of starting memberships `S` of size `m` with `x`
marked cards and `|S ∩ T| = m - k` is a sum over how many `t` marked cards
of `T` land in `S`; the four marked/unmarked × in/outside-T bins are then
independent `choose` factors. This count equals the *reversed* Bernoulli--
Laplace transition numerator (the content of F3 item 3):

    overlap_count (n m r k) x y  =  transitionNumerator (n m r k) y x

`tests/test_exchange_overlap_identity.py` verifies the identity by exact
integer arithmetic on three small decks and all 2,500 Commander `(x, y)`
pairs.  The `Nat` subtraction below is intentional: it matches the
saturation in the counting formula (a bin with a negative requested size
contributes a factor of `Nat.choose _ 0 = 1` times an empty `choose`,
which `Nat.choose` saturates to `0` for an impossible size, so impossible
terms vanish).
-/
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-- The four-bin overlap count: the number of `m`-subsets `S` of an `n`-set,
with `x` marked cards and `|S ∩ T| = m - k`, where `T` is a fixed `m`-subset
holding `y` of the `r` marked identities.  The sum runs over `t`, the number
of marked cards of `T` that land in `S`; the four bins are
(marked/unmarked) × (inside/outside `T`), giving the four `choose` factors. -/
def overlap_count (n m r k x y : Nat) : Nat :=
  Finset.sum (Finset.range (m - k + 1)) fun t =>
    Nat.choose y t * Nat.choose (r - y) (x - t) *
      Nat.choose (m - y) ((m - k) - t) *
      Nat.choose ((n - r) - (m - y)) ((m - x) - ((m - k) - t))
