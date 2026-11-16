module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.TwoPileFiber
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G3: the membership-level `k`-exchange (foundations)

The universal exchange at the membership level: from a left pile `S` of size
`m` in an `N`-card deck, a `k`-exchange moves `k` of `S`'s cards to the right
pile and `k` right-cards to `S`, yielding a new left pile `T` with
`|S \ T| = |T \ S| = k`.

This module sets up the counting structures:
- `ReachSet S` — the memberships `T` reachable from `S` by a `k`-exchange;
- `Lset S` / `Rset S` — the `k`-subsets of `S` (cards leaving) and of its
  complement (cards entering);
- `Lset_card` / `Rset_card` — their sizes, `choose m k` and `choose (N - m) k`.

The next step (`subsetExchangeCount`) is the bijection
`ReachSet S ≃ Lset S × Rset S` giving
`# ReachSet S = choose m k · choose (N - m) k`, and then the uniform kernel.
-/


def ReachSet (N m k : Nat) (_hm : m ≤ N) (_hk : k ≤ m) (_hkm : k ≤ N - m)
    (S : Membership N m) : Finset (Membership N m) :=
  (Finset.univ : Finset (Membership N m)).filter
    (fun T => (S.1 \ T.1).card = k ∧ (T.1 \ S.1).card = k)

def Lset (N m k : Nat) (_hm : m ≤ N) (_hk : k ≤ m) (_hkm : k ≤ N - m) (S : Membership N m) :
    Finset (Finset (Fin N)) := Finset.powersetCard k S.1

def Rset (N m k : Nat) (_hm : m ≤ N) (_hk : k ≤ m) (_hkm : k ≤ N - m) (S : Membership N m) :
    Finset (Finset (Fin N)) := Finset.powersetCard k (Finset.univ \ S.1)

theorem Lset_card (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) : (Lset N m k hm hk hkm S).card = Nat.choose m k := by
  rw [Lset, Finset.card_powersetCard, S.2]
theorem Rset_card (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) : (Rset N m k hm hk hkm S).card = Nat.choose (N - m) k := by
  rw [Rset, Finset.card_powersetCard]
  congr
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), S.2, Finset.card_univ, Fintype.card_fin]

/-! ## Next: `subsetExchangeCount` (T3)

The reachable-exchange count, proved by the inverse-based bijection
`Finset.card_bij'`:

- `i (T : Membership N m) (hT : T ∈ ReachSet S) = (S.1 \ T.1, T.1 \ S.1)`, landing
  in `Lset.prod Rset` (`Finset.mk_mem_product`: `L = S\T` is a `k`-subset of
  `S.1`, `R = T\S` a `k`-subset of `univ \ S.1`).
- `j (p : _ × _) (hp : p ∈ Lset.prod Rset) = ⟨(S.1 \ p.1) ∪ p.2, card = m⟩`.
- `left_inv` / `right_inv` use `S.1 \ (S.1 \ T.1) = S.1 ∩ T.1` and
  `T.1 = (T.1 ∩ S.1) ∪ (T.1 \ S.1)`.

Then `# ReachSet S = #(Lset.prod Rset) = #Lset · #Rset = choose m k · choose
(N-m) k` via `Finset.card_prod` + `Lset_card` + `Rset_card`.  (Leaves of the
finset API still being pinned: `Finset.mk_mem_product`, sdiff-subset, and the
card-of-sdiff.)
-/

end FiniteDeck
end Shufflemath
