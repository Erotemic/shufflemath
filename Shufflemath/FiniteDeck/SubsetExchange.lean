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

/-! ## The `k`-exchange count (`T3`)

The reachable-exchange count, proved by the inverse-based bijection
`Finset.card_bij'`: `ReachSet S ≃ Lset S × Rset S` (via `i (T) = (S.1 \ T.1,
T.1 \ S.1)` and its inverse `j (p) = ⟨(S.1 \ p.1) ∪ p.2, ·⟩`), so
`# ReachSet S = #Lset · #Rset = choose m k · choose (N - m) k`.
-/

/-- A `(leaving, entering)` pair `p` in `Lset.prod Rset` has `p.1 ⊆ S.1` of
  size `k` and `p.2 ⊆ univ \ S.1` of size `k`. -/
theorem decomp (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    p.1 ⊆ S.1 ∧ p.1.card = k ∧ p.2 ⊆ Finset.univ \ S.1 ∧ p.2.card = k := by
  dsimp only [Lset, Rset] at hp
  rw [Finset.mem_product] at hp
  rcases hp with ⟨hL, hR⟩
  rw [Finset.mem_powersetCard] at hL hR
  exact ⟨hL.1, hL.2, hR.1, hR.2⟩

/-- The pile reconstructed from a `(leaving, entering)` pair has size `m`. -/
theorem newpile_card (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    ((S.1 \ p.1) ∪ p.2).card = m := by
  rcases decomp N m k hm hk hkm S p hp with ⟨hle, hlc, hre, hrc⟩
  have hInt : (S.1 \ p.1) ∩ p.2 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx
    have hx2 : x ∈ Finset.univ \ S.1 := hre hx.2
    rw [Finset.mem_sdiff] at hx2
    exact hx2.2 (hx.1.1)
  have hIntCard : ((S.1 \ p.1) ∩ p.2).card = 0 := by rw [hInt, Finset.card_empty]
  rw [Finset.card_union, hIntCard, Finset.card_sdiff_of_subset hle, S.2, hlc, hrc, Nat.sub_zero]
  exact Nat.sub_add_cancel hk

/-- Inversion, first component: `S.1 \ ((S.1 \ p.1) ∪ p.2) = p.1`. -/
theorem inv_first (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    S.1 \ ((S.1 \ p.1) ∪ p.2) = p.1 := by
  rcases decomp N m k hm hk hkm S p hp with ⟨hle, hlc, hre, hrc⟩
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and, not_not, iff_self]
  have hm1 : x ∈ p.1 → x ∈ S.1 := fun h => hle h
  have hm2 : x ∈ p.2 → x ∉ S.1 := fun h => (Finset.mem_sdiff.mp (hre h)).2
  tauto

/-- Inversion, second component: `((S.1 \ p.1) ∪ p.2) \ S.1 = p.2`. -/
theorem inv_second (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    ((S.1 \ p.1) ∪ p.2) \ S.1 = p.2 := by
  rcases decomp N m k hm hk hkm S p hp with ⟨hle, hlc, hre, hrc⟩
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and, not_not, iff_self]
  have hm2 : x ∈ p.2 → x ∉ S.1 := fun h => (Finset.mem_sdiff.mp (hre h)).2
  tauto

/-- The pile reconstructed from a `(leaving, entering)` pair is reachable. -/
theorem newpile_reach (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    ⟨(S.1 \ p.1) ∪ p.2, newpile_card N m k hm hk hkm S p hp⟩ ∈
        ReachSet N m k hm hk hkm S := by
  simp only [ReachSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [inv_first N m k hm hk hkm S p hp, inv_second N m k hm hk hkm S p hp]
  rcases decomp N m k hm hk hkm S p hp with ⟨hle, hlc, hre, hrc⟩
  exact ⟨hlc, hrc⟩

/-- The G3 count: from a left pile of size `m`, a `k`-exchange reaches exactly
  `choose m k · choose (N - m) k` other piles — choose the `k` leaving cards and
  the `k` entering cards, independently. -/
theorem subsetExchangeCount (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S : Membership N m) :
    (ReachSet N m k hm hk hkm S).card = Nat.choose m k * Nat.choose (N - m) k := by
  have hL : (Lset N m k hm hk hkm S).card = Nat.choose m k := Lset_card N m k hm hk hkm S
  have hR : (Rset N m k hm hk hkm S).card = Nat.choose (N - m) k := Rset_card N m k hm hk hkm S
  let i (T : Membership N m) (hT : T ∈ ReachSet N m k hm hk hkm S) :
      Finset (Fin N) × Finset (Fin N) := (S.1 \ T.1, T.1 \ S.1)
  let j (p : Finset (Fin N) × Finset (Fin N))
      (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) : Membership N m :=
      ⟨(S.1 \ p.1) ∪ p.2, newpile_card N m k hm hk hkm S p hp⟩
  have hbij : (ReachSet N m k hm hk hkm S).card =
      (Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S).card := by
    refine Finset.card_bij' i j ?_ ?_ ?_ ?_
    · -- i lands in Lset × Rset
      intro T hT
      rw [Finset.mem_product, Lset, Rset, Finset.mem_powersetCard, Finset.mem_powersetCard]
      simp only [ReachSet, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rcases hT with ⟨hA, hB⟩
      have hsub2 : T.1 \ S.1 ⊆ Finset.univ \ S.1 := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hx.2⟩
      exact ⟨⟨Finset.sdiff_subset, hA⟩, ⟨hsub2, hB⟩⟩
    · -- j lands back in ReachSet
      intro p hp
      exact newpile_reach N m k hm hk hkm S p hp
    · -- left inverse: j (i T) = T
      intro T hT
      dsimp only [i, j]
      refine Subtype.ext ?_
      change (S.1 \ (S.1 \ T.1)) ∪ (T.1 \ S.1) = T.1
      rw [Finset.sdiff_sdiff_self_left, Finset.inter_comm, Finset.union_comm,
          Finset.sdiff_union_inter]
    · -- right inverse: i (j p) = p
      intro p hp
      dsimp only [i, j]
      ext
      · rw [inv_first N m k hm hk hkm S p hp]
      · rw [inv_second N m k hm hk hkm S p hp]
  rw [hbij, Finset.card_product, hL, hR]

end FiniteDeck
end Shufflemath
