module

public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# Multi-pile pairwise exchange count (the general-`k` B4, allocation level)

The two-pile B4 (`SubsetExchange.subsetExchangeCount`) exchanges `k` cards
between the left pile `S` (size `m`) and the right pile `T` (the complement,
size `N - m`): the reachable allocations are in bijection with
`(k-subsets of S) × (k-subsets of T)`, so there are `choose m k * choose
(N-m) k` of them.

This module generalizes that to an **arbitrary pair of disjoint piles** `A`
(size `m`) and `B` (size `n`) of an `N`-card deck — the allocation-level
pairwise exchange that appears in the multi-pile `G5` program.  A `k`-exchange
between them swaps `k` cards each way: given `oi ⊆ A` (the cards leaving `A`)
and `oj ⊆ B` (the cards leaving `B`), the exchanged pair is

    `exchangePair A B oi oj = ((A \ oi) ∪ oj, (B \ oj) ∪ oi)`.

The reconstruction identity `A \ ((A \ oi) ∪ oj) = oi` (and symmetrically for
`B`), which uses only the disjointness of the two piles, makes the exchange
map **injective** on `(k-subsets of A) × (k-subsets of B)`: the exchanged pair
determines `(oi, oj)` by `oi = A \ A'`, `oj = B \ B'`.  Hence the number of
reachable exchanged pairs is the count of the domain,

    `choose m k * choose n k` — the allocation-level denominator of the T5
    histogram kernel.

The two-pile result is the special case `B = univ \ A` (`n = N - m`).  The
proof is structural (membership `ext` + `tauto` over disjointness); there is no
`native_decide` and no enumeration of the full deck.

## Next steps (documented, not yet proven here)
- **Involutivity / reversibility:** `exchangePair ((A\oi)∪oj) ((B\oj)∪oi) oj oi
  = (A, B)`, i.e. the exchange kernel is a reversible symmetric kernel (the
  T5 "unique (out_i, out_j) argument").
- **Histogram lumping:** lump the allocation chain over colors to obtain the
  multivariate-hypergeometric T5 transition and prove its stationarity.
-/

/-- The exchanged pair: `oi` cards leave `A` (entering `B`), `oj` cards leave
    `B` (entering `A`). -/
def exchangePair (N : Nat) (A B oi oj : Finset (Fin N)) :
    Finset (Fin N) × Finset (Fin N) := ((A \ oi) ∪ oj, (B \ oj) ∪ oi)

/-- A card that lies in both `A` and `B` is impossible when they are disjoint. -/
private theorem disjoint_notMem {N : Nat} (A B : Finset (Fin N)) (hDis : Disjoint A B)
    (y : Fin N) : y ∈ A → y ∈ B → False := by
  rintro hyA hyB
  have hInt : y ∈ A ∩ B := Finset.mem_inter.mpr ⟨hyA, hyB⟩
  simpa [Finset.disjoint_iff_inter_eq_empty.mp hDis] using hInt

/-- Finset subset gives the corresponding membership implication. -/
private theorem subset_mem {N : Nat} (A B : Finset (Fin N)) (h : A ⊆ B) (y : Fin N) :
    y ∈ A → y ∈ B := by
  intro hy
  rw [Finset.subset_def] at h
  simpa using h (by simpa using hy)

/-- The exchange map is injective on `(k-subsets of A) × (k-subsets of B)`:
    the exchanged pair determines `(oi, oj)` by `oi = A \ A'`, `oj = B \ B'`. -/
theorem exchangePair_injOn (N : Nat) (A B : Finset (Fin N)) (k : Nat)
    (hDis : Disjoint A B) (s : Finset (Finset (Fin N) × Finset (Fin N)))
    (hs : s ⊆ Finset.powersetCard k A ×ˢ Finset.powersetCard k B) :
    Set.InjOn (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2) s := by
  intro p hp q hq heq
  have hpm : p ∈ Finset.powersetCard k A ×ˢ Finset.powersetCard k B := hs hp
  have hqm : q ∈ Finset.powersetCard k A ×ˢ Finset.powersetCard k B := hs hq
  have hpA : p.1 ⊆ A := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hpm).1)).1
  have hpB : p.2 ⊆ B := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hpm).2)).1
  have hqA : q.1 ⊆ A := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hqm).1)).1
  have hqB : q.2 ⊆ B := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hqm).2)).1
  -- Membership implications (the leaving subsets sit inside their piles).
  have hpa (y : Fin N) : y ∈ p.1 → y ∈ A := subset_mem p.1 A hpA y
  have hpb (y : Fin N) : y ∈ p.2 → y ∈ B := subset_mem p.2 B hpB y
  have hqa (y : Fin N) : y ∈ q.1 → y ∈ A := subset_mem q.1 A hqA y
  have hqb (y : Fin N) : y ∈ q.2 → y ∈ B := subset_mem q.2 B hqB y
  -- Reconstruction: a leaving subset is recovered by removing the exchanged pile.
  have hP1 : A \ ((A \ p.1) ∪ p.2) = p.1 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ p.1 → y ∈ A := hpa y
    have h2 : y ∈ p.1 → y ∉ p.2 := fun hy hb => disjoint_notMem A B hDis y (hpa y hy) (hpb y hb)
    tauto
  have hP2 : B \ ((B \ p.2) ∪ p.1) = p.2 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ p.2 → y ∈ B := hpb y
    have h2 : y ∈ p.2 → y ∉ p.1 := fun hy hb => disjoint_notMem A B hDis y (hpa y hb) (hpb y hy)
    tauto
  have hQ1 : A \ ((A \ q.1) ∪ q.2) = q.1 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ q.1 → y ∈ A := hqa y
    have h2 : y ∈ q.1 → y ∉ q.2 := fun hy hb => disjoint_notMem A B hDis y (hqa y hy) (hqb y hb)
    tauto
  have hQ2 : B \ ((B \ q.2) ∪ q.1) = q.2 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ q.2 → y ∈ B := hqb y
    have h2 : y ∈ q.2 → y ∉ q.1 := fun hy hb => disjoint_notMem A B hDis y (hqa y hb) (hqb y hy)
    tauto
  have hAeq : (A \ p.1) ∪ p.2 = (A \ q.1) ∪ q.2 := congrArg Prod.fst heq
  have hBeq : (B \ p.2) ∪ p.1 = (B \ q.2) ∪ q.1 := congrArg Prod.snd heq
  refine Prod.ext ?_ ?_
  · calc
      p.1 = A \ ((A \ p.1) ∪ p.2) := hP1.symm
      _ = A \ ((A \ q.1) ∪ q.2) := by rw [hAeq]
      _ = q.1 := hQ1
  · calc
      p.2 = B \ ((B \ p.2) ∪ p.1) := hP2.symm
      _ = B \ ((B \ q.2) ∪ q.1) := by rw [hBeq]
      _ = q.2 := hQ2

/-- The pairwise multi-pile exchange count: from disjoint piles `A` (size `m`)
    and `B` (size `n`), a `k`-exchange between them reaches exactly
    `choose m k * choose n k` pairs.  This is the allocation-level denominator
    of the T5 histogram kernel and the multi-pile generalization of
    `SubsetExchange.subsetExchangeCount` (which is the case `B = univ \ A`). -/
theorem pairwiseExchangeCount (N m n k : Nat)
    (A B : Finset (Fin N)) (hA : A.card = m) (hB : B.card = n) (hDis : Disjoint A B) :
    (Finset.image (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2)
        (Finset.powersetCard k A ×ˢ Finset.powersetCard k B)).card =
      Nat.choose m k * Nat.choose n k := by
  let D := Finset.powersetCard k A ×ˢ Finset.powersetCard k B
  have hInj : Set.InjOn (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2) D :=
    exchangePair_injOn N A B k hDis D (Finset.Subset.refl _)
  rw [Finset.card_image_of_injOn hInj, Finset.card_product,
      Finset.card_powersetCard, hA, Finset.card_powersetCard, hB]

end FiniteDeck
end Shufflemath
