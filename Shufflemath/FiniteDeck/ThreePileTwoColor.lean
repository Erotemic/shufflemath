module

public import Shufflemath.FiniteDeck.Piles
public import Shufflemath.FiniteDeck.Histograms
public import Shufflemath.FiniteDeck.MultiPileFiber
public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

/-!
# G5: a concrete 3-pile, 2-category example (the G5 gate)

A worked instance showing the general multi-pile machinery compiles for
`k >= 3` and `c >= 2`: six named cards split into two categories, three piles
of two.  The reusable general theorems do the real work — the fiber count via
`multiPile_card` and the lumped-histogram row/column totals via
`lump_pileTotal` / `lump_categoryTotal`.  The concrete combinatorial premises
(partition, disjointness) are proved constructively; the pure `Nat`/`Finset`
computation facts are discharged by `native_decide`, legitimate here because
the card space is the six-element `Fin 6`, not a `99!` universe.
-/

/-- The two-category (two-color) map on the six cards: cards `0,1,2` are
    category `0` and cards `3,4,5` are category `1` (three of each). -/
def color6 (x : Fin 6) : Fin 2 := if x.val < 3 then 0 else 1

/-- The three-pile partition of the six cards into consecutive pairs: pile
    `i` is the two cards whose index satisfies `x / 2 = i` — pile `0 = {0,1}`,
    pile `1 = {2,3}`, pile `2 = {4,5}`. -/
def pile3 (i : Fin 3) : Finset (Fin 6) :=
  (Finset.univ : Finset (Fin 6)).filter (fun x => x.val / 2 = i.val)

/-- A card `x` lies in pile `i` exactly when `x.val / 2 = i.val`. -/
theorem pile3_mem (x : Fin 6) (i : Fin 3) : x ∈ pile3 i ↔ x.val / 2 = i.val := by
  rw [pile3, Finset.mem_filter]
  -- goal: (x ∈ univ ∧ x.val / 2 = i.val) ↔ (x.val / 2 = i.val)
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨Finset.mem_univ x, h⟩

/-- Every card lies in exactly one pile: coverage and unique ownership. -/
theorem pile3_partition : IsPartition pile3 := by
  constructor
  · -- coverage: card x lives in pile ⟨x.val / 2⟩
    intro x
    have hlt : x.val / 2 < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Fin.isLt x
    use ⟨x.val / 2, hlt⟩
    exact (pile3_mem x ⟨x.val / 2, hlt⟩).mpr (by rfl)
  · -- unique ownership: if x is in pile i and pile j then i.val = j.val, so i = j
    intro i j x h1 h2
    have hi : x.val / 2 = i.val := (pile3_mem x i).mp h1
    have hj : x.val / 2 = j.val := (pile3_mem x j).mp h2
    exact Fin.eq_of_val_eq (by rw [← hi, hj])

/-- Distinct piles are disjoint: a card cannot lie in two different piles. -/
theorem pile3_disjoint : ∀ i j, i ≠ j → Disjoint (pile3 i) (pile3 j) := by
  intro i j hne
  rw [Finset.disjoint_iff_inter_eq_empty]
  refine Finset.ext fun x => ?_
  simp [Finset.mem_inter, pile3_mem]
  -- goal: x.val / 2 = i.val → ¬(x.val / 2 = j.val)
  intro h1
  by_contra h2
  exact hne (Fin.eq_of_val_eq (by rw [← h1, h2]))

/-- The product of the three pile sizes' factorials: `(2!) · (2!) · (2!) = 8`.
    A pure `Nat` computation (`native_decide`), no `Fintype` involved. -/
theorem prod3 : (Finset.univ : Finset (Fin 3)).prod (fun i => Nat.factorial ((pile3 i).card)) = 8 := by
  native_decide

/-- **The fiber count (via the reusable `multiPile_card`).**  The number of
    decks realizing the (pos = card = `pile3`) allocation is `∏ i, (2!) = 8`:
    `multiPile_card` specializes the general-`k` product count, and `prod3`
    checks that product. -/
theorem example3_fiberCard :
    Fintype.card (MultiFiber 6 3 pile3 pile3) = 8 := by
  rw [multiPile_card 6 3 pile3 pile3 pile3_partition pile3_partition (fun i => rfl)]
  exact prod3

/-- **Row total, pile 0 (via `lump_pileTotal`).**  Summing the two category
    counts over pile `0 = {0,1}` recovers the pile size `2`. -/
theorem example3_rowTotal0 :
    (Finset.univ : Finset (Fin 2)).sum (fun j => lump pile3 color6 0 j) = 2 := by
  rw [lump_pileTotal (k := 3) (N := 6) (c := 2) (cardPile := pile3) (color := color6) (i := 0)]
  native_decide

/-- **Column total, category 0 (via `lump_categoryTotal`).**  Summing the
    category-`0` counts over the three piles equals the number of category-`0`
    cards, `3`. -/
theorem example3_colTotal0 :
    (Finset.univ : Finset (Fin 3)).sum (fun i => lump pile3 color6 i 0) = 3 := by
  rw [lump_categoryTotal (k := 3) (N := 6) (c := 2) (cardPile := pile3) (color := color6) (hPiles := pile3_disjoint) (j := 0)]
  native_decide

/-- **Column total, category 1 (via `lump_categoryTotal`).**  Summing the
    category-`1` counts over the three piles equals the number of category-`1`
    cards, `3`. -/
theorem example3_colTotal1 :
    (Finset.univ : Finset (Fin 3)).sum (fun i => lump pile3 color6 i 1) = 3 := by
  rw [lump_categoryTotal (k := 3) (N := 6) (c := 2) (cardPile := pile3) (color := color6) (hPiles := pile3_disjoint) (j := 1)]
  native_decide

end FiniteDeck

end Shufflemath
