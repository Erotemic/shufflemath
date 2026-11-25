module

public import Shufflemath.FiniteDeck.PileEquiv
public import Shufflemath.FiniteDeck.PileFiber
public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

variable (N k : Nat) (P C : Fin k → Finset (Fin N))
variable (hP : IsPartition P) (hC : IsPartition C)
variable (e : (i : Fin k) → Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i})

/-!
# G5: the multi-pile fiber — the general-k fiber `Equiv` and the equiv round-trip

`PileFiber` supplies the two directions of the general-`k` fiber correspondence:
`multiPileToEquivs` (a realizing deck restricts, per pile, to `↥(P i) ≃ ↥(C i)`)
and `equivsToMultiPile` (a family of per-pile equivs is glued into a realizing
deck, realizing by `gluedRealizes`).  This file proves the equiv round-trip and
packages the two directions into the headline fiber `Equiv`.

* `roundTripEquivs` — taking the per-pile equivs of a glued deck recovers the
  family.  (The deck-direction round-trip, `roundTripDecks`, is in `PileFiber`.)
* `multiPile_equivFiber` — **HEADLINE**: the realizing-deck fiber
  `MultiFiber N k P C` is in canonical bijection with the family of per-pile
  equivs `Π i, ↥(P i) ≃ ↥(C i)`.
-/

/-- Equiv round-trip: taking the per-pile equivs of a glued deck recovers the
    family `e`.  Both this and `roundTripDecks` reduce to
    `glueBlocks_apply_member` + `pileF` + `Subtype.ext` (`⟨x.val, x.property⟩
    = x`), once the glued deck's per-pile equiv is recognized as
    `pileEquiv … i (glueBlocks …) (gluedRealizes … i)`. -/
theorem roundTripEquivs :
    multiPileToEquivs N k P C (equivsToMultiPile N k P C hP hC e) = e := by
  funext i
  apply Equiv.ext
  intro x
  change (pileF N k P C i (glueBlocks P C hP hC e) (gluedRealizes N k P C hP hC e i)) x = e i x
  apply Subtype.ext
  dsimp only [pileF]
  have hglue : (glueBlocks P C hP hC e) x.val = (e i ⟨x.val, x.property⟩).val :=
    glueBlocks_apply_member P C hP hC e i x.val x.property
  have hx : ⟨x.val, x.property⟩ = x := Subtype.ext rfl
  simpa [hglue, hx]

/-- **HEADLINE — general-k multi-pile fiber structure.**  The fiber of
    realizing decks of a partition pair `(P, C)` (both partitions of `Fin N`
    into `k` blocks of equal size) is in canonical bijection with the family of
    per-pile equivs `↥(P i) ≃ ↥(C i)`.  Forward: a deck restricts to a per-pile
    equiv (`multiPileToEquivs`).  Inverse: a family of per-pile equivs is glued
    into a realizing deck (`equivsToMultiPile`, realizing by `gluedRealizes`).
    The two round-trips `roundTripDecks` / `roundTripEquivs` make the forward
    map a bijection, so `Equiv.ofBijective` packages the whole thing.  For `k =
    2` this specializes to the earlier two-pile fiber result. -/
noncomputable def multiPile_equivFiber :
    Equiv (MultiFiber N k P C)
          ((i : Fin k) → Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i}) := by
  classical
  apply Equiv.ofBijective (multiPileToEquivs N k P C)
  constructor
  · intro a b hab
    apply Subtype.ext
    have hga : a.1 = (equivsToMultiPile N k P C hP hC (multiPileToEquivs N k P C a)).1 := by
      simpa using (roundTripDecks N k P C hP hC a).symm
    have hgb : b.1 = (equivsToMultiPile N k P C hP hC (multiPileToEquivs N k P C b)).1 := by
      simpa using (roundTripDecks N k P C hP hC b).symm
    calc a.1 = (equivsToMultiPile N k P C hP hC (multiPileToEquivs N k P C a)).1 := hga
      _ = (equivsToMultiPile N k P C hP hC (multiPileToEquivs N k P C b)).1 := by simpa [hab]
      _ = b.1 := hgb.symm
  · intro f
    exact ⟨equivsToMultiPile N k P C hP hC f, roundTripEquivs N k P C hP hC f⟩

/-!
## G5: the fiber count — `|MultiFiber| = ∏ i, (|C i|)!

The headline `multiPile_equivFiber` puts the realizing-deck fiber in bijection
with the family of per-pile equivs; this section counts that family.  The
per-pile count (`equivFiberCard`) says a single pile's equiv fiber has `(|C i|)!`
members (a bijection between two equal-size sets); the product over piles
(`multiPile_card`) then gives the full fiber count.  For `k = 2` this is the
earlier `twoPile_card` headline.
-/

/-- The **per-pile** fiber count: the family of equivs `↥(P i) ≃ ↥(C i)` over a
    single pile has cardinality `(|C i|)!` — each is a bijection between two
    sets of the same size `|P i| = |C i|`, so there are `|C i|!` of them
    (`Fintype.card_equiv`). -/
theorem equivFiberCard (i : Fin k) (hCard : (P i).card = (C i).card) :
    Fintype.card (Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i}) =
      Nat.factorial ((C i).card) := by
  classical
  have he : {x : Fin N // x ∈ P i} ≃ {x : Fin N // x ∈ C i} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hCard])
  rw [Fintype.card_equiv he]
  simp [Fintype.card_coe, hCard]

/-- **G5 count headline.**  The number of realizing decks of a partition pair
    `(P, C)` (pile `i` of `P` the same size as pile `i` of `C` for each `i`) is
    `∏ i, (|C i|)!`: the fiber `MultiFiber N k P C` is in bijection with the
    per-pile equiv family (`multiPile_equivFiber`), whose card is the product,
    over piles, of the per-pile equiv counts (`equivFiberCard`).  For `k = 2`
    this recovers the two-pile count `(|C 0|)! · (|C 1|)!`. -/
theorem multiPile_card (hP : IsPartition P) (hC : IsPartition C)
    (hCardEq : ∀ i, (P i).card = (C i).card) :
    Fintype.card (MultiFiber N k P C) =
      (Finset.univ : Finset (Fin k)).prod (fun i => Nat.factorial ((C i).card)) := by
  classical
  have he := multiPile_equivFiber N k P C hP hC
  rw [Fintype.card_congr he]
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact equivFiberCard N k P C i (hCardEq i)

end FiniteDeck

end Shufflemath
