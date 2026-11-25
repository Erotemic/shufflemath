module

public import Shufflemath.FiniteDeck.PileEquiv
public import Shufflemath.FiniteDeck.Piles
public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

/-!
# G5: the multi-pile fiber — deck ↔ per-pile equivs

The two directions of the general-`k` fiber bijection, built from the per-pile
restriction equiv (`pileEquiv`) and the generic partition/Sigma gluing
(`glueBlocks` / `IsPartition`):

* `multiPileToEquivs d` — a deck `d` realizing the allocation `P → C` gives,
  for each pile `i`, the restriction equiv `↥(P i) ≃ ↥(C i)` (just `pileEquiv`).
* `gluedRealizes` — the deck obtained by **gluing** a family of per-pile equivs
  (via `glueBlocks`) realizes the allocation: each pile `i` is carried onto
  `C i`.  This is the crux: the image `(P i).image (glueBlocks …)` is `C i`,
  with membership decided by `glueBlocks_apply_member` (glued deck on `x ∈ P i`
  equals the local equiv at `x`) and the surjectivity of each local equiv.
* `equivsToMultiPile` — packaging the glued deck with `gluedRealizes` gives the
  realizing deck, i.e. the inverse direction.

The remaining step (next increment) is to prove these two maps are mutual
inverses — `roundTripDecks` / `roundTripEquivs`, both reducing to
`glueBlocks_apply_member` + `pileEquiv_toFun` + `Subtype.ext` — from which the
fiber equivalence `MultiFiber N k P C ≃ Π i, Equiv (↥(P i)) (↥(C i))` and the
count formula `Fintype.card (MultiFiber N k P C) = ∏ i, (|C i|)!` follow.
-/

section

variable (N k : Nat) (P C : Fin k → Finset (Fin N))
variable (hP : IsPartition P) (hC : IsPartition C)
variable (e : (i : Fin k) → Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i})
variable (d : MultiFiber N k P C)

/-- Forward: a realizing deck gives, per pile, the restriction equiv
    `↥(P i) ≃ ↥(C i)`. -/
noncomputable def multiPileToEquivs
    (d : MultiFiber N k P C) : (i : Fin k) → Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i} :=
  fun i => pileEquiv N k P C i d.1 (d.2 i)

/-- The deck obtained by gluing the per-pile equivs (via `glueBlocks`) realizes
    the allocation: each pile `i` is carried onto `C i`. -/
theorem gluedRealizes : realizesAllocation N k P C (glueBlocks P C hP hC e) := by
  intro i
  change (P i).image (glueBlocks P C hP hC e) = C i
  apply Finset.ext
  intro y
  rw [Finset.mem_image]
  constructor
  · intro ⟨q, hq, hqy⟩
    rw [glueBlocks_apply_member P C hP hC e i q hq] at hqy
    simpa [hqy] using (e i ⟨q, hq⟩).property
  · intro hy
    rcases (e i).surjective ⟨y, hy⟩ with ⟨v, hv⟩
    refine ⟨v.1, v.2, ?_⟩
    rw [glueBlocks_apply_member P C hP hC e i v.1 v.2, hv]

/-- Inverse: a family of per-pile equivs gives a realizing deck — the glued
    deck, packaged with `gluedRealizes`. -/
noncomputable def equivsToMultiPile : MultiFiber N k P C :=
  ⟨glueBlocks P C hP hC e, gluedRealizes N k P C hP hC e⟩

/-- Deck round-trip: gluing a deck's own per-pile equivs recovers the deck.
    (The other round-trip, `roundTripEquivs` — taking the per-pile equivs of a
    glued deck recovers the family — is the remaining next step; both reduce to
    `glueBlocks_apply_member` + `pileF` + `Subtype.ext`/`Equiv.ofBijective`.) -/
theorem roundTripDecks : (equivsToMultiPile N k P C hP hC (multiPileToEquivs N k P C d)).1 = d.1 := by
  apply Equiv.ext
  intro x
  obtain ⟨j, hxj⟩ := hP.1 x
  dsimp only [equivsToMultiPile]
  rw [glueBlocks_apply_member P C hP hC (multiPileToEquivs N k P C d) j x hxj]
  dsimp only [multiPileToEquivs]
  simp [pileF, pileEquiv, Equiv.ofBijective]

end

end FiniteDeck
end Shufflemath
