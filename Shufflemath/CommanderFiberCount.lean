module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Basic
public import Shufflemath.BernoulliLaplaceFiber
public import Shufflemath.CommanderPermutation

@[expose] public section

namespace Shufflemath
open Shufflemath.CommanderPermutation

/-!
## Exact counting of the 99-card commander fiber (F1)

`HasCommanderFiberCounts` (stated in `CommanderFullDeckDisintegration`) says
the stationary commander state at a count `x` has mass equal to the fraction of
decks whose `leftOriginalCount = x`.  This module builds the exact finite
combinatorics that proves it.

Status (compiles, no `sorry`/axiom):

* `leftPile S` / `rightPile S` : the 50-card and 49-card piles as plain
  Finset-membership subtypes `{x // x ∈ S}` / `{x // x ∈ Finset.univ \ S}`;
  `Fintype.Subtype.fintype` supplies their `Fintype` instances.
* `leftEquiv S d h` / `rightEquiv S d h` : the left and right actions of a
  deck `d`, restricted to the 50 left (resp. 49 right) positions, as
  bijections `Fin 50 ≃ leftPile S` (resp. `Fin 49 ≃ rightPile S`), built from
  the explicit `leftFun` / `rightFun` via `Equiv.ofBijective` (injective by
  deck injectivity, surjective by the `leftCards d = S` image / permutation
  surjectivity onto the complement).  `leftEquiv_apply` / `rightEquiv_apply`
  recover the deck's card at each index.
* `leftEquiv_card` / `rightEquiv_card` : there are exactly `50!` / `49!` such
  bijections (`Fintype.card_equiv` + `Fintype.card_of_subtype`).
* `deckFun` / `pasteDeck` / `decksWithLeft` : the deck assembled from a left
  and a right bijection (Set-form), and the subtype of decks with a given
  left pile.

Remaining step (F1 completion, see `docs/agent_handoff.md`): build the
deck-level bijection
`decksWithLeft S ≃ (Fin 50 ≃ leftPile S) × (Fin 49 ≃ rightPile S)` and hence
`Fintype.card (decksWithLeft S) = 50! · 49!` (via `Fintype.card_prod` and the
two card theorems), then the Bernoulli–Laplace fiber mass and
`HasCommanderFiberCounts`.
-/

/-- The 49 right positions, as `Fin 99` (the left positions
  `leftPosition` are inherited from `CommanderPermutation`). -/
def rightPosition (j : Fin 49) : Fin 99 := ⟨50 + j.val, by omega⟩

/-- The 49-card right pile as a finite subtype: the complement of `S`, written
  as membership in the Finset set-difference so `Fintype.Subtype.fintype`
  supplies its `Fintype` instance. -/
abbrev rightPile (S : Finset (Fin 99)) := {x : Fin 99 // x ∈ (Finset.univ : Finset (Fin 99)) \ S}

/-- The 50 left-pile cards as a plain Finset-membership subtype. -/
abbrev leftPile (S : Finset (Fin 99)) := {x : Fin 99 // x ∈ S}

/-- The left-pile index of a position in the left half. -/
def leftIndex (p : Fin 99) (h : p.val < 50) : Fin 50 := ⟨p.val, h⟩

/-- The right-pile index of a position in the right half. -/
def rightIndex (p : Fin 99) (h : ¬ p.val < 50) : Fin 49 := ⟨p.val - 50, by omega⟩

theorem leftIndex_leftPos (i : Fin 50) (h : (leftPosition i).val < 50) :
    leftIndex (leftPosition i) h = i := by
  apply Fin.ext; simp only [leftIndex, leftPosition]

theorem rightIndex_rightPos (j : Fin 49) (h : ¬ (rightPosition j).val < 50) :
    rightIndex (rightPosition j) h = j := by
  apply Fin.ext; simp only [rightIndex, rightPosition]; omega

theorem leftPosition_leftIndex (p : Fin 99) (h : p.val < 50) :
    leftPosition (leftIndex p h) = p := by
  apply Fin.ext; simp only [leftPosition, leftIndex]

theorem rightPosition_rightIndex (p : Fin 99) (h : ¬ p.val < 50) :
    rightPosition (rightIndex p h) = p := by
  have hge : 50 ≤ p.val := by omega
  apply Fin.ext; simp only [rightPosition, rightIndex]
  omega

/-- Decks whose left 50 cards are exactly `S`. -/
abbrev decksWithLeft (S : Finset (Fin 99)) := {d : Deck // leftCards d = S}

-- ============================== LEFT ACTION ==============================

def leftCardInS (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (i : Fin 50) :
    d (leftPosition i) ∈ S := by
  have hfin : d (leftPosition i) ∈ leftCards d := Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  rw [h] at hfin
  exact hfin

def leftFun (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (i : Fin 50) :
    leftPile S := ⟨d (leftPosition i), leftCardInS S d h i⟩

theorem leftFun_injective (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Function.Injective (leftFun S d h) := by
  intro i j heq
  have hval : d (leftPosition i) = d (leftPosition j) := by
    simpa [leftFun, leftCardInS] using congrArg Subtype.val heq
  exact Fin.ext (by simpa only [leftPosition] using congrArg Fin.val (d.injective hval))

theorem leftFun_surjective (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Function.Surjective (leftFun S d h) := by
  intro x
  have hx : x.val ∈ leftCards d := by simpa [h] using x.property
  unfold leftCards at hx
  rcases Finset.mem_image.1 hx with ⟨i, _, hval⟩
  use i
  exact Subtype.ext (by simpa [leftFun, leftCardInS] using hval)

/-- The left action of `d`, restricted to the 50 left positions, is a
  bijection `Fin 50 ≃ leftPile S`. -/
noncomputable def leftEquiv (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Equiv (Fin 50) (leftPile S) :=
  Equiv.ofBijective (leftFun S d h) (by
    exact ⟨leftFun_injective S d h, leftFun_surjective S d h⟩)

/-- Applying the left action equiv at a left index recovers the deck's card. -/
theorem leftEquiv_apply (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (i : Fin 50) :
    (leftEquiv S d h) i = ⟨d (leftPosition i), leftCardInS S d h i⟩ := by
  unfold leftEquiv
  change (leftFun S d h) i = ⟨d (leftPosition i), leftCardInS S d h i⟩
  dsimp only [leftFun, leftCardInS]

/-- There are exactly `50!` left action bijections. -/
theorem leftEquiv_card (S : Finset (Fin 99)) (hcard : S.card = 50) :
    Fintype.card (Equiv (Fin 50) (leftPile S)) = Nat.factorial 50 := by
  have hS : Fintype.card (leftPile S) = 50 := by
    classical
    dsimp only [leftPile]
    rw [Fintype.card_of_subtype (p := fun x => x ∈ S) (s := S) (H := fun _ => Iff.rfl)]
    exact hcard
  have e : Fin 50 ≃ leftPile S := (Fintype.equivFinOfCardEq hS).symm
  rw [Fintype.card_equiv e, Fintype.card_fin]

-- ============================== RIGHT ACTION ==============================

def rightCardInS (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (j : Fin 49) :
    d (rightPosition j) ∈ (Finset.univ : Finset (Fin 99)) \ S := by
  simp only [Finset.mem_sdiff]
  constructor
  · exact Finset.mem_univ _
  · intro hin
    have hL : d (rightPosition j) ∈ leftCards d := by simpa [h] using hin
    unfold leftCards at hL
    rcases Finset.mem_image.1 hL with ⟨i, _, hval⟩
    have hpos := d.injective hval
    have hlt : (leftPosition i).val < 50 := by simpa [leftPosition]
    rw [hpos] at hlt
    have hge : 50 ≤ (rightPosition j).val := by simpa [rightPosition]
    omega

def rightFun (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (j : Fin 49) :
    rightPile S := ⟨d (rightPosition j), rightCardInS S d h j⟩

theorem rightFun_injective (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Function.Injective (rightFun S d h) := by
  intro i j heq
  have hval : d (rightPosition i) = d (rightPosition j) := by
    simpa [rightFun, rightCardInS] using congrArg Subtype.val heq
  have hv : (rightPosition i).val = (rightPosition j).val := by
    simpa only [Fin.val] using congrArg Fin.val (d.injective hval)
  exact Fin.ext (by simp only [rightPosition] at hv ⊢; omega)

theorem rightFun_surjective (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Function.Surjective (rightFun S d h) := by
  intro x
  have hp : x.val ∈ (Finset.univ : Finset (Fin 99)) \ S := x.property
  simp only [Finset.mem_sdiff] at hp
  have hxnot : ¬ x.val ∈ S := hp.2
  rcases d.surjective x.val with ⟨p, hp0⟩
  by_cases hleft : p.val < 50
  · have hL : x.val ∈ leftCards d := by
      unfold leftCards
      exact Finset.mem_image.mpr ⟨leftIndex p hleft, by simp, by
        simpa only [leftPosition, leftIndex, hleft] using hp0⟩
    exfalso
    exact hxnot (by simpa [h] using hL)
  · use rightIndex p hleft
    simpa [rightFun, rightCardInS, rightPosition_rightIndex p hleft, hp0]

/-- The right action of `d`, restricted to the 49 right positions, is a
  bijection `Fin 49 ≃ rightPile S` (the complement pile). -/
noncomputable def rightEquiv (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) :
    Equiv (Fin 49) (rightPile S) :=
  Equiv.ofBijective (rightFun S d h) (by
    exact ⟨rightFun_injective S d h, rightFun_surjective S d h⟩)

/-- Applying the right action equiv at a right index recovers the deck's card. -/
theorem rightEquiv_apply (S : Finset (Fin 99)) (d : Deck) (h : leftCards d = S) (j : Fin 49) :
    (rightEquiv S d h) j = ⟨d (rightPosition j), rightCardInS S d h j⟩ := by
  unfold rightEquiv
  change (rightFun S d h) j = ⟨d (rightPosition j), rightCardInS S d h j⟩
  dsimp only [rightFun, rightCardInS]

/-- There are exactly `49!` right action bijections. -/
theorem rightEquiv_card (S : Finset (Fin 99)) (hcard : S.card = 50) :
    Fintype.card (Equiv (Fin 49) (rightPile S)) = Nat.factorial 49 := by
  have hS : Fintype.card (rightPile S) = 49 := by
    classical
    dsimp only [rightPile]
    rw [Fintype.card_of_subtype (p := fun x => x ∈ (Finset.univ : Finset (Fin 99)) \ S)
        (s := (Finset.univ : Finset (Fin 99)) \ S) (H := fun _ => Iff.rfl),
      Finset.card_sdiff_of_subset]
    · simp [Finset.card_univ, hcard]
    · exact Finset.subset_univ S
  have e : Fin 49 ≃ rightPile S := (Fintype.equivFinOfCardEq hS).symm
  rw [Fintype.card_equiv e, Fintype.card_fin]


-- =================== subtype-form deck assembly ===================

def deckFunSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S))
    (eR : Equiv (Fin 49) (rightPile S))
    (p : Fin 99) : Fin 99 :=
  if hL : p.val < 50 then (eL (leftIndex p hL)).val else (eR (rightIndex p hL)).val

def deckFunInvSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S))
    (eR : Equiv (Fin 49) (rightPile S))
    (y : Fin 99) : Fin 99 :=
  if h : y ∈ S then leftPosition (eL.symm ⟨y, h⟩)
  else rightPosition (eR.symm ⟨y, by simp [h, Finset.mem_univ, Finset.mem_sdiff]⟩)

lemma deckFunSub_left (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S))
    (i : Fin 50) : deckFunSub S eL eR (leftPosition i) = (eL i).val := by
  unfold deckFunSub
  split_ifs with hL
  · simpa [leftIndex_leftPos i hL]
  · exfalso
    have hlt : (leftPosition i).val < 50 := by simp only [leftPosition]; exact i.isLt
    exact hL hlt

lemma deckFunSub_right (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S))
    (j : Fin 49) : deckFunSub S eL eR (rightPosition j) = (eR j).val := by
  unfold deckFunSub
  split_ifs with hL
  · exfalso
    have hge : ¬ (rightPosition j).val < 50 := by simp only [rightPosition]; omega
    exact hge hL
  · simpa [rightIndex_rightPos j hL]

theorem left_invSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S))
    (y : Fin 99) : deckFunSub S eL eR (deckFunInvSub S eL eR y) = y := by
  unfold deckFunInvSub
  split_ifs with h
  · let i := eL.symm ⟨y, h⟩
    rw [deckFunSub_left]
    change (eL (eL.symm ⟨y, h⟩)).val = y
    rw [eL.apply_symm_apply]
  · let j := eR.symm ⟨y, by simp [h, Finset.mem_univ, Finset.mem_sdiff]⟩
    rw [deckFunSub_right]
    change (eR (eR.symm ⟨y, by simp [h, Finset.mem_univ, Finset.mem_sdiff]⟩)).val = y
    rw [eR.apply_symm_apply]

noncomputable def pasteDeckSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S)) : Deck :=
  Equiv.ofBijective (deckFunSub S eL eR) (by
    have hSurj : Function.Surjective (deckFunSub S eL eR) := by
      intro y
      exact ⟨deckFunInvSub S eL eR y, left_invSub S eL eR y⟩
    exact ⟨(Finite.injective_iff_surjective (f := deckFunSub S eL eR)).2 hSurj, hSurj⟩)

theorem pasteDeckSub_leftCards (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S)) :
    leftCards (pasteDeckSub S eL eR) = S := by
  have hmain : leftCards (pasteDeckSub S eL eR) =
      (Finset.univ : Finset (Fin 50)).image (fun i => (eL i).val) := by
    dsimp only [leftCards, pasteDeckSub, deckFunSub]
    rw [Equiv.coe_ofBijective]
    congr
    funext i
    simpa [deckFunSub_left]
  rw [hmain]
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hx
    exact (by simpa [hi.symm] using (eL i).property)
  · intro hx
    refine Finset.mem_image.mpr ⟨eL.symm ⟨x, hx⟩, by simp, ?_⟩
    simpa [eL.apply_symm_apply]

-- =================== round-trip lemmas ===================

theorem pasteDeckSub_self (S : Finset (Fin 99)) (d : Deck) (hd : leftCards d = S) :
    pasteDeckSub S (leftEquiv S d hd) (rightEquiv S d hd) = d := by
  unfold pasteDeckSub
  apply Equiv.ext
  intro p
  change (deckFunSub S (leftEquiv S d hd) (rightEquiv S d hd)) p = d p
  unfold deckFunSub
  split_ifs with hL
  · simpa [leftEquiv_apply, leftPosition_leftIndex p hL]
  · simpa [rightEquiv_apply, rightPosition_rightIndex p hL]

theorem leftEquiv_of_pasteDeckSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S)) :
    leftEquiv S (pasteDeckSub S eL eR) (pasteDeckSub_leftCards S eL eR) = eL := by
  apply Equiv.ext
  intro i
  have hcard : (pasteDeckSub S eL eR) (leftPosition i) = (eL i).val := deckFunSub_left S eL eR i
  change (leftFun S (pasteDeckSub S eL eR) (pasteDeckSub_leftCards S eL eR)) i = eL i
  dsimp only [leftFun, leftCardInS]
  apply Subtype.ext
  simpa [hcard]

theorem rightEquiv_of_pasteDeckSub (S : Finset (Fin 99))
    (eL : Equiv (Fin 50) (leftPile S)) (eR : Equiv (Fin 49) (rightPile S)) :
    rightEquiv S (pasteDeckSub S eL eR) (pasteDeckSub_leftCards S eL eR) = eR := by
  apply Equiv.ext
  intro j
  have hcard : (pasteDeckSub S eL eR) (rightPosition j) = (eR j).val := deckFunSub_right S eL eR j
  change (rightFun S (pasteDeckSub S eL eR) (pasteDeckSub_leftCards S eL eR)) j = eR j
  dsimp only [rightFun, rightCardInS]
  apply Subtype.ext
  simpa [hcard]

-- =================== deck-level bijection ===================

abbrev decksLR_prod (S : Finset (Fin 99)) :=
    (Fin 50 ≃ leftPile S) × (Fin 49 ≃ rightPile S)

noncomputable def toLR (S : Finset (Fin 99)) (d : decksWithLeft S) : decksLR_prod S :=
  (leftEquiv S d.val d.property, rightEquiv S d.val d.property)

noncomputable def fromLR (S : Finset (Fin 99)) (p : decksLR_prod S) : decksWithLeft S :=
  ⟨pasteDeckSub S p.1 p.2, pasteDeckSub_leftCards S p.1 p.2⟩

theorem fromLR_toLR (S : Finset (Fin 99)) (d : decksWithLeft S) :
    fromLR S (toLR S d) = d := by
  unfold fromLR toLR
  apply Subtype.ext
  simpa [pasteDeckSub_self S d.val d.property]

theorem toLR_fromLR (S : Finset (Fin 99)) (p : decksLR_prod S) :
    toLR S (fromLR S p) = p := by
  unfold toLR fromLR
  rcases p with ⟨eL, eR⟩
  simp [leftEquiv_of_pasteDeckSub, rightEquiv_of_pasteDeckSub]

noncomputable def decksLR (S : Finset (Fin 99)) :
    decksWithLeft S ≃ decksLR_prod S := by
  have hInj : Function.Injective (toLR S) := by
    intro d1 d2 h
    calc d1 = fromLR S (toLR S d1) := (fromLR_toLR S d1).symm
       _ = fromLR S (toLR S d2) := by rw [h]
       _ = d2 := fromLR_toLR S d2
  have hSurj : Function.Surjective (toLR S) := by
    intro p
    exact ⟨fromLR S p, toLR_fromLR S p⟩
  exact Equiv.ofBijective (toLR S) (by exact ⟨hInj, hSurj⟩)

/-- The 99-card decks with left pile `S` are in bijection with a left and a
  right action, so there are exactly `50! · 49!` of them. -/
theorem decksWithLeft_card (S : Finset (Fin 99)) (hcard : S.card = 50) :
    Fintype.card (decksWithLeft S) = Nat.factorial 50 * Nat.factorial 49 := by
  rw [Fintype.card_congr (decksLR S), Fintype.card_prod]
  simp [leftEquiv_card S hcard, rightEquiv_card S hcard]
end Shufflemath
end
