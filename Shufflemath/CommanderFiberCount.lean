import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Basic
import Shufflemath.BernoulliLaplaceFiber
import Shufflemath.CommanderPermutation

namespace Shufflemath

open Shufflemath.CommanderPermutation

/-!
## Exact counting of the 99-card commander fiber (F1)

`HasCommanderFiberCounts` (stated in `CommanderFullDeckDisintegration`) says
the stationary commander state at a count `x` has mass equal to the fraction of
decks whose `leftOriginalCount = x`.  This module builds the exact finite
combinatorics that proves it.

Status (compiles, no `sorry`/axiom):

* `leftEquiv (d) (h)` : the left action of a deck `d`, restricted to the 50
  left positions, is a bijection `Fin 50 ≃ (left pile = S)`, built with
  `Equiv.ofInjective` plus an equality of its `Set.range` with `S` (avoids
  hand-built subtype witnesses).
* `leftEquiv_card` : there are exactly `50!` such bijections.
* `rightEquiv (d) (h)` : the right action, restricted to the 49 right
  positions, is a bijection `Fin 49 ≃ (Fin 99 ∖ S)` (the complement pile).
* `rightEquiv_card` : there are exactly `49!` such bijections (the right pile
  is the subtype `{x // x ∈ Finset.univ \ S}` with `Finset.card_compl` size 49).

Remaining step (F1 completion, see `docs/agent_handoff.md`): combine the two
actions into a deck-level bijection
`decksWithLeft S ≃ (Fin 50 ≃ S) × (Fin 49 ≃ (Fin 99 ∖ S))`, giving
`Fintype.card (decksWithLeft S) = 50! · 49!`, and the Bernoulli–Laplace fiber
mass.  The one technical subtlety is that `rightEquiv`'s codomain is the *Set*
form `((Finset.univ \ S) : Set)` while `rightPile S` is the *Finset*-membership
subtype; their `Fintype`s coincide (`Fintype.card_coe` / `Finset.card_compl`),
so the two count theorems already agree and only the equiv-level cast between
the two representations is left.
-/

/-- The 49 right positions, as `Fin 99` (the left positions
  `leftPosition` are inherited from `CommanderPermutation`). -/
def rightPosition (j : Fin 49) : Fin 99 := ⟨50 + j.val, by omega⟩

/-- The 49-card right pile as a finite subtype: the complement of `S`, written
  as membership in the Finset set-difference so `Fintype.Subtype.fintype`
  supplies its `Fintype` instance. -/
abbrev rightPile (S : Finset (Fin 99)) := {x : Fin 99 // x ∈ (Finset.univ : Finset (Fin 99)) \ S}


section

variable (S : Finset (Fin 99)) (hcard : S.card = 50)

/-- The left action of `d`, restricted to the 50 left positions, is a
  bijection `Fin 50 ≃ (left pile = S)`. -/
noncomputable def leftEquiv (d : Deck) (h : leftCards d = S) :
    Equiv (Fin 50) (S : Set (Fin 99)) := by
  have hinj : Function.Injective (fun i : Fin 50 => d (leftPosition i)) := by
    intro i j hval
    exact Fin.ext (by
      simpa only [leftPosition] using congrArg Fin.val (d.injective hval))
  have hrange : Set.range (fun i : Fin 50 => d (leftPosition i)) = (S : Set (Fin 99)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hm : d (leftPosition i) ∈ leftCards d :=
        Finset.mem_image.mpr ⟨i, by simp, rfl⟩
      rw [h] at hm
      exact Finset.mem_coe.mpr hm
    · intro hx
      have hfin : x ∈ leftCards d := by simpa only [h, Finset.mem_coe] using hx
      obtain ⟨i, _, hval⟩ := Finset.mem_image.1 hfin
      exact ⟨i, by simpa using hval⟩
  exact hrange ▸ Equiv.ofInjective (fun i : Fin 50 => d (leftPosition i)) hinj

/-- The right action of `d`, restricted to the 49 right positions, is a
  bijection `Fin 49 ≃ (Fin 99 ∖ S)` (the complement of the left pile). -/
noncomputable def rightEquiv (d : Deck) (h : leftCards d = S) :
    Equiv (Fin 49) ((Finset.univ : Finset (Fin 99)) \ S : Set (Fin 99)) := by
  let f (j : Fin 49) : Fin 99 := d (rightPosition j)
  have hinj : Function.Injective f := by
    intro i j hval
    have heq : 50 + i.val = 50 + j.val := by
      simpa only [rightPosition] using congrArg Fin.val (d.injective hval)
    exact Fin.ext (Nat.add_left_cancel heq)
  have hrange : Set.range f = ((Finset.univ : Finset (Fin 99)) \ S : Set (Fin 99)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      have hnotL : d (rightPosition j) ∉ leftCards d := by
        by_contra hc
        obtain ⟨i, _, hv⟩ := Finset.mem_image.1 hc
        have hp : leftPosition i = rightPosition j := d.injective (by simpa using hv)
        have hve : i.val = 50 + j.val := by
          simp only [leftPosition, rightPosition] at hp
          exact congrArg Fin.val hp
        omega
      have hnotS : d (rightPosition j) ∉ S := h ▸ hnotL
      have hnotSset : d (rightPosition j) ∉ (S : Set (Fin 99)) := by
        simpa only [Finset.mem_coe] using hnotS
      exact ⟨by simp, hnotSset⟩
    · intro hx
      rcases hx with ⟨_, hxnotSset⟩
      have hxnot : x ∉ S := by
        simpa only [Finset.mem_coe] using hxnotSset
      obtain ⟨p, hpc⟩ := d.surjective x
      by_cases hp : p.val < 50
      · exfalso
        let iL : Fin 50 := ⟨p.val, hp⟩
        have hLpos : p = leftPosition iL := by
          apply Fin.ext; simp only [leftPosition, iL]
        have hml : d (leftPosition iL) ∈ leftCards d :=
          Finset.mem_image.mpr ⟨iL, Finset.mem_univ iL, by
            apply Fin.ext; simp only [leftPosition, iL]⟩
        have hms : d (leftPosition iL) ∈ S := h ▸ hml
        have hxs : x ∈ S := by rw [hpc.symm, hLpos]; exact hms
        exact hxnot (Finset.mem_coe.mp (Finset.mem_coe.mpr hxs))
      · let iR : Fin 49 := ⟨p.val - 50, by omega⟩
        have hRpos : p = rightPosition iR := by
          apply Fin.ext; simp only [rightPosition, iR]; omega
        refine ⟨iR, ?_⟩
        show d (rightPosition iR) = x
        rw [hRpos.symm]
        exact hpc
  exact hrange ▸ Equiv.ofInjective f hinj

/-- There are `50!` bijections `Fin 50 ≃ S`. -/
theorem leftEquiv_card (S : Finset (Fin 99)) (hcard : S.card = 50) :
    Fintype.card (Equiv (Fin 50) (S : Set (Fin 99))) = Nat.factorial 50 := by
  have hS : Fintype.card (S : Set (Fin 99)) = 50 := by
    rw [← Set.toFinset_card]; simp; exact hcard
  have e : Fin 50 ≃ (S : Set (Fin 99)) := (Fintype.equivFinOfCardEq hS).symm
  rw [Fintype.card_equiv e, Fintype.card_fin]



/-- There are `49!` bijections `Fin 49 ≃ (Fin 99 ∖ S)`. -/
theorem rightEquiv_card (S : Finset (Fin 99)) (hcard : S.card = 50) :
    Fintype.card (Equiv (Fin 49) (rightPile S)) = Nat.factorial 49 := by
  have hR : Fintype.card (rightPile S) = 49 := by
    classical
    dsimp only [rightPile]
    rw [Fintype.card_coe, ← Finset.compl_eq_univ_sdiff, Finset.card_compl,
      Fintype.card_fin, hcard]
  have e : Fin 49 ≃ (rightPile S) := (Fintype.equivFinOfCardEq hR).symm
  rw [Fintype.card_equiv e, Fintype.card_fin]

end

end Shufflemath