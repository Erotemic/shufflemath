module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
public import Shufflemath._Probe47v
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderA3Kernel

open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace
open Finset

/-!
# A3 kernel: the post-exchange count is the Bernoulli-Laplace transition

F3 A3 (the membership-exchange law) has a *count* half and a *measure* half.
This module lands the count half in the main library: the number of `(L, R)`
pairs of 25-subsets whose post-exchange left pile has exactly `n`
originally-left cards equals the Bernoulli--Laplace transition numerator at
the source count `leftOriginalCount d`.

It is the 47v fiber-product kernel
(`_Probe47v.transitionNumerator_eq_fiberProduct`) with the post-exchange-
*count* predicate (`newLeftOriginalCount_eq`) substituted for the raw
marked-count predicate: the two predicates are pointwise equal, so the filtered
sets (over the same `(L, R)` product) are equal, and the deck does not enter the
result — only its source count `leftOriginalCount d` does.  This is the
deck-independence of the post-exchange *count distribution*, the exact
"remaining step" the `hMembershipExchange` assembly plan names for the
`rawExchangeMembership_count` LHS.
-/

variable (d : Deck)

/-- The 25-position-subset choice spaces agree extensionally with the 47v
    kernel's `s50`/`t49`: both are exactly the 25-element subsets of the same
    `Fin 50` / `Fin 49` universes. -/
private theorem leftChoices_eq_s50 : leftChoices = _Probe47v.s50 := by
  apply Finset.ext
  intro L
  simp only [leftChoices, _Probe47v.s50, Finset.mem_powersetCard]

/-- The 25-position-subset choice spaces agree extensionally with the 47v
    kernel's `s50`/`t49` (right pile). -/
private theorem rightChoices_eq_t49 : rightChoices = _Probe47v.t49 := by
  apply Finset.ext
  intro R
  simp only [rightChoices, _Probe47v.t49, Finset.mem_powersetCard]

/-- The number of `(L, R)` pairs of 25-subsets of the two piles whose
    post-exchange left pile contains exactly `n` originally-left (marked) cards
    equals the Bernoulli--Laplace transition numerator
    `transitionNumerator 99 50 25 (leftOriginalCount d) n`: the post-exchange
    count is `leftOriginalCount d - markedInLeft d L + markedInRight d R`
    (`newLeftOriginalCount_eq`), and the 47v fiber-product kernel counts exactly
    that fiber.  In particular the value depends on the deck `d` only through
    its source count `leftOriginalCount d`. -/
theorem newLeftCount_eq_transitionNumerator (d : Deck) (n : Nat) :
    ((leftChoices ×ˢ rightChoices).filter
       (fun p : Finset (Fin 50) × Finset (Fin 49) =>
         (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
      transitionNumerator 99 50 25 (leftOriginalCount d) n := by
  -- rewrite the count predicate to the marked-count fiber (pointwise equal)
  have hPred :
      (leftChoices ×ˢ rightChoices).filter
          (fun p => (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n) =
      (leftChoices ×ˢ rightChoices).filter
        (fun p => (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n) := by
    ext p
    simp only [Finset.mem_filter, newLeftOriginalCount_eq]
  -- bridge the choice spaces to the 47v kernel's s50 ×ˢ t49 (extensionally equal)
  have hSpace :
      (leftChoices ×ˢ rightChoices).filter
          (fun p => (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n) =
      (_Probe47v.s50 ×ˢ _Probe47v.t49).filter
        (fun p => (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n) := by
    simpa [leftChoices_eq_s50, rightChoices_eq_t49]
  calc
    _ =
        ((_Probe47v.s50 ×ˢ _Probe47v.t49).filter
          (fun p => (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n)).card := by
      simpa [hPred, hSpace]
    _ = transitionNumerator 99 50 25 (leftOriginalCount d) n :=
      (_Probe47v.transitionNumerator_eq_fiberProduct d n).symm

/-- **A3 count-half deck-independence.**  Two decks with the same source count
    induce the *same* post-exchange count distribution: the count of `(L, R)`
    pairs landing on `n` originally-left cards is a function of `leftOriginalCount`
    alone.  This is the fiber-average collapse for the `rawExchangeMembership_count`
    LHS: averaging the (deck-independent) count law over the uniform project fiber
    leaves it unchanged. -/
theorem newLeftCount_deckIndependent (d d' : Deck) (n : Nat)
    (h : leftOriginalCount d = leftOriginalCount d') :
    ((leftChoices ×ˢ rightChoices).filter
       (fun p : Finset (Fin 50) × Finset (Fin 49) =>
         (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
      ((leftChoices ×ˢ rightChoices).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (newLeftCards d' p.1 p.2 ∩ leftOrigSet).card = n)).card := by
  calc
    _ = transitionNumerator 99 50 25 (leftOriginalCount d) n :=
        newLeftCount_eq_transitionNumerator d n
    _ = transitionNumerator 99 50 25 (leftOriginalCount d') n := by simpa [h]
    _ =
        ((leftChoices ×ˢ rightChoices).filter
          (fun p => (newLeftCards d' p.1 p.2 ∩ leftOrigSet).card = n)).card :=
        (newLeftCount_eq_transitionNumerator d' n).symm

end CommanderA3Kernel
end Shufflemath
