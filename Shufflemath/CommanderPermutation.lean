import Shufflemath.OracleRefinement
import Shufflemath.GSR
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Shufflemath
namespace CommanderPermutation

/-!
# The complete 99-card permutation space and its BL macro projection

The *microscopic state* is an honest permutation of 99 individually named
cards. Its first 50 positions comprise the left working pile. Cards with
identities 0..49 are the initially-left / marked cards.

For every permutation, at least one marked card is in the left pile:
50 distinct left-position cards cannot all come from the 49 unmarked cards.
This produces a bona fide `CommanderState = Fin 50` (count 1..50), with no
clamping, modulo arithmetic, or extraneous validity subtype.

The subtype `fiber x` below consists of all full permutations whose count
is x+1. `uniformFiber` is a concrete distribution on those permutations,
provided each fiber is inhabited. Proving the resulting kernel's recovery,
identifying the pushforward of the uniform law with the hypergeometric
`commanderStationary`, and showing a physical exchange intertwines are
separate proof obligations. The generic results in `OracleRefinement` then
apply without revisiting the 50-state calculation.
-/

/-- A bijective assignment of the 99 named cards to the 99 deck positions. -/
abbrev Deck := Equiv.Perm (Fin 99)

instance : Nonempty Deck := ⟨Equiv.refl (Fin 99)⟩

/-- Position `i` in the 50-card left pile, viewed in the full deck. -/
def leftPosition (i : Fin 50) : Fin 99 :=
  ⟨i.val, by omega⟩

private theorem leftPosition_injective : Function.Injective leftPosition := by
  intro a b hab
  apply Fin.ext
  simpa [leftPosition] using congrArg Fin.val hab

/-- The cards appearing in the left 50 positions. -/
def leftCards (deck : Deck) : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image (fun i => deck (leftPosition i))

/-- The 49 cards that were initially in the right working pile. -/
def originalRight : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 99)).filter (fun card => 50 ≤ card.val)

/-- Number of initially-left cards among the current left pile. -/
def leftOriginalCount (deck : Deck) : Nat :=
  ((Finset.univ : Finset (Fin 50)).filter
    (fun i => (deck (leftPosition i)).val < 50)).card

/-- Every full deck has 50 distinct identities in the left pile. -/
theorem leftCards_card (deck : Deck) : (leftCards deck).card = 50 := by
  classical
  have hinj : Function.Injective (fun i : Fin 50 => deck (leftPosition i)) :=
    deck.injective.comp leftPosition_injective
  unfold leftCards
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- The macro count cannot exceed the left-pile size. -/
theorem leftOriginalCount_le (deck : Deck) : leftOriginalCount deck ≤ 50 := by
  classical
  have hsub :
      ((Finset.univ : Finset (Fin 50)).filter
        (fun i => (deck (leftPosition i)).val < 50)) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  simpa [leftOriginalCount] using hcard

/-- There are only 49 unmarked cards; they cannot occupy all 50 positions.
This is the precise pigeonhole argument ensuring the BL projection is valid. -/
theorem leftOriginalCount_pos (deck : Deck) : 0 < leftOriginalCount deck := by
  classical
  by_contra hpos
  have hz : leftOriginalCount deck = 0 := by omega
  have hnone :
      ((Finset.univ : Finset (Fin 50)).filter
        (fun i => (deck (leftPosition i)).val < 50)) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hz
  have hsub : leftCards deck ⊆ originalRight := by
    intro card hcard
    change card ∈
      (Finset.univ : Finset (Fin 50)).image
        (fun i => deck (leftPosition i)) at hcard
    rcases Finset.mem_image.mp hcard with ⟨i, _, rfl⟩
    have hnot : ¬ (deck (leftPosition i)).val < 50 := by
      intro hlt
      have hi : i ∈ ((Finset.univ : Finset (Fin 50)).filter
          (fun j => (deck (leftPosition j)).val < 50)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      rw [hnone] at hi
      simpa using hi
    have hright : 50 ≤ (deck (leftPosition i)).val := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hright⟩
  have hr : originalRight.card = 49 := by decide
  have hcard := Finset.card_le_card hsub
  rw [leftCards_card, hr] at hcard
  omega

/-- The concrete full-deck projection to exactly the existing 50 Commander
states, with state 0 representing one marked card and state 49 representing
all 50 marked cards. -/
def project (deck : Deck) : BernoulliLaplace.CommanderState :=
  ⟨leftOriginalCount deck - 1, by
    have hlo := leftOriginalCount_pos deck
    have hhi := leftOriginalCount_le deck
    omega⟩

/-- The projection is exact, with no saturating arithmetic. -/
theorem project_count (deck : Deck) :
    (project deck).val + 1 = leftOriginalCount deck := by
  have hpos := leftOriginalCount_pos deck
  change leftOriginalCount deck - 1 + 1 = leftOriginalCount deck
  omega

/-- Full permutation fiber with the specified number of original-left cards. -/
abbrev Fiber (x : BernoulliLaplace.CommanderState) :=
  {deck : Deck // project deck = x}

/-- A concrete uniform conditional law on the *full permutation fiber*.
The surjectivity argument is explicit, so no empty-fiber distribution can
silently be introduced. Its recovery and hypergeometric marginal theorems
are the next two counting proof obligations. -/
noncomputable def uniformFiber
    (hsurj : Function.Surjective project) :
    FiniteKernel BernoulliLaplace.CommanderState Deck := by
  classical
  intro x
  letI : Nonempty (Fiber x) := by
    obtain ⟨deck, hdeck⟩ := hsurj x
    exact ⟨⟨deck, hdeck⟩⟩
  exact (GSR.uniformDist (Fiber x)).map Subtype.val

/-- Applying a deterministic kernel is the same as pushing the
simplex forward along its underlying function. -/
private theorem apply_deterministic {γ δ : Type*} (mu : Dist γ) (f : γ → δ) :
    FiniteKernel.apply mu (FiniteKernel.deterministic f) = mu.map f := by
  change (mu.map (fun x => Convexity.StdSimplex.single (f x))).join = mu.map f
  rw [Dist.join_sConvexComb]
  calc
    _ = ((mu.map f).map Convexity.StdSimplex.single).sConvexComb := by
      rw [Convexity.StdSimplex.map_map]
    _ = mu.map f := Convexity.StdSimplex.iConvexComb_single (mu.map f)

/-- Uniformly sampling a genuine `project`-fiber recovers its macrostate.
This discharges the left-inverse obligation for the concrete 99-card lift;
only the separate proof that *all* 50 fibers are inhabited is required by
the definition. -/
theorem uniformFiber_recovers (hsurj : Function.Surjective project) :
    FiniteKernel.comp (uniformFiber hsurj)
      (FiniteKernel.deterministic project) = FiniteKernel.identity := by
  classical
  funext x
  haveI : Nonempty (Fiber x) := by
    obtain ⟨deck, hdeck⟩ := hsurj x
    exact ⟨⟨deck, hdeck⟩⟩
  change FiniteKernel.apply ((GSR.uniformDist (Fiber x)).map Subtype.val)
    (FiniteKernel.deterministic project) = Dist.pointMass x
  rw [apply_deterministic]
  rw [Convexity.StdSimplex.map_map]
  have hconstant : (fun deck : Fiber x => project deck.val) = (fun _ => x) := by
    funext deck
    exact deck.property
  change (GSR.uniformDist (Fiber x)).map
    (fun deck : Fiber x => project deck.val) = Dist.pointMass x
  rw [hconstant]
  exact Convexity.StdSimplex.map_const (GSR.uniformDist (Fiber x)) x

/-- The concrete oracle exchange on complete 99-card permutations,
parameterized by the proof that every requested fiber is realizable. -/
noncomputable def idealExchange25
    (hsurj : Function.Surjective project) : FiniteKernel Deck Deck :=
  OracleRefinement.oracleStep project (uniformFiber hsurj)
    BernoulliLaplace.commanderExchange25

/-! ## Full-deck exact statements, with the remaining hypotheses explicit -/

/-- A concrete 99-card permutation-space theorem: as soon as uniform fiber
sampling is shown to recover the `Fin 50` count, two ideal oracle exchanges
have exactly the earlier rational TV distance. This no longer quantifies over
an unspecified microstate type. -/
theorem two_oracle_exchanges_exact
    (hsurj : Function.Surjective project) :
    Dist.tv
      (FiniteKernel.run (idealExchange25 hsurj) 2
        (FiniteKernel.apply
          (Dist.pointMass BernoulliLaplace.commanderSegregatedState)
          (uniformFiber hsurj)))
      (FiniteKernel.apply BernoulliLaplace.commanderStationary
        (uniformFiber hsurj)) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  classical
  exact OracleRefinement.commander_oracle_two_exact
    project (uniformFiber hsurj) (uniformFiber_recovers hsurj)

/-- If the hypergeometric macro law is confirmed to disintegrate the
uniform law on 99! permutations, this is the desired explicit full-deck TV
identity. The conditional premise is intentionally visible: the cardinal
fiber law remains to be proved in Lean. -/
theorem two_oracle_exchanges_uniform
    (hsurj : Function.Surjective project)
    (huniform : FiniteKernel.apply BernoulliLaplace.commanderStationary
      (uniformFiber hsurj) = GSR.uniformDist Deck) :
    Dist.tv
      (FiniteKernel.run (idealExchange25 hsurj) 2
        (FiniteKernel.apply
          (Dist.pointMass BernoulliLaplace.commanderSegregatedState)
          (uniformFiber hsurj)))
      (GSR.uniformDist Deck) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  classical
  rw [← huniform]
  exact two_oracle_exchanges_exact hsurj

end CommanderPermutation
end Shufflemath
