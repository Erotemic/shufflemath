module

public import Shufflemath.GSRSegMembership
public import Shufflemath.CommanderFiberCount
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-!
## Gate 6 batch-5a — the segregated-membership fiber has exactly `50! · 49!` decks

The `rhoRoundIdeal` / `localLift` measure headline (batch 5b) needs the exact
mass of the segregated-membership fiber.  The fiber is the set of decks whose
`membership` equals `segMembership`, which (by `membership_leftCards`) is
exactly the set of decks whose left-card set is the segregated 50-card set
`segLeft`.  That latter set is `decksWithLeft segLeft`, already counted in
`CommanderFiberCount` as `50! · 49!`.

Lemmas:
* `membershipFiber_iff_leftCardsFiber` — the two fiber predicates coincide
  pointwise (`membership d = segMembership ↔ leftCards d = segLeft`).
* `segFiber_equiv` — a bijection between the two fiber subtypes.
* `fiberSegMembership_card` — the fiber has exactly `50! · 49!` decks. This is
  the constant that appears in `localLift_mass segMembership d` and, through
  it, in the measure headline `rhoRoundIdeal = localLift segMembership`.

Proof note: the route is kept out of the `embed_m`/`Equiv.Perm` normalisation
wall (see `docs/agent_handoff.md`) by working only at the `leftCards`/
`membership` level and reusing `decksWithLeft_card`, rather than unfolding the
within-pile embedding.
-/

open Finset
open scoped Nat
open CommanderPermutation
open CommanderMembershipKernels

/-- A deck has the segregated membership exactly when its left-card set is the
  segregated left-position set. The two predicates are the same `Subtype`
  equality: `membership d = segMembership` unfolds (via `membership_leftCards`)
  to `leftCards d = segLeft`, because `segMembership.1 = segLeft`. -/
theorem membershipFiber_iff_leftCardsFiber (d : Deck) :
    membership d = segMembership ↔ leftCards d = segLeft := by
  constructor
  · -- membership d = segMembership → leftCards d = segLeft
    intro h
    have h1 : (membership d).1 = (segMembership).1 := congrArg Subtype.val h
    simpa only [membership_leftCards, segMembership] using h1
  · -- leftCards d = segLeft → membership d = segMembership
    intro h
    apply Subtype.ext
    rw [membership_leftCards]
    simpa only [segMembership] using h

/-- The segregated-membership fiber and the left-card fiber (over `segLeft`)
  are the same set, hence in bijection. This is the `Equiv` that lets the known
  `decksWithLeft_card` count be applied to the membership fiber. -/
noncomputable def segFiber_equiv :
    {d : Deck // membership d = segMembership} ≃ decksWithLeft segLeft := by
  classical
  let f : {d : Deck // membership d = segMembership} → decksWithLeft segLeft :=
    fun a => ⟨a.val, (membershipFiber_iff_leftCardsFiber a.val).mp a.property⟩
  let g : decksWithLeft segLeft → {d : Deck // membership d = segMembership} :=
    fun b => ⟨b.val, (membershipFiber_iff_leftCardsFiber b.val).mpr b.property⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro x; ext; simp only [f, g]
  · intro x; ext; simp only [f, g]

/-- The segregated-membership fiber (the decks whose `membership` is
  `segMembership`) has exactly `50! · 49!` elements: it is in bijection with
  `decksWithLeft segLeft` (the left-card fiber over the segregated 50-card set),
  which `CommanderFiberCount.decksWithLeft_card` counts as `50! · 49!`. -/
theorem fiberSegMembership_card :
    Fintype.card {d : Deck // membership d = segMembership} = Nat.factorial 50 * Nat.factorial 49 := by
  have hcard : segLeft.card = 50 := segMembership.2
  have h1 : Fintype.card {d : Deck // membership d = segMembership} = Fintype.card (decksWithLeft segLeft) :=
    Fintype.card_congr segFiber_equiv
  exact h1.trans (decksWithLeft_card segLeft hcard)

end Shufflemath
