module

public import Shufflemath.GSRDeckRound
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderLocalGSR
public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Tactic

/-!
## The segregated-membership fiber and the within-pile (local-GSR) round (Gate 6)

Gate 6 studies the **within-pile** GSR round on the 99-card deck: the left
(50-card) and right (49-card) piles are each riffled by an *independent* finite
GSR, and the round is the product of the two within-pile permutation laws pushed
through the pile-embedding.  Because the two piles never interleave, the round
preserves which named cards sit in the left pile, so it stays inside a single
**segregated-membership** fiber: the `Membership` whose left set is the 50
left-pile positions `{0..49}`.

This module lands the Commander-frame half of that bridge:

* `segLeft` / `segMembership` — the segregated 50-card left set and the
  corresponding `Membership`.
* `leftCards_id_eq_segLeft` — the identity (segregated-start) deck has exactly
  the segregated left-card set.
* `membership_reorderedDeck_segregated` — reordering the segregated start within
  the piles (the deterministic within-pile reindexing `reorderedDeck`) keeps the
  deck in the segregated-membership fiber, so its `membership` is `segMembership`.

The complementary FiniteDeck-frame fact (the embedding's left-card set is the
segregated left-position set) is `bridgeA_leftCards` in `GSRDeckBridge.lean`.
Together they characterise the within-pile round's support as the
segregated-membership fiber, the structural core of the `rhoRoundIdeal` /
`localLift` bridge (see `docs/agent_handoff.md`).
-/

@[expose] public section

namespace Shufflemath

open Finset
open scoped Nat
open CommanderPermutation
open CommanderMembershipKernels
open CommanderLocalGSR

theorem hm5099 : 50 ≤ 99 := by norm_num

/-- The 50 segregated left-pile positions `{0..49}`. -/
def segLeft : Finset (Fin 99) := FiniteDeck.leftPositions 99 50 hm5099

/-- The segregated left-pile membership (a 50-card left set). -/
def segMembership : Membership :=
  ⟨segLeft, by dsimp only [segLeft]; exact FiniteDeck.leftPositions_card 99 50 hm5099⟩

-- The identity deck (the segregated start) has exactly the segregated left-card set.
theorem leftCards_id_eq_segLeft : leftCards (Equiv.refl (Fin 99)) = segLeft := by
  dsimp only [leftCards, segLeft, FiniteDeck.leftPositions]
  have hfun :
      (fun i : Fin 50 => (Equiv.refl (Fin 99)) (leftPosition i)) =
        (fun i : Fin 50 => (Fin.castLE hm5099) i) := by
    funext i
    dsimp only [leftPosition]
    simp [Fin.castLE]
  rw [hfun]

-- Reordering the segregated start within the piles keeps it in the segregated
-- membership fiber: a within-pile reindexing cannot change which named cards sit
-- in the left pile, so the membership of the result is the segregated one.
theorem membership_reorderedDeck_segregated
    (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    membership (reorderedDeck (Equiv.refl (Fin 99)) pl pr) = segMembership := by
  refine Subtype.ext ?_
  dsimp only [segMembership]
  rw [membership_leftCards, reorderedDeck_leftCards, leftCards_id_eq_segLeft]

/-! **Membership-side bridges for the `rhoRoundIdeal = localLift` headline.**
  These are proved in *this* module deliberately: its import graph excludes
  `FiniteDeck.WithinPileOrbit` (the `fiberMap`/`fiberOrbit` machinery), and that
  absence is what keeps the `Membership` proof-field from triggering a `whnf`
  heartbeat blowup.  They only touch the `.1`/`Finset` field of the
  `Membership` subtype (`dsimp`/`Subtype.ext`/`congrArg Subtype.val`), never the
  `.2` cardinality proof, so they elaborate cheaply. -/

/-- The `.1` field of the segregated membership is the segregated left set. -/
theorem segMembership_one_eq_segLeft : segMembership.1 = segLeft := by
  dsimp only [segMembership]

/-- A deck's membership is the segregated membership iff its left-card set is
  the segregated left set. The equivalence is carried at the `.1` field only, so
  it is the light membership-side bridge the `rhoRoundIdeal = localLift` headline
  needs (used by `roundImage_iff_segMembership`). -/
theorem membership_iff_leftCards (d : Deck) :
    membership d = segMembership ↔ leftCards d = segLeft := by
  constructor
  · intro hm
    have hv : (membership d).1 = segMembership.1 := congrArg Subtype.val hm
    simpa only [membership_leftCards, segMembership_one_eq_segLeft] using hv
  · intro hlc
    apply Subtype.ext
    simpa only [membership_leftCards, segMembership_one_eq_segLeft] using hlc
