module

public import Shufflemath.GSRSegHeadline
public import Shufflemath.GSRSegMembership
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open scoped Nat
open CommanderMembershipKernels

variable (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))

/-- The forward left-card fact (wall-free, all in the `FiniteDeck` frame):
  `embed_m` (hence `roundEmbedMap`) relabels within the piles, so the set of
  cards in the left 50 positions is unchanged = the segregated left set.
  Uses the frame bridge + `FiniteDeck.embed_m_imageLeft` — never the
  `(fiberOrbit_equiv …).val` deck, so no WHNF/recursion blowup. -/
theorem leftCards_embed_eq_segLeft :
    CommanderPermutation.leftCards (FiniteDeck.embed_m 99 50 hm5099 pl pr) = segLeft := by
  rw [← finiteDeck_leftCards_99_50_eq_commander, FiniteDeck.leftCards]
  dsimp only [segLeft]
  exact FiniteDeck.embed_m_imageLeft 99 50 hm5099 pl pr

/-- Forward membership: any `roundEmbedMap` image sits in the segregated-membership
  fiber. Wall-free: the linchpin + `membership_iff_leftCards`. -/
theorem membership_embed_eq_segMembership :
    membership (roundEmbedMap 99 50 hm5099 (pl, pr)) = segMembership := by
  rw [membership_iff_leftCards, roundEmbedMap, leftCards_embed_eq_segLeft]
