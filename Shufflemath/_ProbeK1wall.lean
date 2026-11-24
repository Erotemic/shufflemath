module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.GSRDeckRound
public import Shufflemath.GSRSegHeadline
public import Shufflemath.GSRSegMembership
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath.FiberDisintegration

@[expose]
public section

namespace Shufflemath

open Finset

/-!
# The per-deck orbit-fiber uniformity (the K1 wall)

> **PROMOTED to `Shufflemath.K1Wall`** (real module; identical content, added to the
> aggregator + `dev/verify_next_phase.sh`). This probe is retained only for its
> opposite-order dependents (`_ProbeK1half`, `_ProbeGate6K1`); the canonical version
> of every theorem here now lives in `K1Wall`. The per-deck orbit-fiber uniformity
> theorem `k1wall_riffle_push_mass_factorial` is the reusable core of the Gate-6 K1
> capstone (see `docs/planning/proof-strategies/2026-12-30-k1-correct-order-crack.md`).

Pushing the within-pile *uniform* riffle law from an *arbitrary* 99-card deck
`d'` gives exactly the uniform law on `d'`'s membership fiber: the mass at a
deck `X` is `1 / (50!·49!)` when `X` carries the same 99-card membership as
`d'` and `0` otherwise.

**Representation (no recursion-limit bumps).**  The single finitary object is
the within-pile pair space `P99 = Perm (Fin 50) × Perm (Fin 49)`; the 99!
deck universe never enters any sum.  All `Finset` rewriting on the pair-space
universe happens inside the *generic* lemma `map_injective_uniform_mass`,
where the universe is an opaque type variable.  Instantiating that lemma at
the concrete `P99` is a named-theorem application (`rw` on a small statement),
which does not re-normalize the concrete `Fintype.univ`.  The result is the
per-point mass: `1 / (50!·49!)` on the membership fiber, `0` off it. -/

-- ------------------------------------------------------------------
-- The generic uniform-under-injective-map lemma was promoted to GSR.lean as
-- `GSR.map_injective_uniform_mass` (reusable; see there).  The K1 headline
-- below instantiates it at the concrete within-pile pair space.
-- ------------------------------------------------------------------

-- ------------------------------------------------------------------
-- The 99-card within-pile pair space and the riffle push
-- ------------------------------------------------------------------

abbrev P99 : Type := Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49)

/-- Pushing a within-pile permutation pair onto deck `d'`: definitionally the
    orbit action `act_d 99 50`. -/
def rifflePush (d' : Equiv.Perm (Fin 99)) (z : P99) : Equiv.Perm (Fin 99) :=
  (roundEmbedMap 99 50 hm5099 z).trans d'

/-- `rifflePush` is definitionally the committed orbit action `act_d`. -/
theorem rifflePush_eq_act_d (d' : Equiv.Perm (Fin 99)) (z : P99) :
    rifflePush d' z = FiniteDeck.act_d 99 50 hm5099 d' z.1 z.2 :=
  rfl

-- ------------------------------------------------------------------
-- Membership ↔ left-cards pointwise bridge
-- ------------------------------------------------------------------

/-- Reading the membership of a deck equals `m` iff its left-pile card set is
    `m.1`.  Both `Subtype` proof fields are the 50-card count, so subtype
    equality is the card-set equality. -/
theorem membership_iff_leftCards_gen (d' : Equiv.Perm (Fin 99))
    (m : CommanderMembershipKernels.Membership) :
    CommanderMembershipKernels.membership d' = m ↔
      CommanderPermutation.leftCards d' = m.1 := by
  constructor
  · intro h
    have hv : (CommanderMembershipKernels.membership d').1 = m.1 :=
      congrArg Subtype.val h
    simpa only [CommanderMembershipKernels.membership_leftCards] using hv
  · intro h
    apply Subtype.ext
    simpa only [CommanderMembershipKernels.membership_leftCards] using h

-- ------------------------------------------------------------------
-- Structural facts about the riffle push
-- ------------------------------------------------------------------

/-- `rho99Ideal` unfolded to the uniform law over the 50!·49! within-pile pair
    space pushed through `roundEmbedMap`, so the mass computation never touches
    the 99!-sized carrier. -/
noncomputable abbrev rho99Ideal_pairs : Dist (Equiv.Perm (Fin 99)) :=
  (distProduct (GSR.uniformDist (Equiv.Perm (Fin 50)))
               (GSR.uniformDist (Equiv.Perm (Fin 49)))).map
    (roundEmbedMap 99 50 hm5099)

/-- The 99-card within-pile pair space has `50!·49!` elements (as a `Rat`, so
    it can divide directly in the mass computation). -/
theorem pairSpaceCard_99 : (Fintype.card (P99) : Rat) =
      (Nat.factorial 50 * Nat.factorial 49 : Rat) := by
  simp only [P99, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Nat.cast_mul]

set_option linter.constructorNameAsVariable false

/-- The riffle push `rifflePush d'` is injective: two within-pile pairs
    producing the same deck are equal (the committed `act_d_injective`). -/
theorem k1wall_F_inj (d' : Equiv.Perm (Fin 99)) :
    Function.Injective (rifflePush d') := by
  classical
  intro a b h
  rw [rifflePush_eq_act_d, rifflePush_eq_act_d] at h
  apply (FiniteDeck.act_d_injective 99 50 hm5099 d')
  exact h

/-- `rifflePush d'` carries the same 99-card membership as `d'` (the generic
    `act_d_preservesMembership`, bridged through the left-cards definition). -/
theorem k1wall_F_preserves_membership (d' : Equiv.Perm (Fin 99)) (z : P99) :
    CommanderMembershipKernels.membership (rifflePush d' z) =
      CommanderMembershipKernels.membership d' := by
  have hGen := FiniteDeck.act_d_preservesMembership 99 50 hm5099 d' z.1 z.2
  apply Subtype.ext
  have hL : (CommanderMembershipKernels.membership (rifflePush d' z)).1 =
      CommanderPermutation.leftCards (rifflePush d' z) :=
    CommanderMembershipKernels.membership_leftCards _
  have hR : (CommanderMembershipKernels.membership d').1 =
      CommanderPermutation.leftCards d' := CommanderMembershipKernels.membership_leftCards _
  calc
    (CommanderMembershipKernels.membership (rifflePush d' z)).1 =
        CommanderPermutation.leftCards (rifflePush d' z) := hL
    _ = FiniteDeck.leftCards 99 50 hm5099 (rifflePush d' z) :=
        (finiteDeck_leftCards_99_50_eq_commander (rifflePush d' z)).symm
    _ = FiniteDeck.leftCards 99 50 hm5099 d' :=
        (congrArg Subtype.val hGen)
    _ = CommanderPermutation.leftCards d' :=
        finiteDeck_leftCards_99_50_eq_commander d'
    _ = (CommanderMembershipKernels.membership d').1 := hR.symm

-- ------------------------------------------------------------------
-- The K1 headline: per-deck orbit-fiber uniformity
-- ------------------------------------------------------------------

variable (d' : Equiv.Perm (Fin 99))

/-- A deck `X` has a `rifflePush d'` preimage iff it lies in the membership
    fiber of `d'`.  Forward: `rifflePush` preserves membership, so a preimage
    carries `d'`'s membership.  Backward: the F5 orbit reconstruction
    (`w_eq_embed_m`) writes any same-membership deck as `rifflePush` of a
    within-pile pair. -/
theorem k1wall_exists_iff_mem (X : Equiv.Perm (Fin 99)) :
    (∃ z : P99, rifflePush d' z = X) ↔
      CommanderMembershipKernels.membership X = CommanderMembershipKernels.membership d' := by
  constructor
  · intro ⟨z, hz⟩
    have hPres := k1wall_F_preserves_membership d' z
    simpa [hz] using hPres
  · intro hm
    -- X shares d''s left-pile card set, so the relative permutation
    -- X ∘ d'⁻¹ preserves both piles and is a within-pile pair.
    have hLc : FiniteDeck.leftCards 99 50 hm5099 X =
        FiniteDeck.leftCards 99 50 hm5099 d' := by
      have hmL : (CommanderMembershipKernels.membership X).1 =
          (CommanderMembershipKernels.membership d').1 :=
        congrArg Subtype.val hm
      simpa only [CommanderMembershipKernels.membership_leftCards,
        finiteDeck_leftCards_99_50_eq_commander] using hmL
    let w := X.trans d'.symm
    have hwL := FiniteDeck.wPreservesLeftOfFiber 99 50 hm5099 d' X hLc
    have hwR := FiniteDeck.wPreservesRightOfFiber 99 50 hm5099 d' X hLc
    let z := (FiniteDeck.plOfW_equiv 99 50 hm5099 w hwL,
        FiniteDeck.prOfW_equiv 99 50 hm5099 w hwR)
    have hdeck : FiniteDeck.act_d 99 50 hm5099 d' z.1 z.2 = X := by
      dsimp only [FiniteDeck.act_d]
      have hrec : X.trans d'.symm = FiniteDeck.embed_m 99 50 hm5099 z.1 z.2 :=
        FiniteDeck.w_eq_embed_m 99 50 hm5099 (X.trans d'.symm) hwL hwR
      rw [← hrec]
      simp only [FiniteDeck.trans_d_symm_trans_d]
    use z
    rw [rifflePush_eq_act_d]
    exact hdeck

/-- **K1 wall.**  Pushing the within-pile uniform riffle law from deck `d'`
    gives mass `1 / (50!·49!)` at exactly the decks carrying `d'`'s membership,
    and `0` elsewhere.  Proved by the generic `map_injective_uniform_mass`
    (the riffle push is injective) plus `k1wall_exists_iff_mem`; the only
    finitary object is the 50!·49! pair space, and the 99! deck universe never
    enters a sum.  No recursion-limit bump is required. -/
theorem k1wall_riffle_push_mass_factorial (X : Equiv.Perm (Fin 99)) :
    Dist.mass (rho99Ideal_pairs.map (fun p : Equiv.Perm (Fin 99) => p.trans d')) X =
      (if CommanderMembershipKernels.membership X = CommanderMembershipKernels.membership d'
       then (Nat.factorial 50 * Nat.factorial 49 : Rat)⁻¹ else 0) := by
  classical
  -- (1) the law is the uniform pair law pushed by the (injective) rifflePush
  have hU : rho99Ideal_pairs.map (fun p : Equiv.Perm (Fin 99) => p.trans d') =
      (GSR.uniformDist (P99)).map (rifflePush d') := by
    dsimp only [rho99Ideal_pairs, rifflePush, P99]
    rw [← distProduct_uniform_is_uniformProd, Convexity.StdSimplex.map_map]
    rfl
  rw [hU, GSR.map_injective_uniform_mass (rifflePush d') (k1wall_F_inj d') X]
  by_cases hm : CommanderMembershipKernels.membership X =
      CommanderMembershipKernels.membership d'
  · -- X in the fiber: a preimage exists; reduce both ites to their true
      -- branches with targeted `ite_eq_left` (never a global `simp`, which
      -- would normalize the concrete 50!·49! pair universe).
    have hEx : ∃ z : P99, rifflePush d' z = X :=
      (k1wall_exists_iff_mem d' X).mpr hm
    rw [ite_eq_left hEx, ite_eq_left hm, pairSpaceCard_99]
  · -- X off the fiber: no preimage; both ites are their false branch.
    have hNoEx : ¬∃ z : P99, rifflePush d' z = X := by
      intro ⟨z, hz⟩
      exact hm ((k1wall_exists_iff_mem d' X).mp ⟨z, hz⟩)
    rw [ite_eq_right hNoEx, ite_eq_right hm]

end Shufflemath
