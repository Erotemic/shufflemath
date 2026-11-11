module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberMembership
public import Shufflemath.FiberDisintegration
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderMembershipKernels

/-!
# Concrete membership and perfect-local kernels (F2)

Makes the three-level refinement of `PhysicalExchangeReduction` concrete
for the 99-card deck:

* `Membership` — the exact 50-card left-pile membership (the set of card
  identities in the 50 left positions);
* `membership : Deck -> Membership` — reads that membership;
* `localLift : FiniteKernel Membership Deck` — the *perfect local* kernel:
  uniform orderings of the given membership only (the F1a `decksWithLeft`
  fiber, card `50! * 49!`);
* `membershipLift : FiniteKernel CommanderState Membership` — uniform among
  the memberships carrying a given marked count (the F1b
  `fiberMembershipSets` fiber).

`localLift` preserves pile membership, and
`membershipLift.comp localLift` is exactly the macro fiber law
`FiberDisintegration.fiberLaw project project_surjective` — the two-layer
lift of `commanderFiberLift` through the membership layer.
-/

open BernoulliLaplace
open CommanderPermutation
open Finset

/-!
## The membership type

The membership of a deck is its exact left-pile *content*, independent of
order: the 50 card identities currently in the left positions. A physical
perfect-local shuffle never changes it, which is the invariant the
`localLift` kernel models.
-/

/-- The exact left-pile membership: a 50-element set of card identities. -/
abbrev Membership := {S : Finset (Fin 99) // S.card = 50}

/-- The 50-card subsets of the 99 identities form a finite type: the set
  `{S | S.card = 50}` is a subset of the univ of the finite type of all
  99-card-subsets, so it is finite. -/
noncomputable instance : Fintype Membership := by
  classical
  let s : Set (Finset (Fin 99)) := {S | S.card = 50}
  have hs : s.Finite := Set.Finite.subset Set.finite_univ (fun _ _ => Set.mem_univ _)
  exact Set.Finite.fintype hs

/-- A 50-element `Finset (Fin 99)` — the shape of a possible left pile.
  Phrased as a class so that the `Nonempty` instance below can be resolved by
  typeclass search whenever a 50-set is in view. -/
class IsFifty (S : Finset (Fin 99)) : Prop where
  card : S.card = 50

instance (m : Membership) : IsFifty m.1 := ⟨m.2⟩

/-- Every 50-card set is the left pile of some deck (F1a), so its
  `decksWithLeft` fiber is inhabited. As a resolvable instance this lets the
  `localLift` pushforward unfold cleanly in downstream proofs. -/
noncomputable instance (S : Finset (Fin 99)) [h : IsFifty S] :
    Nonempty (decksWithLeft S) := by
  classical
  have hpos : 0 < Fintype.card (decksWithLeft S) := by
    rw [decksWithLeft_card S h.card]
    exact Nat.mul_pos (Nat.factorial_pos 50) (Nat.factorial_pos 49)
  by_contra hne
  have hzero : Fintype.card (decksWithLeft S) = 0 := by
    letI : IsEmpty (decksWithLeft S) := IsEmpty.mk (fun x => hne (Nonempty.intro x))
    exact Fintype.card_eq_zero
  linarith

/-- Read the left-pile membership of a deck. -/
def membership (d : Deck) : Membership :=
  ⟨leftCards d, leftCards_card d⟩

/-- The membership map is surjective: for every 50-card left-pile set there
  is a deck realizing it. The witness comes from the `Nonempty` instance for
  `decksWithLeft` (50-card sets), and the equality is a `Subtype.ext` on the
  left-card set — no permutation is enumerated. -/
theorem membership_surjective : Function.Surjective membership := by
  intro m
  obtain ⟨d⟩ : Nonempty (decksWithLeft m.1) := inferInstance
  refine ⟨d.val, ?_⟩
  apply Subtype.ext
  exact d.property

/-- The marked-card count carried by a membership: its intersection with
  the originally-left identities. -/
def membershipCount (m : Membership) : Nat := (m.1 ∩ leftOrigSet).card

/-- The first component of the membership read from a deck is its left
  card set. -/
theorem membership_leftCards (d : Deck) : (membership d).1 = leftCards d := by
  unfold membership
  rfl

/-- The marked count of a deck's membership agrees with the commander
  projection of the deck. -/
theorem membershipCount_of_deck (d : Deck) :
    membershipCount (membership d) = commanderLeftCount (project d) := by
  unfold membershipCount membership commanderLeftCount
  rw [← leftOriginalCount_eq_leftCardsInter d, (project_count d).symm]

/-- The commander fiber of a macrostate `x` is exactly the set of decks
  whose membership carries `commanderLeftCount x` marked cards. -/
theorem membershipFiber_iff (d : Deck) (x : CommanderState) :
    project d = x ↔ membershipCount (membership d) = commanderLeftCount x := by
  have hL : membershipCount (membership d) = leftOriginalCount d := by
    unfold membershipCount membership
    exact (leftOriginalCount_eq_leftCardsInter d).symm
  constructor
  · intro h
    rw [hL]
    exact (project_eq_iff_leftOriginalCount d x).mp h
  · intro h
    rw [hL] at h
    exact (project_eq_iff_leftOriginalCount d x).mpr h

/-!
## The perfect-local kernel

A *perfect local* shuffle randomizes only the order of the cards, inside
the piles they already occupy: it never moves a card from one pile to the
other. `localLift` is that operation as a kernel from memberships to
full decks: given the exact left-pile content `m`, resample uniformly
among all decks whose left pile is `m.1`. F1a supplies the fiber count
(`decksWithLeft_card = 50! * 49!`), so the resampling law is exact.

The law `localLift.comp (deterministic membership) = identity` says that
resampling inside a membership and then re-reading the membership is the
identity — the precise statement that pile membership is preserved.
-/ 

/-- The perfect-local kernel: uniform among all decks whose left pile is
  exactly the given membership's 50-card set (the F1a fiber, card
  `50! * 49!`). -/
noncomputable def localLift : FiniteKernel Membership Deck := by
  classical
  exact FiberDisintegration.fiberLaw membership membership_surjective

/-- A perfect-local resample preserves pile membership: applying
  `localLift` and then re-reading `membership` is the identity kernel. -/
theorem localLift_preserves_membership :
    FiniteKernel.comp localLift (FiniteKernel.deterministic membership) =
      FiniteKernel.identity := by
  -- localLift is the generic fiberLaw for the membership observation, so the
  -- preservation law is exactly the generic recovery theorem.
  dsimp only [localLift]
  exact FiberDisintegration.fiberLaw_recovers membership membership_surjective

/-- The pushforward-mass formula for the perfect-local kernel. This is
  exactly the generic `FiberDisintegration.fiberLaw_mass` for the `membership`
  observation: the mass at a deck `d` is the inverse of the fiber cardinality
  when `membership d = m`, and `0` otherwise. The equality predicate is the
  `Membership` (sub-type) equality — *not* the expanded `leftCards d = m.1`
  Finset equality — which keeps the proof out of the `Equiv.Perm`
  normalisation wall. -/
@[simp]
theorem localLift_mass (m : Membership) (d : Deck) :
    Dist.mass (localLift m) d =
      (if membership d = m then
         ((FiberDisintegration.fiberSet membership m).card : Rat)⁻¹ else 0) := by
  dsimp only [localLift]
  exact FiberDisintegration.fiberLaw_mass membership membership_surjective m d

/-!
## The marked-count fiber of the membership type

`MembershipFiber k` is the sub-type of memberships carrying exactly `k`
marked cards. Its `Fintype` instance is the standard set-based one (a
`MembershipFiber k = {m // membershipCount m = k}` is definitionally the
up-cast of the set `{m | membershipCount m = k}`), whose `Fintype.card` is
the F1b count of `fiberMembershipSets k` (itself `choose 50 k * choose 49
(50 - k)`), via the bijection that a membership is its 50-card set.

No custom `Fintype` instance is declared here: a second, hand-written
instance for the same (definitionally equal) type would produce two distinct
`Fintype.card` terms that do not definitionally unify, breaking the
`Fintype.card_ofFinset` bridge used in the macro-kernel normalisation proof.
Keeping the single set-based instance makes that bridge direct.
-/

/-- The memberships carrying exactly `k` marked cards. -/
abbrev MembershipFiber (k : Nat) := {m : Membership // membershipCount m = k}

/-- A membership's marked count is `k` iff its 50-card set lies in the
  F1b `fiberMembershipSets` fiber. -/
theorem membershipCount_iff_fiberMembershipSets (m : Membership) (k : Nat) :
    membershipCount m = k ↔ m.1 ∈ fiberMembershipSets k := by
  simp only [membershipCount, fiberMembershipSets, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.subset_univ]
  constructor
  · intro h
    exact And.intro (by simpa using m.2) h
  · intro h
    exact h.2

/-- The membership fiber over a marked count `k` is in bijection with the
  F1b `fiberMembershipSets k` finset: a membership is exactly its 50-card
  set, so `Fintype.card (MembershipFiber k) = (fiberMembershipSets k).card`,
  which by F1b is `choose 50 k * choose 49 (50 - k)`. -/
theorem MembershipFiber_card (k : Nat) :
    Fintype.card (MembershipFiber k) = (fiberMembershipSets k).card := by
  classical
  have hcard1 : Fintype.card (MembershipFiber k) =
      Fintype.card {S : Finset (Fin 99) // S ∈ fiberMembershipSets k} := by
    apply Fintype.card_congr
    classical
    refine ⟨fun m => ?_, fun S => ?_, ?_, ?_⟩
    · -- toFun : MembershipFiber k → {S // S ∈ fiberMembershipSets k}
      exact ⟨m.1, by
        simp only [fiberMembershipSets, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, m.1.2⟩
        · exact m.property
      ⟩
    · -- invFun : {S // S ∈ fiberMembershipSets k} → MembershipFiber k
      have hmem : S.val ∈ powersetCard 50 (univ : Finset (Fin 99)) ∧
          (S.val ∩ leftOrigSet).card = k := by
        have hprop := S.property
        simp only [fiberMembershipSets, Finset.mem_filter] at hprop
        exact hprop
      have hcard50 : S.val.card = 50 := by
        have h1 : S.val ∈ powersetCard 50 (univ : Finset (Fin 99)) := hmem.1
        simp only [Finset.mem_powersetCard, Finset.subset_univ] at h1
        exact h1.2
      exact ⟨⟨S.val, hcard50⟩, by
        simp only [membershipCount]
        exact hmem.2⟩
    · -- left_inv
      intro m
      apply Subtype.ext
      rfl
    · -- right_inv
      intro S
      apply Subtype.ext
      rfl
  have hcard2 : Fintype.card {S : Finset (Fin 99) // S ∈ fiberMembershipSets k} =
      (fiberMembershipSets k).card := by
    classical
    exact Fintype.card_ofFinset (fiberMembershipSets k) (fun _ => Iff.rfl)
  calc
    Fintype.card (MembershipFiber k) =
      Fintype.card {S : Finset (Fin 99) // S ∈ fiberMembershipSets k} := hcard1
    _ = (fiberMembershipSets k).card := hcard2

/-!
## The macro-to-membership lift and the two-layer fiber law

`membershipLift` is the commander-side half of the F2 disintegration:
from a macrostate `x` it resamples uniformly among the memberships that
carry `commanderLeftCount x` marked cards. Composed with the perfect
local `localLift`, it is exactly the macro fiber law of `project` —
the two-layer lift of `commanderFiberLift` through the membership layer.

The weight is written with the F1b *Finset* count
`(fiberMembershipSets k).card = choose 50 k * choose 49 (50 - k)` rather
than a `Fintype.card` of the membership sub-fintype, so the
normalisation is a pure finite-cardinality computation.
-/

/-- The macro-to-membership lift: uniform among the memberships carrying
  `commanderLeftCount x` marked cards (the F1b fiber, with count
  `choose 50 k * choose 49 (50 - k)`). -/
/- The F1b fiber count `choose 50 k * choose 49 (50 - k)`, written as a
  standalone `def` so the normalisation proof below can reference the
  concrete `Nat` product without whnf-expanding the `fiberMembershipSets`
  finset definition (whose `univ : Finset (Fin 99)` base carries a
  `Fintype` instance that cycles under aggressive whnf). -/
def membershipFiberCount (k : Nat) : Nat :=
  Nat.choose 50 k * Nat.choose 49 (50 - k)

/-- The standalone count agrees with the F1b finset count. -/
theorem membershipFiberCount_eq_fiberMembershipSets (k : Nat) :
    membershipFiberCount k = (fiberMembershipSets k).card :=
  (fiberMembershipSets_card k).symm

/-- The macro-to-membership lift: from a macrostate `x` it resamples
  uniformly among the memberships whose marked count equals
  `commanderLeftCount x`, and assigns zero mass to the rest. This is the
  commander-side half of the F2 disintegration; composing it with the
  perfect-local `localLift` recovers the full `project`-fiber uniform
  resampling. The normalisation (sum-to-one) proof reduces the weighted
  sum to the F1b fiber count times its reciprocal. -/
noncomputable def membershipLift : FiniteKernel CommanderState Membership :=
  fun x => Dist.ofFun
    (fun m => if membershipCount m = commanderLeftCount x
        then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat)
        else 0)
    (fun m => by split_ifs <;> positivity)
    (by
      let k := commanderLeftCount x
      have hsum1 : (∑ m : Membership, if membershipCount m = k
          then 1 / (↑(membershipFiberCount k) : Rat) else 0) =
          ((membershipFiberCount k) : Rat) *
            (1 / (↑(membershipFiberCount k) : Rat)) := by
        calc
          (∑ m : Membership, if membershipCount m = k
              then 1 / (↑(membershipFiberCount k) : Rat) else 0) =
            (∑ m ∈ (Finset.univ : Finset Membership),
              if membershipCount m = k
              then 1 / (↑(membershipFiberCount k) : Rat) else 0) := by
            rfl
          _ = ((Finset.univ.filter (fun m => membershipCount m = k)).card : Rat) *
              (1 / (↑(membershipFiberCount k) : Rat)) := by
            rw [FiberDisintegration.sum_if_constant
                (Finset.univ : Finset Membership) (fun m => membershipCount m = k)
                (1 / (↑(membershipFiberCount k) : Rat))]
          _ = ((membershipFiberCount k) : Rat) *
              (1 / (↑(membershipFiberCount k) : Rat)) := by
            -- The univ-filter count is the Fintype card of the membership
            -- sub-fintype (F2c-i), which is the F1b finset card, which is
            -- the standalone choose product by F1b.
            have hfin : (Finset.univ.filter (fun m => membershipCount m = k)).card =
                Fintype.card (MembershipFiber k) := by
              exact (@Fintype.card_ofFinset Membership (fun m => membershipCount m = k)
                  (Finset.univ.filter (fun m => membershipCount m = k))
                  (fun m => by
                    simp [Finset.mem_filter, Finset.mem_univ]
                    exact Iff.rfl)).symm
            have hcard : (Finset.univ.filter (fun m => membershipCount m = k)).card =
                membershipFiberCount k := by
              calc
                (Finset.univ.filter (fun m => membershipCount m = k)).card =
                    Fintype.card (MembershipFiber k) := hfin
                _ = (fiberMembershipSets k).card := MembershipFiber_card k
                _ = membershipFiberCount k :=
                    (membershipFiberCount_eq_fiberMembershipSets k).symm
            rw [hcard]
      rw [hsum1]
      have hpos : 0 < membershipFiberCount k := by
        unfold membershipFiberCount
        have hk1 : 1 ≤ k := by
          change 1 ≤ x.val + 1
          omega
        have hk2 : k ≤ 50 := by
          change (x.val + 1) ≤ 50
          omega
        exact Nat.mul_pos (Nat.choose_pos hk2) (Nat.choose_pos (by omega))
      have hnonzero : (↑(membershipFiberCount k) : Rat) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hpos
      field_simp [hnonzero])

/-- The mass of `apply μ K` at `b` is the two-level weighted sum over the
  intermediate states: the standard pushforward formula. -/
theorem apply_mass_eq_sum
    {α β : Type*} [Fintype α] [DecidableEq α]
    (μ : Dist α) (K : FiniteKernel α β) (b : β) :
    Dist.mass (FiniteKernel.apply μ K) b =
      (∑ a : α, Dist.mass μ a * Dist.mass (K a) b) := by
  unfold Dist.mass FiniteKernel.apply
  simp only [Dist.join_sConvexComb, Convexity.StdSimplex.map,
      Convexity.StdSimplex.weights_sConvexComb, Finsupp.sum_apply,
      Finsupp.smul_apply]
  -- ((μ.weights).mapDomain K).sum (fun L r => r • (L.weights b)) =
  --   (μ.weights).sum (fun a r => r • (K a).weights b)
  have hFubini : ((μ.weights).mapDomain K).sum
      (fun (L : Dist β) (r : Rat) => r • (L.weights b)) =
      (μ.weights).sum (fun a (r : Rat) => r • ((K a).weights b)) := by
    classical
    exact Finsupp.sum_mapDomain_index
      (fun _ => by simp)
      (fun _ _ _ => by ring)
  rw [hFubini]
  simpa using (μ.weights).sum_fintype
    (fun a (r : Rat) => r • ((K a).weights b))
    (fun _ => by simp)

/-!
## The two-layer fiber law

`membershipLift.comp localLift` resamples a macrostate's fiber in two
stages: first a membership (uniform among those with the macrostate's marked
count), then a deck ordering (uniform within that membership). This section
proves that equals the direct `FiberDisintegration.fiberLaw project`.

The first steps are structural: the `project` fiber over `x` is exactly the
(disjoint) union, over the memberships carrying `commanderLeftCount x`, of
the membership fibers.
-/ 

/-- The memberships carrying a given marked count `k`, as a finset. -/
noncomputable def memCountFiber (k : Nat) : Finset Membership :=
  (Finset.univ : Finset Membership).filter (fun m => membershipCount m = k)

/-- The `project` fiber over a macrostate `x` is the disjoint union, over
  the memberships carrying `commanderLeftCount x` marked cards, of the
  membership fibers. -/
theorem fiberSet_project_decomp (x : CommanderState) :
    FiberDisintegration.fiberSet project x =
      (memCountFiber (commanderLeftCount x)).biUnion
        (fun m => FiberDisintegration.fiberSet membership m) := by
  classical
  ext d
  simp only [FiberDisintegration.fiberSet, memCountFiber, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, and_true]
  -- project d = x ↔ ∃ m, membershipCount m = commanderLeftCount x ∧ membership d = m
  constructor
  · intro h
    refine ⟨membership d, ?_, rfl⟩
    exact (membershipFiber_iff d x).mp h
  · rintro ⟨m, hmcount, hmem⟩
    have hcnt : membershipCount (membership d) = commanderLeftCount x := by
      rw [hmem]
      exact hmcount
    exact (membershipFiber_iff d x).mpr hcnt

/-- Distinct memberships have disjoint deck fibers: a deck has a unique
  left-pile membership. -/
theorem membershipFiber_disjoint (m m' : Membership) (h : m ≠ m') :
    Disjoint (FiberDisintegration.fiberSet membership m)
      (FiberDisintegration.fiberSet membership m') := by
  classical
  by_contra hND
  rw [Finset.not_disjoint_iff] at hND
  rcases hND with ⟨d, hd1, hd2⟩
  simp only [FiberDisintegration.fiberSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hd1 hd2
  -- hd1 : membership d = m, hd2 : membership d = m'
  exact h (hd1.symm.trans hd2)

end CommanderMembershipKernels
end Shufflemath
end
