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

/-- Read the left-pile membership of a deck. -/
def membership (d : Deck) : Membership :=
  ⟨leftCards d, leftCards_card d⟩

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
  intro m
  letI : Nonempty (decksWithLeft m.1) := by
    have hpos : 0 < Fintype.card (decksWithLeft m.1) := by
      rw [decksWithLeft_card m.1 m.2]
      exact Nat.mul_pos (Nat.factorial_pos 50) (Nat.factorial_pos 49)
    by_contra hne
    have hzero : Fintype.card (decksWithLeft m.1) = 0 := by
      letI : IsEmpty (decksWithLeft m.1) := IsEmpty.mk (fun x => hne (Nonempty.intro x))
      exact Fintype.card_eq_zero
    linarith
  exact (GSR.uniformDist (decksWithLeft m.1)).map Subtype.val

/-- A perfect-local resample preserves pile membership: applying
  `localLift` and then re-reading `membership` is the identity kernel. -/
theorem localLift_preserves_membership :
    FiniteKernel.comp localLift (FiniteKernel.deterministic membership) =
      FiniteKernel.identity := by
  funext m
  haveI : Nonempty (decksWithLeft m.1) := by
    have hpos : 0 < Fintype.card (decksWithLeft m.1) := by
      rw [decksWithLeft_card m.1 m.2]
      exact Nat.mul_pos (Nat.factorial_pos 50) (Nat.factorial_pos 49)
    by_contra hne
    have hzero : Fintype.card (decksWithLeft m.1) = 0 := by
      letI : IsEmpty (decksWithLeft m.1) := IsEmpty.mk (fun x => hne (Nonempty.intro x))
      exact Fintype.card_eq_zero
    linarith
  change FiniteKernel.apply
      ((GSR.uniformDist (decksWithLeft m.1)).map Subtype.val)
      (FiniteKernel.deterministic membership) = Dist.pointMass m
  rw [apply_deterministic, Convexity.StdSimplex.map_map]
  have hconstant :
      (fun (d : decksWithLeft m.1) => membership (d.val)) = (fun _ => m) := by
    funext d
    apply Subtype.ext
    rw [membership_leftCards (d.val)]
    exact d.property
  change (GSR.uniformDist (decksWithLeft m.1)).map
      (fun (d : decksWithLeft m.1) => membership (d.val)) = Dist.pointMass m
  rw [hconstant]
  exact Convexity.StdSimplex.map_const (GSR.uniformDist (decksWithLeft m.1)) m

/-!
## The marked-count fiber of the membership type

`MembershipFiber k` is the sub-fintype of memberships carrying exactly `k`
marked cards. Its `Fintype.card` is the F1b count of
`fiberMembershipSets k` (itself `choose 50 k * choose 49 (50 - k)`), via
the bijection that a membership is its 50-card set.
-/ 

/-- The memberships carrying exactly `k` marked cards. -/
def MembershipFiber (k : Nat) := {m : Membership // membershipCount m = k}

/-- The marked-count fiber of the membership type is finite: it is a
  subset of the univ of the (finite) membership type. -/
noncomputable instance (k : Nat) : Fintype (MembershipFiber k) := by
  classical
  let s : Set Membership := {m | membershipCount m = k}
  have hs : s.Finite := Set.Finite.subset Set.finite_univ (fun _ _ => Set.mem_univ _)
  exact Set.Finite.fintype hs

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

end CommanderMembershipKernels
end Shufflemath
end
