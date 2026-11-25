module

public import Shufflemath.Gate6K1Bridges
public import Shufflemath.FiniteDeck.Gate6ThreeRound
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderA3ExchangeCard
public import Shufflemath.FiniteDeck.SubsetExchange

@[expose] public section

namespace Shufflemath.QwenMorningHints

/-! Uncompiled candidate. Small, generic lemmas first. No new 99-card mass
calculation is required to identify the two segregated fiber laws. -/

theorem same_fiber_law {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [Nonempty X]
    (f : X → Y) (g : X → Z) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (y : Y) (z : Z)
    (h : ∀ x, f x = y ↔ g x = z) :
    FiberDisintegration.fiberLaw f hf y = FiberDisintegration.fiberLaw g hg z := by
  classical
  have hs : FiberDisintegration.fiberSet f y = FiberDisintegration.fiberSet g z := by
    ext x
    simpa only [FiberDisintegration.fiberSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using h x
  ext x
  change Dist.mass (FiberDisintegration.fiberLaw f hf y) x =
    Dist.mass (FiberDisintegration.fiberLaw g hg z) x
  rw [FiberDisintegration.fiberLaw_mass, FiberDisintegration.fiberLaw_mass, hs]
  by_cases hx : f x = y
  · rw [if_pos hx, if_pos ((h x).mp hx)]
  · rw [if_neg hx, if_neg (fun hx' => hx ((h x).mpr hx'))]

/-- If a row E depends only on an observation f, no probability computation is
needed to construct its factorization through f. -/
noncomputable def rowFactor {X Y Z : Type*} (f : X → Y)
    (hf : Function.Surjective f) (E : FiniteKernel X Z) : FiniteKernel Y Z :=
  fun y => E (Classical.choose (hf y))

theorem rowFactor_at {X Y Z : Type*} (f : X → Y)
    (hf : Function.Surjective f) (E : FiniteKernel X Z)
    (h : ∀ x x', f x = f x' → E x = E x') (x : X) :
    E x = rowFactor f hf E (f x) := by
  change E x = E (Classical.choose (hf (f x)))
  exact h _ _ (Classical.choose_spec (hf (f x))).symm

theorem rowFactor_comp {X Y Z : Type*} (f : X → Y)
    (hf : Function.Surjective f) (E : FiniteKernel X Z)
    (h : ∀ x x', f x = f x' → E x = E x') :
    E = FiniteKernel.comp (FiniteKernel.deterministic f) (rowFactor f hf E) := by
  rw [GSR.comp_deterministic_left]
  exact funext (rowFactor_at f hf E h)

/-- Erasing the initial ordering gives identical runs after at least one ideal
round. Use this with the compiled reset_absorption and K1 factorization. -/
theorem run_from_reset_eq_point {X : Type*} (H L : FiniteKernel X X)
    (hHL : FiniteKernel.comp H L = L) (x : X) (t : Nat) :
    FiniteKernel.run L (t+1) (H x) =
      FiniteKernel.run L (t+1) (Dist.pointMass x) := by
  apply equal_after_first_run
  calc
    FiniteKernel.apply (H x) L =
        FiniteKernel.apply (FiniteKernel.apply (Dist.pointMass x) H) L := by
          rw [FiniteKernel.apply_pointMass]
    _ = FiniteKernel.apply (Dist.pointMass x) (FiniteKernel.comp H L) :=
          FiniteKernel.apply_comp _ _ _
    _ = _ := by rw [hHL]

open CommanderPermutation CommanderMembershipKernels CommanderPhysicalExchange

/-- Define the exchange choice map by a name, so only this definition needs to
be unfolded when connecting it to rawExchangeMembership. -/
def exchangeChoiceImage (d : Deck) (c : exchangeChoice) : Membership :=
  newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)

theorem exchangeChoiceImage_injective (d : Deck) :
    Function.Injective (exchangeChoiceImage d) := by
  intro a b hab
  have hv : newLeftCards d a.1.1 a.2.1 = newLeftCards d b.1.1 b.2.1 :=
    congrArg Subtype.val hab
  obtain ⟨hL, hR⟩ := newLeftCards_injective d a.1.1 b.1.1 a.2.1 b.2.1 hv
  exact Prod.ext (Subtype.ext hL) (Subtype.ext hR)

-- The remaining nontrivial concrete lemma is the ReachSet containment. Use
-- newMembership_overlap_25, the two 50-card size proofs, and Finset.card_sdiff.
-- The main guide gives the exact route. Do not invent an inverse choice map.

end Shufflemath.QwenMorningHints
