module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderA3UniformPushforward
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderA3ExchangePushforward

open BernoulliLaplace
open BernoulliLaplaceGeneral
open CommanderMembershipExchange
open CommanderMembershipKernels
open CommanderPermutation
open CommanderPhysicalExchange
open FiniteKernel
open Finset

/-! A3 part (i), the concrete 99-card exchange's membership point mass. -/

/-- **Exchange membership point mass (A3 part (i) normalization, concrete).**
    `rawExchangeMembership d` is *definitionally* the pushforward of the uniform `(L, R)`
    choice law `GSR.uniformDist exchangeChoice` by the post-exchange membership map (its own
    def, `CommanderPhysicalExchange.lean:670`).  So the general `uniformPushforward_pointMass`
    (the 53rd-session A3 normalization) applies directly — no `.map`-on-`Dist` construction,
    no `Finsupp.mapDomain` bookkeeping.  The exchange puts mass `(1 / #exchangeChoice)` at
    `m` for each `(L, R)` choice whose post-exchange membership is `m`:
    `Dist.mass (rawExchangeMembership d) m
       = (1 / #exchangeChoice) * #{j : exchangeChoice | newMembership d j.1.1
         (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2) = m}`.
    Since `#exchangeChoice = transitionDenominator 99 50 25` (`exchangeChoice_card_eq_transitionDenominator`),
    this is the raw-exchange mass at `m` in the Bernoulli--Laplace transition normalization —
    the concrete instance of the part-(i) inner-sum's point-mass term. -/
theorem rawExchangeMembership_pointMass (d : Deck) (m : Membership) :
    Dist.mass (rawExchangeMembership d) m =
      (Fintype.card exchangeChoice : Rat)⁻¹ *
        (#{j ∈ (Finset.univ : Finset exchangeChoice) |
           newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2) = m} : Rat) := by
  classical
  dsimp [rawExchangeMembership]
  apply uniformPushforward_pointMass (fun c : exchangeChoice =>
    newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)) m

/- **Exchange-choice / flat-product bijection (A3 part (i) inner-sum bridge).**
    The 99-card exchange choice space `exchangeChoice` (a `Prod` of the two 25-subset
    subtypes `{L // L ∈ leftChoices}` × `{R // R ∈ rightChoices}`) is in bijection with the
    flat product of the two 25-subset families, targeted at the *direct-and* subtype
    `{p : Finset (Fin 50) × Finset (Fin 49) // p.1 ∈ leftChoices ∧ p.2 ∈ rightChoices}`.

    The target is the direct-and (not `leftChoices ×ˢ rightChoices`): *building* the
    `×ˢ`-membership term `Finset.mem_product.mpr` recurses on the large `powersetCard`
    product, but the direct-and reuses the original subtype proofs and elaborates cleanly.
    Reading the image's value projection (`.1.1`, `.1.2`) also does not recurse.  This is
    the bridge that transports the post-exchange membership count predicate from the
    choice space to the flat `(L, R)` product, for the part-(i) inner-sum assembly. -/
def exchangeChoice_equiv_lr :
    exchangeChoice ≃ {p : Finset (Fin 50) × Finset (Fin 49) //
                      p.1 ∈ leftChoices ∧ p.2 ∈ rightChoices} := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro j
    exact ⟨⟨j.1.1, j.2.1⟩, ⟨j.1.2, j.2.2⟩⟩
  · intro p
    exact ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
  · intro j
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext; rfl
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · rfl

end CommanderA3ExchangePushforward
end Shufflemath
