module

-- WIP (51st session) — the A3 part-(i) inner-sum:
--   rawExchange_membershipCount_mass
--   total mass of the post-exchange membership law into the c-fiber = the BL
--   transition probability from the source count to c.
--
-- PROVEN inputs already in the library (CommanderMembershipExchange / A3Kernel):
--   * membershipCount_newMembership :
--       membershipCount (newMembership d L hL R hR) = (newLeftCards d L R ∩ leftOrigSet).card
--   * newLeftOriginalCount_eq (CommanderPhysicalExchange) :
--       (newLeftCards d L R ∩ leftOrigSet).card = (leftOriginalCount d - markedInLeft d L) + markedInRight d R
--   * newLeftCount_eq_transitionNumerator (CommanderA3Kernel) :
--       #{(L,R) : (leftOriginalCount d - markedInLeft d L) + markedInRight d R = c}
--         = transitionNumerator 99 50 25 (leftOriginalCount d) c
--       (on the choice space leftChoices ×ˢ rightChoices == exchangeChoice)
--   * exchangeChoice_card_eq_transitionDenominator (CommanderMembershipExchange) :
--       #exchangeChoice = transitionDenominator 99 50 25
--
-- REMAINING (Finsupp/measure bookkeeping) — the 4 sorrys below. The cleanest
-- route AVOIDS the .map-on-Dist instance wrinkle by computing the fiber-sum as a
-- Finset.sum over exchangeChoice directly:
--   (i)  mass ((uniformDist exchangeChoice).map memF) m
--          = Finset.sum {ch // memF ch = m} (fun ch => 1 / #exchangeChoice)      [pushforward sum]
--        use the CommanderLocalGSR.lean:205 pattern:
--          simp only [Convexity.StdSimplex.map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
--   (ii) sum over the c-fiber of m = sum over the preimage {ch : membershipCount (memF ch) = c}
--        (double-sum-over-fibers = sum-over-preimage; Finset.sum_bifurcate / sum_sigma)
--   (iii) # {ch : membershipCount (memF ch) = c} = # {ch : (newLeftCards ... ∩ leftOrigSet).card = c}
--        [membershipCount_newMembership]
--   (iv) that = transitionNumerator 99 50 25 (leftOriginalCount d) c
--        [newLeftOriginalCount_eq + newLeftCount_eq_transitionNumerator; the choice
--         space leftChoices ×ˢ rightChoices is extensionally exchangeChoice]
--   (v)  normalize # by exchangeChoice_card_eq_transitionDenominator.
--
-- 51st-session finding (de-risks step (i)): `rawExchangeMembership d` is
-- `(GSR.uniformDist exchangeChoice).map (fun c => newMembership …)`, and `StdSimplex.map`
-- is NOT a plain `Finsupp.map` — it carries the simplex constraints (total mass 1,
-- nonnegativity). `dsimp [Dist.mass, Convexity.StdSimplex.map]` + `rw [Finsupp.mapDomain]`
-- does NOT reduce the pushforward mass cleanly (leaves a `Finset` in a `ℚ`-typed hole:
-- "has type Finset exchangeChoice but is expected to have ℚ"). Step (i) must either go
-- through the `StdSimplex.weights` Finsupp explicitly, or (cleaner) compute the fiber-sum
-- as a `Finset.sum` over `exchangeChoice` FROM SCRATCH (not via `rawExchangeMembership`'s
-- `.map`):  Σ_{ch in univ} (1/#) * [membershipCount (memF ch) = c]  —  i.e. skip the
-- membership-level pushforward entirely and count the (L,R) preimage directly.

public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderA3Kernel
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open BernoulliLaplaceGeneral
open CommanderMembershipExchange
open CommanderMembershipKernels
open CommanderPermutation
open CommanderPhysicalExchange
open CommanderA3Kernel
open Finset
open Fin

-- choice -> membership (exactly rawExchangeMembership's .map argument)
def memF (d : Deck) (ch : exchangeChoice) : Membership :=
  newMembership d ch.1.1 (leftCard25 ch.1.2) ch.2.1 (rightCard25 ch.2.2)

def cntF (d : Deck) (ch : exchangeChoice) : Nat := membershipCount (memF d ch)

theorem rawExchange_membershipCount_mass (d : Deck) (c : Nat) :
    (Finset.univ : Finset Membership).filter (fun m => membershipCount m = c)
      |>.sum (fun m => Dist.mass (rawExchangeMembership d) m)
      = (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat) /
        (transitionDenominator 99 50 25 : Rat) := by
  -- (i) pushforward mass at m: the (L,R)-fiber sum
  -- (ii) fiber-sum -> preimage-sum  [SOMETHING HERE]
  -- (iii) + (iv) the preimage count = transitionNumerator  [see header]
  -- (v) normalize
  sorry

end Shufflemath
