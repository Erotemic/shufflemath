import Shufflemath.PhysicalRefinement

namespace Shufflemath
namespace PhysicalExchangeReduction

/-!
# Three-level physical exchange refinement

There are three distinct state spaces in a physically shuffled deck:

* `α`: the number of marked cards currently in the left working pile;
* `γ`: the *set of named cards* in the left pile (pile membership);
* `β`: the ordered full deck, including order within each pile.

A physical perfect-local shuffle *preserves* the pile-membership state.
Consequently it cannot be modeled by immediately resampling uniformly over
an entire `α`-fiber: that would also randomize membership, an operation a
local shuffle does not perform.

Instead, we separate `macroLift : α → Dist γ` (uniform membership given
count) from `localLift : γ → Dist β` (uniform orders within fixed piles).
A physical exchange followed by `membership ; localLift` then intertwines
with the macro kernel if the raw exchange maps macro-fiber-uniform input
to the correct *membership* law. This is the precise remaining physical
exchange-counting obligation.
-/

variable {α γ β : Type*}

/-- A true local-perfect reshuffle: read exact membership and resample
only microscopic states in that membership fiber. The application-specific
proof that `localLift` is supported on the correct membership fiber is
separate from the kernel-composition identity. -/
noncomputable def localReset (membership : β → γ) (localLift : FiniteKernel γ β) :
    FiniteKernel β β :=
  FiniteKernel.comp (FiniteKernel.deterministic membership) localLift

/-- A local-resampling kernel really preserves exact pile membership
when its conditional law is supported on that membership fiber. This
hypothesis is separate from the macro exchange distribution. -/
theorem localReset_preserves_membership
    (membership : β → γ) (localLift : FiniteKernel γ β)
    (hlocal : FiniteKernel.comp localLift
      (FiniteKernel.deterministic membership) = FiniteKernel.identity) :
    FiniteKernel.comp (localReset membership localLift)
      (FiniteKernel.deterministic membership) =
    FiniteKernel.deterministic membership := by
  unfold localReset
  calc
    FiniteKernel.comp
        (FiniteKernel.comp (FiniteKernel.deterministic membership) localLift)
        (FiniteKernel.deterministic membership) =
      FiniteKernel.comp (FiniteKernel.deterministic membership)
        (FiniteKernel.comp localLift
          (FiniteKernel.deterministic membership)) :=
            FiniteKernel.comp_assoc _ _ _
    _ = FiniteKernel.comp (FiniteKernel.deterministic membership)
          FiniteKernel.identity := by rw [hlocal]
    _ = FiniteKernel.deterministic membership :=
          FiniteKernel.comp_id_right _

/-- Exchange physical positions, then perfectly randomize the order of
each pile without altering its post-exchange membership. -/
noncomputable def exchangeThenLocalReset (membership : β → γ)
    (localLift : FiniteKernel γ β) (exchange : FiniteKernel β β) :
    FiniteKernel β β :=
  FiniteKernel.comp exchange (localReset membership localLift)

/-- One projected-exchange identity at the *membership* level suffices
for full-deck intertwining after actual perfect-local resampling.

Note that `hMembershipExchange` concerns the entire membership law, not
merely the number of marked cards. Merely checking the macro count after
an exchange is insufficient to prove that orders become uniform. -/
theorem intertwining_of_membership_exchange
    (macroLift : FiniteKernel α γ) (localLift : FiniteKernel γ β)
    (membership : β → γ) (exchange : FiniteKernel β β)
    (macroK : FiniteKernel α α)
    (hMembershipExchange :
      FiniteKernel.comp
        (FiniteKernel.comp (FiniteKernel.comp macroLift localLift) exchange)
        (FiniteKernel.deterministic membership) =
      FiniteKernel.comp macroK macroLift) :
    FiniteKernel.comp (FiniteKernel.comp macroLift localLift)
      (exchangeThenLocalReset membership localLift exchange) =
    FiniteKernel.comp macroK (FiniteKernel.comp macroLift localLift) := by
  unfold exchangeThenLocalReset localReset
  calc
    FiniteKernel.comp (FiniteKernel.comp macroLift localLift)
        (FiniteKernel.comp exchange
          (FiniteKernel.comp (FiniteKernel.deterministic membership) localLift)) =
      FiniteKernel.comp
        (FiniteKernel.comp
          (FiniteKernel.comp
            (FiniteKernel.comp macroLift localLift) exchange)
            (FiniteKernel.deterministic membership)) localLift := by
              simp only [← FiniteKernel.comp_assoc]
    _ = FiniteKernel.comp (FiniteKernel.comp macroK macroLift) localLift := by
          rw [hMembershipExchange]
    _ = FiniteKernel.comp macroK (FiniteKernel.comp macroLift localLift) :=
          FiniteKernel.comp_assoc _ _ _

/-- Total variation after any number of ideal physical exchanges is
exactly the macrostate TV, *once* the real membership-exchange law and
the recoverability of the two-layer lift are proved. The theorem does
not equate the physical kernel pointwise to a resampling oracle. -/
theorem run_tv_eq_macro_of_membership_exchange
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (macroLift : FiniteKernel α γ) (localLift : FiniteKernel γ β)
    (membership : β → γ) (exchange : FiniteKernel β β)
    (macroK : FiniteKernel α α) (project : β → α)
    (hrecover : FiniteKernel.comp (FiniteKernel.comp macroLift localLift)
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (hMembershipExchange :
      FiniteKernel.comp
        (FiniteKernel.comp (FiniteKernel.comp macroLift localLift) exchange)
        (FiniteKernel.deterministic membership) =
      FiniteKernel.comp macroK macroLift)
    (start stationary : Dist α) (n : Nat) :
    Dist.tv
      (FiniteKernel.run (exchangeThenLocalReset membership localLift exchange) n
        (FiniteKernel.apply start (FiniteKernel.comp macroLift localLift)))
      (FiniteKernel.apply stationary (FiniteKernel.comp macroLift localLift)) =
      Dist.tv (FiniteKernel.run macroK n start) stationary := by
  exact FiberLifting.run_tv_eq_macro (FiniteKernel.comp macroLift localLift)
    (FiniteKernel.deterministic project) macroK
    (exchangeThenLocalReset membership localLift exchange) hrecover
    (intertwining_of_membership_exchange macroLift localLift membership
      exchange macroK hMembershipExchange)
    start stationary n

end PhysicalExchangeReduction
end Shufflemath
