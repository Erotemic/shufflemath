import Shufflemath.OracleRefinement

namespace Shufflemath
namespace PhysicalRefinement

/-!
# The correct refinement theorem for physically implemented exchange steps

The canonical project/macro/resample oracle is **not** the same pointwise
kernel as swapping selected positions followed by independent perfect
local pile shuffles. Their outputs agree after averaging over a uniform
macrostate fiber, which is a kernel *intertwining* condition.

Therefore a real finite-GSR protocol should be compared by a weighted
telescope to the physical *perfect-local* protocol, not naively to the
canonical resampling oracle row by row. The ideal physical steps only need
intertwining after a conditional lift. This module isolates the exact
abstract result so the later combinatorial exchange proof has an explicit
Lean theorem it can discharge.
-/

variable {α β : Type*}

/-- A heterogeneous sequence of microscopic kernels that intertwine with
corresponding macro kernels also intertwines after composition. Note that
this has no reversibility, homogeneity, or kernel equality hypothesis. -/
theorem schedule_intertwining
    (lift : FiniteKernel α β)
    (macroSchedule : List (FiniteKernel α α))
    (micro : List (FiniteKernel β β))
    (hsteps : List.Forall₂
      (fun K L => FiniteKernel.comp lift L = FiniteKernel.comp K lift)
      macroSchedule micro) :
    FiniteKernel.comp lift (compList micro) =
      FiniteKernel.comp (compList macroSchedule) lift := by
  induction hsteps with
  | nil =>
      simp
  | @cons K L Ks Ls hstep hrest ih =>
      rw [compList_cons, compList_cons]
      calc
        FiniteKernel.comp lift (FiniteKernel.comp L (compList Ls)) =
          FiniteKernel.comp (FiniteKernel.comp lift L) (compList Ls) :=
            (FiniteKernel.comp_assoc _ _ _).symm
        _ = FiniteKernel.comp (FiniteKernel.comp K lift) (compList Ls) := by
              rw [hstep]
        _ = FiniteKernel.comp K (FiniteKernel.comp lift (compList Ls)) :=
              FiniteKernel.comp_assoc _ _ _
        _ = FiniteKernel.comp K (FiniteKernel.comp (compList Ks) lift) := by
              rw [ih]
        _ = FiniteKernel.comp (FiniteKernel.comp K (compList Ks)) lift :=
              (FiniteKernel.comp_assoc _ _ _).symm

/-- Distribution-level transport for a physical ideal protocol. -/
theorem schedule_apply
    (lift : FiniteKernel α β)
    (macroSchedule : List (FiniteKernel α α))
    (micro : List (FiniteKernel β β))
    (hsteps : List.Forall₂
      (fun K L => FiniteKernel.comp lift L = FiniteKernel.comp K lift)
      macroSchedule micro)
    (start : Dist α) :
    FiniteKernel.apply (FiniteKernel.apply start lift) (compList micro) =
      FiniteKernel.apply (FiniteKernel.apply start (compList macroSchedule)) lift := by
  calc
    FiniteKernel.apply (FiniteKernel.apply start lift) (compList micro) =
      FiniteKernel.apply start (FiniteKernel.comp lift (compList micro)) :=
        FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply start (FiniteKernel.comp (compList macroSchedule) lift) := by
          rw [schedule_intertwining lift macroSchedule micro hsteps]
    _ = FiniteKernel.apply (FiniteKernel.apply start (compList macroSchedule)) lift :=
          (FiniteKernel.apply_comp _ _ _).symm

/-- The physical perfect-local protocol's exact TV distance is the macro
TV distance whenever every step intertwines the same conditional lift. -/
theorem ideal_physical_tv_eq_macro
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (lift : FiniteKernel α β) (project : β → α)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (macroSchedule : List (FiniteKernel α α))
    (idealPhysical : List (FiniteKernel β β))
    (hsteps : List.Forall₂
      (fun K L => FiniteKernel.comp lift L = FiniteKernel.comp K lift)
      macroSchedule idealPhysical)
    (start stationary : Dist α) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift)
        (compList idealPhysical))
      (FiniteKernel.apply stationary lift) =
    Dist.tv (FiniteKernel.apply start (compList macroSchedule)) stationary := by
  rw [schedule_apply lift macroSchedule idealPhysical hsteps start]
  exact FiberLifting.tv_apply_eq_of_leftInverse lift
    (FiniteKernel.deterministic project) hrecover
    (FiniteKernel.apply start (compList macroSchedule)) stationary

/-- The relevant quantitative certificate for finite physical GSR steps.

`actual` contains the physically finite local-riffle steps, while
`idealPhysical` uses perfect-local steps with the *same exchange selection*.
The `hsteps` proof connects ideal-physical execution to the macro chain.
The existing weighted kernel telescope bounds `actual` versus
`idealPhysical`, not versus the unrelated canonical oracle rows.
-/
theorem finite_local_protocol_bound
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty β]
    (lift : FiniteKernel α β) (project : β → α)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (macroSchedule : List (FiniteKernel α α))
    (idealPhysical actual : List (FiniteKernel β β))
    (hsteps : List.Forall₂
      (fun K L => FiniteKernel.comp lift L = FiniteKernel.comp K lift)
      macroSchedule idealPhysical)
    (hlen : actual.length = idealPhysical.length)
    (start stationary : Dist α) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
      (FiniteKernel.apply stationary lift) ≤
    ProtocolCertificate.errorBudget actual idealPhysical +
      Dist.tv (FiniteKernel.apply start (compList macroSchedule)) stationary := by
  have h := ProtocolCertificate.terminalTV_le_reference_add_budget
    actual idealPhysical hlen
    (FiniteKernel.apply start lift) (FiniteKernel.apply stationary lift)
  calc
    Dist.tv
        (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
        (FiniteKernel.apply stationary lift) ≤
      ProtocolCertificate.errorBudget actual idealPhysical +
      Dist.tv
        (FiniteKernel.apply (FiniteKernel.apply start lift)
          (compList idealPhysical))
        (FiniteKernel.apply stationary lift) := h
    _ = ProtocolCertificate.errorBudget actual idealPhysical +
        Dist.tv (FiniteKernel.apply start (compList macroSchedule)) stationary := by
          rw [ideal_physical_tv_eq_macro lift project hrecover macroSchedule
            idealPhysical hsteps start stationary]

/-- End-to-end full-deck version after the stationary fiber disintegration
is known. The target is a genuinely uniform microscopic law, not merely a
macrostate stationarity assertion. -/
theorem finite_local_uniform_bound
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty β]
    (lift : FiniteKernel α β) (project : β → α)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (macroSchedule : List (FiniteKernel α α))
    (idealPhysical actual : List (FiniteKernel β β))
    (hsteps : List.Forall₂
      (fun K L => FiniteKernel.comp lift L = FiniteKernel.comp K lift)
      macroSchedule idealPhysical)
    (hlen : actual.length = idealPhysical.length)
    (start stationary : Dist α) (uniform : Dist β)
    (huniform : FiniteKernel.apply stationary lift = uniform) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
      uniform ≤
    ProtocolCertificate.errorBudget actual idealPhysical +
      Dist.tv (FiniteKernel.apply start (compList macroSchedule)) stationary := by
  rw [← huniform]
  exact finite_local_protocol_bound lift project hrecover macroSchedule idealPhysical
    actual hsteps hlen start stationary

end PhysicalRefinement
end Shufflemath
