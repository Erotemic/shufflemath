import Shufflemath.FiberLifting
import Shufflemath.BernoulliLaplaceSemantic
import Shufflemath.ProtocolCertificate

namespace Shufflemath
namespace OracleRefinement

/-!
# A canonical oracle exchange on refined finite states

A macrostate x is refined by a conditional kernel `lift x` on microscopic
states.  A deterministic projection recovers x.  The *oracle* microscopic
step first observes the macrostate, takes one macro transition, and samples
an entirely fresh microscopic configuration from its conditional fiber.

The oracle kernel is a mathematically explicit model: it should not be
silently identified with swapping physical cards and shuffling each pile.
That identification is a further exchange-intertwining theorem.

The important consequence here is that the canonical oracle commutes with
`lift` for every macro kernel.  The proof only uses the already-verified
kernel algebra and a left-inverse property, not any symmetry calculation.
The same holds for heterogeneous schedules, so the existing exact rational
Commander certificates transport unchanged to a microstate model once its
fiber laws have been constructed.
-/

variable {α β : Type*}

/-- Project a microscopic state, make one macroscopic Markov transition,
then resample the full microscopic configuration from the resulting fiber. -/
noncomputable def oracleStep (project : β → α)
    (lift : FiniteKernel α β) (macroK : FiniteKernel α α) :
    FiniteKernel β β :=
  FiniteKernel.comp (FiniteKernel.deterministic project)
    (FiniteKernel.comp macroK lift)

/-- The oracle acts on a fiber-uniform start exactly like the macro step,
then a fresh conditional draw. This is the single-step intertwining law. -/
theorem oracle_intertwining
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (macroK : FiniteKernel α α) :
    FiniteKernel.comp lift (oracleStep project lift macroK) =
      FiniteKernel.comp macroK lift := by
  unfold oracleStep
  calc
    FiniteKernel.comp lift
        (FiniteKernel.comp (FiniteKernel.deterministic project)
          (FiniteKernel.comp macroK lift)) =
      FiniteKernel.comp
        (FiniteKernel.comp lift (FiniteKernel.deterministic project))
        (FiniteKernel.comp macroK lift) :=
          (FiniteKernel.comp_assoc _ _ _).symm
    _ = FiniteKernel.comp FiniteKernel.identity
        (FiniteKernel.comp macroK lift) := by rw [hrecover]
    _ = FiniteKernel.comp macroK lift := FiniteKernel.comp_id_left _

/-- A heterogeneous macro protocol, lifted into the same oracle model. -/
noncomputable def oracleSchedule (project : β → α)
    (lift : FiniteKernel α β) (schedule : List (FiniteKernel α α)) :
    List (FiniteKernel β β) :=
  schedule.map (oracleStep project lift)

@[simp]
theorem oracleSchedule_nil (project : β → α) (lift : FiniteKernel α β) :
    oracleSchedule project lift [] = [] := rfl

@[simp]
theorem oracleSchedule_cons (project : β → α) (lift : FiniteKernel α β)
    (K : FiniteKernel α α) (Ks : List (FiniteKernel α α)) :
    oracleSchedule project lift (K :: Ks) =
      oracleStep project lift K :: oracleSchedule project lift Ks := rfl

/-- A complete *inhomogeneous* exchange schedule commutes with refinement.
The right-hand composite is in execution order, as in `compList`. -/
theorem schedule_intertwining
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (schedule : List (FiniteKernel α α)) :
    FiniteKernel.comp lift (compList (oracleSchedule project lift schedule)) =
      FiniteKernel.comp (compList schedule) lift := by
  induction schedule with
  | nil =>
      simp [oracleSchedule]
  | cons K Ks ih =>
      rw [oracleSchedule_cons, compList_cons, compList_cons]
      calc
        FiniteKernel.comp lift
            (FiniteKernel.comp (oracleStep project lift K)
              (compList (oracleSchedule project lift Ks))) =
          FiniteKernel.comp
            (FiniteKernel.comp lift (oracleStep project lift K))
            (compList (oracleSchedule project lift Ks)) :=
              (FiniteKernel.comp_assoc _ _ _).symm
        _ = FiniteKernel.comp (FiniteKernel.comp K lift)
            (compList (oracleSchedule project lift Ks)) := by
              rw [oracle_intertwining project lift hrecover K]
        _ = FiniteKernel.comp K
            (FiniteKernel.comp lift
              (compList (oracleSchedule project lift Ks))) :=
                FiniteKernel.comp_assoc _ _ _
        _ = FiniteKernel.comp K (FiniteKernel.comp (compList Ks) lift) :=
              by rw [ih]
        _ = FiniteKernel.comp (FiniteKernel.comp K (compList Ks)) lift :=
              (FiniteKernel.comp_assoc _ _ _).symm

/-- The full microstate law after the oracle schedule is precisely the
refinement of the macrostate law after the original schedule. -/
theorem schedule_apply
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (schedule : List (FiniteKernel α α)) (start : Dist α) :
    FiniteKernel.apply (FiniteKernel.apply start lift)
      (compList (oracleSchedule project lift schedule)) =
    FiniteKernel.apply (FiniteKernel.apply start (compList schedule)) lift := by
  calc
    FiniteKernel.apply (FiniteKernel.apply start lift)
        (compList (oracleSchedule project lift schedule)) =
      FiniteKernel.apply start
        (FiniteKernel.comp lift
          (compList (oracleSchedule project lift schedule))) :=
            FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply start (FiniteKernel.comp (compList schedule) lift) := by
          rw [schedule_intertwining project lift hrecover schedule]
    _ = FiniteKernel.apply (FiniteKernel.apply start (compList schedule)) lift :=
          (FiniteKernel.apply_comp _ _ _).symm

/-- Exact TV is preserved for *every* oracle schedule, not only a
homogeneous sequence of equally sized exchanges. -/
theorem schedule_tv_eq_macro
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (schedule : List (FiniteKernel α α)) (start stationary : Dist α) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift)
        (compList (oracleSchedule project lift schedule)))
      (FiniteKernel.apply stationary lift) =
    Dist.tv (FiniteKernel.apply start (compList schedule)) stationary := by
  rw [schedule_apply project lift hrecover schedule start]
  exact FiberLifting.tv_apply_eq_of_leftInverse lift
    (FiniteKernel.deterministic project) hrecover
    (FiniteKernel.apply start (compList schedule)) stationary

/-- For a homogeneous oracle process, the existing exact mixing theorem
transfers directly to the microscopic state space. -/
theorem run_tv_eq_macro
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (macroK : FiniteKernel α α) (start stationary : Dist α) (n : Nat) :
    Dist.tv
      (FiniteKernel.run (oracleStep project lift macroK) n
        (FiniteKernel.apply start lift))
      (FiniteKernel.apply stationary lift) =
    Dist.tv (FiniteKernel.run macroK n start) stationary := by
  exact FiberLifting.run_tv_eq_macro lift
    (FiniteKernel.deterministic project) macroK
    (oracleStep project lift macroK) hrecover
    (oracle_intertwining project lift hrecover macroK) start stationary n

/-- A verified TV bound for a *physical* schedule follows from two
separate ingredients: a row-wise discrepancy against the oracle steps and
an exact macrostate TV certificate. The latter has no extra microscopic
proof obligations. The discrepancy is deliberately not assumed zero. -/
theorem actual_protocol_error_bound
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty β]
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (schedule : List (FiniteKernel α α))
    (actual : List (FiniteKernel β β))
    (hlen : actual.length = schedule.length)
    (start stationary : Dist α) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
      (FiniteKernel.apply stationary lift) ≤
    ProtocolCertificate.errorBudget actual
      (oracleSchedule project lift schedule) +
    Dist.tv (FiniteKernel.apply start (compList schedule)) stationary := by
  have hlift : actual.length = (oracleSchedule project lift schedule).length := by
    simpa [oracleSchedule] using hlen
  have h := ProtocolCertificate.terminalTV_le_reference_add_budget
    actual (oracleSchedule project lift schedule) hlift
    (FiniteKernel.apply start lift) (FiniteKernel.apply stationary lift)
  calc
    Dist.tv
        (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
        (FiniteKernel.apply stationary lift) ≤
      ProtocolCertificate.errorBudget actual
        (oracleSchedule project lift schedule) +
      Dist.tv
        (FiniteKernel.apply (FiniteKernel.apply start lift)
          (compList (oracleSchedule project lift schedule)))
        (FiniteKernel.apply stationary lift) := h
    _ = ProtocolCertificate.errorBudget actual
          (oracleSchedule project lift schedule) +
        Dist.tv (FiniteKernel.apply start (compList schedule)) stationary := by
          rw [schedule_tv_eq_macro project lift hrecover schedule start stationary]

/-- When a stationary macro law lifts to the desired microscopic uniform
law, the same estimate is automatically an end-to-end physical error bound.
This theorem *does not* assert that the identification holds for 99 cards;
that counting theorem must be provided separately. -/
theorem actual_protocol_uniform_bound
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty β]
    (project : β → α) (lift : FiniteKernel α β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity)
    (schedule : List (FiniteKernel α α))
    (actual : List (FiniteKernel β β))
    (hlen : actual.length = schedule.length)
    (start stationary : Dist α) (uniform : Dist β)
    (huniform : FiniteKernel.apply stationary lift = uniform) :
    Dist.tv
      (FiniteKernel.apply (FiniteKernel.apply start lift) (compList actual))
      uniform ≤
    ProtocolCertificate.errorBudget actual
      (oracleSchedule project lift schedule) +
    Dist.tv (FiniteKernel.apply start (compList schedule)) stationary := by
  rw [← huniform]
  exact actual_protocol_error_bound project lift hrecover schedule actual hlen
    start stationary

/-! ## Exact Commander distances, on any recovered 99-card refinement -/

open BernoulliLaplace

/-- The exact *two*-exchange rational distance holds on any concrete
microstate space equipped with a recovered fiber law.  In particular,
this theorem is ready to specialize once the permutation-fiber kernel and
the hypergeometric/uniform-law identification have been established. -/
theorem commander_oracle_two_exact
    [Fintype β] [DecidableEq β]
    (project : β → CommanderState)
    (lift : FiniteKernel CommanderState β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity) :
    Dist.tv
      (FiniteKernel.run (oracleStep project lift commanderExchange25) 2
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState) lift))
      (FiniteKernel.apply commanderStationary lift) =
      (12255318415559330995522631403472464258192877 /
        4933350368865509640837610315994582805439728012 : Rat) := by
  rw [run_tv_eq_macro project lift hrecover commanderExchange25
    (Dist.pointMass commanderSegregatedState) commanderStationary 2]
  exact BernoulliLaplace.commander_tv_after_two_semantic

/-- The exact *three*-exchange rational microstate distance is inherited
from the existing 50-state certificate under the same recovered lift. -/
theorem commander_oracle_three_exact
    [Fintype β] [DecidableEq β]
    (project : β → CommanderState)
    (lift : FiniteKernel CommanderState β)
    (hrecover : FiniteKernel.comp lift
      (FiniteKernel.deterministic project) = FiniteKernel.identity) :
    Dist.tv
      (FiniteKernel.run (oracleStep project lift commanderExchange25) 3
        (FiniteKernel.apply (Dist.pointMass commanderSegregatedState) lift))
      (FiniteKernel.apply commanderStationary lift) =
      (172379525755689183991816396516567920780192827919620440221147749 /
        6691837923759692633601708022649918108038775216019298375918637677488 : Rat) := by
  rw [run_tv_eq_macro project lift hrecover commanderExchange25
    (Dist.pointMass commanderSegregatedState) commanderStationary 3]
  exact BernoulliLaplace.commander_tv_after_three_semantic

end OracleRefinement
end Shufflemath
