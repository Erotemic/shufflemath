module

public import Shufflemath.FiniteDeck.TerminalReset
public import Shufflemath.FiniteDeck.Gate6Row
public import Shufflemath.Gate6K1Swap

@[expose] public section

namespace Shufflemath
namespace GeneralSchedule

open CommanderPermutation CommanderMembershipKernels CommanderPhysicalExchange TerminalReset

/-!
## The general-schedule form — membership-preserving schedules erased by the terminal reset

This module lands the **interspersed-`J` H-erasure law** (part of the A1–A3
terminal-reset deletion story, the deck-level general-schedule form of the
A4 exchange-count lower bound — see `docs/lean_plan.md`, A4 current thread,
and the 2026-11-26 evening finish-line guide, section A4).

The setting is a *schedule* of uniform 25-position exchanges (`S`) interspersed
with membership-preserving shuffles `J` — deck-level kernels whose effect on
the pile-membership observation is the identity (`J ; P = P`). The reward is
two clean identities:

* **`membership_readback_schedule`** — the observed membership law after the
  whole schedule depends *only* on the initial membership read-back and the
  number of exchanges, never on the within-pile order or the identity/order of
  the shuffles. This is the "observed membership law after `t` swaps is exactly
  `Q^t`" claim of the guide, for an arbitrary interspersed membership-preserving
  schedule.
* **`schedule_then_H`** — applying the terminal reset `H` to the output of the
  schedule erases only the within-pile order and leaves the ideal-run law.
  Together with **`run_L_succ`** (the ideal full-round run `L` is the ideal-run
  law, `t ≥ 1`) it yields the deck-level deletion identity
  **`general_schedule_H_erased`**: applying `H` to a schedule output, with at
  least one exchange, leaves `run L t mu` — the `S^t ; H = L^t` identity of
  `KernelReset.lean`, now for an *arbitrary* interspersed schedule.

The zero-exchange case is deliberately not claimed as a `run L t` identity
(the guide: "when there are no exchanges, use the desired terminal reset target
directly; do not claim the positive-length identity for `t=0`"): with no
exchanges the schedule output is `apply mu (buildSchedule sch)` and `H` erases
exactly the within-pile order, leaving the terminal reset of the initial
membership — which is not `mu`.

Everything here is kernel-level and Fintype-free (no `Fintype (Equiv.Perm (Fin 99))`
or cardinal arguments anywhere).
-/

/-- A membership-preserving kernel: applying it and re-reading pile membership
is the same as re-reading the membership of the input deck — `comp J (det membership) = det membership`. -/
def MembershipPreserving (J : FiniteKernel Deck Deck) : Prop :=
  FiniteKernel.comp J (FiniteKernel.deterministic membership) =
    FiniteKernel.deterministic membership

/-- One step of a schedule: a membership-preserving shuffle (with its
preservation proof) or the literal 25-position exchange kernel `S`. -/
inductive ScheduleStep where
  | shuffle (J : FiniteKernel Deck Deck) (h : MembershipPreserving J)
  | exchange

namespace ScheduleStep

/-- The kernel of a schedule step: the shuffle itself, or the exchange kernel
(`S`, the literal 25-position exchange — the swap law `swapLaw` pushed through
its deck action). -/
noncomputable def kernel : ScheduleStep → FiniteKernel Deck Deck
  | .shuffle J _ => J
  | .exchange => FiniteDeck.permutationActionKernel Gate6Crux.swapLaw

/-- The number of exchanges in a schedule. -/
def countExchanges : List ScheduleStep → Nat
  | [] => 0
  | .exchange :: rest => 1 + countExchanges rest
  | _ :: rest => countExchanges rest

end ScheduleStep

/-- The schedule kernel: the composition of the step kernels in execution order
(the first step runs first). -/
noncomputable def buildSchedule : List ScheduleStep → FiniteKernel Deck Deck
  | [] => FiniteKernel.identity
  | k :: rest => FiniteKernel.comp (ScheduleStep.kernel k) (buildSchedule rest)

/-- A membership-preserving kernel leaves the membership read-back unchanged. -/
theorem membership_readback_apply_J (nu : Dist Deck) (J : FiniteKernel Deck Deck)
    (hJ : MembershipPreserving J) :
    FiniteKernel.apply (FiniteKernel.apply nu J) (FiniteKernel.deterministic membership) =
      FiniteKernel.apply nu (FiniteKernel.deterministic membership) := by
  rw [FiniteKernel.apply_comp, hJ]

/-- The exchange kernel's membership read-back: applying the exchange kernel and
re-reading membership gives the post-exchange membership law, i.e. the
initial membership composed with the ideal membership kernel. -/
theorem membership_readback_apply_exchange (nu : Dist Deck) :
    FiniteKernel.apply (FiniteKernel.apply nu S) (FiniteKernel.deterministic membership) =
      FiniteKernel.apply (FiniteKernel.apply nu (FiniteKernel.deterministic membership)) idealMembershipKernel := by
  show FiniteKernel.apply (FiniteKernel.apply nu (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw))
      (FiniteKernel.deterministic membership) = _
  rw [FiniteKernel.apply_comp, k1_swapMembership_eq_exchangeMembership, rawExchangeMembership_eq_comp_rowFactor]
  rw [FiniteKernel.apply_comp]

/-- The exchange kernel composed with the membership read-back is the
membership-level exchange kernel. -/
theorem comp_S_det_membership :
    FiniteKernel.comp S (FiniteKernel.deterministic membership) =
      FiniteKernel.comp (FiniteKernel.deterministic membership) idealMembershipKernel := by
  show FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
      (FiniteKernel.deterministic membership) = _
  rw [k1_swapMembership_eq_exchangeMembership, rawExchangeMembership_eq_comp_rowFactor]

/-- The ideal full-round kernel composed with the membership read-back is the
membership-level exchange kernel: `comp L (det membership) = comp (det membership) idealMembershipKernel`.
The terminal reset `H` is absorbed by the membership read-back. -/
theorem comp_L_det_membership :
    FiniteKernel.comp L (FiniteKernel.deterministic membership) =
      FiniteKernel.comp (FiniteKernel.deterministic membership) idealMembershipKernel := by
  unfold L
  rw [FiniteKernel.comp_assoc]
  have hH : FiniteKernel.comp H (FiniteKernel.deterministic membership) =
      FiniteKernel.deterministic membership := by
    rw [H_eq_idealLocalReset]
    unfold idealLocalReset
    rw [FiniteKernel.comp_assoc, localLift_preserves_membership]
    exact FiniteKernel.comp_id_right _
  rw [hH, comp_S_det_membership]

/-- `comp K (compPow K n) = compPow K (n + 1)` — the membership-level composition. -/
theorem comp_compPow_eq_compPow_succ (K : FiniteKernel Membership Membership) (n : Nat) :
    FiniteKernel.comp K (FiniteKernel.compPow K n) = FiniteKernel.compPow K (n + 1) := by
  induction n with
  | zero => simp [FiniteKernel.compPow]
  | succ m ih =>
    rw [FiniteKernel.compPow_succ]
    calc FiniteKernel.comp K (FiniteKernel.comp (FiniteKernel.compPow K m) K)
        = FiniteKernel.comp (FiniteKernel.comp K (FiniteKernel.compPow K m)) K :=
          (FiniteKernel.comp_assoc K (FiniteKernel.compPow K m) K).symm
      _ = FiniteKernel.comp (FiniteKernel.compPow K (m + 1)) K := by rw [ih]
      _ = FiniteKernel.compPow K (m + 2) := FiniteKernel.compPow_succ K (m + 1)

/-- The membership read-back of the whole schedule depends only on the initial
membership read-back and the number of exchanges — never on the within-pile
order or the identity/order of the shuffles. -/
theorem membership_readback_schedule (mu : Dist Deck) (sch : List ScheduleStep) :
    FiniteKernel.apply (FiniteKernel.apply mu (buildSchedule sch)) (FiniteKernel.deterministic membership) =
      FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership))
        (FiniteKernel.compPow idealMembershipKernel (ScheduleStep.countExchanges sch)) := by
  induction sch generalizing mu with
  | nil =>
    simp [buildSchedule, FiniteKernel.compPow_zero, FiniteKernel.apply_id_left, ScheduleStep.countExchanges]
  | cons step rest ih =>
    have hstep : buildSchedule (step :: rest) =
        FiniteKernel.comp (ScheduleStep.kernel step) (buildSchedule rest) := rfl
    rw [hstep, FiniteKernel.apply_comp, FiniteKernel.comp_assoc, ← FiniteKernel.apply_comp]
    have ih' := ih (FiniteKernel.apply mu (ScheduleStep.kernel step))
    rw [FiniteKernel.apply_comp] at ih'
    rw [ih']
    cases step with
    | shuffle J hJ =>
      simp only [ScheduleStep.kernel] at ⊢
      have hJ1 : FiniteKernel.apply (FiniteKernel.apply mu J) (FiniteKernel.deterministic membership) =
          FiniteKernel.apply mu (FiniteKernel.deterministic membership) :=
        membership_readback_apply_J mu J hJ
      rw [hJ1]
      simp [ScheduleStep.countExchanges]
    | exchange =>
      have hex : FiniteKernel.apply (FiniteKernel.apply mu (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)) (FiniteKernel.deterministic membership) =
          FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership)) idealMembershipKernel :=
        membership_readback_apply_exchange mu
      simp only [ScheduleStep.kernel] at ⊢
      rw [hex]
      rw [FiniteKernel.apply_comp, comp_compPow_eq_compPow_succ]
      rw [show ScheduleStep.countExchanges (ScheduleStep.exchange :: rest) = 1 + ScheduleStep.countExchanges rest from rfl]
      rw [Nat.add_comm]

/-- The membership read-back of the ideal full-round run `L`: applying the
membership kernel to `run L t mu` recovers the ideal membership law. -/
theorem run_L_readback (mu : Dist Deck) (t : Nat) :
    FiniteKernel.apply (FiniteKernel.run L t mu) (FiniteKernel.deterministic membership) =
      FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership))
        (FiniteKernel.compPow idealMembershipKernel t) := by
  induction t with
  | zero =>
    show FiniteKernel.apply mu (FiniteKernel.deterministic membership) = _
    rw [FiniteKernel.compPow_zero, FiniteKernel.apply_id_left]
  | succ t ih =>
    rw [FiniteKernel.run_succ_add, FiniteKernel.apply_comp, comp_L_det_membership, ← FiniteKernel.apply_comp, ih, FiniteKernel.apply_comp, FiniteKernel.compPow_succ]

/-- **The H-erasure law (the general-schedule form):** applying the terminal
reset `H` to the output of an arbitrary interspersed schedule erases only the
within-pile order and leaves the ideal-run law. -/
theorem schedule_then_H (mu : Dist Deck) (sch : List ScheduleStep) :
    FiniteKernel.apply (FiniteKernel.apply mu (buildSchedule sch)) H =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership))
        (FiniteKernel.compPow idealMembershipKernel (ScheduleStep.countExchanges sch))) localLift := by
  rw [H_eq_idealLocalReset]
  unfold idealLocalReset
  rw [← FiniteKernel.apply_comp, membership_readback_schedule mu sch]

/-- The ideal full-round run `L` equals the ideal-run law (`t ≥ 1`). -/
theorem run_L_succ (mu : Dist Deck) (t : Nat) :
    FiniteKernel.run L (Nat.succ t) mu =
      FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership))
        (FiniteKernel.compPow idealMembershipKernel (Nat.succ t))) localLift := by
  induction t with
  | zero =>
    rw [FiniteKernel.run_succ 0]
    show FiniteKernel.apply mu L = _
    unfold L
    rw [← FiniteKernel.apply_comp, H_eq_idealLocalReset]
    unfold idealLocalReset
    rw [← FiniteKernel.apply_comp, membership_readback_apply_exchange]
    simp [FiniteKernel.compPow, FiniteKernel.comp_id_left]
  | succ t ih =>
    calc FiniteKernel.run L (Nat.succ (Nat.succ t)) mu
        = FiniteKernel.apply (FiniteKernel.run L (Nat.succ t) mu) L :=
          FiniteKernel.run_succ _ _ _
      _ = FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.run L (Nat.succ t) mu) S) H := by
          show FiniteKernel.apply (FiniteKernel.run L (Nat.succ t) mu) (FiniteKernel.comp S H) = _
          rw [FiniteKernel.apply_comp]
      _ = FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.run L (Nat.succ t) mu) S) (FiniteKernel.deterministic membership)) localLift := by
          rw [H_eq_idealLocalReset]
          unfold idealLocalReset
          rw [← FiniteKernel.apply_comp]
      _ = FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.run L (Nat.succ t) mu) (FiniteKernel.deterministic membership)) idealMembershipKernel) localLift := by
          rw [membership_readback_apply_exchange]
      _ = FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership)) (FiniteKernel.compPow idealMembershipKernel (Nat.succ t))) idealMembershipKernel) localLift := by
          rw [run_L_readback]
      _ = FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply mu (FiniteKernel.deterministic membership)) (FiniteKernel.compPow idealMembershipKernel (Nat.succ (Nat.succ t)))) localLift := by
          simp only [Nat.succ_eq_add_one, FiniteKernel.compPow_succ]
          rw [← FiniteKernel.apply_comp, ← FiniteKernel.compPow_succ, ← FiniteKernel.apply_comp]
          rw [FiniteKernel.compPow_succ, ← FiniteKernel.apply_comp]

/-- **The deck-level deletion identity (the general-schedule form):** applying
the terminal reset `H` to the output of an arbitrary interspersed membership-
preserving schedule, with at least one exchange, erases the within-pile order
and leaves `run L t mu` with `t` = the number of exchanges in the schedule —
the A1-style identity `S^t ; H = L^t` (`KernelReset.lastReset_run`) extended to
arbitrary interspersed `J`s. The zero-exchange case is not claimed (there is
no `run L t` content — `H` erases the within-pile order from `mu` itself, which
is not the identity). -/
theorem general_schedule_H_erased (mu : Dist Deck) (sch : List ScheduleStep)
    (ht : 1 ≤ ScheduleStep.countExchanges sch) :
    FiniteKernel.apply (FiniteKernel.apply mu (buildSchedule sch)) H =
      FiniteKernel.run L (ScheduleStep.countExchanges sch) mu := by
  have ⟨t, ht_eq⟩ : ∃ t, ScheduleStep.countExchanges sch = Nat.succ t := by
    refine ⟨ScheduleStep.countExchanges sch - 1, ?_⟩
    have hle : ScheduleStep.countExchanges sch - 1 + 1 = ScheduleStep.countExchanges sch :=
      Nat.sub_add_cancel ht
    omega
  rw [ht_eq, schedule_then_H, ht_eq, ← run_L_succ]

end GeneralSchedule
end Shufflemath
