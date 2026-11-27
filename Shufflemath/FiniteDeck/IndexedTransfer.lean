module

public import Shufflemath.IndexedRun
public import Shufflemath.FiniteDeck.UniformTransport

@[expose] public section

/-!
# Arbitrary-length changing-capacity transfer schedules

The general changing-capacities arc (G7) was parked as a fixed-length composition:
2-step and 3-step transfer chains in `UniformTransport.lean`.  This module proves the
*arbitrary-length* version with one indexed-run theorem, replacing the parked
`LegalChain` representation (a changing capacity vector is data, not an inductive
family parameter).

A **transfer schedule** `cap : Nat → Fin p → Nat` starts at `n₀` and each step
transfers `amount t` cards from pile `src t` into pile `dst t`.  The successor
capacities are **definitionally** the `transferCap` of the previous capacities, so a
`FiniteKernel (Allocation N p (cap t)) (Allocation N p (cap (t+1)))` fits without any
`Eq.rec` casts.

Three facts make the run transport the uniform law:
1. `transferSchedule_sum` — the schedule preserves feasibility (`∑ cap = N`) by
   induction through `transferCap_sum`.
2. `transferStep` — the typed one-step transfer kernel.
3. `indexedTransfer_reference` — the **headline**: the run of uniform-law transport
   kernels from the uniform law on the initial carrier is the uniform law on the final
   carrier.  Built once from `indexedRun_reference` + the one-step
   `uniform_transport_transferKernel`.

No concrete capacity vectors, `Fintype` instances, or lengths are assumed.
-/

namespace Shufflemath.FiniteDeck

open Classical

/-- The capacity schedule of a finite transfer run: starting at `n₀`, each step
transfers `amount t` cards from pile `src t` into pile `dst t`.  Each successor is
definitionally the `transferCap` of the previous capacities. -/
noncomputable def transferSchedule (p : Nat) (n₀ : Fin p → Nat)
    (src dst : Nat → Fin p) (amount : Nat → Nat) (t : Nat) : Fin p → Nat :=
  Nat.recOn t n₀ (fun s prev => transferCap prev (src s) (dst s) (amount s))

/-- Total capacities are preserved along any legal transfer schedule, by induction
through `transferCap_sum`. -/
theorem transferSchedule_sum (N : Nat) (p : Nat) (n₀ : Fin p → Nat)
    (hsum₀ : (∑ i, n₀ i) = N)
    (src dst : Nat → Fin p) (amount : Nat → Nat)
    (hsrc : ∀ t, src t ≠ dst t)
    (ht : ∀ t, amount t ≤ transferSchedule p n₀ src dst amount t (src t))
    (t : Nat) : (∑ i, transferSchedule p n₀ src dst amount t i) = N := by
  induction t with
  | zero => exact hsum₀
  | succ t ih => exact transferCap_sum ih (ht t) (hsrc t)

/-- The typed kernel of one step of the transfer schedule: the uniform-law-
transporting kernel `transferKernel` between consecutive carriers (the successor
carrier is definitionally the `transferCap` of the current one). -/
noncomputable def transferStep (N : Nat) (p : Nat) (n₀ : Fin p → Nat)
    (src dst : Nat → Fin p) (amount : Nat → Nat)
    (hsrc : ∀ t, src t ≠ dst t)
    (ht : ∀ t, amount t ≤ transferSchedule p n₀ src dst amount t (src t))
    (t : Nat) :
    FiniteKernel (Allocation N p (transferSchedule p n₀ src dst amount t))
      (Allocation N p (transferSchedule p n₀ src dst amount (Nat.succ t))) :=
  transferKernel (src t) (dst t) (amount t) (hsrc t) (ht t)

/-- **Arbitrary-length changing-capacity uniform transport.**  The run of uniform-law
transport kernels from the uniform law on the initial carrier is the uniform law on
the final carrier — one theorem for the whole schedule, not a growing list of
fixed-length corollaries. -/
theorem indexedTransfer_reference (N : Nat) (p : Nat) (n₀ : Fin p → Nat)
    (hsum₀ : (∑ i, n₀ i) = N)
    (src dst : Nat → Fin p) (amount : Nat → Nat)
    (hsrc : ∀ t, src t ≠ dst t)
    (ht : ∀ t, amount t ≤ transferSchedule p n₀ src dst amount t (src t))
    (t : Nat) :
    indexedRun (transferStep N p n₀ src dst amount hsrc ht)
      (uniformAlloc hsum₀) t =
    uniformAlloc (transferSchedule_sum N p n₀ hsum₀ src dst amount hsrc ht t) := by
  have hstep : ∀ t, FiniteKernel.apply
      (uniformAlloc (transferSchedule_sum N p n₀ hsum₀ src dst amount hsrc ht t))
      (transferStep N p n₀ src dst amount hsrc ht t) =
      uniformAlloc (transferSchedule_sum N p n₀ hsum₀ src dst amount hsrc ht (Nat.succ t)) := by
    intro s
    have h := uniform_transport_transferKernel (src s) (dst s) (amount s)
      (hsrc s) (ht s) (transferSchedule_sum N p n₀ hsum₀ src dst amount hsrc ht s)
    exact h.trans (uniformAlloc_eq_uniformTransferAlloc (hsrc s) (ht s)
      (transferSchedule_sum N p n₀ hsum₀ src dst amount hsrc ht s))
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [indexedRun_succ, ih, hstep t]

end Shufflemath.FiniteDeck
