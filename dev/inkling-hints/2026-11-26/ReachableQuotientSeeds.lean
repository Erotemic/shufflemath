module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.Markov
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.InklingNov26

/-! Proposed, NOT independently compiled. These lemmas deliberately require
no Fintype, DecidableEq, Nonempty, or enumeration of the raw observation type.
The raw observation can be an integer-valued function. Compile this file first,
then migrate the generic declarations into the library. -/

/-- Only attainable observation values are states. -/
def ReachObs {X Y : Type*} (f : X → Y) := {y : Y // ∃ x : X, f x = y}

def observe {X Y : Type*} (f : X → Y) (x : X) : ReachObs f :=
  ⟨f x, ⟨x, rfl⟩⟩

noncomputable def representative {X Y : Type*} (f : X → Y)
    (y : ReachObs f) : X := Classical.choose y.property

theorem observe_representative {X Y : Type*} (f : X → Y) (y : ReachObs f) :
    observe f (representative f y) = y := by
  apply Subtype.ext
  exact Classical.choose_spec y.property

theorem observe_surjective {X Y : Type*} (f : X → Y) :
    Function.Surjective (observe f) := fun y => ⟨representative f y, observe_representative f y⟩

/-- An explicit left inverse to the inclusion, defined only when there is a
reachable default. Off the range its value is immaterial. -/
noncomputable def retract {X Y : Type*} (f : X → Y) (d : ReachObs f)
    (y : Y) : ReachObs f := by
  classical
  exact if h : ∃ x : X, f x = y then ⟨y, h⟩ else d

theorem retract_val {X Y : Type*} (f : X → Y) (d z : ReachObs f) :
    retract f d z.val = z := by
  classical
  unfold retract
  rw [dif_pos z.property]

/-- Equality of pushforwards can be cancelled using a left inverse, without
point masses or a Fintype instance. -/
theorem cancel_map_leftInverse {X Y : Type*} (g : X → Y) (r : Y → X)
    (hr : Function.LeftInverse r g) (μ ν : Dist X)
    (h : μ.map g = ν.map g) : μ = ν := by
  have hm := congrArg (fun w : Dist Y => w.map r) h
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map] at hm
  have hi : r ∘ g = id := funext hr
  rw [hi, Convexity.StdSimplex.map_id, Convexity.StdSimplex.map_id] at hm
  exact hm

/-- Raw equality of observed rows implies equality on the reachable carrier.
The essential bridge from signedHist_lumpable to a genuine quotient. -/
theorem reachable_map_eq {X Y : Type*} (f : X → Y) (μ ν : Dist X)
    (d : ReachObs f) (h : μ.map f = ν.map f) :
    μ.map (observe f) = ν.map (observe f) := by
  apply cancel_map_leftInverse (fun z : ReachObs f => z.val) (retract f d)
    (retract_val f d)
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  exact h

/-- A normalized quotient row by representative choice. -/
noncomputable def quotient {X Y : Type*} (f : X → Y) (K : FiniteKernel X X) :
    FiniteKernel (ReachObs f) (ReachObs f) :=
  fun y => (K (representative f y)).map (observe f)

theorem quotient_at {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f) (x : X) :
    quotient f K (observe f x) = (K x).map (observe f) := by
  apply reachable_map_eq f _ _ (observe f x)
  exact hl _ _ (Classical.choose_spec (observe f x).property)

/-- The actual commuting square, not a row-sum identity. -/
theorem quotient_intertwines {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f) :
    FiniteKernel.comp K (FiniteKernel.deterministic (observe f)) =
      FiniteKernel.comp (FiniteKernel.deterministic (observe f)) (quotient f K) := by
  funext x
  change FiniteKernel.apply (K x) (FiniteKernel.deterministic (observe f)) =
    FiniteKernel.apply (Dist.pointMass (observe f x)) (quotient f K)
  rw [GSR.apply_deterministic, FiniteKernel.apply_pointMass]
  exact (quotient_at f K hl x).symm

/-- Generic commuting-square transport, no finite sums. -/
theorem apply_observation {X Y : Type*} (f : X → Y)
    (K : FiniteKernel X X) (Q : FiniteKernel Y Y)
    (h : FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) (μ : Dist X) :
    (FiniteKernel.apply μ K).map f = FiniteKernel.apply (μ.map f) Q := by
  calc
    _ = FiniteKernel.apply (FiniteKernel.apply μ K) (FiniteKernel.deterministic f) :=
      (GSR.apply_deterministic _ _).symm
    _ = FiniteKernel.apply μ (FiniteKernel.comp K (FiniteKernel.deterministic f)) :=
      FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply μ (FiniteKernel.comp (FiniteKernel.deterministic f) Q) := by rw [h]
    _ = FiniteKernel.apply (FiniteKernel.apply μ (FiniteKernel.deterministic f)) Q :=
      (FiniteKernel.apply_comp _ _ _).symm
    _ = _ := by rw [GSR.apply_deterministic]

theorem quotient_stationary {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f)
    (μ : Dist X) (hμ : FiniteKernel.apply μ K = μ) :
    FiniteKernel.apply (μ.map (observe f)) (quotient f K) = μ.map (observe f) := by
  have h := apply_observation (observe f) K (quotient f K)
    (quotient_intertwines f K hl) μ
  rw [hμ] at h
  exact h.symm

/-- Exact simulation of all t steps, not just one step or stationary starts. -/
theorem run_observation {X Y : Type*} (f : X → Y)
    (K : FiniteKernel X X) (Q : FiniteKernel Y Y)
    (h : FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) (t : Nat) (μ : Dist X) :
    (FiniteKernel.run K t μ).map f = FiniteKernel.run Q t (μ.map f) := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
    rw [Nat.succ_eq_add_one, FiniteKernel.run_rec_eq, FiniteKernel.run_rec_eq,
      ih, apply_observation f K Q h]

end Shufflemath.InklingNov26
