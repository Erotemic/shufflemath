import Shufflemath.IndexedRun
import Shufflemath.GSR

/-! Candidate generic G7 bridge. All types may change with time. -/
namespace Shufflemath.Nov27Seeds
universe u v

theorem apply_hetero_observe {A B : Type u} {C D : Type v}
    (f : A → C) (g : B → D) (K : FiniteKernel A B) (Q : FiniteKernel C D)
    (h : FiniteKernel.comp K (FiniteKernel.deterministic g) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) (μ : Dist A) :
    (FiniteKernel.apply μ K).map g = FiniteKernel.apply (μ.map f) Q := by
  calc
    _ = FiniteKernel.apply (FiniteKernel.apply μ K) (FiniteKernel.deterministic g) :=
      (GSR.apply_deterministic _ _).symm
    _ = FiniteKernel.apply μ (FiniteKernel.comp K (FiniteKernel.deterministic g)) :=
      FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply μ (FiniteKernel.comp (FiniteKernel.deterministic f) Q) := by rw [h]
    _ = FiniteKernel.apply (FiniteKernel.apply μ (FiniteKernel.deterministic f)) Q :=
      (FiniteKernel.apply_comp _ _ _).symm
    _ = _ := by rw [GSR.apply_deterministic]

theorem indexedRun_observe {X : Nat → Type u} {Y : Nat → Type v}
    (K : (t : Nat) → FiniteKernel (X t) (X (t+1)))
    (Q : (t : Nat) → FiniteKernel (Y t) (Y (t+1)))
    (f : (t : Nat) → X t → Y t)
    (h : ∀ t, FiniteKernel.comp (K t) (FiniteKernel.deterministic (f (t+1))) =
      FiniteKernel.comp (FiniteKernel.deterministic (f t)) (Q t))
    (μ : Dist (X 0)) (t : Nat) :
    (indexedRun K μ t).map (f t) = indexedRun Q (μ.map (f 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [indexedRun_succ, indexedRun_succ, apply_hetero_observe (f t) (f (t+1)) (K t) (Q t) (h t), ih]

end Shufflemath.Nov27Seeds
