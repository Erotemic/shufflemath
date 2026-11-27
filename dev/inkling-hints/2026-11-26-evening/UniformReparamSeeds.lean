module

public import Shufflemath.FiniteDeck.HistogramKernel
public import Shufflemath.GSR

@[expose] public section

namespace Shufflemath.FinishHints

/-! Proposed, uncompiled. The target Z need not have a Fintype; the only
finite types are the abstract choice domains. This is the key to both the
fixed-pair exchange quotient and the binary-riffle bridge. -/

theorem uniform_map_eq_of_reparam {A B Z : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) (f : A → Z) (g : B → Z)
    (h : ∀ x, f x = g (e x)) :
    (GSR.uniformDist A).map f = (GSR.uniformDist B).map g := by
  calc
    _ = (GSR.uniformDist A).map (fun a => g (e a)) := by
      rw [show f = (fun a => g (e a)) from funext h]
    _ = ((GSR.uniformDist A).map e).map g := by
      rw [Convexity.StdSimplex.map_map]
    _ = _ := by rw [GSR.map_bijective_uniformDist e]

/-- Observation maps need only be injective on their actual carrier. To
recover law equality, use a left inverse with an arbitrary default, not an
universe of all lists. The existing cancel_map_leftInverse is Fintype-free. -/
theorem cancel_injective_map {X Y : Type*} [Nonempty X]
    (f : X → Y) (hf : Function.Injective f) (mu nu : Dist X)
    (h : mu.map f = nu.map f) : mu = nu := by
  classical
  let r : Y → X := fun y => if hy : ∃ x, f x = y then Classical.choose hy
    else Classical.choice (inferInstance : Nonempty X)
  have hr : Function.LeftInverse r f := by
    intro x
    dsimp only [r]
    split
    · next hy => exact hf (Classical.choose_spec hy)
    · next hy => exact False.elim (hy ⟨x, rfl⟩)
  exact GenericQuotient.cancel_map_leftInverse f r hr mu nu h

end Shufflemath.FinishHints
