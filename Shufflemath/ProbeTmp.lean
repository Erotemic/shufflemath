import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

section
variable (U : Finset ℕ) (M : ℕ) (f : Finset ℕ → ℕ)

theorem probe (u : Finset ℕ) :
    (∑ a ∈ Finset.range 3, if _ : a = 0 then (∑ v ∈ U.powerset, f v) else 0) =
      ∑ a ∈ Finset.range 3, if _ : a = 0 then (∑ v ∈ U.powerset, f v) else 0 := by
  rw [show (∑ v ∈ U.powerset, f v) = ∑ v ∈ U.powerset, f v, rfl]
  rfl
end
