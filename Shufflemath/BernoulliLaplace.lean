import Mathlib

namespace Shufflemath
namespace BernoulliLaplace

/-- The first-mode factor appearing in the unequal two-urn Bernoulli--Laplace
exchange chain. At this stage we formalize the exact arithmetic expression; a later
file will prove that it is the corresponding eigenvalue of the finite transition
kernel. -/
def firstModeFactor (N m k : ℕ) : ℚ :=
  1 - ((N : ℚ) * k) / ((m : ℚ) * (N - m))

/-- Exchange sizes 1 through 49, encoded by zero-based `Fin 49`. -/
def commanderExchangeSize (k : Fin 49) : ℕ := k.val + 1

/-- First-mode factor for the 99-card, 50/49 split. -/
def commanderFirstMode (k : Fin 49) : ℚ :=
  firstModeFactor 99 50 (commanderExchangeSize k)

/-- `Fin 49` value corresponding to exchanging 25 cards. -/
def exchange25 : Fin 49 := ⟨24, by decide⟩

/-- `Fin 49` value corresponding to exchanging 24 cards. -/
def exchange24 : Fin 49 := ⟨23, by decide⟩

/-- `Fin 49` value corresponding to exchanging 26 cards. -/
def exchange26 : Fin 49 := ⟨25, by decide⟩

@[simp]
theorem commander_factor_25 : commanderFirstMode exchange25 = -(1 / 98 : ℚ) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange25, firstModeFactor]

@[simp]
theorem commander_factor_24 : commanderFirstMode exchange24 = (37 / 1225 : ℚ) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange24, firstModeFactor]

@[simp]
theorem commander_factor_26 : commanderFirstMode exchange26 = -(62 / 1225 : ℚ) := by
  norm_num [commanderFirstMode, commanderExchangeSize, exchange26, firstModeFactor]

/-- Among integer exchanges 1..49, 25 minimizes the absolute value of the
Commander 50/49 first-mode factor. This theorem is finite exact arithmetic; its
spectral interpretation depends on the future kernel/eigenvalue theorem. -/
theorem commander_exchange25_minimizes_first_mode :
    ∀ k : Fin 49, |commanderFirstMode exchange25| ≤ |commanderFirstMode k| := by
  native_decide

end BernoulliLaplace
end Shufflemath
