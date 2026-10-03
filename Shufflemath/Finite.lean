import Mathlib

namespace Shufflemath

/-- A finite signed/rational weight. Probability distributions are weights satisfying
`IsProbability`. Keeping the carrier as a plain function makes exact finite matrix
calculations straightforward. -/
abbrev Weight (α : Type*) := α → ℚ

namespace Weight

variable {α β γ : Type*}

/-- Total mass of a finite weight. -/
def total [Fintype α] (μ : Weight α) : ℚ := ∑ x, μ x

/-- Predicate saying that a finite rational weight is a probability distribution. -/
def IsProbability [Fintype α] (μ : Weight α) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ total μ = 1

/-- Point mass at `x`. -/
def pointMass [DecidableEq α] (x : α) : Weight α :=
  fun y => if y = x then 1 else 0

/-- Uniform rational weight on a nonempty finite type. -/
def uniform [Fintype α] [Nonempty α] : Weight α :=
  fun _ => 1 / (Fintype.card α : ℚ)

/-- Total-variation distance for finite rational weights. It is a genuine TV metric
when both inputs are probability distributions. -/
def tv [Fintype α] (μ ν : Weight α) : ℚ :=
  (1 / 2 : ℚ) * ∑ x, |μ x - ν x|

@[simp]
theorem tv_self [Fintype α] (μ : Weight α) : tv μ μ = 0 := by
  simp [tv]

theorem tv_comm [Fintype α] (μ ν : Weight α) : tv μ ν = tv ν μ := by
  simp only [tv]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_sub_comm]

end Weight

/-- A finite rational transition kernel. `IsMarkov` records row normalization. -/
abbrev Kernel (α β : Type*) := α → β → ℚ

namespace Kernel

variable {α β γ : Type*}

/-- Apply a kernel to a finite input weight. -/
def apply [Fintype α] (μ : Weight α) (K : Kernel α β) : Weight β :=
  fun y => ∑ x, μ x * K x y

/-- Compose kernels in execution order: first `K`, then `L`. -/
def comp [Fintype β] (K : Kernel α β) (L : Kernel β γ) : Kernel α γ :=
  fun x z => ∑ y, K x y * L y z

/-- Every row of the kernel is a probability distribution. -/
def IsMarkov [Fintype β] (K : Kernel α β) : Prop :=
  ∀ x, Weight.IsProbability (K x)

/-- Kernel induced by a deterministic state transformation. -/
def deterministic [DecidableEq β] (f : α → β) : Kernel α β :=
  fun x y => if y = f x then 1 else 0

/-- Identity kernel. -/
def identity [DecidableEq α] : Kernel α α := deterministic id

@[simp]
theorem deterministic_apply_pointMass
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (x : α) (f : α → β) :
    apply (Weight.pointMass x) (deterministic f) = Weight.pointMass (f x) := by
  funext y
  simp [apply, Weight.pointMass, deterministic]

end Kernel

end Shufflemath
