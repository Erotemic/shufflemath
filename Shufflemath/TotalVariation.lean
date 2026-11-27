module

public import Shufflemath.Matrix
public import Shufflemath.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Sub.Basic

@[expose] public section

namespace Shufflemath

/-- Exact total-variation distance for two rational finite vectors. -/
def vectorTV {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : Rat :=
  (1 / 2 : Rat) *
    Finset.sum Finset.univ (fun x => |p x - q x|)

@[simp]
theorem vectorTV_self {alpha : Type*} [Fintype alpha]
    (p : alpha -> Rat) : vectorTV p p = 0 := by
  simp [vectorTV]

theorem vectorTV_comm {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : vectorTV p q = vectorTV q p := by
  unfold vectorTV
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm (p x) (q x)

theorem vectorTV_nonneg {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat) : 0 <= vectorTV p q := by
  unfold vectorTV
  positivity

/-- Triangle inequality: total variation is a metric on finite rational
vectors. Pointwise, `|p x - r x| = |(p x - q x) + (q x - r x)|` and `abs_add`;
then the sum splits over the two terms. -/
theorem vectorTV_triangle {alpha : Type*} [Fintype alpha]
    (p q r : alpha -> Rat) :
    vectorTV p r <= vectorTV p q + vectorTV q r := by
  have hterm : forall x, |p x - r x| <= |p x - q x| + |q x - r x| := by
    intro x
    have h : p x - r x = (p x - q x) + (q x - r x) := by ring
    calc
      |p x - r x| = |(p x - q x) + (q x - r x)| := by rw [h]
      _ <= |p x - q x| + |q x - r x| := by exact abs_add_le _ _
  unfold vectorTV
  calc
    (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - r x|) <=
        (1 / 2 : Rat) * (Finset.sum Finset.univ (fun x => |p x - q x|) +
          Finset.sum Finset.univ (fun x => |q x - r x|)) := by
      rw [← Finset.sum_add_distrib]
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hterm x))
      norm_num
    _ = vectorTV p q + vectorTV q r := by
      simp [vectorTV]
      ring

/-- Probability vectors are at total-variation distance at most one. -/
theorem vectorTV_le_one_of_probability
    {alpha : Type*} [Fintype alpha]
    (p q : alpha -> Rat)
    (hp : forall x, 0 <= p x)
    (hq : forall x, 0 <= q x)
    (hp1 : Finset.sum Finset.univ p = 1)
    (hq1 : Finset.sum Finset.univ q = 1) :
    vectorTV p q <= 1 := by
  have hterm : forall x, |p x - q x| <= p x + q x := by
    intro x
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using
      (abs_add_le (p x) (-q x))
  have hsum :
      Finset.sum Finset.univ (fun x => |p x - q x|) <=
        Finset.sum Finset.univ (fun x => p x + q x) := by
    exact Finset.sum_le_sum (fun x _ => hterm x)
  calc
    vectorTV p q <=
        (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => p x + q x) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 1 := by
      rw [Finset.sum_add_distrib, hp1, hq1]
      norm_num

/-- Zero TV distance is exactly equality of the mass functions: a sum of
nonnegatives is zero iff every term is zero (`Finset.single_le_sum`). -/
theorem vectorTV_eq_zero {alpha : Type*} [Fintype alpha] (p q : alpha -> Rat) :
    vectorTV p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsum : Finset.sum Finset.univ (fun x => |p x - q x|) = 0 := by
      have h' : (1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - q x|) = 0 := by
        unfold vectorTV at h
        exact h
      calc
        Finset.sum Finset.univ (fun x => |p x - q x|) =
            2 * ((1 / 2 : Rat) * Finset.sum Finset.univ (fun x => |p x - q x|)) := by ring
        _ = 2 * 0 := by rw [h']
        _ = 0 := by norm_num
    ext x
    have hterm : |p x - q x| = 0 := by
      apply le_antisymm
      · calc
          |p x - q x| <= Finset.sum Finset.univ (fun i => |p i - q i|) :=
            Finset.single_le_sum (fun i _ => abs_nonneg (p i - q i)) (Finset.mem_univ x)
          _ = 0 := hsum
      · exact abs_nonneg (p x - q x)
    rw [abs_eq_zero] at hterm
    exact sub_eq_zero.mp hterm
  · intro h
    rw [h, vectorTV_self]

namespace Dist

/-- Total variation on semantic exact finite distributions. -/
def tv {alpha : Type*} [Fintype alpha] (p q : Dist alpha) : Rat :=
  vectorTV (mass p) (mass q)

@[simp]
theorem tv_self {alpha : Type*} [Fintype alpha] (p : Dist alpha) :
    tv p p = 0 := by
  simp [tv]

theorem tv_comm {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q = tv q p := by
  exact vectorTV_comm _ _

theorem tv_nonneg {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    0 <= tv p q := by
  exact vectorTV_nonneg _ _

theorem tv_triangle {alpha : Type*} [Fintype alpha] (p q r : Dist alpha) :
    tv p r <= tv p q + tv q r := by
  simpa [tv] using vectorTV_triangle _ _ _

/-- Zero TV distance is exactly pointwise equality of the mass functions.
(Mass level: for `StdSimplex` this already determines the distribution
itself — see `tv_zero_iff_eq`. Equal mass functions give equal `Finsupp`
weights, and the two proof fields are proof-irrelevant.) -/
theorem tv_eq_zero {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q = 0 ↔ ∀ x, mass p x = mass q x := by
  simp only [tv]
  rw [vectorTV_eq_zero]
  exact ⟨fun h => fun x => congrFun h x, fun h => funext h⟩

/-- Total variation separates points: `tv p q = 0` iff `p = q`. The
`StdSimplex` structure is determined by its `Finsupp` weight field (the
`nonneg`/`total` proof fields are proof-irrelevant), so pointwise equality
of the mass functions determines the distribution. This is the metric
separation fact the mass-level `tv_eq_zero` stops short of. -/
theorem tv_zero_iff_eq {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q = 0 ↔ p = q := by
  constructor
  · intro h
    rw [tv_eq_zero] at h
    ext x
    simpa [mass] using h x
  · intro h
    rw [h]
    exact tv_self _

/-- Fubini for two finite univ-sums with one factor depending only on the
second index: `\sum_i \sum_j a_j b_{i j} = \sum_j a_j \sum_i b_{i j}`.
Used for all mass-exchange arguments in the contraction proofs. -/
theorem double_sum_pullout {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (a : beta → Rat) (b : alpha → beta → Rat) :
    (∑ i, ∑ j, a j * b i j) = ∑ j, a j * ∑ i, b i j := by
  classical
  have : (∑ i ∈ (Finset.univ : Finset alpha), ∑ j ∈ (Finset.univ : Finset beta), a j * b i j) =
        ∑ j ∈ (Finset.univ : Finset beta), a j * ∑ i ∈ (Finset.univ : Finset alpha), b i j := by
    classical
    induction (Finset.univ : Finset alpha) using Finset.induction with
    | empty => simp
    | insert c t hc ih =>
      rw [Finset.sum_insert hc]
      rw [ih]
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl fun j _ =>
          (mul_add (a j) (b c j) (Finset.sum t (fun i => b i j))).symm]
      rw [Finset.sum_congr rfl fun j _ =>
          congrArg (fun u => a j * u) (Finset.sum_insert hc (f := fun i => b i j)).symm]
  simpa using this

/-! ## 4. Batch 2 (e) — the generic same-source coupling inequality -/

/-- The nonnegative triangle-inequality form for {0,1} indicators:
    `|ind(a = x) − ind(b = x)| ≤ ind(a = x) + ind(b = x)`. -/
theorem boole_diff_abs_le_sum {X : Type*} [DecidableEq X] (a b x : X) :
    |(if a = x then (1 : Rat) else 0) - (if b = x then 1 else 0)| ≤
      (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
  split_ifs <;> norm_num

/-- The mismatch factor: multiplying the pointwise difference of the two
    singleton indicators by `(if F w = G w then 0 else mass ρ w)` leaves it
    unchanged — matched weights already contribute `0` everywhere. -/
theorem mismatch_mass_mul_boole_diff {Ω X : Type*}
    [Fintype Ω] [Fintype X] [DecidableEq X] (ρ : Dist Ω)
    (F G : Ω → X) (w : Ω) (x : X) :
    (if F w = G w then (0 : Rat) else mass ρ w) *
        ((if F w = x then 1 else 0) - (if G w = x then 1 else 0)) =
      mass ρ w * ((if F w = x then 1 else 0) - (if G w = x then 1 else 0)) := by
  by_cases h : F w = G w
  · by_cases h2 : F w = x
    · by_cases h3 : G w = x
      · simp [h, h3]
      · simp [h, h3]
    · by_cases h3 : G w = x
      · simp [h, h3]
      · simp [h, h3]
  · simp [h]

/- **Key fact (e)** — the generic same-source coupling inequality: the TV of
   two pushforwards from one source is at most the source-mass of the set on
   which the two maps disagree. (L1 proof: per-target fiber sums, mismatch
   factor, `abs_sub_le` + nonnegative triangle form, Fubini, `1/2` cancels
   against the two singleton indicators.) -/
theorem tv_maps_le_mismatch {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (ρ : Dist Ω) (F G : Ω → X) :
    tv (ρ.map F) (ρ.map G) ≤
      (Finset.univ : Finset Ω).sum
        (fun w => (if F w = G w then (0 : Rat) else mass ρ w)) := by
  let C (w : Ω) : Rat := (if F w = G w then (0 : Rat) else mass ρ w)
  let Bf (w : Ω) (x : X) : Rat := (if F w = x then (1 : Rat) else 0)
  let Bg (w : Ω) (x : X) : Rat := (if G w = x then (1 : Rat) else 0)
  -- (1) Pointwise fiber forms of the pushforward masses, indicator style.
  have hμ (x : X) :
      mass (ρ.map F) x =
        (Finset.univ : Finset Ω).sum (fun w => mass ρ w * Bf w x) := by
    rw [map_mass_eq_univ_fiber ρ F x]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [Bf]
    by_cases h : F w = x
    · simp [h]
    · simp [h]
  have hν (x : X) :
      mass (ρ.map G) x =
        (Finset.univ : Finset Ω).sum (fun w => mass ρ w * Bg w x) := by
    rw [map_mass_eq_univ_fiber ρ G x]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [Bg]
    by_cases h : G w = x
    · simp [h]
    · simp [h]
  -- (2) The pointwise difference, with the mismatch factor pulled in.
  have hdiff (x : X) :
      mass (ρ.map F) x - mass (ρ.map G) x =
        (Finset.univ : Finset Ω).sum (fun w => C w * (Bf w x - Bg w x)) := by
    have hsub : mass (ρ.map F) x - mass (ρ.map G) x =
        (Finset.univ : Finset Ω).sum (fun w => mass ρ w * (Bf w x - Bg w x)) := by
      rw [hμ x, hν x, sub_eq_add_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    rw [hsub]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [Bf, Bg, C]
    exact (mismatch_mass_mul_boole_diff ρ F G w x).symm
  -- (3) Pointwise: |C w · (Bf − Bg)| ≤ C w · (Bf + Bg) for C w ≥ 0.
  have hterm (x : X) (w : Ω) :
      |C w * (Bf w x - Bg w x)| ≤ C w * (Bf w x + Bg w x) := by
    dsimp only [Bf, Bg, C]
    by_cases hmg : F w = G w
    · simp [hmg, mul_zero, abs_zero]
    · have hnn : 0 ≤ mass ρ w := mass_nonneg ρ w
      simp [hmg]
      by_cases h1 : F w = x
      · by_cases h2 : G w = x
        · simp [h1, h2, mul_zero]
        · simp [h1, h2, mul_one]
          rw [abs_of_nonneg hnn]
      · by_cases h2 : G w = x
        · simp [h1, h2, mul_one]
          rw [abs_of_nonneg hnn]
        · simp [h1, h2, mul_zero, abs_zero]
  -- (4) Pointwise: |μ x − ν x| ≤ ∑_w C w · (Bf w x + Bg w x).
  have hpt (x : X) :
      |mass (ρ.map F) x - mass (ρ.map G) x| ≤
        (Finset.univ : Finset Ω).sum (fun w => C w * (Bf w x + Bg w x)) := by
    calc
      _ = |(Finset.univ : Finset Ω).sum (fun w => C w * (Bf w x - Bg w x))| := by
        rw [hdiff x]
      _ ≤ (Finset.univ : Finset Ω).sum (fun w => |C w * (Bf w x - Bg w x)|) :=
        Finset.abs_sum_le_sum_abs (fun w => C w * (Bf w x - Bg w x))
          (Finset.univ : Finset Ω)
      _ ≤ (Finset.univ : Finset Ω).sum (fun w => C w * (Bf w x + Bg w x)) := by
        exact Finset.sum_le_sum (fun w _ => hterm x w)
  -- (5) The inner X-sum: ∑_x C w · (Bf + Bg) = 2 · C w.
  have hinner (w : Ω) :
      (Finset.univ : Finset X).sum (fun x => C w * (Bf w x + Bg w x)) =
        2 * C w := by
    rw [show (Finset.univ : Finset X).sum (fun x => C w * (Bf w x + Bg w x)) =
        (Finset.univ : Finset X).sum (fun x => C w * Bf w x + C w * Bg w x) from by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_add]]
    rw [Finset.sum_add_distrib]
    have hF : (Finset.univ : Finset X).sum (fun x => C w * Bf w x) = C w := by
      rw [show (Finset.univ : Finset X).sum (fun x => C w * Bf w x) =
          (Finset.univ : Finset X).sum (fun x => (if F w = x then C w else 0)) from by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [Bf]
        by_cases h : F w = x
        · simp [h, mul_one]
        · simp [h, mul_zero]]
      rw [Finset.sum_ite_eq (Finset.univ : Finset X) (F w) (fun _ => C w),
        ite_eq_left (Finset.mem_univ _)]
    have hG : (Finset.univ : Finset X).sum (fun x => C w * Bg w x) = C w := by
      rw [show (Finset.univ : Finset X).sum (fun x => C w * Bg w x) =
          (Finset.univ : Finset X).sum (fun x => (if G w = x then C w else 0)) from by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [Bg]
        by_cases h : G w = x
        · simp [h, mul_one]
        · simp [h, mul_zero]]
      rw [Finset.sum_ite_eq (Finset.univ : Finset X) (G w) (fun _ => C w),
        ite_eq_left (Finset.mem_univ _)]
    rw [hF, hG]
    ring
  -- (5b) The same with the factor pulled outside: C w · ∑_x (Bf + Bg) = 2·C w
  --     (no distribution needed: the inner sum is the constant 2).
  have hinner2 (w : Ω) :
      C w * ((Finset.univ : Finset X).sum (fun x => Bf w x + Bg w x)) =
        2 * C w := by
    have hB : (Finset.univ : Finset X).sum (fun x => Bf w x + Bg w x) = 2 := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq (Finset.univ : Finset X) (F w) (fun _ => (1 : Rat)),
        Finset.sum_ite_eq (Finset.univ : Finset X) (G w) (fun _ => (1 : Rat)),
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]
      norm_num
    rw [hB, mul_comm]
  -- (6) Sum over X, multiply by 1/2, Fubini, and close.
  calc
    tv (ρ.map F) (ρ.map G) =
        (1 / 2 : Rat) *
          (Finset.univ : Finset X).sum
            (fun x => |mass (ρ.map F) x - mass (ρ.map G) x|) := by
      simp only [tv, vectorTV]
    _ ≤ (1 / 2 : Rat) * (Finset.univ : Finset Ω).sum (fun w => 2 * C w) := by
      apply mul_le_mul_of_nonneg_left
      · trans (Finset.univ : Finset X).sum
          (fun x => (Finset.univ : Finset Ω).sum (fun w => C w * (Bf w x + Bg w x)))
        · exact Finset.sum_le_sum (fun x _ => hpt x)
        · rw [double_sum_pullout (fun w => C w) (fun x w => Bf w x + Bg w x)]
          exact Finset.sum_le_sum (fun w _ => by rw [hinner2 w])
      · norm_num
    _ = (1 / 2 : Rat) *
        ((Finset.univ : Finset Ω).sum (fun w => C w) +
          (Finset.univ : Finset Ω).sum (fun w => C w)) := by
      rw [show (Finset.univ : Finset Ω).sum (fun w => 2 * C w) =
        (Finset.univ : Finset Ω).sum (fun w => C w + C w) from by
        apply Finset.sum_congr rfl
        intro w _
        ring]
      rw [Finset.sum_add_distrib]
    _ = (Finset.univ : Finset Ω).sum (fun w => C w) := by ring
    _ = (Finset.univ : Finset Ω).sum
          (fun w => (if F w = G w then (0 : Rat) else mass ρ w)) := by
      dsimp only [C]

/-- Pushforward by a deterministic map is a TV non-expansion: applying the same
map `f` to two laws cannot increase their total variation.  This is the
contraction step of the Gate 6 batch 3 one-round local-error bound. -/
theorem tv_map_contraction {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (μ ν : Dist Ω) (f : Ω → X) : Dist.tv (μ.map f) (ν.map f) ≤ Dist.tv μ ν := by
  unfold Dist.tv vectorTV
  let Fμ (w : Ω) (x : X) : Rat := if f w = x then Dist.mass μ w else 0
  let Fν (w : Ω) (x : X) : Rat := if f w = x then Dist.mass ν w else 0
  let Δ (w : Ω) : Rat := Dist.mass μ w - Dist.mass ν w
  have hμ (x : X) : Dist.mass (μ.map f) x = (Finset.univ : Finset Ω).sum (fun w => Fμ w x) := by
    simpa [Fμ] using Dist.map_mass_eq_univ_fiber μ f x
  have hν (x : X) : Dist.mass (ν.map f) x = (Finset.univ : Finset Ω).sum (fun w => Fν w x) := by
    simpa [Fν] using Dist.map_mass_eq_univ_fiber ν f x
  have hsub (x : X) :
      (Finset.univ : Finset Ω).sum (fun w => Fμ w x) - (Finset.univ : Finset Ω).sum (fun w => Fν w x) =
        (Finset.univ : Finset Ω).sum (fun w => Fμ w x - Fν w x) := by
    rw [Finset.sum_sub_distrib]
  have habs (w : Ω) (x : X) : |Fμ w x - Fν w x| = (if f w = x then |Δ w| else 0) := by
    dsimp only [Fμ, Fν, Δ]
    by_cases hf : f w = x
    · simp [hf]
    · simp [hf]
  calc
    _ = (1 / 2 : Rat) * (∑ x : X, |(∑ w : Ω, Fμ w x) - (∑ w : Ω, Fν w x)|) := by
      congr 1
      apply Finset.sum_congr rfl; intro x _
      rw [hμ x, hν x]
    _ = (1 / 2 : Rat) * (∑ x : X, |(Finset.univ : Finset Ω).sum (fun w => Fμ w x - Fν w x)|) := by
      congr 1
      apply Finset.sum_congr rfl; intro x _
      rw [hsub x]
    _ ≤ (1 / 2 : Rat) * (∑ x : X, (Finset.univ : Finset Ω).sum (fun w => |Fμ w x - Fν w x|)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum; intro x _
        exact Finset.abs_sum_le_sum_abs (fun w => Fμ w x - Fν w x) Finset.univ
      · norm_num
    _ = (1 / 2 : Rat) * (∑ x : X, (Finset.univ : Finset Ω).sum (fun w => (if f w = x then |Δ w| else 0))) := by
      congr 1
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro w _
      exact habs w x
    _ = (1 / 2 : Rat) * (∑ w : Ω, (Finset.univ : Finset X).sum (fun x => (if f w = x then |Δ w| else 0))) := by
      congr 1
      rw [Finset.sum_comm]
    _ = (1 / 2 : Rat) * (∑ w : Ω, (if f w = f w then |Δ w| else 0)) := by
      congr 1
      apply Finset.sum_congr rfl; intro w _
      calc
        _ = (Finset.univ : Finset X).sum (fun x => (if x = f w then |Δ w| else 0)) := by
          apply Finset.sum_congr rfl; intro x _
          by_cases h : f w = x
          · simp [h]
          · have hn : ¬(x = f w) := fun h' => h (h'.symm)
            simp [h, hn]
        _ = (if f w ∈ (Finset.univ : Finset X) then |Δ w| else 0) := by
          simpa using Finset.sum_ite_eq' (Finset.univ : Finset X) (f w) (fun _ => |Δ w|)
        _ = (if f w = f w then |Δ w| else 0) := by simp
    _ = (1 / 2 : Rat) * (∑ w : Ω, |Δ w|) := by
      congr 1
      apply Finset.sum_congr rfl; intro w _
      simp
    _ = Dist.tv μ ν := by
      simp [Dist.tv, vectorTV, Dist.mass, Δ]

/-- Total variation contracts under kernel application: pushing two distributions
through the same (row-stochastic) kernel cannot increase their TV distance.
`TV(Kμ, Kν) ≤ TV(μ, ν)`. Proof: pointwise triangle inequality in the weighted
form `|∑_j a_j w_j| ≤ ∑_j |a_j| w_j` for nonnegative weights, then Fubini
(double_sum_pullout) and the row-stochasticity `∑_i K(j, i) = 1`. -/
theorem kernel_contraction {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (K : FiniteKernel alpha beta) (mu nu : Dist alpha) :
    tv (FiniteKernel.apply mu K) (FiniteKernel.apply nu K) ≤ tv mu nu := by
  simp only [tv, vectorTV, FiniteKernel.apply_mass]
  have hdiff : ∀ (i : beta), (∑ j, mass mu j * mass (K j) i) -
      (∑ j, mass nu j * mass (K j) i) =
      ∑ j, (mass mu j - mass nu j) * mass (K j) i := by
    intro i
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl fun i _ => congrArg abs (hdiff i)]
  have hpointwise : ∀ (i : beta),
      |∑ j, (mass mu j - mass nu j) * mass (K j) i| ≤
      ∑ j, |mass mu j - mass nu j| * mass (K j) i := by
    intro i
    calc
      _ ≤ ∑ j, |((mass mu j - mass nu j) * mass (K j) i)| :=
          Finset.abs_sum_le_sum_abs
            (fun j => (mass mu j - mass nu j) * mass (K j) i) Finset.univ
      _ = ∑ j, |mass mu j - mass nu j| * mass (K j) i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (mass_nonneg (K j) i)]
  calc
    (1 / 2 : Rat) * ∑ i, |∑ j, (mass mu j - mass nu j) * mass (K j) i| ≤
        (1 / 2 : Rat) * ∑ i, ∑ j, |mass mu j - mass nu j| * mass (K j) i := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i _
        exact hpointwise i
      · norm_num
    _ = (1 / 2 : Rat) * ∑ j, |mass mu j - mass nu j| * ∑ i, mass (K j) i := by
      apply congrArg _
      rw [double_sum_pullout (fun j => |mass mu j - mass nu j|)
          (fun i j => mass (K j) i)]
    _ = (1 / 2 : Rat) * ∑ j, |mass mu j - mass nu j| * 1 := by
      apply congrArg _
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_mass]
    _ = (1 / 2 : Rat) * ∑ j, |mass mu j - mass nu j| := by
      apply congrArg _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_one]

theorem tv_le_one {alpha : Type*} [Fintype alpha] (p q : Dist alpha) :
    tv p q <= 1 := by
  apply vectorTV_le_one_of_probability
  · exact mass_nonneg p
  · exact mass_nonneg q
  · exact sum_mass p
  · exact sum_mass q

/-- **Overlap identity.** For two exact finite probability laws `P`, `Q`
(total mass `1` each, by `sum_mass`), the TV distance equals one minus their
pointwise-overlap mass:
`tv P Q = 1 - ∑ x, min (mass P x) (mass Q x)`.
This is the standard `TV = 1 − overlap` fact, and it underlies the Dobrushin
coefficient bound `dobrushinCoeff K ≤ 1 − min_x mass (K x) z` (one term of the
overlap sum dominates at any fixed state `z`). -/
theorem tv_eq_one_sub_overlap {α : Type*} [Fintype α] (P Q : Dist α) :
    tv P Q = 1 - (Finset.univ : Finset α).sum (fun x => min (mass P x) (mass Q x)) := by
  rw [tv]
  have hsumP : (Finset.univ : Finset α).sum (fun x => mass P x) = 1 := sum_mass P
  have hsumQ : (Finset.univ : Finset α).sum (fun x => mass Q x) = 1 := sum_mass Q
  have hper : ∀ x : α, min (mass P x) (mass Q x) + (1 / 2 : Rat) * |mass P x - mass Q x| =
      (1 / 2 : Rat) * (mass P x + mass Q x) := by
    intro x
    by_cases h : mass P x ≤ mass Q x
    · have habs : |mass P x - mass Q x| = mass Q x - mass P x := by
        rw [← neg_sub, abs_neg, abs_of_nonneg (sub_nonneg.mpr h)]
      rw [min_eq_left h, habs]
      ring
    · have habs : |mass P x - mass Q x| = mass P x - mass Q x := by
        exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt (not_le.mp h)))
      rw [min_eq_right (le_of_lt (not_le.mp h)), habs]
      ring
  set Smin := (Finset.univ : Finset α).sum (fun x => min (mass P x) (mass Q x))
  set Sabs := (Finset.univ : Finset α).sum (fun x => |mass P x - mass Q x|)
  have hsum : Smin + (1 / 2 : Rat) * Sabs = 1 := by
    calc
      _ = (Finset.univ : Finset α).sum (fun x => min (mass P x) (mass Q x) +
          (1 / 2 : Rat) * |mass P x - mass Q x|) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (Finset.univ : Finset α).sum (fun x => (1 / 2 : Rat) * (mass P x + mass Q x)) :=
        Finset.sum_congr rfl (fun x _ => hper x)
      _ = (1 / 2 : Rat) * (Finset.univ : Finset α).sum (fun x => mass P x + mass Q x) := by
        rw [Finset.mul_sum]
      _ = (1 / 2 : Rat) * ((Finset.univ : Finset α).sum (fun x => mass P x) +
          (Finset.univ : Finset α).sum (fun x => mass Q x)) := by
        rw [Finset.sum_add_distrib]
      _ = (1 / 2 : Rat) * (1 + 1) := by rw [hsumP, hsumQ]
      _ = 1 := by ring
  rw [vectorTV]
  have hhalf : (1 / 2 : Rat) * Sabs = 1 - Smin := by linarith
  exact hhalf

/-- TV of a point mass against a law is one minus the law's mass at the point. -/
theorem tv_pointMass {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (x : alpha) (nu : Dist alpha) :
    tv (Dist.pointMass x) nu = 1 - mass nu x := by
  rw [tv_eq_one_sub_overlap]
  rw [Finset.sum_eq_single x]
  · simp only [mass_pointMass, ite_true]
    have hle : mass nu x ≤ 1 :=
      (Finset.single_le_sum (s := Finset.univ) (fun m _ => mass_nonneg nu m) (Finset.mem_univ x)).trans_eq
        (sum_mass nu)
    rw [min_eq_right hle]
  · intro y _ hy
    simp only [mass_pointMass]
    rw [ite_eq_right hy, min_eq_left (mass_nonneg nu y)]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end Dist

section PositiveSet

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The set of coordinates where `p` strictly exceeds `q`. -/
def positiveSet (p q : alpha -> Rat) : Finset alpha :=
  (Finset.univ : Finset alpha).filter (fun x => p x > q x)

/-- Total mass by which `p` exceeds `q`, counted only at the coordinates
where it is larger. For probability vectors this equals the TV distance
(vectorTV_eq_positive_set) and upper-bounds `\sum_S (p - q)` for every
`S` (vectorTV_sum_le_positive_set). -/
def positiveSum (p q : alpha -> Rat) : Rat :=
  Finset.sum (positiveSet p q) (fun x => p x - q x)

/-- Pointwise: the positive parts of `a - b` and `b - a` add to `|a - b|`
and differ by `a - b`. -/
theorem maxDiffAbs {a b : Rat} :
    max 0 (a - b) + max 0 (b - a) = |a - b| := by
  cases le_total a b with
  | inl h =>
    have h1 : max 0 (a - b) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    have h2 : max 0 (b - a) = b - a := by
      exact max_eq_right (sub_nonneg_of_le h)
    rw [h1, h2]
    simpa only [zero_add, abs_sub_comm] using (abs_of_nonneg (sub_nonneg_of_le h)).symm
  | inr h =>
    have h1 : max 0 (a - b) = a - b := by
      exact max_eq_right (sub_nonneg_of_le h)
    have h2 : max 0 (b - a) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    rw [h1, h2]
    simpa only [add_zero] using (abs_of_nonneg (sub_nonneg_of_le h)).symm

theorem maxDiffSub {a b : Rat} :
    max 0 (a - b) - max 0 (b - a) = a - b := by
  cases le_total a b with
  | inl h =>
    have h1 : max 0 (a - b) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    have h2 : max 0 (b - a) = b - a := by
      exact max_eq_right (sub_nonneg_of_le h)
    rw [h1, h2]
    simpa only [zero_sub] using neg_sub b a
  | inr h =>
    have h1 : max 0 (a - b) = a - b := by
      exact max_eq_right (sub_nonneg_of_le h)
    have h2 : max 0 (b - a) = 0 := by
      exact max_eq_left (sub_nonpos_of_le h)
    rw [h1, h2]
    simp only [sub_zero]

/-- The univ-sum of the positive part of `p - q` is exactly the positive
sum: off the positive set the positive part vanishes, and on it it is
`p - q` itself. (Probability hypotheses are only used to state the result
in TV-friendly form; the identity itself is pointwise. -/
theorem sumPosPartEqPositiveSum
    (p q : alpha -> Rat) :
    Finset.sum Finset.univ (fun x => max 0 (p x - q x)) = positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  have hzero : forall x, x ∈ Finset.univ \ positiveSet p q -> u x = 0 := by
    intro x hx
    have hnot : ¬ p x > q x := by
      have hnot2 : x ∉ positiveSet p q := (Finset.mem_sdiff.mp hx).2
      intro hpos
      have hm : x ∈ positiveSet p q := by
        rw [positiveSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hpos⟩
      exact hnot2 hm
    have hle : p x <= q x := by
      exact not_lt.mp hnot
    change max 0 (p x - q x) = 0
    exact max_eq_left (sub_nonpos_of_le hle)
  have hzero2 : Finset.sum (Finset.univ \ positiveSet p q) u = 0 := by
    rw [Finset.sum_congr rfl (fun x hx => hzero x hx)]
    rw [Finset.sum_const_zero]
  rw [← Finset.sum_sdiff (Finset.subset_univ (positiveSet p q)), hzero2, zero_add,
      positiveSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hpos : p x > q x := by
    rw [positiveSet, Finset.mem_filter] at hx
    exact hx.2
  change max 0 (p x - q x) = p x - q x
  exact max_eq_right (le_of_lt (sub_pos_of_lt hpos))

/-- For probability vectors, the TV distance equals the excess mass of `p`
over `q` on the positive set (equivalently, the maximum of
`\sum_S (p - q)` over all `S`, attained at the positive set).

Proof: with `u x = max 0 (p x - q x)` and
`v x = max 0 (q x - p x)`, pointwise `|p x - q x| = u x + v x` and
`u x - v x = p x - q x`; since `\sum (p - q) = 0` the univ sums of `u` and
`v` coincide, so `\sum |p - q| = 2 * \sum u` and the factor `1 / 2` cancels.
-/
theorem vectorTV_eq_positive_set
    (p q : alpha -> Rat)
    (_hp : forall x, 0 <= p x) (_hq : forall x, 0 <= q x)
    (hp1 : Finset.sum Finset.univ p = 1) (hq1 : Finset.sum Finset.univ q = 1) :
    vectorTV p q = positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  let v := fun x => max 0 (q x - p x)
  have hterm : forall x, |p x - q x| = u x + v x := by
    intro x
    change |p x - q x| = max 0 (p x - q x) + max 0 (q x - p x)
    exact (maxDiffAbs (a := p x) (b := q x)).symm
  have hdiff : forall x, u x - v x = p x - q x := by
    intro x
    change max 0 (p x - q x) - max 0 (q x - p x) = p x - q x
    exact maxDiffSub (a := p x) (b := q x)
  have hsum0 : Finset.sum Finset.univ (fun x => u x - v x) = 0 := by
    rw [Finset.sum_congr rfl (fun x _ => hdiff x)]
    rw [Finset.sum_sub_distrib, hp1, hq1]
    norm_num
  have hsumuv : Finset.sum Finset.univ u = Finset.sum Finset.univ v := by
    rw [Finset.sum_sub_distrib] at hsum0
    exact sub_eq_zero.mp hsum0
  have hsumabs : Finset.sum Finset.univ (fun x => |p x - q x|) =
      2 * Finset.sum Finset.univ u := by
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    rw [Finset.sum_add_distrib]
    rw [hsumuv]
    ring
  unfold vectorTV
  rw [hsumabs]
  ring_nf
  exact sumPosPartEqPositiveSum p q

/-- For probability vectors, the signed mass `p - q` accumulated on any set
is at most the positive sum, i.e. at most the TV distance: this is the
max-event characterization `TV(p, q) = sup {\sum_S (p - q) | S}` with the
supremum attained at the positive set. (The inequality actually holds for
arbitrary `p q`; the probability hypotheses are kept so the statement
reads as the TV statement.) -/
theorem vectorTV_sum_le_positive_set
    (p q : alpha -> Rat)
    (_hp : forall x, 0 <= p x) (_hq : forall x, 0 <= q x)
    (_hp1 : Finset.sum Finset.univ p = 1) (_hq1 : Finset.sum Finset.univ q = 1)
    (S : Finset alpha) :
    Finset.sum S (fun x => p x - q x) <= positiveSum p q := by
  let u := fun x => max 0 (p x - q x)
  let v := fun x => max 0 (q x - p x)
  have hdiff : forall x, u x - v x = p x - q x := by
    intro x
    change max 0 (p x - q x) - max 0 (q x - p x) = p x - q x
    exact maxDiffSub (a := p x) (b := q x)
  have hsumu : Finset.sum Finset.univ u = positiveSum p q :=
    sumPosPartEqPositiveSum p q
  have hvn : 0 <= Finset.sum S v :=
    Finset.sum_nonneg fun _ _ => le_max_left 0 _
  -- Embed the `S`-sum as a `univ`-sum of an ite: the resulting fold is
  -- over `univ` (cheap) rather than over `univ \ S` (its sdiff fold
  -- whnfs badly in the kernel while `S` is a variable, and times out
  -- even with a raised heartbeat).
  have hite : Finset.sum S u = Finset.sum Finset.univ (fun x => if x ∈ S then u x else 0) := by
    simp
  have hpt : forall x, (if x ∈ S then u x else 0) <= u x := by
    intro x
    split_ifs with hx
    · exact le_rfl
    · change 0 <= max 0 (p x - q x)
      exact le_max_left 0 (p x - q x)
  calc
    Finset.sum S (fun x => p x - q x) = Finset.sum S u - Finset.sum S v := by
      have h1 : Finset.sum S (fun x => p x - q x) =
          Finset.sum S (fun x => u x - v x) :=
        Finset.sum_congr rfl fun x _ => (hdiff x).symm
      have h2 : Finset.sum S (fun x => u x - v x) =
          Finset.sum S u - Finset.sum S v :=
        Finset.sum_sub_distrib (fun x => u x) (fun x => v x)
      exact Eq.trans h1 h2
    _ <= Finset.sum S u :=
      sub_le_self _ hvn
    _ = Finset.sum Finset.univ (fun x => if x ∈ S then u x else 0) :=
      hite
    _ <= Finset.sum Finset.univ u :=
      Finset.sum_le_sum fun x _ => hpt x
    _ = positiveSum p q :=
      hsumu

end PositiveSet

namespace MatrixTV

variable {alpha : Type*}

/-- TV distance between two rows of a rational transition matrix.
Compatibility view on fixed-size matrices; the canonical (semantic)
kernel version is `Dobrushin.rowTV`, with `dobrushinCoeff_matrix_link`
bridging the two for row-stochastic matrices. -/
def rowTV [Fintype alpha] (P : Matrix alpha alpha Rat) (i j : alpha) : Rat :=
  vectorTV (P i) (P j)

/-- The finite set of all pairwise row distances.
Compatibility view (canonical kernel version: `Dobrushin.pairDistances`). -/
def pairDistances [Fintype alpha] [DecidableEq alpha]
    (P : Matrix alpha alpha Rat) : Finset Rat :=
  ((Finset.univ : Finset alpha).product Finset.univ).image
    (fun ij => rowTV P ij.1 ij.2)

theorem pairDistances_nonempty
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) : (pairDistances P).Nonempty := by
  classical
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  exact ⟨rowTV P x x, by simp [pairDistances, x]⟩

/-- Exact finite Dobrushin coefficient: maximum TV distance between matrix
rows. Compatibility view (canonical kernel version: `Dobrushin.dobrushinCoeff`;
equality via `dobrushinCoeff_matrix_link`). -/
def dobrushinCoeff
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) : Rat :=
  (pairDistances P).max' (pairDistances_nonempty P)

theorem rowTV_le_dobrushin
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) (i j : alpha) :
    rowTV P i j <= dobrushinCoeff P := by
  unfold dobrushinCoeff
  apply Finset.le_max'
  simp [pairDistances]

@[simp]
theorem dobrushinCoeff_nonneg
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat) :
    0 <= dobrushinCoeff P := by
  let x : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have h := rowTV_le_dobrushin P x x
  simpa [rowTV] using h

/-- A row-stochastic rational matrix has Dobrushin coefficient at most one. -/
theorem dobrushinCoeff_le_one
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (P : Matrix alpha alpha Rat)
    (hP : P ∈ Matrix.rowStochastic Rat alpha) :
    dobrushinCoeff P <= 1 := by
  unfold dobrushinCoeff
  apply Finset.max'_le
  intro d hd
  rw [pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  apply vectorTV_le_one_of_probability
  · intro x
    exact Matrix.nonneg_of_mem_rowStochastic hP
  · intro x
    exact Matrix.nonneg_of_mem_rowStochastic hP
  · exact Matrix.sum_row_of_mem_rowStochastic hP ij.1
  · exact Matrix.sum_row_of_mem_rowStochastic hP ij.2

end MatrixTV
theorem distProduct_tv_subadditive
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    (μ μ' : Dist α) (ν ν' : Dist β) :
    Dist.tv (distProduct μ ν) (distProduct μ' ν') ≤
      Dist.tv μ μ' + Dist.tv ν ν' := by
  classical
  haveI : DecidableEq (α × β) := inferInstance
  have hν : (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν b) = 1 := by simp [Dist.sum_mass]
  have hν' : (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν' b) = 1 := by simp [Dist.sum_mass]
  have hμ' : (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ' a) = 1 := by simp [Dist.sum_mass]
  have hμnn : ∀ a, 0 ≤ Dist.mass μ a := fun _ => Dist.mass_nonneg μ _
  have hμ'n : ∀ a, 0 ≤ Dist.mass μ' a := fun _ => Dist.mass_nonneg μ' _
  have hνnn : ∀ b, 0 ≤ Dist.mass ν b := fun _ => Dist.mass_nonneg ν _
  have hUniv : (Finset.univ : Finset (α × β)) =
      (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β) := by
    ext p
    simp [Finset.mem_univ]
  have hterm : ∀ (a : α) (b : β),
      |Dist.mass μ a * Dist.mass ν b - Dist.mass μ' a * Dist.mass ν' b| ≤
        |Dist.mass μ a - Dist.mass μ' a| * Dist.mass ν b +
          Dist.mass μ' a * |Dist.mass ν b - Dist.mass ν' b| := by
    intro a b
    have hsplit : Dist.mass μ a * Dist.mass ν b - Dist.mass μ' a * Dist.mass ν' b =
        (Dist.mass μ a - Dist.mass μ' a) * Dist.mass ν b +
          Dist.mass μ' a * (Dist.mass ν b - Dist.mass ν' b) := by ring
    calc
      |Dist.mass μ a * Dist.mass ν b - Dist.mass μ' a * Dist.mass ν' b| =
          |(Dist.mass μ a - Dist.mass μ' a) * Dist.mass ν b +
             Dist.mass μ' a * (Dist.mass ν b - Dist.mass ν' b)| := by rw [hsplit]
      _ ≤ |(Dist.mass μ a - Dist.mass μ' a) * Dist.mass ν b| +
            |Dist.mass μ' a * (Dist.mass ν b - Dist.mass ν' b)| := by exact abs_add_le _ _
      _ = |Dist.mass μ a - Dist.mass μ' a| * Dist.mass ν b +
            Dist.mass μ' a * |Dist.mass ν b - Dist.mass ν' b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hνnn b), abs_of_nonneg (hμ'n a)]
  -- S1 = ∑_p |Δμ p.1| · ν p.2  =  ∑_a |Δμ a|
  have S1 : (∑ p ∈ (Finset.univ : Finset (α × β)), |Dist.mass μ p.1 - Dist.mass μ' p.1| * Dist.mass ν p.2) =
      (∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a|) := by
    calc
      (∑ p ∈ (Finset.univ : Finset (α × β)), |Dist.mass μ p.1 - Dist.mass μ' p.1| * Dist.mass ν p.2) =
        (∑ p ∈ (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β), |Dist.mass μ p.1 - Dist.mass μ' p.1| * Dist.mass ν p.2) := by rw [hUniv]
      _ = (∑ a ∈ (Finset.univ : Finset α), ∑ b ∈ (Finset.univ : Finset β), |Dist.mass μ a - Dist.mass μ' a| * Dist.mass ν b) := by rw [Finset.sum_product]
      _ = (∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a| * (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν b)) := by
        rw [Finset.sum_congr rfl (fun a _ => (Finset.mul_sum (Finset.univ) (fun b => Dist.mass ν b) (|Dist.mass μ a - Dist.mass μ' a|)).symm)]
      _ = (∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a| * 1) := by rw [hν]
      _ = (∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a|) := by
        rw [Finset.sum_congr rfl (fun a _ => mul_one (|Dist.mass μ a - Dist.mass μ' a|))]
  -- S2 = ∑_p μ' p.1 · |Δν p.2|  =  ∑_b |Δν b|
  have S2 : (∑ p ∈ (Finset.univ : Finset (α × β)), Dist.mass μ' p.1 * |Dist.mass ν p.2 - Dist.mass ν' p.2|) =
      (∑ b ∈ (Finset.univ : Finset β), |Dist.mass ν b - Dist.mass ν' b|) := by
    let C : Rat := (∑ b ∈ (Finset.univ : Finset β), |Dist.mass ν b - Dist.mass ν' b|)
    calc
      (∑ p ∈ (Finset.univ : Finset (α × β)), Dist.mass μ' p.1 * |Dist.mass ν p.2 - Dist.mass ν' p.2|) =
        (∑ p ∈ (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β), Dist.mass μ' p.1 * |Dist.mass ν p.2 - Dist.mass ν' p.2|) := by rw [hUniv]
      _ = (∑ a ∈ (Finset.univ : Finset α), ∑ b ∈ (Finset.univ : Finset β), Dist.mass μ' a * |Dist.mass ν b - Dist.mass ν' b|) := by rw [Finset.sum_product]
      _ = (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ' a * C) := by
        rw [Finset.sum_congr rfl (fun a _ => (Finset.mul_sum (Finset.univ) (fun b => |Dist.mass ν b - Dist.mass ν' b|) (Dist.mass μ' a)).symm)]
      _ = (∑ a ∈ (Finset.univ : Finset α), C * Dist.mass μ' a) := by
        rw [Finset.sum_congr rfl (fun a _ => by rw [mul_comm])]
      _ = C * (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ' a) := by
        rw [Finset.mul_sum]
      _ = C * 1 := by rw [hμ']
      _ = C := by rw [mul_one]
  -- main:  (1/2)∑_p |..|  ≤  (1/2)(∑_a |Δμ a| + ∑_b |Δν b|)  =  TV μ μ' + TV ν ν'
  have hA : (Finset.sum (Finset.univ : Finset (α × β)) (fun p =>
          |Dist.mass μ p.1 - Dist.mass μ' p.1| * Dist.mass ν p.2 +
            Dist.mass μ' p.1 * |Dist.mass ν p.2 - Dist.mass ν' p.2|)) =
      (∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a|) +
        (∑ b ∈ (Finset.univ : Finset β), |Dist.mass ν b - Dist.mass ν' b|) := by
    rw [Finset.sum_add_distrib, S1, S2]
  unfold Dist.tv
  simp only [vectorTV, distProduct_mass]
  calc
    (1 / 2 : Rat) * Finset.sum (Finset.univ : Finset (α × β))
        (fun p => |Dist.mass μ p.1 * Dist.mass ν p.2 - Dist.mass μ' p.1 * Dist.mass ν' p.2|) ≤
      (1 / 2 : Rat) * Finset.sum (Finset.univ : Finset (α × β))
        (fun p => |Dist.mass μ p.1 - Dist.mass μ' p.1| * Dist.mass ν p.2 +
          Dist.mass μ' p.1 * |Dist.mass ν p.2 - Dist.mass ν' p.2|) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hterm p.1 p.2))
      norm_num
    _ = (1 / 2 : Rat) *
        ((∑ a ∈ (Finset.univ : Finset α), |Dist.mass μ a - Dist.mass μ' a|) +
          (∑ b ∈ (Finset.univ : Finset β), |Dist.mass ν b - Dist.mass ν' b|)) := by
      rw [hA]
    _ = (1 / 2 : Rat) * (Finset.sum (Finset.univ : Finset α) (fun a => |Dist.mass μ a - Dist.mass μ' a|)) +
        (1 / 2 : Rat) * (Finset.sum (Finset.univ : Finset β) (fun b => |Dist.mass ν b - Dist.mass ν' b|)) := by
      ring
    _ = Dist.tv μ μ' + Dist.tv ν ν' := by
      simp [Dist.tv, vectorTV]


/-! ## F4.3: Fintype-free total variation on distribution supports

The `Dist.tv` above assumes a `Fintype` state space.  The F4.3 two-pile
`GSR` product kernel acts on `List (Fin n)`, which is **not** a `Fintype`,
so we work with the distribution's `Finsupp` weights and their finite
supports directly.  `tvFinsupp` is the same total-variation quantity,
summed over the finite union of the two supports instead of over
`Finset.univ`.  These lemmas are the Fintype-free analog of
`distProduct_tv_subadditive` and its components. -/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Fintype-free total variation: half the `L1` distance of two
distribution mass functions, summed over the (finite) union of their
supports.  Coincides with `Dist.tv` when the state space is a `Fintype`. -/
def tvFinsupp {γ : Type*} [DecidableEq γ] (p q : Dist γ) : Rat :=
  (1 / 2 : Rat) * (p.weights.support ∪ q.weights.support).sum
      (fun x => |p.weights x - q.weights x|)

/-- Summing over `Finset.univ` equals summing over `S` whenever the function
vanishes on `univ \ S`.  Modeled on `sumOverEnlarged_eq_one`. -/
theorem sum_univ_eq_zero_outside_support [Fintype α] (S : Finset α) (f : α → Rat)
    (h : ∀ x ∉ S, f x = 0) : (Finset.univ : Finset α).sum f = S.sum f := by
  have hite : (Finset.univ : Finset α).sum f =
      (Finset.univ : Finset α).sum (fun x => if x ∈ S then f x else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S
    · simp [hx]
    · simpa [hx] using h x hx
  rw [hite, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ : Finset α).filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ]
    tauto
  rw [hfilter]

/-- Fintype↔Finsupp TV bridge: on a `Fintype` state space the `Finsupp`-level
`tvFinsupp` coincides with `Dist.tv` — the `Finset.univ` sum equals the sum
over the union of the two supports, because the mass difference is `0` at
every point outside that union.  This is what lets the Fintype per-pile GSR
bound feed the Fintype-free product machinery in Gate 6 batch 3. -/
theorem tv_eq_tvFinsupp [Fintype α] (p q : Dist α) : Dist.tv p q = tvFinsupp p q := by
  unfold Dist.tv tvFinsupp vectorTV Dist.mass
  let S : Finset α := p.weights.support ∪ q.weights.support
  have hzero (x) (h : x ∉ S) : |p.weights x - q.weights x| = 0 := by
    have hno : x ∉ p.weights.support ∧ x ∉ q.weights.support := by simpa [S] using h
    have hp0 : p.weights x = 0 := by by_contra hne; exact hno.1 (Finsupp.mem_support_iff.mpr hne)
    have hq0 : q.weights x = 0 := by by_contra hne; exact hno.2 (Finsupp.mem_support_iff.mpr hne)
    simp [hp0, hq0]
  have hcore : (Finset.univ : Finset α).sum (fun x => |p.weights x - q.weights x|) =
      S.sum (fun x => |p.weights x - q.weights x|) :=
    sum_univ_eq_zero_outside_support S (fun x => |p.weights x - q.weights x|) (by simpa using hzero)
  rw [hcore]

/-- The support of the Fintype-free product `distProductFinsupp μ ν` is the
Cartesian product of the factor supports.  This is the Fintype-free
replacement for the `Finset.univ`-over-`α × β` bookkeeping used in the
Fintype subadditivity proof. -/
theorem suppDistProductFinsupp (μ : Dist α) (ν : Dist β) :
    (distProductFinsupp μ ν).weights.support = μ.weights.support ×ˢ ν.weights.support := by
  ext z
  simp only [Finsupp.mem_support_iff, Finset.mem_product]
  have hz : (distProductFinsupp μ ν).weights z = μ.weights z.1 * ν.weights z.2 :=
    distProductFinsupp_mass μ ν z.1 z.2
  rw [hz, mul_ne_zero_iff]

/-- Twice the Fintype-free total variation is exactly the (un-halved)
`L1` distance summed over the union of the two supports. -/
theorem twoTv_eq_unionSum {γ : Type*} [DecidableEq γ] (p q : Dist γ) :
    (2 : Rat) * tvFinsupp p q =
        (p.weights.support ∪ q.weights.support).sum (fun x => |p.weights x - q.weights x|) := by
  simp [tvFinsupp]

/-- A point outside a distribution's support carries zero mass. -/
theorem not_mem_support_zero {γ : Type*} [DecidableEq γ] (μ : Dist γ) (w : γ)
    (h : w ∉ μ.weights.support) : μ.weights w = 0 := by
  by_contra hne
  exact h (Finsupp.mem_support_iff.mpr hne)

/-- Summing a distribution's mass over any set that contains its support
gives total mass `1`.  Needed because the Fintype-free subadditivity sums
over the enlarged set `supp μ ∪ supp μ'` rather than over the exact
support. -/
theorem sumOverEnlarged_eq_one {γ : Type*} [DecidableEq γ] (ν : Dist γ) (B : Finset γ)
    (hB : ν.weights.support ⊆ B) : B.sum (fun b => ν.weights b) = 1 := by
  have hzero_out {b} (h : b ∉ ν.weights.support) : ν.weights b = 0 := by
    by_contra hne
    exact h (Finsupp.mem_support_iff.mpr hne)
  have hite : B.sum (fun b => ν.weights b) =
      B.sum (fun b => if b ∈ ν.weights.support then ν.weights b else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ ν.weights.support
    · simp [hb]
    · simp [hb, hzero_out hb]
  rw [hite, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : B.filter (fun b => b ∈ ν.weights.support) = ν.weights.support := by
    ext x
    constructor
    · intro h; simp only [Finset.mem_filter] at h; exact h.2
    · intro h; simp only [Finset.mem_filter]; exact ⟨hB h, h⟩
  rw [hfilter]
  change ν.weights.sum (fun _ r => r) = 1
  exact ν.total

/-- Pointwise subadditivity for a product of two nonnegative factors: the
`L1` difference of two product masses is bounded by the sum of the
per-factor differences, each weighted by the corresponding mass of the
second law.  This is the scalar core of the product TV subadditivity. -/
theorem productMassBound (a b : Rat) (a' b' : Rat) (hbn : 0 ≤ b) (hann' : 0 ≤ a') :
    |a * b - a' * b'| ≤ |a - a'| * b + a' * |b - b'| := by
  have hsplit : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  calc
    |a * b - a' * b'| = |(a - a') * b + a' * (b - b')| := by rw [hsplit]
    _ ≤ |(a - a') * b| + |a' * (b - b')| := by exact abs_add_le _ _
    _ = |a - a'| * b + a' * |b - b'| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hbn, abs_of_nonneg hann']

/-- Fintype-free total-variation subadditivity for the two-pile product.
This is the Fintype-free analog of `distProduct_tv_subadditive`: the total
variation between two `distProductFinsupp` products is bounded by the sum of
the total variations of the two factor pairs.  It is the GSR two-pile
analogue of the Fintype F4.3 contraction, needed because the GSR state space
`List (Fin n)` is not a `Fintype`. -/
theorem distProductFinsupp_tv_subadditive (μ μ' : Dist α) (ν ν' : Dist β) :
    tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') ≤
      tvFinsupp μ μ' + tvFinsupp ν ν' := by
  let A := μ.weights.support ∪ μ'.weights.support
  let B := ν.weights.support ∪ ν'.weights.support
  let f (z : α × β) := |μ.weights z.1 * ν.weights z.2 - μ'.weights z.1 * ν'.weights z.2|
  let pP := (μ.weights.support ×ˢ ν.weights.support) ∪ (μ'.weights.support ×ˢ ν'.weights.support)
  have hzero : ∀ z ∈ A ×ˢ B, z ∉ pP → f z = 0 := by
    intro z _ hnot
    dsimp only [pP] at hnot
    have hnL : z.1 ∈ μ.weights.support ∧ z.2 ∈ ν.weights.support → False := by
      intro h
      have hmem : z ∈ μ.weights.support ×ˢ ν.weights.support := by simpa [Finset.mem_product] using h
      exact hnot (Finset.mem_union.mpr (Or.inl hmem))
    have hnR : z.1 ∈ μ'.weights.support ∧ z.2 ∈ ν'.weights.support → False := by
      intro h
      have hmem : z ∈ μ'.weights.support ×ˢ ν'.weights.support := by simpa [Finset.mem_product] using h
      exact hnot (Finset.mem_union.mpr (Or.inr hmem))
    have hL0 : μ.weights z.1 * ν.weights z.2 = 0 := by
      by_cases h1 : z.1 ∈ μ.weights.support
      · have h2 : z.2 ∉ ν.weights.support := by by_contra h2; exact hnL ⟨h1, h2⟩
        rw [not_mem_support_zero ν z.2 h2, mul_zero]
      · rw [not_mem_support_zero μ z.1 (by simpa [not_not] using h1), zero_mul]
    have hR0 : μ'.weights z.1 * ν'.weights z.2 = 0 := by
      by_cases h1 : z.1 ∈ μ'.weights.support
      · have h2 : z.2 ∉ ν'.weights.support := by by_contra h2; exact hnR ⟨h1, h2⟩
        rw [not_mem_support_zero ν' z.2 h2, mul_zero]
      · rw [not_mem_support_zero μ' z.1 (by simpa [not_not] using h1), zero_mul]
    dsimp only [f]
    simp only [hL0, hR0, mul_zero, zero_mul, sub_self, abs_zero]
  have hunion : (2 : Rat) * tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') = pP.sum f := by
    rw [twoTv_eq_unionSum, suppDistProductFinsupp, suppDistProductFinsupp]
    dsimp only [pP]
    apply Finset.sum_congr rfl
    intro z _
    rw [distProductFinsupp_mass μ ν z.1 z.2, distProductFinsupp_mass μ' ν' z.1 z.2]
  have hsub : pP ⊆ A ×ˢ B := by
    intro z hz
    simp only [pP, A, B, Finset.mem_union, Finset.mem_product] at hz ⊢
    rcases hz with hL | hR
    · constructor
      · left; exact hL.1
      · left; exact hL.2
    · constructor
      · right; exact hR.1
      · right; exact hR.2
  have hAB : pP.sum f = (A ×ˢ B).sum f := by
    have hf : (A ×ˢ B).filter (fun z => z ∈ pP) = pP := by
      ext z
      constructor
      · intro h; simp only [Finset.mem_filter] at h; exact h.2
      · intro h; simp only [Finset.mem_filter]; exact ⟨hsub h, h⟩
    have h1 : (A ×ˢ B).sum f = (A ×ˢ B).sum (fun z => if z ∈ pP then f z else 0) := by
      apply Finset.sum_congr rfl
      intro z hzAB
      by_cases hz : z ∈ pP
      · simp [hz]
      · rw [hzero z hzAB hz]; simp
    have hcalc : (A ×ˢ B).sum f = pP.sum f := by
      calc
        (A ×ˢ B).sum f = (A ×ˢ B).sum (fun z => if z ∈ pP then f z else 0) := h1
        _ = ((A ×ˢ B).filter (fun z => z ∈ pP)).sum f +
            ((A ×ˢ B).filter (fun z => z ∉ pP)).sum (fun _ => 0) := by
          rw [Finset.sum_ite]
        _ = ((A ×ˢ B).filter (fun z => z ∈ pP)).sum f := by
          rw [Finset.sum_const_zero, add_zero]
        _ = pP.sum f := by rw [hf]
    exact hcalc.symm
  have hbound : (A ×ˢ B).sum f ≤
      (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2 +
        μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) := by
    apply Finset.sum_le_sum
    intro z _
    have h0 : 0 ≤ ν.weights z.2 := Dist.mass_nonneg ν z.2
    have h1 : 0 ≤ μ'.weights z.1 := Dist.mass_nonneg μ' z.1
    exact productMassBound (μ.weights z.1) (ν.weights z.2) (μ'.weights z.1) (ν'.weights z.2) h0 h1
  have hsplit : (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2 +
        μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) =
      (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2) +
      (A ×ˢ B).sum (fun z => μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) := by
    rw [Finset.sum_add_distrib]
  have hA_tv : A.sum (fun a => |μ.weights a - μ'.weights a|) = (2 : Rat) * tvFinsupp μ μ' := by
    rw [← twoTv_eq_unionSum]
  have hB_tv : B.sum (fun b => |ν.weights b - ν'.weights b|) = (2 : Rat) * tvFinsupp ν ν' := by
    rw [← twoTv_eq_unionSum]
  have hA1 : B.sum (fun b => ν.weights b) = 1 := by
    have hBsup : ν.weights.support ⊆ B := by simp [B, Finset.mem_union]
    exact sumOverEnlarged_eq_one ν B hBsup
  have hB1 : A.sum (fun a => μ'.weights a) = 1 := by
    have hAsup : μ'.weights.support ⊆ A := by simp [A, Finset.mem_union]
    exact sumOverEnlarged_eq_one μ' A hAsup
  have hfactL : (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2) =
      (A.sum (fun a => |μ.weights a - μ'.weights a|)) * (B.sum (fun b => ν.weights b)) := by
    rw [Finset.sum_product]
    simp only [Prod.fst, Prod.snd]
    rw [← Finset.sum_mul_sum]
    <;> simp
  have hfactR : (A ×ˢ B).sum (fun z => μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) =
      (A.sum (fun a => μ'.weights a)) * (B.sum (fun b => |ν.weights b - ν'.weights b|)) := by
    rw [Finset.sum_product]
    simp only [Prod.fst, Prod.snd]
    rw [← Finset.sum_mul_sum]
    <;> simp
  have h6 : (A.sum (fun a => |μ.weights a - μ'.weights a|)) * (B.sum (fun b => ν.weights b)) +
      (A.sum (fun a => μ'.weights a)) * (B.sum (fun b => |ν.weights b - ν'.weights b|)) =
      (2 : Rat) * tvFinsupp μ μ' + (2 : Rat) * tvFinsupp ν ν' := by
    rw [hA_tv, hB_tv, hA1, hB1]
    ring
  have h5 : (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2 +
        μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) =
      (2 : Rat) * tvFinsupp μ μ' + (2 : Rat) * tvFinsupp ν ν' := by
    rw [hsplit, hfactL, hfactR, h6]
  have h7 : (2 : Rat) * tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') ≤
      (2 : Rat) * tvFinsupp μ μ' + (2 : Rat) * tvFinsupp ν ν' := by
    calc
      _ = (A ×ˢ B).sum f := by rw [hunion, hAB]
      _ ≤ (A ×ˢ B).sum (fun z => |μ.weights z.1 - μ'.weights z.1| * ν.weights z.2 +
          μ'.weights z.1 * |ν.weights z.2 - ν'.weights z.2|) := hbound
      _ = (2 : Rat) * tvFinsupp μ μ' + (2 : Rat) * tvFinsupp ν ν' := h5
  have h8 : (2 : Rat) * tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') ≤
      (2 : Rat) * (tvFinsupp μ μ' + tvFinsupp ν ν') := by
    rw [← mul_add] at h7
    exact h7
  have h9 : tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') ≤
      tvFinsupp μ μ' + tvFinsupp ν ν' := by
    have h13 : (1 / 2 : Rat) * (2 * tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν')) ≤
        (1 / 2 : Rat) * (2 * (tvFinsupp μ μ' + tvFinsupp ν ν')) :=
      mul_le_mul_of_nonneg_left h8 (by norm_num)
    have h14 : (1 / 2 : Rat) * (2 * tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν')) =
        tvFinsupp (distProductFinsupp μ ν) (distProductFinsupp μ' ν') := by ring
    have h15 : (1 / 2 : Rat) * (2 * (tvFinsupp μ μ' + tvFinsupp ν ν')) =
        tvFinsupp μ μ' + tvFinsupp ν ν' := by ring
    simpa [h14, h15] using h13
  exact h9

/-- If `A ⊆ B` and `f ≥ 0` on `B`, then `A.sum f ≤ B.sum f`. -/
theorem subsetSum_le {ι : Type*} [DecidableEq ι] {A B : Finset ι} (f : ι → Rat)
    (hsub : A ⊆ B) (hnneg : ∀ x ∈ B, 0 ≤ f x) : A.sum f ≤ B.sum f := by
  have h : (B \ A).sum f + A.sum f = B.sum f := Finset.sum_sdiff hsub
  have h0 : 0 ≤ (B \ A).sum f := by
    apply Finset.sum_nonneg
    intro x hx
    exact hnneg x (Finset.mem_sdiff.mp hx).1
  linarith [h, h0]

/-- Extending a Finsupp mass-weighted sum from the support to a larger finite
set: the extra terms vanish when the weight `μ x = 0` off the support. -/
theorem sumOverLargerSupport {γ β : Type*} [DecidableEq γ] (μ : Dist γ) (B : Finset γ)
    (hB : μ.weights.support ⊆ B) (g : γ → Dist β) (y : β) :
    B.sum (fun x => Dist.mass μ x * Dist.mass (g x) y) =
      μ.weights.support.sum (fun x => Dist.mass μ x * Dist.mass (g x) y) := by
  set f := fun (x : γ) => Dist.mass μ x * Dist.mass (g x) y with hf
  have h : (B \ μ.weights.support).sum f + μ.weights.support.sum f = B.sum f := Finset.sum_sdiff hB
  have hzero : (B \ μ.weights.support).sum f = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases h2 : x ∈ μ.weights.support
    · exfalso; exact (Finset.mem_sdiff.mp hx).2 h2
    · unfold Dist.mass
      rw [not_mem_support_zero μ x h2, zero_mul]
  have h' : μ.weights.support.sum f = B.sum f := by simpa [hzero, add_zero] using h
  simpa [hf] using h'.symm

/-- Summing a probability law's mass over any finite set is at most 1. -/
theorem supportSum_le_one {β : Type*} [DecidableEq β] (ν : Dist β) (T : Finset β) :
    T.sum (fun b => Dist.mass ν b) ≤ 1 := by
  let B := ν.weights.support ∪ T
  have hB : ν.weights.support ⊆ B := Finset.subset_union_left
  have hfull : B.sum (fun b => Dist.mass ν b) = 1 := sumOverEnlarged_eq_one ν B hB
  have hsub : T ⊆ B := Finset.subset_union_right
  calc
    _ ≤ B.sum (fun b => Dist.mass ν b) :=
      subsetSum_le (fun b => Dist.mass ν b) hsub fun b hb => Dist.mass_nonneg ν b
    _ = 1 := hfull

/-- A stochastic kernel is 1-Lipschitz in total variation: pushing two laws
through the same kernel cannot increase their TV.  Fintype-free — it uses the
finite `Finsupp` supports, so no `[Fintype α]` is required.  This is the
F4.5 building block for telescoping finite-GSR schedules over non-Fintype
deck state spaces. -/
theorem kernel_apply_lipschitz {α β : Type*} [DecidableEq α] [DecidableEq β]
    (mu nu : Dist α) (K : FiniteKernel α β) :
    tvFinsupp (FiniteKernel.apply mu K) (FiniteKernel.apply nu K) ≤ tvFinsupp mu nu := by
  set P := FiniteKernel.apply mu K with hP
  set Q := FiniteKernel.apply nu K with hQ
  let Smu := mu.weights.support
  let Snu := nu.weights.support
  let S := Smu ∪ Snu
  have hSmu : Smu ⊆ S := Finset.subset_union_left
  have hSnu : Snu ⊆ S := Finset.subset_union_right
  have hPmass (y : β) : Dist.mass P y = S.sum (fun j => Dist.mass mu j * Dist.mass (K j) y) := by
    rw [FiniteKernel.apply_mass_finsupp]
    rw [← sumOverLargerSupport mu S hSmu K y]
  have hQmass (y : β) : Dist.mass Q y = S.sum (fun j => Dist.mass nu j * Dist.mass (K j) y) := by
    rw [FiniteKernel.apply_mass_finsupp]
    rw [← sumOverLargerSupport nu S hSnu K y]
  have hPsub (y : β) : Dist.mass P y - Dist.mass Q y =
      S.sum (fun j => (Dist.mass mu j - Dist.mass nu j) * Dist.mass (K j) y) := by
    rw [hPmass, hQmass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoint (y : β) : |Dist.mass P y - Dist.mass Q y| ≤
      S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * Dist.mass (K j) y) := by
    rw [hPsub]
    have h1 := Finset.abs_sum_le_sum_abs (fun j => (Dist.mass mu j - Dist.mass nu j) * Dist.mass (K j) y) S
    have h2 : S.sum (fun j => |(Dist.mass mu j - Dist.mass nu j) * Dist.mass (K j) y|) =
        S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * Dist.mass (K j) y) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (Dist.mass_nonneg (K j) y)]
    exact le_trans h1 (le_of_eq h2)
  let T := P.weights.support ∪ Q.weights.support
  have hA : (2 : Rat) * tvFinsupp P Q = T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) := by
    dsimp only [T]
    unfold Dist.mass
    rw [twoTv_eq_unionSum]
  have hB : T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) ≤
      T.sum (fun y => S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * Dist.mass (K j) y)) := by
    apply Finset.sum_le_sum
    intro y _
    exact hpoint y
  have hC : T.sum (fun y => S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * Dist.mass (K j) y)) =
      S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * T.sum (fun y => Dist.mass (K j) y)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
  have hD : S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * T.sum (fun y => Dist.mass (K j) y)) ≤
      S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * 1) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · exact supportSum_le_one (K j) T
    · exact abs_nonneg _
  have hE : S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * 1) =
      S.sum (fun j => |Dist.mass mu j - Dist.mass nu j|) := by
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hF : S.sum (fun j => |Dist.mass mu j - Dist.mass nu j|) = (2 : Rat) * tvFinsupp mu nu := by
    dsimp only [S, Smu, Snu]
    unfold Dist.mass
    simpa using (twoTv_eq_unionSum mu nu).symm
  have hcalc : (2 : Rat) * tvFinsupp P Q ≤ (2 : Rat) * tvFinsupp mu nu := by
    calc
      _ = T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) := hA
      _ ≤ T.sum (fun y => S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * Dist.mass (K j) y)) := hB
      _ = S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * T.sum (fun y => Dist.mass (K j) y)) := hC
      _ ≤ S.sum (fun j => |Dist.mass mu j - Dist.mass nu j| * 1) := hD
      _ = S.sum (fun j => |Dist.mass mu j - Dist.mass nu j|) := hE
      _ = (2 : Rat) * tvFinsupp mu nu := hF
  simpa [mul_assoc, mul_one] using hcalc

/-- The un-halved L1 distance of two laws, summed over any finite set that
contains the union of their supports, equals twice their TV (the extra terms
vanish because both laws carry zero mass outside their supports). -/
theorem l1OverEnlarged_eq_twoTv {γ : Type*} [DecidableEq γ] (p q : Dist γ) (T : Finset γ)
    (hT : p.weights.support ∪ q.weights.support ⊆ T) :
    T.sum (fun x => |p.weights x - q.weights x|) = (2 : Rat) * tvFinsupp p q := by
  let U := p.weights.support ∪ q.weights.support
  have hzero : (T \ U).sum (fun x => |p.weights x - q.weights x|) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hnotp : x ∉ p.weights.support := by
      intro hp; exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union.mpr (Or.inl hp))
    have hnotq : x ∉ q.weights.support := by
      intro hq; exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union.mpr (Or.inr hq))
    rw [not_mem_support_zero p x hnotp, not_mem_support_zero q x hnotq, sub_zero, abs_zero]
  have hsd : (T \ U).sum (fun x => |p.weights x - q.weights x|) + U.sum (fun x => |p.weights x - q.weights x|) =
      T.sum (fun x => |p.weights x - q.weights x|) := Finset.sum_sdiff hT
  have hmid : U.sum (fun x => |p.weights x - q.weights x|) = T.sum (fun x => |p.weights x - q.weights x|) := by
    simpa [hzero, add_zero] using hsd
  have hU : U.sum (fun x => |p.weights x - q.weights x|) = (2 : Rat) * tvFinsupp p q := by
    dsimp only [U]
    exact (twoTv_eq_unionSum p q).symm
  simpa [hmid] using hU

/-- A mixture (convex combination) of laws is no further from a reference than
the mixture-weighted average of the component distances.  In particular, pushing
a law through a kernel is 1-Lipschitz (take the reference to be another push).
Fintype-free. -/
theorem mixtureTV_le {σ β : Type*} [DecidableEq σ] [DecidableEq β] (μ : Dist σ)
    (K : σ → Dist β) (ref : Dist β) (S : Finset σ) (hS : μ.weights.support ⊆ S) :
    tvFinsupp (FiniteKernel.apply μ K) ref ≤ S.sum (fun s => Dist.mass μ s * tvFinsupp (K s) ref) := by
  set P := FiniteKernel.apply μ K with hP
  let X := S.biUnion (fun j => (K j).weights.support)
  let Y := P.weights.support ∪ ref.weights.support ∪ X
  have hsum1 : S.sum (fun j => Dist.mass μ j) = 1 := sumOverEnlarged_eq_one μ S hS
  have hPmass (y : β) : Dist.mass P y = S.sum (fun j => Dist.mass μ j * Dist.mass (K j) y) := by
    rw [FiniteKernel.apply_mass_finsupp]
    rw [← sumOverLargerSupport μ S hS K y]
  have hPsub (y : β) : Dist.mass P y - Dist.mass ref y =
      S.sum (fun j => Dist.mass μ j * (Dist.mass (K j) y - Dist.mass ref y)) := by
    rw [hPmass]
    apply Eq.symm
    have hd : S.sum (fun j => Dist.mass μ j * (Dist.mass (K j) y - Dist.mass ref y)) =
        S.sum (fun j => Dist.mass μ j * Dist.mass (K j) y - Dist.mass μ j * Dist.mass ref y) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h1e : (S.sum (fun j => Dist.mass μ j)) * Dist.mass ref y = Dist.mass ref y := by
      rw [hsum1, one_mul]
    rw [hd, Finset.sum_sub_distrib, ← Finset.sum_mul, h1e]
  have hpoint (y : β) : |Dist.mass P y - Dist.mass ref y| ≤
      S.sum (fun j => Dist.mass μ j * |Dist.mass (K j) y - Dist.mass ref y|) := by
    rw [hPsub]
    have h1 := Finset.abs_sum_le_sum_abs (fun j => Dist.mass μ j * (Dist.mass (K j) y - Dist.mass ref y)) S
    have h2 : S.sum (fun j => |Dist.mass μ j * (Dist.mass (K j) y - Dist.mass ref y)|) =
        S.sum (fun j => Dist.mass μ j * |Dist.mass (K j) y - Dist.mass ref y|) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (Dist.mass_nonneg μ j)]
    exact le_trans h1 (le_of_eq h2)
  have hA : (2 : Rat) * tvFinsupp P ref = Y.sum (fun y => |Dist.mass P y - Dist.mass ref y|) := by
    dsimp only [Y, X]
    unfold Dist.mass
    exact (l1OverEnlarged_eq_twoTv P ref Y Finset.subset_union_left).symm
  have hB : Y.sum (fun y => |Dist.mass P y - Dist.mass ref y|) ≤
      Y.sum (fun y => S.sum (fun j => Dist.mass μ j * |Dist.mass (K j) y - Dist.mass ref y|)) := by
    apply Finset.sum_le_sum; intro y _; exact hpoint y
  have hC : Y.sum (fun y => S.sum (fun j => Dist.mass μ j * |Dist.mass (K j) y - Dist.mass ref y|)) =
      S.sum (fun j => Dist.mass μ j * Y.sum (fun y => |Dist.mass (K j) y - Dist.mass ref y|)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
  have hD : S.sum (fun j => Dist.mass μ j * Y.sum (fun y => |Dist.mass (K j) y - Dist.mass ref y|)) ≤
      S.sum (fun j => Dist.mass μ j * ((2 : Rat) * tvFinsupp (K j) ref)) := by
    apply Finset.sum_le_sum
    intro j hjS
    apply mul_le_mul_of_nonneg_left
    · have hKsup : (K j).weights.support ⊆ X := by
        intro x hx
        apply Finset.mem_biUnion.mpr
        exact ⟨j, hjS, hx⟩
      have hUj : (K j).weights.support ∪ ref.weights.support ⊆ Y := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hA | hB
        · dsimp only [Y, X]
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          exact ⟨j, hjS, hA⟩
        · dsimp only [Y, X]
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          exact hB
      have hle : Y.sum (fun y => |Dist.mass (K j) y - Dist.mass ref y|) = (2 : Rat) * tvFinsupp (K j) ref := by
        dsimp only [Y, X]
        unfold Dist.mass
        exact l1OverEnlarged_eq_twoTv (K j) ref Y hUj
      exact le_of_eq hle
    · exact Dist.mass_nonneg μ j
  have hE : (2 : Rat) * tvFinsupp P ref ≤
      S.sum (fun j => Dist.mass μ j * ((2 : Rat) * tvFinsupp (K j) ref)) := by
    calc
      _ = Y.sum (fun y => |Dist.mass P y - Dist.mass ref y|) := hA
      _ ≤ Y.sum (fun y => S.sum (fun j => Dist.mass μ j * |Dist.mass (K j) y - Dist.mass ref y|)) := hB
      _ = S.sum (fun j => Dist.mass μ j * Y.sum (fun y => |Dist.mass (K j) y - Dist.mass ref y|)) := hC
      _ ≤ S.sum (fun j => Dist.mass μ j * ((2 : Rat) * tvFinsupp (K j) ref)) := hD
  have hF : S.sum (fun j => Dist.mass μ j * ((2 : Rat) * tvFinsupp (K j) ref)) =
      (2 : Rat) * S.sum (fun j => Dist.mass μ j * tvFinsupp (K j) ref) := by
    rw [show S.sum (fun j => Dist.mass μ j * ((2 : Rat) * tvFinsupp (K j) ref)) =
          S.sum (fun j => (2 : Rat) * (Dist.mass μ j * tvFinsupp (K j) ref)) from
      by apply Finset.sum_congr rfl; intro j _; ring,
      ← Finset.mul_sum]
  have hcalc : (2 : Rat) * tvFinsupp P ref ≤ (2 : Rat) * S.sum (fun j => Dist.mass μ j * tvFinsupp (K j) ref) := by
    rw [hF] at hE
    exact hE
  have hG : tvFinsupp P ref ≤ S.sum (fun j => Dist.mass μ j * tvFinsupp (K j) ref) := by
    have h13 : (1 / 2 : Rat) * (2 * tvFinsupp P ref) ≤ (1 / 2 : Rat) * (2 * S.sum (fun j => Dist.mass μ j * tvFinsupp (K j) ref)) :=
      mul_le_mul_of_nonneg_left hcalc (by norm_num)
    simpa [mul_assoc, mul_one] using h13
  simpa [hP] using hG

  /-- A homogeneous kernel that is 1-Lipschitz in one step is non-expansive for
      arbitrarily many steps: iterating it `n` times never increases the total
      variation between two starting laws.  Fintype-free (no finiteness of the
      state space), so it applies to infinite deck-list spaces.  This is the
      Fintype-free substitute for the Dobrushin / weighted-telescope iteration:
      it composes the one-step kernel contraction `kernel_apply_lipschitz` along
      the `run` iteration, bounding the terminal TV of any schedule of
      1-Lipschitz moves (in particular, a schedule of GSR shuffles) by the TV
      of the two starting laws. -/
  theorem run_nonexpansive {α : Type*} [DecidableEq α] (K : FiniteKernel α α)
      (n : Nat) (mu nu : Dist α) :
      tvFinsupp (FiniteKernel.run K n mu) (FiniteKernel.run K n nu) ≤ tvFinsupp mu nu := by
    induction n generalizing mu nu with
    | zero =>
      simp [FiniteKernel.run]
    | succ n ih =>
      rw [FiniteKernel.run_succ_add, FiniteKernel.run_succ_add]
      calc
        _ ≤ tvFinsupp (FiniteKernel.run K n mu) (FiniteKernel.run K n nu) :=
          kernel_apply_lipschitz (FiniteKernel.run K n mu) (FiniteKernel.run K n nu) K
        _ ≤ tvFinsupp mu nu := ih mu nu

end Shufflemath


end
