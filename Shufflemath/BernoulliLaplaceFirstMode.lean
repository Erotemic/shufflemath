module

public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.Finite
public import Shufflemath.Markov
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace BernoulliLaplaceGeneral

/-! ### First mode: hypergeometric means and the first eigenfunction

The exchange kernel is affine on the macrostate: `E[y | x] = x - a
mean + b mean` with the means given by the 1-D hypergeometric
computations below. From that, the centered macrostate
`f(x) = x - m*r/N` is an eigenfunction with eigenvalue
`blFirstModeFactor = 1 - N*k/(m*(N-m))`. -/
variable {N m r k : Nat}

/-- The first-mode factor of the general exchange kernel: the eigenvalue
of the first centered linear mode. The coefficient is independent of
`r` (the centering, not the contraction, depends on `r`). For the
Commander split (`N = 99`, `m = 50`) this specializes to the concrete
`firstModeFactor` of `Shufflemath.BernoulliLaplace` (agreement is proved
in the bridge module). -/
def blFirstModeFactor (N m k : Nat) : Rat :=
  1 - ((N : Rat) * k) / ((m : Rat) * (N - m))

/-- Pointwise `y`-product and its `(x-a)` / `(y-(x-a))` split parts, as
`Nat` terms. Wrapper `def`s keep the `Nat.cast` of a product opaque
(a `: Rat` ascription on a product would normalize to a product of
casts, which the `Nat.cast_*` lemmas cannot match). -/
def gProd (N m r k x a y : Nat) : Nat := y * (guardedTerm N m r k x a y)
def gProdA (N m r k x a y : Nat) : Nat := (x - a) * (guardedTerm N m r k x a y)
def gProdB (N m r k x a y : Nat) : Nat := (y - (x - a)) * (guardedTerm N m r k x a y)
def gSplit (N m r k x a y : Nat) : Nat :=
  (x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y)

/-- Weighted inner reindexing: for fixed `a <= k`, the `y`-sum of
`(y : Rat) * (guarded term)` over `y < m + 1` equals
`(x - a) * (b-sum) + (b-weighted b-sum)`, all as `Rat` sums.
The `y = (x-a) + (y-(x-a))` split is done in `Nat` (inside `Nat.cast`);
each half is then bridged to its `b`-sum by `innerYToB` / `innerYToB_b`. -/
theorem innerYToB_w (N m r k x a : Nat) (hm : x <= m) (ha : a <= k) :
    (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
      ((x : Rat) - (a : Rat)) * (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat))
      + (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) := by
  by_cases hax : a <= x
  · -- `a <= x`: genuine `x - a`.
    -- The unweighted `y`-sum (as a `Rat` sum of casts) is the unweighted `b`-sum.
    have hB : (∑ y ∈ Finset.range (m + 1), (guardedTerm N m r k x a y : Rat)) =
        (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      rw [show (∑ y ∈ Finset.range (m + 1), guardedTerm N m r k x a y) =
            (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b)
        from innerYToB N m r k x a hm ha]
    -- The `b`-weighted `b`-sum is the `(y - (x-a))`-weighted `y`-sum
    -- (cast of `innerYToB_b`).
    have hBw : (∑ y ∈ Finset.range (m + 1), (gProdB N m r k x a y : Rat)) =
        (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) := by
      have hN := innerYToB_b N m r k x a hm ha
      have hR : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (Nat.cast ((b : Nat) * (exchangeTerm N m r k x a b)) : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← Nat.cast_mul]
      rw [hR]
      change (∑ y ∈ Finset.range (m + 1), Nat.cast ((y - (x - a)) * (guardedTerm N m r k x a y))) = _
      rw [← Nat.cast_sum, hN, Nat.cast_sum]
    -- Per term, inside the cast: `y * g = (x-a) * g + (y-x+a) * g`
    -- (a genuine subtraction distributes; otherwise `g = 0`).
    have hS1 : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
        (∑ y ∈ Finset.range (m + 1), (gSplit N m r k x a y : Rat)) := by
      apply Finset.sum_congr rfl
      intro y _
      -- Work in `Nat` (inside the cast): `y * g = (x-a) * g + (y-x+a) * g`.
      refine congrArg (Nat.cast ·) ?_
      change y * (guardedTerm N m r k x a y) =
          (x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y)
      by_cases hgy : x - a <= y
      · -- Genuine: `y = (y-x+a) + (x-a)`, so the `Nat` product distributes.
        have hsum : y = (y - (x - a)) + (x - a) := by
          rw [Nat.sub_add_cancel hgy]
        rw [hsum]
        rw [Nat.add_mul]
        rw [show ((y - (x - a)) + (x - a)) - (x - a) = y - (x - a) from by
          rw [Nat.add_sub_cancel_right]]
        ring
      · -- `y < x - a`: the guarded term vanishes.
        have hgz : (guardedTerm N m r k x a y) = 0 := by
          simp only [guardedTerm]
          rw [ite_eq_right hgy]
        rw [hgz]
        simp
    -- The sum of the two cast halves is the cast of the split `Nat` sum.
    have hS2 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) +
          (∑ y ∈ Finset.range (m + 1), (gProdB N m r k x a y : Rat)) =
        (∑ y ∈ Finset.range (m + 1), (gSplit N m r k x a y : Rat)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      change Nat.cast ((x - a) * (guardedTerm N m r k x a y)) +
            Nat.cast ((y - (x - a)) * (guardedTerm N m r k x a y)) =
          Nat.cast ((x - a) * (guardedTerm N m r k x a y) + (y - (x - a)) * (guardedTerm N m r k x a y))
      rw [← Nat.cast_add]
    -- The constant half factors out of the sum.
    have hS3 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) =
        (Nat.cast (x - a)) * (∑ y ∈ Finset.range (m + 1), (guardedTerm N m r k x a y : Rat)) := by
      have h0 : (∑ y ∈ Finset.range (m + 1), (gProdA N m r k x a y : Rat)) =
          (∑ y ∈ Finset.range (m + 1), (Nat.cast (x - a)) * (Nat.cast (guardedTerm N m r k x a y))) := by
        apply Finset.sum_congr rfl
        intro y _
        change Nat.cast ((x - a) * (guardedTerm N m r k x a y)) =
            (Nat.cast (x - a)) * (Nat.cast (guardedTerm N m r k x a y))
        rw [Nat.cast_mul]
      rw [h0, ← Finset.mul_sum]
    -- Assemble: fold each half to its `b`-sum and match the `Rat` difference.
    rw [hS1, ← hS2]
    rw [hS3, ← hBw]
    rw [hB, Nat.cast_sub hax]
  · -- `a > x`: `C(x, a) = 0` kills both `g` and `E`, so both sides are `0`.
    have hxlt : x < a := by omega
    have hgz (y : Nat) : (guardedTerm N m r k x a y) = 0 := by
      simp only [guardedTerm]
      by_cases h1 : x - a <= y
      · by_cases h2 : y - (x - a) <= k
        · -- Both guards pass: the product; `C(x, a) = 0` kills it.
          rw [ite_eq_left h1, ite_eq_left h2, Nat.choose_eq_zero_of_lt hxlt]
          simp
        · -- Inner guard fails: the inner `else 0`.
          rw [ite_eq_left h1, ite_eq_right h2]
      · -- Outer guard fails: the outer `else 0`.
        rw [ite_eq_right h1]
    have hez (b : Nat) : (exchangeTerm N m r k x a b) = 0 := by
      simp only [exchangeTerm]
      rw [Nat.choose_eq_zero_of_lt hxlt]
      simp
    have hL : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) = 0 := by
      have h1 : (∑ y ∈ Finset.range (m + 1), (gProd N m r k x a y : Rat)) =
          (∑ y ∈ Finset.range (m + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [gProd]
        rw [hgz y]
        simp
      rw [h1]
      simp
    have hB : (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) = 0 := by
      have h1 : (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hez b]
        simp
      rw [h1]
      simp
    have hBw : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) = 0 := by
      have h1 : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
          (∑ b ∈ Finset.range (k + 1), (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hez b]
        simp
      rw [h1]
      simp
    rw [hL, hB, hBw]
    simp
/-- Per-term Pascal shift: `(x + 1) * C(n, x+1) = n * C(n-1, x)`.
Holds for all `n x`: when `x >= n` both sides are `0`. -/
theorem chooseSucc_weighted (n x : Nat) :
    (x + 1) * (Nat.choose n (x + 1)) = n * (Nat.choose (n - 1) x) := by
  by_cases h : x < n
  · -- `x <= n - 1`: Pascal + the `(x+1)`-weighted Pascal recurrence.
    have h1 : Nat.choose n (x + 1) = Nat.choose (n - 1) x + Nat.choose (n - 1) (x + 1) := by
      have : n - 1 + 1 = n := by omega
      rw [← this]
      rw [Nat.choose_succ_succ (n - 1) x]
      simp
    have h2 : (x + 1) * (Nat.choose (n - 1) (x + 1)) =
        (Nat.choose (n - 1) x) * (n - 1 - x) := by
      rw [Nat.mul_comm]
      rw [Nat.choose_succ_right_eq (n - 1) x]
    calc
      (x + 1) * (Nat.choose n (x + 1)) =
          (x + 1) * (Nat.choose (n - 1) x + Nat.choose (n - 1) (x + 1)) := by rw [h1]
      _ = (x + 1) * (Nat.choose (n - 1) x) + (x + 1) * (Nat.choose (n - 1) (x + 1)) := by ring
      _ = (x + 1) * (Nat.choose (n - 1) x) + (Nat.choose (n - 1) x) * (n - 1 - x) := by rw [h2]
      _ = (Nat.choose (n - 1) x) * ((x + 1) + (n - 1 - x)) := by
        rw [Nat.mul_comm]
        ring
      _ = n * (Nat.choose (n - 1) x) := by
        have hle : x <= n - 1 := by omega
        have : (x + 1) + (n - 1 - x) = n := by
          have h1 : (n - 1 - x) + x = n - 1 := Nat.sub_add_cancel hle
          omega
        rw [this]
        exact Nat.mul_comm (Nat.choose (n - 1) x) n
  · -- `x >= n`: both binomials vanish (`n = 0` handled separately).
    by_cases hn0 : n = 0
    · simp [hn0]
    ·
      have hxn : x >= n := Nat.not_lt.mp h
      have h1 : n < x + 1 := by omega
      have h2 : n - 1 < x := by
        have hnn : n = (n - 1) + 1 := by
          have : 0 < n := Nat.pos_of_ne_zero hn0
          omega
        rw [hnn] at hxn
        omega
      have hz1 : Nat.choose n (x + 1) = 0 := by
        rw [Nat.choose_eq_zero_iff]
        exact h1
      have hz2 : Nat.choose (n - 1) x = 0 := by
        rw [Nat.choose_eq_zero_iff]
        exact h2
      rw [hz1, hz2]
      simp

/-- 1-D hypergeometric mean, exact rational form: a pile of `n` cards
holding `x` marked ones, drawing `k`: the expected number of marked
cards drawn is `k*x/n`. Equivalently the weighted sum identity -/
theorem chooseSum_weighted (n x k : Nat) (hx : x <= n) :
    (∑ a ∈ Finset.range (k + 1),
      (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
      (k : Rat) * (x : Rat) / (n : Rat) * (Nat.choose n k : Rat) := by
  by_cases hk : k = 0
  · -- The only summand has `a = 0` (hence is 0); the right side has `k = 0`.
    simp [hk]
  ·
    by_cases hx0 : x = 0
    · -- `C(0, a)` is 0 for `a >= 1` and the `a = 0` summand has a `0` factor;
      -- the right side has an `x = 0` factor.
    
      have hL : (∑ a ∈ Finset.range (k + 1),
          (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a = 0
        · simp [ha]
        · have ha1 : 0 < a := Nat.pos_of_ne_zero ha
          have hz : Nat.choose x a = 0 := by
            rw [Nat.choose_eq_zero_iff]
            simpa [hx0] using ha1
          simp [hz]
      rw [hL]
      simp [hx0]
    ·
      -- `0 < x <= n`, so `0 < n`: the division by `n` is an honest one.
      have hx1 : 0 < x := Nat.pos_of_ne_zero hx0
      have hn1 : 0 < n := Nat.lt_of_lt_of_le hx1 hx
      have hnpos : (n : Rat) ≠ 0 := by
        intro h
        have h1 : (0 : Rat) < (n : Rat) := Nat.cast_pos.mpr hn1
        rw [h] at h1
        linarith
      -- Step 1: drop the zero `a = 0` summand and reindex `a = i + 1` (`i < k`),
      -- using `k - (i+1) = k - 1 - i`.
      have h1 :
          (∑ a ∈ Finset.range (k + 1),
            (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
          (∑ i ∈ Finset.range k,
            ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) *
              (Nat.choose (n - x) (k - 1 - i) : Rat)) := by
        -- `range (k+1) \ {0}` is in bijection with `range k` via `i + 1`.
        have hdrop : (∑ a ∈ Finset.range (k + 1),
              (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) =
              (∑ a ∈ Finset.range (k + 1) \ {0},
                (a : Rat) * (Nat.choose x a : Rat) * (Nat.choose (n - x) (k - a) : Rat)) := by
          have hsub : ({0} : Finset Nat) ⊆ Finset.range (k + 1) := by
            intro x hx
            simp only [Finset.mem_singleton] at hx
            rw [hx]
            simp
          rw [← Finset.sum_sdiff hsub]
          simp
        rw [hdrop]
        apply Finset.sum_bij (fun a _ => a - 1)
        · intro a ha
          simp at ha
          rcases ha with ⟨hle, hne⟩
          have hpos : 0 < a := Nat.pos_of_ne_zero hne
          simp
          omega
        · intro a₁ h₁ a₂ h₂ h
          have h1 : 0 < a₁ := by
            simp at h₁
            rcases h₁ with ⟨_, hn⟩
            exact Nat.pos_of_ne_zero hn
          have h2 : 0 < a₂ := by
            simp at h₂
            rcases h₂ with ⟨_, hn⟩
            exact Nat.pos_of_ne_zero hn
          have h' : a₁ - 1 = a₂ - 1 := h
          omega
        · intro b hb
          use b + 1
          simp at hb
          simp
          omega
        · intro a ha
          have h0a : 0 < a := by
            simp at ha
            rcases ha with ⟨_, hne⟩
            exact Nat.pos_of_ne_zero hne
          have h1a : 1 ≤ a := Nat.succ_le_of_lt h0a
          have h2 : a - 1 + 1 = a := by omega
          have h3 : k - 1 - (a - 1) = k - a := by omega
          have hcast : (a : Rat) = (Nat.cast (a - 1) : Rat) + 1 := by
            have hsub : (Nat.cast (a - 1) : Rat) = (a : Rat) - 1 := by
              rw [Nat.cast_sub h1a]
              ring
            rw [hsub]
            ring
          rw [h2, h3, hcast]
      -- Step 2: per-term shift `(i+1) * C(x, i+1) = x * C(x-1, i)`; the sum
      -- factors as `x * (sum over i < k of C(x-1, i) * C(n-x, k-1-i))`.
      rw [h1]
      have h2 :
          (∑ i ∈ Finset.range k,
            ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) *
              (Nat.choose (n - x) (k - 1 - i) : Rat)) =
          (x : Rat) * (∑ i ∈ Finset.range k,
            (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat)) := by
        -- The per-term identity is `chooseSucc_weighted x i`, cast to `Rat`.
        calc
          _ = ∑ i ∈ Finset.range k,
              ((x : Rat) * (Nat.choose (x - 1) i : Rat)) *
                (Nat.choose (n - x) (k - 1 - i) : Rat) := by
            apply Finset.sum_congr rfl
            intro i _
            have hN : (i + 1) * (Nat.choose x (i + 1)) = x * (Nat.choose (x - 1) i) :=
              chooseSucc_weighted x i
            have hR : ((i + 1) : Rat) * (Nat.choose x (i + 1) : Rat) =
                (x : Rat) * (Nat.choose (x - 1) i : Rat) := by
              have hA : (i : Rat) + 1 = (Nat.cast (i + 1) : Rat) := by
                rw [Nat.cast_add, Nat.cast_one]
              rw [hA, ← Nat.cast_mul, ← Nat.cast_mul]
              exact congrArg Nat.cast hN
            rw [hR]
          _ = (x : Rat) * ∑ i ∈ Finset.range k,
            (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      rw [h2]
      -- Step 3: Vandermonde: the range sum is the antidiagonal sum, which
      -- is `C((x-1) + (n-x), k-1) = C(n-1, k-1)` (with `x >= 1` the Nat
      -- subtraction is honest and `(x-1) + (n-x) = n-1`).
      have h3 : (∑ i ∈ Finset.range k,
          (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) (k - 1 - i) : Rat)) =
          (Nat.choose (n - 1) (k - 1) : Rat) := by
        have hk1 : k - 1 + 1 = k := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          omega
        rw [show (Finset.range k : Finset Nat) = Finset.range (k - 1 + 1) from
            congrArg Finset.range hk1.symm]
        have hN : (∑ ij ∈ Finset.antidiagonal (k - 1),
            (Nat.choose (x - 1) ij.1) * (Nat.choose (n - x) ij.2)) =
            (Nat.choose ((x - 1) + (n - x)) (k - 1)) := by
          rw [← Nat.add_choose_eq (x - 1) (n - x) (k - 1)]
        have hmid : (∑ ij ∈ Finset.antidiagonal (k - 1),
            (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat)) =
            (Nat.choose ((x - 1) + (n - x)) (k - 1) : Rat) := by
          have hA : (∑ ij ∈ Finset.antidiagonal (k - 1),
              (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat)) =
              (∑ ij ∈ Finset.antidiagonal (k - 1),
                (Nat.cast (Nat.choose (x - 1) ij.1 * (Nat.choose (n - x) ij.2)) : Rat)) := by
            apply Finset.sum_congr rfl
            intro ij _
            rw [← Nat.cast_mul]
          rw [hA]
          rw [← Nat.cast_sum]
          exact congrArg Nat.cast hN
        calc
          _ = ∑ ij ∈ Finset.antidiagonal (k - 1),
              (Nat.choose (x - 1) ij.1 : Rat) * (Nat.choose (n - x) ij.2 : Rat) := by
            rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => (Nat.choose (x - 1) i : Rat) * (Nat.choose (n - x) j : Rat))
                (k - 1)]
          _ = (Nat.choose ((x - 1) + (n - x)) (k - 1) : Rat) := by
            exact hmid
          _ = (Nat.choose (n - 1) (k - 1) : Rat) := by
            have hsum : (x - 1) + (n - x) = n - 1 := by omega
            rw [hsum]
      rw [h3]
      -- Step 4: close. The goal is
      -- `(n : Rat) * ((x : Rat) * C(n-1, k-1)) = (k : Rat) * (x : Rat) / (n : Rat) * C(n, k)`.
      -- Both sides are `x * ( ... )`; inside, the coefficient relation
      -- `n * C(n-1, k-1) = k * C(n, k)` is exactly `chooseSucc_weighted n (k-1)`,
      -- and the right side's `/ (n : Rat) * (n : Rat)` cancels (`n ≠ 0`).
      have h4 : (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) =
          (k : Rat) * (Nat.choose n k : Rat) := by
        have h0 : (k - 1 + 1) * (Nat.choose n (k - 1 + 1)) = n * (Nat.choose (n - 1) (k - 1)) :=
          chooseSucc_weighted n (k - 1)
        have hk1 : k - 1 + 1 = k := by
          have : 0 < k := Nat.pos_of_ne_zero hk
          omega
        have hN : n * (Nat.choose (n - 1) (k - 1)) = k * (Nat.choose n k) := by
          simpa [hk1] using h0.symm
        rw [show (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) =
               (Nat.cast (n * (Nat.choose (n - 1) (k - 1))) : Rat) by
              rw [← Nat.cast_mul],
            show (k : Rat) * (Nat.choose n k : Rat) =
               (Nat.cast (k * (Nat.choose n k)) : Rat) by
              rw [← Nat.cast_mul]]
        exact congrArg Nat.cast hN
      -- Rewrite the right side into the `x * (...)` shape.
      have hR : (k : Rat) * (x : Rat) / (n : Rat) * (Nat.choose n k : Rat) =
          (x : Rat) * ((k : Rat) * (Nat.choose n k : Rat) / (n : Rat)) := by
        field_simp [hnpos]
      rw [hR]
      -- Clear the fraction using `n * C(n-1,k-1) = k * C(n,k)` (chooseSucc_weighted n (k-1)).
      have hdiv : (k : Rat) * (Nat.choose n k : Rat) / (n : Rat) =
          (Nat.choose (n - 1) (k - 1) : Rat) := by
        rw [show (k : Rat) * (Nat.choose n k : Rat) =
               (n : Rat) * (Nat.choose (n - 1) (k - 1) : Rat) from h4.symm]
        field_simp [hnpos]
      rw [hdiv]

/-! G3, part 1: the `b`-sum of the exchange term, for a fixed `a`.
For fixed `a` (special cards leaving the left pile) the `b`-sum
(`b` = special cards returning from the right) splits into the
`a`-dependent constant `C(x,a)·C(m-x,k-a)` and the Vandermonde
convolution of the two right-pile binomials, which collapses to
`C(N-m, k)`. The `Rat` lift `bSumE` is the form used by the
conditional-mean computation. -/

/-- The `b`-sum of the exchange term for fixed `a` is the `a`-factor
times the right-pile Vandermonde: `C(x,a)·C(m-x,k-a)·C(N-m,k)`. -/
theorem bSumE_nat (N m r k x a : Nat) (hrx : r - x ≤ N - m) :
    (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b) =
      (Nat.choose x a * Nat.choose (m - x) (k - a)) * Nat.choose (N - m) k := by
  have h1 : (∑ b ∈ Finset.range (k + 1), exchangeTerm N m r k x a b) =
      (∑ b ∈ Finset.range (k + 1),
        (Nat.choose x a * Nat.choose (m - x) (k - a)) *
          (Nat.choose (r - x) b * Nat.choose (N - m - (r - x)) (k - b))) := by
    apply Finset.sum_congr rfl
    intro b _
    simp only [exchangeTerm]
    ring
  rw [h1, ← Finset.mul_sum, vandermondeRange (r - x) (N - m - (r - x)) k]
  rw [show (r - x) + (N - m - (r - x)) = N - m from by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hrx]

/-- The `b`-sum lifted to `Rat`: the unweighted exchange-term sum is
the `a`-factor times `C(N-m, k)`, with a single cast at the end. -/
theorem bSumE (N m r k x a : Nat) (hrx : r - x ≤ N - m) :
    (∑ b ∈ Finset.range (k + 1), (exchangeTerm N m r k x a b : Rat)) =
      (Nat.choose x a * Nat.choose (m - x) (k - a) * Nat.choose (N - m) k : Rat) := by
  rw [← Nat.cast_sum, bSumE_nat N m r k x a hrx, Nat.cast_mul, Nat.cast_mul]

/-! G3, part 2: the `b`-**weighted** `b`-sum, for a fixed `a`.
The `b`-weighted exchange-term sum factors into the `a`-factor
`C(x,a)·C(m-x,k-a)` and the hypergeometric mean of the right pile:
`∑_b b·C(r-x,b)·C(N-m-(r-x),k-b) = k·(r-x)/(N-m)·C(N-m,k)`
(`chooseSum_weighted`). -/

/-- The `b`-weighted `b`-sum lifted to `Rat`: the `a`-factor times
`k·(r-x)/(N-m)`, times `C(N-m, k)`. -/
theorem bSumE_w (N m r k x a : Nat) (hmn : m < N) (hxr : x ≤ r) (hrx : r - x ≤ N - m) :
    (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
      ((Nat.choose x a * Nat.choose (m - x) (k - a) : Rat)) *
        ((k : Rat) * (r - x : Rat) / (N - m : Rat) * (Nat.choose (N - m) k : Rat)) := by
  set C1 := Nat.choose x a
  set C2 := Nat.choose (m - x) (k - a)
  set C3 := fun b => Nat.choose (r - x) b
  set C4 := fun b => Nat.choose (N - m - (r - x)) (k - b)
  have h1 : (∑ b ∈ Finset.range (k + 1), (b : Rat) * (exchangeTerm N m r k x a b : Rat)) =
      (∑ b ∈ Finset.range (k + 1),
        ((C1 * C2 : Rat)) * ((b : Rat) * (C3 b : Rat) * (C4 b : Rat))) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [show exchangeTerm N m r k x a b = C1 * C2 * (C3 b * C4 b) from by
      simp only [exchangeTerm, C1, C2, C3, C4]
      ring]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    ring
  rw [h1]
  rw [← Finset.mul_sum]
  rw [chooseSum_weighted (N - m) (r - x) k hrx]
  -- The instantiated `chooseSum_weighted` carries opaque `Nat.cast` of the
  -- subtractions; our ascriptions are distributed. `Nat.cast_sub` bridges
  -- both (its stored form is `↑(m - n) = ↑m - ↑n`).
  rw [Nat.cast_sub (Nat.le_of_lt hmn)]
  rw [Nat.cast_sub hxr]

/-! G3, part 3: the `a`-level Vandermonde, lifted to `Rat`.
The `a`-sum of `C(x,a)·C(m-x,k-a)` (special cards leaving the left
pile, over all admissible `a`) is the left-pile Vandermonde
`C(m, k)`; this is the `a`-analogue of `bSumE`. -/

/-- The `a`-sum of the left-pile factor pair, lifted to `Rat`: it is
`C(m, k)`. The ascription on the `Nat` product elaborates to the product
of the two ascriptions (one kernel term), so `Nat.cast_sum` (via
`convert`, which unifies up to that `rfl` and the per-term `Nat.cast_mul`
bridge) identifies the `Rat` sum with the cast of the `Nat` sum; the
`Nat` Vandermonde is then applied inside the cast. -/
theorem aSumE (m x k : Nat) (hx : x ≤ m) :
    (∑ a ∈ Finset.range (k + 1),
      (Nat.choose x a : Rat) * (Nat.choose (m - x) (k - a) : Rat)) =
      (Nat.choose m k : Rat) := by
  convert (Nat.cast_sum (Finset.range (k + 1))
      (fun a => Nat.choose x a * Nat.choose (m - x) (k - a))).symm using 2
  · -- Per term: the product of the two casts is the cast of the product.
    rw [← Nat.cast_mul]
  · -- The `Nat` Vandermonde, applied inside the cast.
    rw [show (∑ a ∈ Finset.range (k + 1),
        Nat.choose x a * Nat.choose (m - x) (k - a)) = Nat.choose m k from by
      rw [vandermondeRange x (m - x) k]
      rw [show x + (m - x) = m from by
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel hx]]

/-! G3: the conditional mean `E[y | x]`. The `y`-weighted numerator is
reindexed (per `a`) by `innerYToB_w` to the two `b`-sums, which are the
`bSumE` / `bSumE_w` closed forms; the `a`-sums are the `aSumE`
Vandermonde and the `chooseSum_weighted` hypergeometric mean; the
transition denominator then cancels. -/

/-- The conditional mean of the exchange kernel: for admissible `p` and
state `x`, the mean of the next state is the linear function
`x - (k/m)·x + (k/(N-m))·(r-x)`. This is the eigenfunction equation of
the first (centered linear) mode at the kernel level: the centering
`m·r/N` is a fixed point of this mean, and the slope is
`blFirstModeFactor`. -/
theorem blConditionalMean (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    (∑ y ∈ stateFinset p.N p.m p.r,
      (y : Rat) * (transitionWeight p.N p.m p.r p.k x.val y)) =
      (x.val : Rat) - (p.k : Rat) * (x.val : Rat) / (p.m : Rat) +
      (p.k : Rat) * ((p.r - x.val) : Rat) / ((p.N - p.m) : Rat) := by
  -- State bounds (from the `BLState` membership).
  have hx : x.val ≤ p.m := x.2.2.trans (min_le_left p.m p.r)
  have hlo : blLo p.N p.m p.r ≤ x.val := x.2.1
  have hxr : x.val ≤ p.r := x.2.2.trans (min_le_right p.m p.r)
  have hmn := p.hmn
  -- The transition denominator is positive, hence its `Rat` cast is
  -- nonzero (needed to cancel it at the end).
  have hdenPos : 0 < transitionDenominator p.N p.m p.k := by
    rw [transitionDenominator]
    exact Nat.mul_pos (Nat.choose_pos p.hkm) (Nat.choose_pos p.hknm)
  have hden : (transitionDenominator p.N p.m p.k : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h
    rw [h] at hdenPos
    exact lt_irrefl 0 hdenPos

  -- Step 1: pull the division by the (constant) denominator out of the
  -- `y`-sum: `∑ y, (y·(num/den)) = (∑ y, (y·num)) / den`.
  -- Per term, `(y:Rat)·((num:Rat)/(den:Rat))` is the same kernel term as
  -- `((y·num):Rat)/(den:Rat)` (the ascription on the product distributes
  -- to the product of the two casts; `mul_div_assoc` bridges the
  -- association).
  have hsumdiv :
      (∑ y ∈ stateFinset p.N p.m p.r,
        (y : Rat) * (transitionWeight p.N p.m p.r p.k x.val y)) =
      (∑ y ∈ stateFinset p.N p.m p.r,
        (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat)) /
        (transitionDenominator p.N p.m p.k : Rat) := by
    dsimp only [transitionWeight]
    -- Per term: `(y:Rat)·((num:Rat)/(den:Rat))` = `((y·num:Rat)/(den:Rat))`.
    have hper :
        (∑ y ∈ stateFinset p.N p.m p.r,
          (y : Rat) * ((transitionNumerator p.N p.m p.r p.k x.val y : Rat) /
            (transitionDenominator p.N p.m p.k : Rat))) =
        (∑ y ∈ stateFinset p.N p.m p.r,
          (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat) /
            (transitionDenominator p.N p.m p.k : Rat)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← mul_div_assoc]
    rw [hper, ← Finset.sum_div]

  -- Step 2: extend the `y`-sum over `stateFinset` to `range (m+1)`,
  -- mirroring `blRowStochastic`. The count vanishes below the window and
  -- above `r` (when the window top `blHi = r < m`), and the `y`-weight
  -- keeps the term zero (it is a pure `Nat` factor).
  have hsub : stateFinset p.N p.m p.r ⊆ Finset.range (p.m + 1) := by
    intro y hy
    simp only [stateFinset, blLo_def, blHi_def, Finset.mem_Icc, Finset.mem_range] at hy ⊢
    omega
  have hzero : (∑ y ∈ Finset.range (p.m + 1) \ stateFinset p.N p.m p.r,
      (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Finset.mem_sdiff, stateFinset, Finset.mem_Icc, Finset.mem_range] at hy
    by_cases hyl : y < blLo p.N p.m p.r
    · -- Below the window: the count is zero, so is `y·(0:Rat)`.
      have hym : y ≤ p.m := by omega
      have hnum0 : transitionNumerator p.N p.m p.r p.k x.val y = 0 :=
        num_zero_below_lo p x.val y hx hlo hyl hym
      rw [hnum0, Nat.cast_zero, mul_zero]
    · -- `y ≥ blLo` and `y ≤ m` but `y ∉ Icc (blLo) (blHi)`: so
      -- `y > blHi` while `y ≤ m`.
      have hle : blLo p.N p.m p.r ≤ y := Nat.le_of_not_lt hyl
      have hym : y ≤ p.m := by omega
      have hnot : ¬(y ≤ blHi p.N p.m p.r) := by
        intro hyy
        exact hy.2 ⟨hle, hyy⟩
      by_cases hmr : p.m ≤ p.r
      · -- `blHi = p.m`: `¬(y ≤ p.m)` contradicts `y ≤ p.m`.
        have hnot' : ¬(y ≤ p.m) := by
          simpa only [blHi_def, min_eq_left hmr] using hnot
        exact False.elim (hnot' hym)
      · -- `blHi = p.r`: `y > p.r`; the count is zero there.
        have hrle : p.r ≤ p.m := Nat.le_of_lt (Nat.not_le.mp hmr)
        have hnot' : ¬(y ≤ p.r) := by
          simpa only [blHi_def, min_eq_right hrle] using hnot
        have hyr : y > p.r := Nat.not_le.mp hnot'
        have hnum0 : transitionNumerator p.N p.m p.r p.k x.val y = 0 :=
          num_zero_above_r p x.val y hx hxr hyr
        rw [hnum0, Nat.cast_zero, mul_zero]
  have hext : (∑ y ∈ stateFinset p.N p.m p.r,
      (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat)) =
      (∑ y ∈ Finset.range (p.m + 1),
        (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat)) := by
    rw [← Finset.sum_sdiff hsub]
    rw [hzero, zero_add]
  rw [hsumdiv, hext]

  -- Step 3: the `y`-weighted numerator over `range (m+1)` is the
  -- `a`-sum of the per-`a` `y`-sums. Per `y`, `num y` is the `a`-sum of
  -- the `guardedTerm`s, so `y·(num y)` is (by `Finset.mul_sum`) the
  -- `a`-sum of `y·(g a y)`, and the casts line up by `Nat.cast_sum`.
  set g := fun (a : Nat) (y : Nat) => guardedTerm p.N p.m p.r p.k x.val a y
  have hperY :
      (∑ y ∈ Finset.range (p.m + 1),
        (y * transitionNumerator p.N p.m p.r p.k x.val y : Rat)) =
      (∑ y ∈ Finset.range (p.m + 1),
        (∑ a ∈ Finset.range (p.k + 1), (y * g a y : Rat))) := by
    apply Finset.sum_congr rfl
    intro y _
    -- `num y` is definitionally the `a`-sum of the `guardedTerm`s.
    have hnn : transitionNumerator p.N p.m p.r p.k x.val y =
        (∑ a ∈ Finset.range (p.k + 1), g a y) := by
      rw [transitionNumerator, show (∑ a ∈ Finset.range (p.k + 1),
          (if x.val - a ≤ y then
             if y - (x.val - a) ≤ p.k then
               Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) *
                 Nat.choose (p.r - x.val) (y - (x.val - a)) *
                 Nat.choose (p.N - p.m - (p.r - x.val)) (p.k - (y - (x.val - a)))
             else 0
           else 0)) = (∑ a ∈ Finset.range (p.k + 1), g a y) from rfl]
    -- The weighted RHS summand pulls `y` out of the `a`-sum, and the
    -- numerator is exactly that `a`-sum (`hnn`). Everything is a bare
    -- `Rat` ring term once the casts distribute over the products, so
    -- `mul_sum` / `Nat.cast_sum` apply at the `Rat` level.
    have hR : (∑ a ∈ Finset.range (p.k + 1), (y * g a y : Rat)) =
        (y * (∑ a ∈ Finset.range (p.k + 1), g a y) : Rat) := by
      -- After both rewrites the goal is `↑y·↑(∑ a, g a y) = (y·(∑ a, g a y):Rat)`
      -- and the ascription distributes, so `rw` auto-closes.
      rw [← Finset.mul_sum, ← Nat.cast_sum]
    -- `hR` rewrites the RHS sum to `y·(∑ a, g a y)`; `hnn` rewrites the LHS
    -- numerator (inside its `Rat` cast) to the same `a`-sum. The two sides
    -- then coincide, and `rw` auto-closes.
    rw [hR, hnn]
  have hinner : (∑ y ∈ Finset.range (p.m + 1),
      (∑ a ∈ Finset.range (p.k + 1), (y * g a y : Rat))) =
      (∑ a ∈ Finset.range (p.k + 1),
        (∑ y ∈ Finset.range (p.m + 1), (y * g a y : Rat))) := by
    rw [Finset.sum_comm]
  rw [hperY, hinner]

  -- Step 4: per `a`, reindex the `y`-sum by `innerYToB_w`. The
  -- `y`-weighted `guardedTerm` sum splits into the `(x-a)`-weighted and
  -- the `b`-weighted `exchangeTerm` sums.
  set E := fun (a b : Nat) => exchangeTerm p.N p.m p.r p.k x.val a b
  have hinner2 : (∑ a ∈ Finset.range (p.k + 1),
      (∑ y ∈ Finset.range (p.m + 1), (y * g a y : Rat))) =
      (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) * (∑ b ∈ Finset.range (p.k + 1), (E a b : Rat))) +
      (∑ a ∈ Finset.range (p.k + 1),
        (∑ b ∈ Finset.range (p.k + 1), (b : Rat) * (E a b : Rat))) := by
    -- The `y`-summand is the `gProd` wrapper (`y * (g a y)`).
    have h1 : (∑ a ∈ Finset.range (p.k + 1),
        (∑ y ∈ Finset.range (p.m + 1), (y * g a y : Rat))) =
        (∑ a ∈ Finset.range (p.k + 1),
          (∑ y ∈ Finset.range (p.m + 1), (gProd p.N p.m p.r p.k x.val a y : Rat))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      rw [gProd, Nat.cast_mul]
    rw [h1]
    -- Per `a`, `innerYToB_w` splits the `y`-sum into the two `b`-sums;
    -- then the `a`-sum splits over that `+` (`Finset.sum_add_distrib`).
    rw [Finset.sum_congr rfl (fun a (ha : a ∈ Finset.range (p.k + 1)) => by
      simp only [Finset.mem_range] at ha
      exact innerYToB_w p.N p.m p.r p.k x.val a hx (by
        -- `a < k + 1`, so `a ≤ k`.
        omega))]
    rw [Finset.sum_add_distrib]
  rw [hinner2]

  -- Step 5: evaluate the two `b`-sums (`bSumE`, `bSumE_w`). The window
  -- bound `r - x ≤ N - m` holds because `blLo ≤ x`.
  have hsubwin : p.r - x.val ≤ p.N - p.m := by
    have hlo2 : p.r - (p.N - p.m) ≤ x.val :=
      (Nat.le_max_left (p.r - (p.N - p.m)) 0).trans hlo
    by_cases h2m : p.r ≤ p.N - p.m
    · -- `r ≤ N - m`: `r - x ≤ r ≤ N - m`.
      calc
        p.r - x.val ≤ p.r := Nat.sub_le p.r x.val
        _ ≤ p.N - p.m := h2m
    · -- `r > N - m`: `r - (N - m) ≤ x` is a genuine subtraction.
      have hle : p.r ≤ x.val + (p.N - p.m) :=
        (Nat.sub_le_iff_le_add).mp hlo2
      have hle2 : p.r ≤ (p.N - p.m) + x.val := by
        rw [Nat.add_comm] at hle
        exact hle
      exact (Nat.sub_le_iff_le_add).mpr hle2
  -- Combine the two `b`-sum pieces into a sum of their closed forms.
  -- Split the `a`-sum over the `+` (keeping the `+` outside the summand,
  -- per the parser-bug workaround), then close each `b`-sum per `a`
  -- (`bSumE` / `bSumE_w`).
  have hcomb :
      (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) * (∑ b ∈ Finset.range (p.k + 1), (E a b : Rat))) +
      (∑ a ∈ Finset.range (p.k + 1),
        (∑ b ∈ Finset.range (p.k + 1), (b : Rat) * (E a b : Rat))) =
      (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) *
          (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) *
            Nat.choose (p.N - p.m) p.k : Rat)) +
      (∑ a ∈ Finset.range (p.k + 1),
        (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) : Rat) *
        ((p.k : Rat) * (p.r - x.val : Rat) / (p.N - p.m : Rat) *
          (Nat.choose (p.N - p.m) p.k : Rat))) := by
    -- The `+` is at the top level (the `hinner2` split); rewrite each of the
    -- two `a`-sums per `a` (`bSumE` / `bSumE_w`).
    rw [show (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) * (∑ b ∈ Finset.range (p.k + 1), (E a b : Rat))) =
        (∑ a ∈ Finset.range (p.k + 1),
          ((x.val : Rat) - (a : Rat)) *
            (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) *
              Nat.choose (p.N - p.m) p.k : Rat)) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [bSumE p.N p.m p.r p.k x.val a hsubwin],
        show (∑ a ∈ Finset.range (p.k + 1),
          (∑ b ∈ Finset.range (p.k + 1), (b : Rat) * (E a b : Rat))) =
          (∑ a ∈ Finset.range (p.k + 1),
            (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) : Rat) *
            ((p.k : Rat) * (p.r - x.val : Rat) / (p.N - p.m : Rat) *
              (Nat.choose (p.N - p.m) p.k : Rat))) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [bSumE_w p.N p.m p.r p.k x.val a hmn hxr hsubwin]]
  rw [hcomb]

  -- Step 6: the two `a`-sums. The common `a`-factor is
  -- `F a = (C(x,a)·C(m-x,k-a) : Rat)`; the right-pile binomial
  -- `C(N-m,k)` and the hypergeometric mean factor `M = k·(r-x)/(N-m)`
  -- do not depend on `a` and come out of the sums.
  -- The common per-`a` binomial factor, the right-pile binomial, and the
  -- hypergeometric mean factor. None of these depends on `a` in the places
  -- that matter, so they come out of the sums.
  set F := fun (a : Nat) =>
    (Nat.choose x.val a : Rat) * (Nat.choose (p.m - x.val) (p.k - a) : Rat)
  set C3 := (Nat.choose (p.N - p.m) p.k : Rat)
  set M := (p.k : Rat) * (p.r - x.val : Rat) / (p.N - p.m : Rat)

  -- The first `a`-sum: `∑ a, (x-a)·(C1·C2·C3) = C3·∑ a, (x-a)·F a`.
  have hA : (∑ a ∈ Finset.range (p.k + 1),
      ((x.val : Rat) - (a : Rat)) *
        (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) *
          Nat.choose (p.N - p.m) p.k : Rat)) =
      C3 * (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) * F a) := by
    -- The ascription on the 3-factor product is `((C1·C2)·C3)`, so the
    -- summand is `(x-a)·(F a)·C3`; `ring` normalizes the association.
    have h1 : (∑ a ∈ Finset.range (p.k + 1),
        ((x.val : Rat) - (a : Rat)) *
          (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) *
            Nat.choose (p.N - p.m) p.k : Rat)) =
        (∑ a ∈ Finset.range (p.k + 1),
          ((x.val : Rat) - (a : Rat)) * F a * C3) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    -- Pull the constant `C3` out of the sum, then commute to the left.
    rw [h1, ← Finset.sum_mul, mul_comm]
  -- The second `a`-sum: `∑ a, F a·M·C3 = (M·C3)·∑ a, F a`.
  -- The second `a`-sum: `∑ a, (C1·C2)·(M·C3) = (M·C3)·∑ a, F a`.
  have hB : (∑ a ∈ Finset.range (p.k + 1),
      (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) : Rat) *
      ((p.k : Rat) * (p.r - x.val : Rat) / (p.N - p.m : Rat) *
        (Nat.choose (p.N - p.m) p.k : Rat))) =
      M * C3 * (∑ a ∈ Finset.range (p.k + 1), F a) := by
    -- The summand is `F a·M·C3`; pull the constant `M·C3` out.
    have h1 : (∑ a ∈ Finset.range (p.k + 1),
        (Nat.choose x.val a * Nat.choose (p.m - x.val) (p.k - a) : Rat) *
        ((p.k : Rat) * (p.r - x.val : Rat) / (p.N - p.m : Rat) *
          (Nat.choose (p.N - p.m) p.k : Rat))) =
        (∑ a ∈ Finset.range (p.k + 1), F a * (M * C3)) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    -- Pull the constant `M·C3` out, then commute to the left.
    rw [h1, ← Finset.sum_mul, mul_comm]

  -- Pull `C3` out of both `a`-sums.
  rw [hA, hB]

  -- Step 7: the `a`-sums. Let `S = ∑ a, F a = C(m,k)` (`aSumE`) and
  -- `∑ a, (a:Rat)·F a = (k·x/m)·C(m,k)` (`chooseSum_weighted`). Then
  -- `∑ a, (x-a)·F a = x·S - (k·x/m)·S` and the hypergeometric-mean
  -- factor is constant.
  -- `∑ a, F a = C(m,k)` (`aSumE`); `F a` unfolds to the explicit product.
  have hS : (∑ a ∈ Finset.range (p.k + 1), F a) = (Nat.choose p.m p.k : Rat) := by
    have h1 : (∑ a ∈ Finset.range (p.k + 1), F a) =
        (∑ a ∈ Finset.range (p.k + 1),
          (Nat.choose x.val a : Rat) * (Nat.choose (p.m - x.val) (p.k - a) : Rat)) := by
      apply Finset.sum_congr rfl
      intro a _
      rfl
    rw [h1, aSumE p.m x.val p.k hx]
  -- `∑ a, a·F a = (k·x/m)·C(m,k)` (`chooseSum_weighted`).
  have hwa : (∑ a ∈ Finset.range (p.k + 1), (a : Rat) * F a) =
      (p.k : Rat) * (x.val : Rat) / (p.m : Rat) * (Nat.choose p.m p.k : Rat) := by
    have h1 : (∑ a ∈ Finset.range (p.k + 1), (a : Rat) * F a) =
        (∑ a ∈ Finset.range (p.k + 1),
          (a : Rat) * (Nat.choose x.val a : Rat) *
            (Nat.choose (p.m - x.val) (p.k - a) : Rat)) := by
      apply Finset.sum_congr rfl
      intro a _
      -- `a·(C1·C2)` vs `(a·C1)·C2`: same product up to association.
      ring
    rw [h1, chooseSum_weighted p.m x.val p.k hx]
  -- `∑ a, (x-a)·F a = (∑ a, x·F a) - (∑ a, a·F a)`.
  have hxs : (∑ a ∈ Finset.range (p.k + 1),
      ((x.val : Rat) - (a : Rat)) * F a) =
      (∑ a ∈ Finset.range (p.k + 1), (x.val : Rat) * F a) -
      (∑ a ∈ Finset.range (p.k + 1), (a : Rat) * F a) := by
    -- Split the difference of sums; per `a`, `(x-a)·F a = x·F a - a·F a`.
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  -- `∑ a, x·F a = x·(∑ a, F a)` (the constant `x` out of the sum).
  have hxs2 : (∑ a ∈ Finset.range (p.k + 1), (x.val : Rat) * F a) =
      (x.val : Rat) * (∑ a ∈ Finset.range (p.k + 1), F a) := by
    rw [← Finset.mul_sum]
  -- `∑ a, (x-a)·F a = (∑ a, F a)·(x - k·x/m)`.
  have hxS : (∑ a ∈ Finset.range (p.k + 1),
      ((x.val : Rat) - (a : Rat)) * F a) =
      (∑ a ∈ Finset.range (p.k + 1), F a) *
        ((x.val : Rat) - (p.k : Rat) * (x.val : Rat) / (p.m : Rat)) := by
    rw [hxs, hxs2, hwa]
    -- Replace `C(m,k)` by `∑ a, F a` (`hS`), then factor.
    rw [← hS]
    ring
  -- The numerator factors as `(∑ a, F a)·C3·(x - k·x/m + M)`; `hxS` is
  -- applied inside `hnumfact`, so the outer goal keeps the pre-`hxS` form.
  have hnumfact : C3 * (∑ a ∈ Finset.range (p.k + 1),
      ((x.val : Rat) - (a : Rat)) * F a) +
      M * C3 * (∑ a ∈ Finset.range (p.k + 1), F a) =
      (∑ a ∈ Finset.range (p.k + 1), F a) * C3 *
        ((x.val : Rat) - (p.k : Rat) * (x.val : Rat) / (p.m : Rat) + M) := by
    rw [hxS]
    ring
  have hden2 : (transitionDenominator p.N p.m p.k : Rat) =
      (Nat.choose p.m p.k : Rat) * (Nat.choose (p.N - p.m) p.k : Rat) := by
    rw [transitionDenominator, Nat.cast_mul]
  have hden3 : (transitionDenominator p.N p.m p.k : Rat) =
      (∑ a ∈ Finset.range (p.k + 1), F a) * C3 := by
    rw [hden2, ← hS]
  rw [hnumfact]
  -- Clear the division: the numerator is `(∑ a, F a)·C3·(x - k·x/m + M)`
  -- and the denominator is `(∑ a, F a)·C3`.
  have hsc3 : (∑ a ∈ Finset.range (p.k + 1), F a) * C3 ≠ 0 := by
    have hSpos : 0 < (∑ a ∈ Finset.range (p.k + 1), F a) := by
      -- `∑ a, F a = C(m,k)` and `0 < C(m,k)`.
      rw [hS]
      exact Nat.cast_pos.mpr (Nat.choose_pos p.hkm)
    have hC3pos : 0 < C3 := Nat.cast_pos.mpr (Nat.choose_pos p.hknm)
    have hpos : 0 < (∑ a ∈ Finset.range (p.k + 1), F a) * C3 := mul_pos hSpos hC3pos
    intro h
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  have hm0 : (p.m : Rat) ≠ 0 := by
    intro h
    have hpos : 0 < (p.m : Rat) := Nat.cast_pos.mpr p.h0m
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  have hnm0 : (p.N - p.m : Rat) ≠ 0 := by
    intro h
    have hpos : 0 < (p.N - p.m : Rat) := by
      -- `(N-m : Rat)` = `(N:Rat) - (m:Rat)` = `↑(N-m)`.
      rw [show (p.N - p.m : Rat) = (p.N : Rat) - (p.m : Rat) from rfl,
          ← Nat.cast_sub (Nat.le_of_lt hmn)]
      exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt hmn)
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  field_simp [hden3, hsc3, hden, hm0, hnm0, Nat.cast_ne_zero]
  -- `field_simp` cleared the divisions; both sides now share the factor
  -- `(x·m - x·k + m·M)`, and the remaining difference is exactly `hden3`.
  rw [hden3]
  -- The remaining goal is a polynomial identity over `Rat` in the atoms
  -- `∑ a, F a`, `C3`, `x`, `k`, `m`, `M`: `ring` closes it.
  ring

/-! G4: the first *centered* eigenfunction. The centered observable
`f(x) = x - μ` (stationary mean `μ = m·r/N`) satisfies
`applyFn (blExchangeKernel p) f = blFirstModeFactor • f`: the conditional
mean (`blConditionalMean`) is affine in `x`, the kernel is stochastic
(`blRowStochastic`), and the stationary mean `μ` is a fixed point of the
conditional mean, so the centered mean is a scalar multiple of the
centered state. This is the first centered linear mode; it is not a claim
about the largest nontrivial eigenvalue in absolute value. -/

theorem blFirstModeFunc (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    applyFn (blExchangeKernel p) (fun y =>
      (y.val : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat)) x =
      blFirstModeFactor p.N p.m p.k *
        ((x.val : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat)) := by
  set μ := (p.m : Rat) * (p.r : Rat) / (p.N : Rat)
  -- `applyFn` is the `stateFinset` mass-weighted sum of the centered
  -- observable; bridge `Finset.univ` to `stateFinset` via the `val`
  -- bijection (the kernel's `ofFun` mass is the raw `transitionWeight`).
  have happly :
      applyFn (blExchangeKernel p) (fun (y : BLState p.N p.m p.r) => (y.val : Rat) - μ) x =
      (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionWeight p.N p.m p.r p.k x.val y : Rat) * ((y : Rat) - μ)) := by
    dsimp only [applyFn, blExchangeKernel]
    simp only [Dist.mass_ofFun]
    apply Finset.sum_bij
      (fun (y : BLState p.N p.m p.r) (_ : y ∈ Finset.univ) => y.val)
    · -- image in `stateFinset`
      intro y _
      simp only [stateFinset, Finset.mem_Icc]
      exact ⟨y.2.1, y.2.2⟩
    · -- injective
      intro y1 _ y2 _ h12
      exact Subtype.coe_injective h12
    · -- surjective onto `stateFinset`
      intro z hz
      simp only [stateFinset, Finset.mem_Icc] at hz
      exact ⟨⟨z, hz⟩, Fintype.complete _, rfl⟩
    · -- the summand is the raw formula at `y.val`
      intro y _
      rfl
  rw [happly]
  -- Linearity: `∑ W·(y - μ) = ∑ y·W - μ·∑ W`. Work backwards from the
  -- target so the `∑, (· - ·)` form only ever appears as a goal state, not
  -- in source (the `+`/`-`-inside-`∑` parser bug).
  have hsplit :
      (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionWeight p.N p.m p.r p.k x.val y : Rat) * ((y : Rat) - μ)) =
      (∑ y ∈ stateFinset p.N p.m p.r,
        (y : Rat) * (transitionWeight p.N p.m p.r p.k x.val y : Rat)) -
      μ * (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionWeight p.N p.m p.r p.k x.val y : Rat)) := by
    apply Eq.symm
    -- `μ·(∑ W) = ∑ μ·W`; then `(∑ y·W) - (∑ μ·W) = ∑ (y·W - μ·W)`;
    -- per `y`, `y·W - μ·W = W·(y - μ)`.
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsplit]
  -- `∑ W·y` is the conditional mean; `∑ W` is `1` (row stochasticity).
  have hmass : (∑ y ∈ stateFinset p.N p.m p.r,
      (transitionWeight p.N p.m p.r p.k x.val y : Rat)) = 1 := by
    have h1 : (∑ y ∈ stateFinset p.N p.m p.r,
        (transitionWeight p.N p.m p.r p.k x.val y : Rat)) =
        (∑ y ∈ stateFinset p.N p.m p.r,
          (transitionNumerator p.N p.m p.r p.k x.val y : Rat) /
            (transitionDenominator p.N p.m p.k : Rat)) := by
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [transitionWeight]
    rw [h1, blRowStochastic p x]
  rw [blConditionalMean p x, hmass]
  -- Now: `x - (k/m)·x + (k/(N-m))·(r-x) - μ = blFirstModeFactor·(x - μ)`.
  -- Clear the divisions and close the polynomial identity.
  have hm0 : (p.m : Rat) ≠ 0 := by
    intro h
    have hpos : 0 < (p.m : Rat) := Nat.cast_pos.mpr p.h0m
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  have hnm0 : (p.N - p.m : Rat) ≠ 0 := by
    intro h
    have hpos : 0 < (p.N - p.m : Rat) := by
      rw [show (p.N - p.m : Rat) = (p.N : Rat) - (p.m : Rat) from rfl,
          ← Nat.cast_sub (Nat.le_of_lt p.hmn)]
      exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt p.hmn)
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  have hN0 : (p.N : Rat) ≠ 0 := by
    intro h
    have hpos : 0 < (p.N : Rat) := Nat.cast_pos.mpr (Nat.lt_trans p.h0m p.hmn)
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  -- Unfold the first-mode factor and the local mean `μ` (both have internal
  -- divisions) before clearing, so the result is a pure polynomial in
  -- `x`, `k`, `m`, `N`, `r` that `ring` closes.
  dsimp only [blFirstModeFactor, μ]
  field_simp [hm0, hnm0, hN0, Nat.cast_ne_zero]
  ring

  /-- `a - b < c` from `a < b + c` and `b ≤ a` (the subtraction is proper, so
  `a - b + b = a < b + c`; commute and cancel `b`). Used to show the
  admissible interval's lower end stays below the smaller pile size. -/
  lemma subLtM {a b c : Nat} (h : a < b + c) (hb : b ≤ a) : a - b < c := by
    have hsum : a - b + b = a := Nat.sub_add_cancel hb
    have hlt : a - b + b < b + c := by
      rw [hsum]
      exact h
    have hlt2 : b + (a - b) < b + c := by
      rw [show a - b + b = b + (a - b) from Nat.add_comm (a - b) b] at hlt
      exact hlt
    linarith

  /-- Nonzero-eigenfunction companion to `blFirstModeFunc`. The bare identity
  `K f = λ₁ f` remains true in the degenerate cases `r = 0` and `r = N`, but
  there the macrostate space collapses to a *single* state and
  `f(x) = x - m·r/N` vanishes at that state, so the equation is the vacuous
  `0 = λ₁·0` and `λ₁` is not yet a genuine eigenvalue. Under
  `0 < r < N` (with the admissible `0 < m < N`) the interval
  `blLo .. blHi` has at least two distinct states and the centered observable
  (affine, slope 1) is not identically zero, so `blFirstModeFactor` is an
  actual eigenvalue with a nonzero eigenfunction. This isolates the
  eigenfunction *identity* (`blFirstModeFunc`) from the *existence* of a
  nonzero eigenfunction. -/
  theorem blFirstModeFunc_nonzero (p : ExchangeAdmissible)
      (h0 : 0 < p.r) (hN : p.r < p.N) :
      ∃ x : BLState p.N p.m p.r,
        (x.val : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat) ≠ 0 := by
    -- The lower end of the admissible interval sits strictly below both pile
    -- sizes, hence below `blHi = min m r`, so the interval holds ≥2 states:
    --   * `r - (N - m) < r`  (from `0 < r`, `0 < N - m`);
    --   * `r - (N - m) < m`  (from `r < N = (N - m) + m`, `0 < m`).
    have hlo : blLo p.N p.m p.r = p.r - (p.N - p.m) := by
      simp only [blLo_def]
      simp
    have hblLo_r : p.r - (p.N - p.m) < p.r := by
      have hLpos : 0 < p.N - p.m := Nat.sub_pos_of_lt p.hmn
      omega
    have hblLo_m : p.r - (p.N - p.m) < p.m := by
      by_cases hle : p.N - p.m ≤ p.r
      · -- proper subtraction: `r < N = (N - m) + m`, so `r - (N - m) < m`.
        have h : p.r < (p.N - p.m) + p.m := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt p.hmn)]
          exact hN
        exact subLtM h hle
      · -- `r < N - m`, so `r - (N - m) = 0 < m`.
        have hlt : p.r < p.N - p.m := Nat.not_le.mp hle
        rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
        exact p.h0m
    have hlo_lt_hi : blLo p.N p.m p.r < blHi p.N p.m p.r := by
      rw [hlo, blHi_def]
      simp only [lt_min_iff]
      exact ⟨hblLo_m, hblLo_r⟩
    -- Two concrete distinct states: `blLo` and `blLo + 1`.
    have hxlo : blLo p.N p.m p.r ≤ blHi p.N p.m p.r := Nat.le_of_lt hlo_lt_hi
    have hxlo1 : blLo p.N p.m p.r + 1 ≤ blHi p.N p.m p.r := by
      omega
    -- If the centered observable vanished at every state it would vanish at
    -- both `blLo` and `blLo + 1`; their centered values differ by exactly
    -- `1`, so that is impossible.
    by_contra h
    have hforall : ∀ (x : BLState p.N p.m p.r),
        (x.val : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat) = 0 := by
      intro x
      by_contra hne
      exact h ⟨x, hne⟩
    -- At `val = blLo`: the centered value is `↑blLo - c = 0`.
    have hA : (blLo p.N p.m p.r : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat) = 0 :=
      hforall ⟨blLo p.N p.m p.r, ⟨Nat.le_refl _, hxlo⟩⟩
    -- At `val = blLo + 1`: the centered value is `↑(blLo + 1) - c = 0`, i.e.
    -- `↑blLo + 1 - c = 0` since `↑(blLo + 1) = ↑blLo + 1`.
    have hB : (blLo p.N p.m p.r : Rat) + 1 - (p.m : Rat) * (p.r : Rat) / (p.N : Rat) = 0 := by
      have h := hforall ⟨blLo p.N p.m p.r + 1, ⟨by omega, hxlo1⟩⟩
      have hcast : (Nat.cast (blLo p.N p.m p.r + 1) : Rat) =
          (blLo p.N p.m p.r : Rat) + 1 := by
        simp only [Nat.cast_succ]
      rw [hcast] at h
      exact h
    -- `↑blLo - c = 0` and `↑blLo + 1 - c = 0` together force `1 = 0`.
    linarith

end BernoulliLaplaceGeneral
end Shufflemath
