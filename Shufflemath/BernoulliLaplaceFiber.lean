/-
Detailed balance for the general Bernoulli--Laplace exchange kernel,
proved by counting the microscopic exchange fiber.

Separated from `BernoulliLaplaceGeneral.lean` (2026-10-08 cleanup):
the ~950 lines of fiber machinery are the proof scaffolding for the
three theorems at the end of this file (`blDetailedBalance`,
`blStationaryDist_is_stationary`, `blStationaryRun`). Keeping them
out of the main general-theory file keeps that file readable; this
file is the single place to look (or eventually delete) if the fiber
counting is superseded by a lighter detailed-balance proof.
Stationarity itself is the generic `stationary_of_detailedBalance`
(`Shufflemath/Markov.lean`) applied to `blDetailedBalance` — no
local TV machinery.

Dependency direction is one-way: this module imports
`Shufflemath.BernoulliLaplaceGeneral` (for `ExchangeAdmissible`,
`BLState`, `transitionWeight`, `blStationary`, `blStationaryDist`,
`blExchangeKernel`, `stateFinset`); the general file does NOT import
this one, and both are listed in the library root `Shufflemath.lean`,
so no import cycle can form.
-/
import Shufflemath.BernoulliLaplaceGeneral
import Shufflemath.Markov
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Order
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace Shufflemath
namespace BernoulliLaplaceGeneral

variable {N m r k : Nat}

/-! ## Detailed balance, part 1: the exchange fiber and its count

The exchange step "move `k` cards from the top pile `S` to the bottom and
`k` cards back" is counted by 7-tuples `(S1, S2, a, A1, A2, B1, B2)`:
`S1 ⊆ stars`, `|S1| = x`, `S2 ⊆ plain`, `|S2| = m - x` (the pile `S`),
`a` specials moved out (`A1`, `|A1| = a`), `A2` ordinary cards moved out
(`|A2| = k - a`), `B1` specials moved in (`|B1| = y - (x - a)`), and
`B2` ordinary cards moved in (`|B2| = k - (y - (x - a))`).  The new pile
has `x - a + (y - (x - a)) = y` specials, so the fiber count with the
numerator guard is exactly
`choose r x * choose (N - r) (m - x) * transitionNumerator x y`.

The involution `(S, A, B) ↦ (S \ A ∪ B, B, A)` then swaps the fiber of
`(x, y)` with that of `(y, x)`, giving detailed balance.
-/

section detailedBalance

variable (p : ExchangeAdmissible)

/-- The universe of special cards (there are `r` of them) and the universe
of ordinary cards (there are `N - r` of them), as concrete `Fin` types.
Choosing a pile `S` of size `m` with `x` specials is the same as choosing
`S1 ⊆ starsUniv` with `|S1| = x` and `S2 ⊆ plainUniv` with
`|S2| = m - x`. -/
private def starsUniv (p : ExchangeAdmissible) : Finset (Fin p.r) :=
  Finset.univ

private def plainUniv (p : ExchangeAdmissible) : Finset (Fin (p.N - p.r)) :=
  Finset.univ

/-- The exchange fiber count for the macrostate pair `(x, y)`: see the
section comment. -/
private def fiberSum (p : ExchangeAdmissible) (x y : Nat) : Nat :=
  ∑ S1 ∈ (starsUniv p).powersetCard x,
  ∑ S2 ∈ (plainUniv p).powersetCard (p.m - x),
  ∑ a ∈ (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k),
      (∑ _A1 ∈ S1.powersetCard a,
      ∑ _A2 ∈ S2.powersetCard (p.k - a),
      ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
      ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)

/-- A sum of constant `1`s over a finset is its cardinality. -/
private theorem sumOnes {α : Type*} (s : Finset α) : (∑ _x ∈ s, 1 : Nat) = s.card := by
  rw [Finset.sum_const_nat (fun _ _ => rfl)]
  simp

/-- The `(A, B)` part of the fiber, given the pile `(S1, S2)` and the
special-exchange index `a`: the four nested sums of `1`s collapse to the
product of the four `powersetCard` cardinalities. -/
private theorem fiberABcount (p : ExchangeAdmissible) (x y a : Nat)
    (S1 : Finset (Fin p.r)) (_hS1 : S1 ∈ (starsUniv p).powersetCard x)
    (S2 : Finset (Fin (p.N - p.r))) (_hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x))
    (_ha : a ∈ Finset.range (p.k + 1)) :
    (∑ _A1 ∈ S1.powersetCard a,
    ∑ _A2 ∈ S2.powersetCard (p.k - a),
    ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
    ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
    (S1.powersetCard a).card * (S2.powersetCard (p.k - a)).card *
      ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
      ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
  have h4 :
      (∑ B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
        ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [sumOnes]
  have h3 :
      (∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
        (∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)) =
        ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
          ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [h4, Finset.sum_const_nat (fun _ _ => rfl)]
  have h2 :
      (∑ _A2 ∈ S2.powersetCard (p.k - a),
        (∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
          (∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1))) =
        (S2.powersetCard (p.k - a)).card *
          ((starsUniv p \ S1).powersetCard (y - (x - a))).card *
          ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card := by
    rw [h3, Finset.sum_const_nat (fun _ _ => rfl)]
    ring_nf
  rw [h2, Finset.sum_const_nat (fun _ _ => rfl)]
  ring_nf


/-- Given the pile and the index `a`, the `(A, B)` part of the fiber is
the product of the four `powersetCard` cardinalities, i.e. the
`a`-summand factors with the plain-card count written as
`(N - r) - (m - x)`. -/
private theorem fiberABchoose (p : ExchangeAdmissible) (x y a : Nat)
    (S1 : Finset (Fin p.r)) (hS1 : S1 ∈ (starsUniv p).powersetCard x)
    (S2 : Finset (Fin (p.N - p.r))) (hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x))
    (ha : a ∈ Finset.range (p.k + 1))
    (_hg : x - a ≤ y ∧ y - (x - a) ≤ p.k) :
    (∑ _A1 ∈ S1.powersetCard a,
    ∑ _A2 ∈ S2.powersetCard (p.k - a),
    ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
    ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1) =
    Nat.choose x a * Nat.choose (p.m - x) (p.k - a) *
      Nat.choose (p.r - x) (y - (x - a)) *
      Nat.choose ((p.N - p.r) - (p.m - x)) (p.k - (y - (x - a))) := by
  have hS1c : S1.card = x := (Finset.mem_powersetCard.1 hS1).2
  have hS2c : S2.card = p.m - x := (Finset.mem_powersetCard.1 hS2).2
  have hS1s : S1 ⊆ starsUniv p := (Finset.mem_powersetCard.1 hS1).1
  have hS2s : S2 ⊆ plainUniv p := (Finset.mem_powersetCard.1 hS2).1
  rw [fiberABcount p x y a S1 hS1 S2 hS2 ha]
  rw [Finset.card_powersetCard, Finset.card_powersetCard, hS1c, hS2c]
  have h3c : ((starsUniv p \ S1).powersetCard (y - (x - a))).card =
      (p.r - x).choose (y - (x - a)) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff]
    have hi : S1 ∩ starsUniv p = S1 := Finset.inter_eq_left.mpr hS1s
    rw [hi]
    have hcard : (starsUniv p).card - S1.card = p.r - x := by
      show (Finset.univ : Finset (Fin p.r)).card - S1.card = p.r - x
      rw [Finset.card_fin p.r, hS1c]
    rw [hcard]
  rw [h3c]
  have h4c : ((plainUniv p \ S2).powersetCard (p.k - (y - (x - a)))).card =
      ((p.N - p.r) - (p.m - x)).choose (p.k - (y - (x - a))) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff]
    have hi : S2 ∩ plainUniv p = S2 := Finset.inter_eq_left.mpr hS2s
    rw [hi]
    have hcard : (plainUniv p).card - S2.card = (p.N - p.r) - (p.m - x) := by
      show (Finset.univ : Finset (Fin (p.N - p.r))).card - S2.card =
        (p.N - p.r) - (p.m - x)
      rw [Finset.card_fin (p.N - p.r), hS2c]
    rw [hcard]
  rw [h4c]

/-! The main counting lemma: the exchange fiber of `(x, y)` factors into
the stationary-weight factors and the transition numerator. -/
private theorem fiberSum_eq (p : ExchangeAdmissible) (x y : Nat)
    (hx : x ∈ stateFinset p.N p.m p.r) :
    fiberSum p x y =
      Nat.choose p.r x * Nat.choose (p.N - p.r) (p.m - x) *
        transitionNumerator p.N p.m p.r p.k x y := by
  have hlo : blLo p.N p.m p.r ≤ x := by
    simp only [stateFinset, Finset.mem_Icc] at hx
    exact hx.1
  have hhi : x ≤ blHi p.N p.m p.r := by
    simp only [stateFinset, Finset.mem_Icc] at hx
    exact hx.2
  have hxm : x ≤ p.m := hhi.trans (Nat.min_le_left p.m p.r)
  have hxr : x ≤ p.r := hhi.trans (Nat.min_le_right p.m p.r)
  -- The two plain-card counts `(N - r) - (m - x)` and `(N - m) - (r - x)`
  -- agree for `x` in the window: both sides are exact exactly when
  -- `m + r - x ≤ N`, and in that case both equal `N - r - m + x`;
  -- otherwise both saturate to `0`.
  have hfour : (p.N - p.r) - (p.m - x) = (p.N - p.m) - (p.r - x) := by
    by_cases hsum : p.m + p.r ≤ p.N + x
    · -- Both differences are exact.
      have h1 : p.m - x ≤ p.N - p.r := by
        have hA : p.m + p.r - x ≤ p.N := (Nat.sub_le_iff_le_add).mpr (by omega)
        have hB : p.r + (p.m - x) = (p.m + p.r) - x := by
          simpa [Nat.add_comm] using (Nat.add_sub_assoc hxm p.r).symm
        have hC : (p.m - x) + p.r ≤ p.N := by
          simpa [Nat.add_comm, hB] using hA
        exact (Nat.le_sub_iff_add_le p.hrN).mpr hC
      have h2 : p.r - x ≤ p.N - p.m := by
        have hA : p.m + p.r - x ≤ p.N := (Nat.sub_le_iff_le_add).mpr (by omega)
        have hB : p.m + (p.r - x) = (p.m + p.r) - x := by
          simpa [Nat.add_comm] using (Nat.add_sub_assoc hxr p.m).symm
        have hC : p.m + (p.r - x) ≤ p.N := by
          simpa [hB] using hA
        have hC' : p.r - x + p.m ≤ p.N := by
          simpa [Nat.add_comm] using hC
        exact (Nat.le_sub_iff_add_le p.hmn.le).mpr hC'
        
      have hL : (↑((p.N - p.r) - (p.m - x)) : ℤ) =
          (p.N : ℤ) - (p.r : ℤ) - (p.m : ℤ) + (x : ℤ) := by
        rw [Int.ofNat_sub h1, Int.ofNat_sub p.hrN, Int.ofNat_sub hxm]
        ring
      have hR : (↑((p.N - p.m) - (p.r - x)) : ℤ) =
          (p.N : ℤ) - (p.m : ℤ) - (p.r : ℤ) + (x : ℤ) := by
        rw [Int.ofNat_sub h2, Int.ofNat_sub p.hmn.le, Int.ofNat_sub hxr]
        ring
      have heq : (↑((p.N - p.r) - (p.m - x)) : ℤ) =
          (↑((p.N - p.m) - (p.r - x)) : ℤ) := by
        rw [hL, hR]
        ring
      exact Int.natCast_inj.mp heq
    · -- `m + r > N + x`: both differences saturate to `0`.
      have hL0 : (p.N - p.r) - (p.m - x) = 0 := by
        have hK : p.N - p.r ≤ p.m - x := by
          have h1 : (↑(p.N - p.r) : ℤ) ≤ (↑(p.m - x) : ℤ) := by
            rw [Int.ofNat_sub p.hrN, Int.ofNat_sub hxm]
            have hsum' : (p.N : ℤ) + (x : ℤ) < (p.m : ℤ) + (p.r : ℤ) := by
              norm_cast
              omega
            linarith
          exact Int.ofNat_le.mp h1
        rw [Nat.sub_eq_zero_iff_le]
        exact hK
      have hR0 : (p.N - p.m) - (p.r - x) = 0 := by
        have hK : p.N - p.m ≤ p.r - x := by
          have h1 : (↑(p.N - p.m) : ℤ) ≤ (↑(p.r - x) : ℤ) := by
            rw [Int.ofNat_sub p.hmn.le, Int.ofNat_sub hxr]
            have hsum' : (p.N : ℤ) + (x : ℤ) < (p.m : ℤ) + (p.r : ℤ) := by
              norm_cast
              omega
            linarith
          exact Int.ofNat_le.mp h1
        rw [Nat.sub_eq_zero_iff_le]
        exact hK
      rw [hL0, hR0]
  dsimp only [fiberSum]
  -- The `(A, B)` fiber of a fixed pile `(S1, S2)` and index `a` is the
  -- `a`-summand of the transition numerator.
  have hnum (S1 : Finset (Fin p.r))
      (hS1 : S1 ∈ (starsUniv p).powersetCard x)
      (S2 : Finset (Fin (p.N - p.r)))
      (hS2 : S2 ∈ (plainUniv p).powersetCard (p.m - x)) :
      (∑ a ∈ (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k),
          (∑ _A1 ∈ S1.powersetCard a,
          ∑ _A2 ∈ S2.powersetCard (p.k - a),
          ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
          ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)) =
      transitionNumerator p.N p.m p.r p.k x y := by
    rw [transitionNumerator]
    -- The filter-domain a-sum equals the ite-sum over the full range.
    rw [Finset.sum_filter (fun a : Nat => x - a ≤ y ∧ y - (x - a) ≤ p.k) _]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only
    by_cases c1 : x - a ≤ y
    · by_cases c2 : y - (x - a) ≤ p.k
      · -- Both ite branches select the positive side: `simp` has already
        -- unfolded the four level sums into a product of `choose` factors
        -- indexed by the pile cards.
        simp [c1, c2]
        have hS1if : S1 ∈ (starsUniv p).powersetCard x ↔
            S1 ⊆ starsUniv p ∧ S1.card = x := Finset.mem_powersetCard
        have hS1c : S1.card = x := (hS1if.mp hS1).2
        have hS1s : S1 ⊆ starsUniv p := (hS1if.mp hS1).1
        have hS2if : S2 ∈ (plainUniv p).powersetCard (p.m - x) ↔
            S2 ⊆ plainUniv p ∧ S2.card = p.m - x := Finset.mem_powersetCard
        have hS2c : S2.card = p.m - x := (hS2if.mp hS2).2
        have hS2s : S2 ⊆ plainUniv p := (hS2if.mp hS2).1
        have hU1 : (starsUniv p \ S1).card = p.r - x := by
          rw [Finset.card_sdiff]
          have hi : S1 ∩ starsUniv p = S1 := Finset.inter_eq_left.mpr hS1s
          rw [hi]
          have hcard : (starsUniv p).card - S1.card = p.r - x := by
            show (Finset.univ : Finset (Fin p.r)).card - S1.card = p.r - x
            rw [Finset.card_fin p.r, hS1c]
          rw [hcard]
        have hU2 : (plainUniv p \ S2).card = (p.N - p.r) - (p.m - x) := by
          rw [Finset.card_sdiff]
          have hi : S2 ∩ plainUniv p = S2 := Finset.inter_eq_left.mpr hS2s
          rw [hi]
          have hcard : (plainUniv p).card - S2.card =
              (p.N - p.r) - (p.m - x) := by
            show (Finset.univ : Finset (Fin (p.N - p.r))).card - S2.card =
              (p.N - p.r) - (p.m - x)
            rw [Finset.card_fin (p.N - p.r), hS2c]
          rw [hcard]
        rw [hS1c, hS2c, hU1, hU2, hfour]
        ring
      · simp [c1, c2]
    · by_cases c2 : y - (x - a) ≤ p.k
      · simp [c1, c2]
      · simp [c1, c2]
  -- Peel off the pile sums: the `a`-sum is the same for every pile.
  rw [Finset.sum_congr rfl (fun S1 hS1 => Finset.sum_congr rfl (fun S2 hS2 => hnum S1 hS1 S2 hS2))]
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.sum_const_nat (fun _ _ => rfl)]
  rw [Finset.card_powersetCard, Finset.card_powersetCard]
  have hcard1 : (starsUniv p).card = p.r := by
    show (Finset.univ : Finset (Fin p.r)).card = p.r
    rw [Finset.card_fin p.r]
  have hcard2 : (plainUniv p).card = p.N - p.r := by
    show (Finset.univ : Finset (Fin (p.N - p.r))).card = p.N - p.r
    rw [Finset.card_fin (p.N - p.r)]
  rw [hcard1, hcard2]
  ring_nf


/-! ### Flat 7-tuple formulation for the involution argument

The exchange fiber is counted by a finset of 7-tuples `(S1, S2, a, A1, A2,
B1, B2)` drawn from the powersets of the two card universes and the index
range, restricted by a single predicate. The involution
`(S1, S2, a, A1, A2, B1, B2) ↦ (S1 \ A1 ∪ B1, S2 \ A2 ∪ B2, B1.card,
B1, B2, A1, A2)` is a bijection between the `(x, y)` and `(y, x)`
instances of this finset. -/

private abbrev fiber7Tuple (p : ExchangeAdmissible) :=
  (((((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) × Nat) ×
    Finset (Fin p.r)) × Finset (Fin (p.N - p.r))) × Finset (Fin p.r)) ×
  Finset (Fin (p.N - p.r))

private def tS1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.1.1
private def tS2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.1.2
private def tA {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.1.2
private def tA1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.1.2
private def tA2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.1.2
private def tB1 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.1.2
private def tB2 {p : ExchangeAdmissible} (t : fiber7Tuple p) := t.2

private def fiber7U1 (p : ExchangeAdmissible) :=
  (starsUniv p).powerset ×ˢ (plainUniv p).powerset
private def fiber7U2 (p : ExchangeAdmissible) := fiber7U1 p ×ˢ Finset.range (p.k + 1)
private def fiber7U3 (p : ExchangeAdmissible) := fiber7U2 p ×ˢ (starsUniv p).powerset
private def fiber7U4 (p : ExchangeAdmissible) := fiber7U3 p ×ˢ (plainUniv p).powerset
private def fiber7U5 (p : ExchangeAdmissible) := fiber7U4 p ×ˢ (starsUniv p).powerset
private def fiber7Univ (p : ExchangeAdmissible) : Finset (fiber7Tuple p) :=
  fiber7U5 p ×ˢ (plainUniv p).powerset

abbrev fiber7Pred (p : ExchangeAdmissible) (x y : Nat) : fiber7Tuple p → Prop := fun t =>
  (tS1 t).card = x ∧ (tS2 t).card = p.m - x ∧ tA1 t ⊆ tS1 t ∧ tA2 t ⊆ tS2 t ∧
  tB1 t ⊆ starsUniv p \ tS1 t ∧ tB2 t ⊆ plainUniv p \ tS2 t ∧
  (tA1 t).card = tA t ∧ (tA2 t).card = p.k - tA t ∧
  (tB1 t).card = y - (x - tA t) ∧ (tB2 t).card = p.k - (y - (x - tA t)) ∧
  x - tA t ≤ y ∧ y - (x - tA t) ≤ p.k

private def fiber7Set (p : ExchangeAdmissible) (x y : Nat) : Finset (fiber7Tuple p) := by
  exact (fiber7Univ p).filter (fiber7Pred p x y)

/-- The 7-tuple repackaged as the 3-tuple `(S1, (S2, a))`. -/
private def t3Of {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ) :=
  (t.1.1.1.1.1.1, (t.1.1.1.1.1.2, t.1.1.1.1.2))

/-- The 7-tuple repackaged as the 4-tuple `((A1, A2), (B1, B2))`. -/
private def t4Of {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) :=
  ((t.1.1.1.2, t.1.1.2), (t.1.2, t.2))

/-- A 7-tuple rebuilt from a 3-tuple `((S1, S2), a)` and a 4-tuple
`((A1, A2), (B1, B2))`. -/
private def mk7 {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) : fiber7Tuple p :=
  by
    have S1 := t3.1
    have S2 := t3.2.1
    have a := t3.2.2
    have A1 := t4.1.1
    have A2 := t4.1.2
    have B1 := t4.2.1
    have B2 := t4.2.2
    exact ((((((S1, S2), a), A1), A2), B1), B2)

/-- The re-packaging is lossless in both directions. -/
private theorem re7 {p : ExchangeAdmissible} (t : fiber7Tuple p) :
    mk7 (t3Of t) (t4Of t) = t := by
  rfl

private theorem re7' {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :
    t3Of (mk7 t3 t4) = t3 := by
  rfl

private theorem re7'' {p : ExchangeAdmissible}
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :
    t4Of (mk7 t3 t4) = t4 := by
  rfl

/-- The 3-tuple part of the fiber: the two piles and the index, with the
cardinality and guard restrictions. -/
private def fiber3Set (p : ExchangeAdmissible) (x y : Nat) :
    Finset (Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ)) :=
  (starsUniv p).powersetCard x ×ˢ (plainUniv p).powersetCard (p.m - x) ×ˢ
    (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k)

/-- The ambient 4-tuple space. -/
private def fiber4Max (p : ExchangeAdmissible) :
    Finset ((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :=
  ((starsUniv p).powerset ×ˢ (plainUniv p).powerset) ×ˢ
    ((starsUniv p).powerset ×ˢ (plainUniv p).powerset)

/-- The 4-tuple `(A1, A2, B1, B2)` is a valid fiber element over the
3-tuple `t3 = ((S1, S2), a)`. -/
private abbrev isFiber4 (p : ExchangeAdmissible) (x y : Nat)
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
    (t4 : (Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) : Prop :=
  t4.1.1 ∈ (t3.1).powersetCard (t3.2.2) ∧
    t4.1.2 ∈ (t3.2.1).powersetCard (p.k - t3.2.2) ∧
    t4.2.1 ∈ (starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)) ∧
    t4.2.2 ∈ (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2)))

/-- The 4-tuple fiber over a fixed 3-tuple. -/
private def fiber4Set (p : ExchangeAdmissible) (x y : Nat)
    (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ)) :
    Finset ((Finset (Fin p.r) × Finset (Fin (p.N - p.r))) ×
      (Finset (Fin p.r) × Finset (Fin (p.N - p.r)))) :=
  ((t3.1.powersetCard t3.2.2 ×ˢ t3.2.1.powersetCard (p.k - t3.2.2)) ×ˢ
    ((starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)) ×ˢ
      (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2)))))


/-! The fiber sum equals the cardinality of the 7-tuple fiber: the bridge
that lets the involution count the fiber. The 7-tuple repackages as a
3-tuple (the two piles and the index) together with a 4-tuple (the
exchanged cards); for a fixed 3-tuple the 4-tuple part is exactly the
`fiberABchoose` fiber. -/
private theorem fiberFlat (p : ExchangeAdmissible) (x y : Nat) :
    fiberSum p x y = (fiber7Set p x y).card := by
  dsimp only [fiberSum]
  -- (1) The 7-tuple fiber is in bijection with the filtered product of the
  -- 3-tuple set and the ambient 4-tuple space.
  have hcard7 : (fiber7Set p x y).card =
      ((fiber3Set p x y ×ˢ fiber4Max p).filter
        (fun z => isFiber4 p x y z.1 z.2)).card := by
    refine Finset.card_bij (fun t7 ht => (t3Of t7, t4Of t7)) ?_ ?_ ?_
    · -- hi: the re-packaged pair is in the target set
      intro t7 ht
      have hU7 : t7 ∈ fiber7Univ p := (Finset.mem_filter.mp ht).1
      have hP7 : fiber7Pred p x y t7 := (Finset.mem_filter.mp ht).2
      simp only [fiber7Univ, fiber7U5, fiber7U4, fiber7U3, fiber7U2, fiber7U1,
        fiber7Pred, tS1, tS2, tA, tA1, tA2, tB1, tB2, t3Of, t4Of, fiber3Set,
        fiber4Max, isFiber4, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_range] at hU7 hP7 ⊢
      aesop (add simp [Finset.mem_product, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.mem_filter, Finset.mem_range, and_assoc, and_left_comm])
    · -- inj
      intro a _ b _ h
      have hm : mk7 (t3Of a) (t4Of a) = mk7 (t3Of b) (t4Of b) :=
        congrArg (fun z => mk7 z.1 z.2) h
      rw [← re7 a, ← re7 b]
      exact hm
    · -- surj: every target point is the re-packaging of its mk7
      intro z hz
      use mk7 z.1 z.2
      have hmem : mk7 z.1 z.2 ∈ fiber7Set p x y := by
        have h3 : z.1 ∈ fiber3Set p x y :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
        have h4 : z.2 ∈ fiber4Max p :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
        have hF4 : isFiber4 p x y z.1 z.2 := (Finset.mem_filter.mp hz).2
        simp only [fiber7Set, fiber7Univ, fiber7U5, fiber7U4, fiber7U3, fiber7U2,
          fiber7U1, fiber7Pred, tS1, tS2, tA, tA1, tA2, tB1, tB2, mk7,
          fiber3Set, fiber4Max, isFiber4, Finset.mem_product,
          Finset.mem_powerset, Finset.mem_powersetCard, Finset.mem_filter,
          Finset.mem_range] at h3 h4 hF4 ⊢
        aesop (add simp [Finset.mem_product, Finset.mem_powerset, Finset.mem_powersetCard,
          Finset.mem_filter, Finset.mem_range, and_assoc, and_left_comm])
      exact ⟨hmem, rfl⟩
  -- (2) The card of the filtered product is the sum over the 3-tuples of
  -- the card of the 4-tuple fiber.
  have hsum : ((fiber3Set p x y ×ˢ fiber4Max p).filter
      (fun z => isFiber4 p x y z.1 z.2)).card =
      ∑ t3 ∈ fiber3Set p x y,
        ((fiber4Max p).filter (fun t4 => isFiber4 p x y t3 t4)).card := by
    rw [← sumOnes]
    rw [Finset.sum_finset_product
      ((fiber3Set p x y ×ˢ fiber4Max p).filter
        (fun z => isFiber4 p x y z.1 z.2))
      (fiber3Set p x y)
      (fun c => (fiber4Max p).filter (fun t4 => isFiber4 p x y c t4))
      (fun z => by simp only [Finset.mem_product, Finset.mem_filter]; tauto)]
    rw [Finset.sum_congr rfl (fun c _ => sumOnes ((fiber4Max p).filter
      (fun t4 => isFiber4 p x y c t4)))]
  -- (3) For a 3-tuple in the fiber set, the 4-tuple fiber is `fiber4Set`.
  have hfiber (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ))
      (ht3 : t3 ∈ fiber3Set p x y) :
      (fiber4Max p).filter (fun t4 => isFiber4 p x y t3 t4) =
        fiber4Set p x y t3 := by
    ext t4
    constructor
    · simp only [Finset.mem_filter, isFiber4, fiber4Set, Finset.mem_product]
      rintro ⟨hU4, hF41, hF42, hF43, hF44⟩
      exact ⟨⟨hF41, hF42⟩, ⟨hF43, hF44⟩⟩
    · intro h
      simp only [fiber4Set, Finset.mem_product] at h ⊢
      rcases h with ⟨⟨hF41, hF42⟩, ⟨hF43, hF44⟩⟩
      have hU4 : t4 ∈ fiber4Max p := by
        simp only [fiber4Max, Finset.mem_product, Finset.mem_powerset]
        have hS1 : t3.1 ⊆ starsUniv p := by
          simp only [fiber3Set, Finset.mem_product] at ht3
          exact (Finset.mem_powersetCard.mp ht3.1).1
        have hS2 : t3.2.1 ⊆ plainUniv p := by
          simp only [fiber3Set, Finset.mem_product] at ht3
          exact (Finset.mem_powersetCard.mp ht3.2.1).1
        exact ⟨⟨Finset.Subset.trans (Finset.mem_powersetCard.mp hF41).1 hS1,
                Finset.Subset.trans (Finset.mem_powersetCard.mp hF42).1 hS2⟩,
          ⟨Finset.Subset.trans (Finset.mem_powersetCard.mp hF43).1
             (Finset.sdiff_subset : (starsUniv p \ t3.1) ⊆ starsUniv p),
            Finset.Subset.trans (Finset.mem_powersetCard.mp hF44).1
             (Finset.sdiff_subset : (plainUniv p \ t3.2.1) ⊆ plainUniv p)⟩⟩
      simp only [Finset.mem_filter, isFiber4]
      exact ⟨hU4, hF41, hF42, hF43, hF44⟩
  -- (4) The card of the 4-tuple fiber is the four-level sum of ones.
  have hf4 (t3 : Finset (Fin p.r) × (Finset (Fin (p.N - p.r)) × ℕ)) :
      (fiber4Set p x y t3).card =
        (∑ _A1 ∈ t3.1.powersetCard t3.2.2,
        ∑ _A2 ∈ t3.2.1.powersetCard (p.k - t3.2.2),
        ∑ _B1 ∈ (starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)),
        ∑ _B2 ∈ (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2))), 1) := by
    rw [← sumOnes]
    dsimp only [fiber4Set]
    rw [Finset.sum_finset_product _
      (t3.1.powersetCard t3.2.2 ×ˢ t3.2.1.powersetCard (p.k - t3.2.2))
      (fun _ => (starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)) ×ˢ
        (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2))))
      (by simp [Finset.mem_product])]
    rw [Finset.sum_congr rfl (fun _ _ => by
      rw [Finset.sum_finset_product _
        ((starsUniv p \ t3.1).powersetCard (y - (x - t3.2.2)))
        (fun _ => (plainUniv p \ t3.2.1).powersetCard (p.k - (y - (x - t3.2.2))))
        (by simp [Finset.mem_product])])]
    rw [Finset.sum_finset_product _ (t3.1.powersetCard t3.2.2)
      (fun _ => t3.2.1.powersetCard (p.k - t3.2.2)) (by simp [Finset.mem_product])]
  -- (5) Assemble: the right-hand side is the definition of `fiberSum`.
  have hRHS : (fiber7Set p x y).card =
      (∑ S1 ∈ (starsUniv p).powersetCard x,
      ∑ S2 ∈ (plainUniv p).powersetCard (p.m - x),
      ∑ a ∈ (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k),
        (∑ _A1 ∈ S1.powersetCard a,
        ∑ _A2 ∈ S2.powersetCard (p.k - a),
        ∑ _B1 ∈ (starsUniv p \ S1).powersetCard (y - (x - a)),
        ∑ _B2 ∈ (plainUniv p \ S2).powersetCard (p.k - (y - (x - a))), 1)) := by
    rw [hcard7, hsum]
    rw [Finset.sum_congr rfl (fun t3 ht3 => by rw [hfiber t3 ht3, hf4 t3])]
    -- The 3-tuple set is the right-nested product `U1 ×ˢ (U2 ×ˢ rangeF)`;
    -- peel it to the nested sums.
    rw [Finset.sum_finset_product (fiber3Set p x y) ((starsUniv p).powersetCard x)
      (fun _ => (plainUniv p).powersetCard (p.m - x) ×ˢ
        (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k))
      (by simp [Finset.mem_product, fiber3Set])]
    rw [Finset.sum_congr rfl (fun _ _ => by
      rw [Finset.sum_finset_product
        ((plainUniv p).powersetCard (p.m - x) ×ˢ
          (Finset.range (p.k + 1)).filter (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k))
        ((plainUniv p).powersetCard (p.m - x))
        (fun _ => (Finset.range (p.k + 1)).filter
          (fun a => x - a ≤ y ∧ y - (x - a) ≤ p.k)) (by simp [Finset.mem_product])]
      )]
  simpa using hRHS.symm


/-! ### The exchange involution and the fiber-sum swap

The `(x, y)` fiber and the `(y, x)` fiber of the 7-tuple construction are
in bijection under the involution
`(S1, S2, a, A1, A2, B1, B2) ↔ (S1 \ A1 ∪ B1, S2 \ A2 ∪ B2, #B1,
B1, B2, A1, A2)`. Since `fiberFlat` identifies each fiber sum with the
cardinality of the corresponding fiber, the involution yields
`fiberSum p x y = fiberSum p y x`: the combinatorial core of the detailed
balance identity. -/

set_option linter.unusedVariables false
/-- The exchange involution on 7-tuples. Applied to a tuple in the
`(x, y)` fiber it lands in the `(y, x)` fiber; applying it again recovers
the original tuple. -/
private def fiber7Inv (p : ExchangeAdmissible) (x y : Nat) (t : fiber7Tuple p) :
    fiber7Tuple p := by
  let S1' := tS1 t \ tA1 t ∪ tB1 t
  let S2' := tS2 t \ tA2 t ∪ tB2 t
  let a' := (tB1 t).card
  exact ((((((S1', S2'), a'), tB1 t), tB2 t), tA1 t), tA2 t)
set_option linter.unusedVariables true

private theorem fiber7Inv_mem (p : ExchangeAdmissible) (x y : Nat) (hxle : x ≤ p.m)
    (t : fiber7Tuple p) (ht : t ∈ fiber7Set p x y) :
    fiber7Inv p x y t ∈ fiber7Set p y x := by
  -- The left-pile capacity `x ≤ p.m` is *not* forced by the 12 fiber
  -- conditions (they stay consistent with `x > p.m`, where `p.m - x = 0`),
  -- and for such tuples the image of the involution leaves the `(y, x)`
  -- fiber: the `#S2' = p.m - y` computation breaks down. Physically `x`
  -- counts stars in a pile of `p.m` slots, so this hypothesis is exactly
  -- state realizability, and the `#S2'` arithmetic below uses it.
  have hU : t ∈ fiber7Univ p := (Finset.mem_filter.mp ht).1
  have hp : fiber7Pred p x y t := (Finset.mem_filter.mp ht).2
  -- Keep `hp` in def form (no dsimp): the bullets `change` their goals to
  -- def-level shapes so the rw patterns (also def-named) match.
  rcases hp with ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12⟩
  -- Unpack the universe membership into its 7 components. The powerset
  -- memberships must be simp'd to plain subset facts *first*: raw
  -- `s ∈ u.powerset` is an inductive mess that `rcases` cannot eliminate
  -- (dependent elimination fails inside `Multiset.powersetAux`).
  -- The `And` chain splits off the LAST leaf at each level, so the
  -- projections mirror the 7-tuple shape.
  -- (hu1 S1 ⊆ stars, hu2 S2 ⊆ plain, hu3 a < k+1, hu4 A1 ⊆ stars,
  --  hu5 A2 ⊆ plain, hu6 B1 ⊆ stars, hu7 B2 ⊆ plain.)
  simp only [fiber7Univ, fiber7U5, fiber7U4, fiber7U3, fiber7U2, fiber7U1,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_range] at hU
  -- Extract the 7 conjuncts by projection: `rcases` tries to case-split
  -- the `⊆` (a `∀`) conjuncts and fails.
  have hu1 : tS1 t ⊆ starsUniv p := hU.1.1.1.1.1.1
  have hu2 : tS2 t ⊆ plainUniv p := hU.1.1.1.1.1.2
  have hu3 : tA t < p.k + 1 := hU.1.1.1.1.2
  have hu4 : tA1 t ⊆ starsUniv p := hU.1.1.1.2
  have hu5 : tA2 t ⊆ plainUniv p := hU.1.1.2
  have hu6 : tB1 t ⊆ starsUniv p := hU.1.2
  have hu7 : tB2 t ⊆ plainUniv p := hU.2
  -- `a ≤ x`: `A1 ⊆ S1` carries `#A1 = a` of the `#S1 = x` cards; the
  -- omega arithmetic in bullets 9/10 needs it.
  have ha_le_x : (tA t) ≤ x := by
    have := Finset.card_le_card hc3
    rw [hc7, hc1] at this
    exact this
  -- The right pile holds `m - x` cards and `A2 ⊆ S2` holds `k - a` of them,
  -- so `k - a ≤ m - x`; needed in two size computations below.
  have hA2le : p.k - (tA t) ≤ p.m - x := by
    have := Finset.card_le_card hc4
    rw [hc8, hc2] at this
    exact this
  simp only [fiber7Set, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · -- The image tuple lies in the ambient universe. The 7 leaves are
    -- rebuilt with explicit `Finset.mem_product.mpr` calls: the simp-driven
    -- peel of the `×ˢ` chain stops one level short on the let-expr tuple,
    -- and the resulting `And` is left-nested (so `⟨7⟩` cannot match it).
    dsimp only [fiber7Inv, tS1, tS2, tA, tA1, tA2, tB1, tB2,
      fiber7Univ, fiber7U5, fiber7U4, fiber7U3, fiber7U2, fiber7U1]
    refine Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr
              ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_product.mpr
                      ⟨Finset.mem_product.mpr
                          ⟨?_, ?_⟩
                          , ?_⟩
                      , ?_⟩
                  , ?_⟩
              , ?_⟩
          , ?_⟩
    · -- S1' = (S1 \ A1) ∪ B1 ⊆ stars
      exact Finset.mem_powerset.mpr
        (Finset.union_subset (Finset.Subset.trans Finset.sdiff_subset hu1) hu6)
    · -- S2' = (S2 \ A2) ∪ B2 ⊆ plain
      exact Finset.mem_powerset.mpr
        (Finset.union_subset (Finset.Subset.trans Finset.sdiff_subset hu2) hu7)
    · -- a' = #B1 = y - (x - a) ≤ k < k + 1
      have haa : (tB1 t).card < p.k + 1 := by
        rw [hc9]
        omega
      exact Finset.mem_range.mpr haa
    · -- A1' = B1 ⊆ stars
      exact Finset.mem_powerset.mpr hu6
    · -- A2' = B2 ⊆ plain
      exact Finset.mem_powerset.mpr hu7
    · -- B1' = A1 ⊆ stars
      exact Finset.mem_powerset.mpr hu4
    · -- B2' = A2 ⊆ plain
      exact Finset.mem_powerset.mpr hu5
  · -- The 12 fiber conditions, now at (y, x). The image slots are
    -- `S1' = S1 \ A1 ∪ B1`, `S2' = S2 \ A2 ∪ B2`, `a' = #B1`, `A1' = B1`,
    -- `A2' = B2`, `B1' = A1`, `B2' = A2`; each bullet `change`s its goal
    -- to that def-level shape so the rw patterns (def-named) match.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- #(S1 \ A1 ∪ B1) = (x - a) + (y - (x - a)) = y
      have hd1 : Disjoint (tS1 t \ tA1 t) (tB1 t) := by
        rw [Finset.disjoint_left]
        intro z hzS1A1 hB1
        exact (Finset.mem_sdiff.mp (hc5 hB1)).2 (Finset.mem_sdiff.mp hzS1A1).1
      have hcard1 : (tS1 t \ tA1 t).card = x - (tA1 t).card := by
        rw [Finset.card_sdiff_of_subset hc3, hc1, hc7]
      change (tS1 t \ tA1 t ∪ tB1 t).card = y
      rw [Finset.card_union_of_disjoint hd1, hcard1, hc7, hc9]
      omega
    · -- #(S2 \ A2 ∪ B2) = (m - x - (k - a)) + (k - (y - (x - a))) = m - y.
      -- The plain-side arithmetic is a nested Nat-subtraction computation
      -- that `omega` cannot do directly; the `x ≤ p.m` hypothesis is what
      -- discharges it (see the small lemmas in the scratch log).
      have hd2 : Disjoint (tS2 t \ tA2 t) (tB2 t) := by
        rw [Finset.disjoint_left]
        intro z hzS2A2 hB2
        exact (Finset.mem_sdiff.mp (hc6 hB2)).2 (Finset.mem_sdiff.mp hzS2A2).1
      have hcard2 : (tS2 t \ tA2 t).card = p.m - x - (tA2 t).card := by
        rw [Finset.card_sdiff_of_subset hc4, hc2, hc8]
      change (tS2 t \ tA2 t ∪ tB2 t).card = p.m - y
      rw [Finset.card_union_of_disjoint hd2, hcard2, hc8, hc10]
      -- goal: p.m - x - (p.k - a) + (p.k - (y - (x - a))) = p.m - y
      have ha_le_k : (tA t) ≤ p.k := by omega
      have h2' : (p.k - (tA t)) + x ≤ p.m := by
        rw [← Nat.le_sub_iff_add_le hxle]
        exact hA2le
      have hre : (p.k - (tA t)) + x = p.k + (x - (tA t)) := by omega
      have hwkm : p.k + (x - (tA t)) ≤ p.m := by
        rw [← hre]
        exact h2'
      have e2 : p.k - (y - (x - (tA t))) = p.k + (x - (tA t)) - y := by omega
      have e3 : x + (p.k - (tA t)) = (x - (tA t)) + p.k := by omega
      have hyB : y ≤ p.k + (x - (tA t)) := by
        rw [← Nat.sub_add_cancel hc11]
        exact Nat.add_le_add_right hc12 (x - (tA t))
      rw [Nat.sub_sub, e3, e2]
      rw [← Nat.add_sub_assoc hyB]
      have hfin : (x - (tA t)) + p.k ≤ p.m := by
        rw [add_comm]
        exact hwkm
      omega
    · -- B1' = B1 ⊆ S1' = S1 \ A1 ∪ B1
      change tB1 t ⊆ tS1 t \ tA1 t ∪ tB1 t
      intro z hz
      exact Finset.mem_union.mpr (Or.inr hz)
    · -- B2' = B2 ⊆ S2'
      change tB2 t ⊆ tS2 t \ tA2 t ∪ tB2 t
      intro z hz
      exact Finset.mem_union.mpr (Or.inr hz)
    · -- A1 ⊆ stars \ S1'
      change tA1 t ⊆ starsUniv p \ (tS1 t \ tA1 t ∪ tB1 t)
      intro z hz
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.Subset.trans hc3 hu1 hz
      · intro hzS1'
        rcases (Finset.mem_union.mp hzS1') with h1 | h2
        · rcases (Finset.mem_sdiff.mp h1) with ⟨_, hnotA1⟩
          exact hnotA1 hz
        · exact (Finset.mem_sdiff.mp (hc5 h2)).2 (hc3 hz)
    · -- A2 ⊆ plain \ S2'
      change tA2 t ⊆ plainUniv p \ (tS2 t \ tA2 t ∪ tB2 t)
      intro z hz
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.Subset.trans hc4 hu2 hz
      · intro hzS2'
        rcases (Finset.mem_union.mp hzS2') with h1 | h2
        · rcases (Finset.mem_sdiff.mp h1) with ⟨_, hnotA2⟩
          exact hnotA2 hz
        · exact (Finset.mem_sdiff.mp (hc6 h2)).2 (hc4 hz)
    · -- #A1' = #B1 = a'
      rfl
    · -- #A2' = #B2 = k - (y - (x - a)) = k - a'
      change (tB2 t).card = p.k - (tB1 t).card
      rw [hc10, hc9]
    · -- #B1' = #A1 = a = x - (y - a')
      change (tA1 t).card = x - (y - (tB1 t).card)
      rw [hc7, hc9]
      omega
    · -- #B2' = #A2 = k - a = k - (x - (y - a'))
      change (tA2 t).card = p.k - (x - (y - (tB1 t).card))
      rw [hc8, hc9]
      omega
    · -- y - a' ≤ x
      change y - (tB1 t).card ≤ x
      rw [hc9]
      omega
    · -- x - (y - a') ≤ k
      change x - (y - (tB1 t).card) ≤ p.k
      rw [hc9]
      have halk : (tA t) ≤ p.k := by omega
      omega

private theorem fiber7Inv_inv (p : ExchangeAdmissible) (x y : Nat) (t : fiber7Tuple p)
    (ht : t ∈ fiber7Set p x y) :
    fiber7Inv p y x (fiber7Inv p x y t) = t := by
  -- `hp` is kept in def form (no dsimp) so the `hc*` facts are def-named
  -- and match the `change`d def-level goals below.
  have hp : fiber7Pred p x y t := (Finset.mem_filter.mp ht).2
  rcases hp with ⟨_, _, hc3, hc4, hc5, hc6, hc7, _, _, _, _, _⟩
  let u := fiber7Inv p x y t
  let v := fiber7Inv p y x u
  -- The A/B slots rotate back definitionally: the image carries
  -- `(B1, B2, A1, A2)` into the `(A1, A2, B1, B2)` positions, and the
  -- double image lands on `(A1, A2, B1, B2)` again.
  have hA1 : tA1 v = tA1 t := rfl
  have hA2 : tA2 v = tA2 t := rfl
  have hB1 : tB1 v = tB1 t := rfl
  have hB2 : tB2 v = tB2 t := rfl
  -- a'' = #B1 (intermediate) = #A1 = a
  have ha : tA v = tA t := by
    dsimp only [fiber7Inv, tA, tB1, tA1]
    exact hc7
  -- S1'' = (S1 \ A1 ∪ B1) \ B1 ∪ A1 = S1, since B1 ⊆ stars \ S1 kills A1.
  have hS1 : tS1 v = tS1 t := by
    change ((tS1 t \ tA1 t ∪ tB1 t) \ tB1 t ∪ tA1 t) = tS1 t
    ext z
    constructor
    · intro hz
      rcases (Finset.mem_union.mp hz) with h1 | h2
      · rcases (Finset.mem_sdiff.mp h1) with ⟨hzS1u, hnotB1⟩
        rcases (Finset.mem_union.mp hzS1u) with hS1A | hB1
        · rcases (Finset.mem_sdiff.mp hS1A) with ⟨hS1, _⟩
          exact hS1
        · exfalso
          exact hnotB1 hB1
      · exact hc3 h2
    · intro hzS1
      by_cases hzA1 : z ∈ tA1 t
      · exact Finset.mem_union.mpr (Or.inr hzA1)
      · apply Finset.mem_union.mpr
        apply Or.inl
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, ?_⟩
        · -- z ∈ S1 \ A1 ∪ B1, via the S1 \ A1 side
          apply Finset.mem_union.mpr
          apply Or.inl
          apply Finset.mem_sdiff.mpr
          exact ⟨hzS1, hzA1⟩
        · -- z ∉ B1
          by_contra hzB1
          exact (Finset.mem_sdiff.mp (hc5 hzB1)).2 hzS1
  -- S2'' = (S2 \ A2 ∪ B2) \ B2 ∪ A2 = S2.
  have hS2 : tS2 v = tS2 t := by
    change ((tS2 t \ tA2 t ∪ tB2 t) \ tB2 t ∪ tA2 t) = tS2 t
    ext z
    constructor
    · intro hz
      rcases (Finset.mem_union.mp hz) with h1 | h2
      · rcases (Finset.mem_sdiff.mp h1) with ⟨hzS2u, hnotB2⟩
        rcases (Finset.mem_union.mp hzS2u) with hS2A | hB2
        · rcases (Finset.mem_sdiff.mp hS2A) with ⟨hS2, _⟩
          exact hS2
        · exfalso
          exact hnotB2 hB2
      · exact hc4 h2
    · intro hzS2
      by_cases hzA2 : z ∈ tA2 t
      · exact Finset.mem_union.mpr (Or.inr hzA2)
      · apply Finset.mem_union.mpr
        apply Or.inl
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, ?_⟩
        · -- z ∈ S2 \ A2 ∪ B2, via the S2 \ A2 side
          apply Finset.mem_union.mpr
          apply Or.inl
          apply Finset.mem_sdiff.mpr
          exact ⟨hzS2, hzA2⟩
        · -- z ∉ B2
          by_contra hzB2
          exact (Finset.mem_sdiff.mp (hc6 hzB2)).2 hzS2
  -- Assemble the 7 component equalities into the tuple equality.
  refine Prod.ext ?_ ?_
  · refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · refine Prod.ext ?_ ?_
        · refine Prod.ext ?_ ?_
          · refine Prod.ext ?_ ?_
            · exact hS1
            · exact hS2
          · exact ha
        · exact hA1
      · exact hA2
    · exact hB1
  · exact hB2

private theorem fiberSum_swap (p : ExchangeAdmissible) (x y : Nat)
    (hxle : x ≤ p.m) (hylo : y ≤ p.m) :
    fiberSum p x y = fiberSum p y x := by
  rw [fiberFlat p x y, fiberFlat p y x]
  refine Finset.card_bij (fun t ht => fiber7Inv p x y t) ?_ ?_ ?_
  · -- the image lands in the (y, x) fiber
    intro t ht
    exact fiber7Inv_mem p x y hxle t ht
  · -- injective: applying twice recovers the input
    intro a ha b hb h
    have h2 := congrArg (fiber7Inv p y x) h
    rw [fiber7Inv_inv p x y a ha, fiber7Inv_inv p x y b hb] at h2
    exact h2
  · -- surjective: the image of its own image
    intro z hz
    use fiber7Inv p y x z
    constructor
    · -- f (x, y) (inv (y, x) z) = z, since inv is an involution
      exact fiber7Inv_inv p y x z hz
    · -- the witness lies in the (x, y) fiber
      exact fiber7Inv_mem p y x hylo z hz

/-! ### Detailed balance

Microscopic reversibility for the exchange kernel: the hypergeometric
stationary distribution and the transition kernel satisfy
`π(x) W(x, y) = π(y) W(y, x)`. Both sides reduce to the same fiber count
over the same denominator, `C(N, m)·C(m, k)·C(N - m, k)`: the stationary
mass carries the Vandermonde factor `C(r, z)·C(N-r, m-z)` and the
transition numerator is the rest of the fiber count (`fiberSum_eq`), so
the identity is exactly `fiberSum_swap`. -/

private theorem detailedBalance (p : ExchangeAdmissible) (x y : BLState p.N p.m p.r) :
    blStationary p.N p.m p.r x * transitionWeight p.N p.m p.r p.k x.val y.val =
      blStationary p.N p.m p.r y * transitionWeight p.N p.m p.r p.k y.val x.val := by
  -- The common denominator: the deck choice times the exchange-pair
  -- choice, as a product of two casts.
  let D := (Nat.choose p.N p.m : Rat) * (transitionDenominator p.N p.m p.k : Rat)
  -- Each side is the corresponding fiber count over that denominator:
  -- `π(z) = C(r, z)·C(N-r, m-z) / C(N, m)` and
  -- `W(z, w) = num(z, w) / (C(m, k)·C(N-m, k))`, while
  -- `fiberSum(z, w) = C(r, z)·C(N-r, m-z)·num(z, w)` (fiberSum_eq).
  have hside (z : BLState p.N p.m p.r) (w : Nat) :
      blStationary p.N p.m p.r z * transitionWeight p.N p.m p.r p.k z.val w =
        (fiberSum p z.val w : Rat) / D := by
    have hC : (Nat.choose p.N p.m : Rat) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.pos_iff_ne_zero.mp (Nat.choose_pos (Nat.le_of_lt p.hmn))
    have hD2 : (transitionDenominator p.N p.m p.k : Rat) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.pos_iff_ne_zero.mp (transitionDenominator_pos p)
    have hzmem : z.val ∈ stateFinset p.N p.m p.r := by
      simp only [stateFinset, Finset.mem_Icc]
      exact ⟨z.2.1, z.2.2⟩
    simp only [blStationary, transitionWeight, transitionDenominator]
    field_simp [hC, hD2]
    -- Gather the numerator's two casts into one (whose inner product is
    -- the fiber count), split the gathered denominator cast back into
    -- the two-cast shape of `D`, and unfold the let.
    rw [← Nat.cast_mul, ← fiberSum_eq p z.val w hzmem, Nat.cast_mul]
    dsimp only [D, transitionDenominator]
    -- The deck factor was moved to the right side's numerator by
    -- field_simp; cancel it (hC says it is nonzero). The final rw splits
    -- the right side's cast-of-product denominator (field_simp regathers
    -- it, so the split must come last) to match the left side.
    field_simp [hC]
    rw [Nat.cast_mul]
  -- Both macrostates are physical: they lie in the left pile's window.
  have hxm : x.val ≤ p.m := x.2.2.trans (Nat.min_le_left p.m p.r)
  have hym : y.val ≤ p.m := y.2.2.trans (Nat.min_le_left p.m p.r)
  calc
    blStationary p.N p.m p.r x * transitionWeight p.N p.m p.r p.k x.val y.val =
      (fiberSum p x.val y.val : Rat) / D := hside x (y.val)
    _ = (fiberSum p y.val x.val : Rat) / D := by
      rw [fiberSum_swap p x.val y.val hxm hym]
    _ = blStationary p.N p.m p.r y * transitionWeight p.N p.m p.r p.k y.val x.val :=
      (hside y (x.val)).symm

/-! ### Stationarity of the exchange kernel

`blStationaryDist` is stationary for `blExchangeKernel`: at the
`Dist`/`FiniteKernel` level it satisfies `DetailedBalance` (the
`detailedBalance` theorem unpacked through `mass_ofFun`), and detailed
balance implies stationarity. -/

theorem blDetailedBalance (p : ExchangeAdmissible) :
    DetailedBalance (blStationaryDist p) (blExchangeKernel p) := by
  intro x y
  -- Both masses reduce to their defining functions via the mass-evaluation
  -- simp lemmas (no `ofFun` unfolding).
  simp only [mass_blStationaryDist, mass_blExchangeKernel]
  exact detailedBalance p x y

/-- The stationary distribution is fixed by the exchange kernel: one
application of `blExchangeKernel` leaves `blStationaryDist` unchanged.
This is the generic `stationary_of_detailedBalance` applied to
`blDetailedBalance`. -/
theorem blStationaryDist_is_stationary (p : ExchangeAdmissible) :
    Stationary (blStationaryDist p) (blExchangeKernel p) :=
  stationary_of_detailedBalance _ _ (blDetailedBalance p)

/-- The stationary distribution is fixed by any number of exchange steps. -/
theorem blStationaryRun (p : ExchangeAdmissible) (n : Nat) :
    FiniteKernel.run (blExchangeKernel p) n (blStationaryDist p) = blStationaryDist p := by
  exact stationary_run n _ _ (blStationaryDist_is_stationary p)

end detailedBalance
end BernoulliLaplaceGeneral
end Shufflemath
