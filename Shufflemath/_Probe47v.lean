module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderFiberCount
public import Shufflemath.FinsetCombinatorics
public import Shufflemath._Probe47p
public import Shufflemath._Probe47s
public import Shufflemath._Probe47t
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace
open CommanderMarkedRightCount
open Finset

namespace _Probe47v

variable {d : Deck}

abbrev s50 : Finset (Finset (Fin 50)) := (Finset.univ : Finset (Fin 50)).powersetCard 25
abbrev t49 : Finset (Finset (Fin 49)) := (Finset.univ : Finset (Fin 49)).powersetCard 25

def H (d : Deck) (x n : Nat) (a : Nat) : Nat :=
  (s50.filter (fun L : Finset (Fin 50) => markedInLeft d L = a)).card *
    (t49.filter (fun R : Finset (Fin 49) => (x - a) + markedInRight d R = n)).card

-- The integrand of `transitionNumerator 99 50 25 x n`, written out.
def integrand (x n a : Nat) : Nat :=
  let r := x - a
  if r ≤ n then
    let b := n - r
    if b ≤ 25 then
      Nat.choose x a * Nat.choose (50 - x) (25 - a) *
        Nat.choose (50 - x) b * Nat.choose (49 - (50 - x)) (25 - b)
    else 0
  else 0

lemma markedInLeftImage_subset_range26 (d : Deck) :
    s50.image (fun L : Finset (Fin 50) => markedInLeft d L) ⊆ Finset.range 26 := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨L, hLmem, rfl⟩
  have hL : L.card = 25 := (Finset.mem_powersetCard.mp hLmem).2
  have hb : (markedLeftPos d ∩ L).card ≤ 25 := by
    have hsub : markedLeftPos d ∩ L ⊆ L := fun _ h => (Finset.mem_inter.mp h).2
    simpa [hL] using card_mono hsub
  rw [Finset.mem_range, markedInLeft]
  omega

lemma fiberSum_extendsTo_range26 (d : Deck) (x n : Nat) :
    (s50.image (fun L : Finset (Fin 50) => markedInLeft d L)).sum (H d x n) =
      (Finset.range 26).sum (H d x n) := by
  let A := s50.image (fun L : Finset (Fin 50) => markedInLeft d L)
  have hsub : A ⊆ Finset.range 26 := markedInLeftImage_subset_range26 d
  have hUnion : Finset.range 26 = A ∪ (Finset.range 26 \ A) := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hr : a ∈ Finset.range 26
    · by_cases hi : a ∈ A
      · simp [hi, hr]
      · simp [hi, hr]
    · by_cases hi : a ∈ A
      · exfalso
        exact hr (hsub hi)
      · simp [hi, hr]
  have hDisj : Disjoint A (Finset.range 26 \ A) :=
    Finset.disjoint_sdiff (s := A) (t := Finset.range 26)
  have hHzero : ∀ a ∈ Finset.range 26 \ A, H d x n a = 0 := by
    intro a ha
    have ha2 : a ∉ s50.image (fun L : Finset (Fin 50) => markedInLeft d L) := by
      simpa [A] using (Finset.mem_sdiff.mp ha).2
    have hcard0 : (s50.filter (fun L : Finset (Fin 50) => markedInLeft d L = a)).card = 0 := by
      have hempty : s50.filter (fun L : Finset (Fin 50) => markedInLeft d L = a) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro L hmem
        have hLmem : L ∈ s50 := (Finset.mem_filter.mp hmem).1
        have hmark : markedInLeft d L = a := (Finset.mem_filter.mp hmem).2
        have hwit : a ∈ s50.image (fun L : Finset (Fin 50) => markedInLeft d L) :=
          Finset.mem_image.mpr ⟨L, hLmem, hmark⟩
        exact ha2 hwit
      simpa using hempty
    simp only [H, hcard0, mul_zero, zero_mul]
  have hComplSum0 : (Finset.range 26 \ A).sum (H d x n) = 0 := by
    rw [Finset.sum_congr rfl fun a ha => hHzero a ha, Finset.sum_const_zero]
  have h1 : (A ∪ (Finset.range 26 \ A)).sum (H d x n) =
      A.sum (H d x n) + (Finset.range 26 \ A).sum (H d x n) := Finset.sum_union hDisj
  have h2 : A.sum (H d x n) + (Finset.range 26 \ A).sum (H d x n) = A.sum (H d x n) := by
    rw [hComplSum0]
    simp
  exact (h1.trans h2).symm.trans (congrArg (·.sum (H d x n)) hUnion.symm)

lemma fiberSummand_eq_transitionIntegrand (d : Deck) (n a : Nat) (ha : a ∈ Finset.range 26) :
    H d (leftOriginalCount d) n a = integrand (leftOriginalCount d) n a := by
  let x := leftOriginalCount d
  have ha25 : a ≤ 25 := by
    have hlt : a < 26 := Finset.mem_range.mp ha
    omega
  let f := fun (L : Finset (Fin 50)) => markedInLeft d L
  have hL : (s50.filter (fun L => f L = a)).card =
      Nat.choose (leftOriginalCount d) a * Nat.choose (50 - leftOriginalCount d) (25 - a) := by
    simpa [s50, f] using _Probe47p.leftCountByMarked (d := d) a ha25
  have hR : (t49.filter (fun R => (x - a) + markedInRight d R = n)).card =
      if x - a ≤ n then
        (if n - (x - a) ≤ 25 then
           Nat.choose (markedRightPos d).card (n - (x - a)) *
             Nat.choose (49 - (markedRightPos d).card) (25 - (n - (x - a)))
         else 0)
      else 0 := by
    simpa [t49] using _Probe47t.rightFilterGuarded (d := d) x a n
  have hMRC : (markedRightPos d).card = 50 - x := by
    simpa [x] using markedRightPos_card d
  unfold H
  rw [hL, hR, hMRC]
  have hxs : x = leftOriginalCount d := by dsimp [x]
  rw [hxs]
  dsimp only [integrand]
  split_ifs with _ _
  <;> simp [mul_assoc, mul_comm, mul_left_comm, mul_zero, zero_mul, Nat.sub_sub]
  <;> (try ring_nf)
  <;> (try omega)
  <;> (try rfl)

/-!
# F3 A3 transition kernel: the Bernoulli-Laplace transition count as a fiber product

The capstone connecting the per-deck Bernoulli-Laplace transition count
(`transitionNumerator 99 50 25 (leftOriginalCount d) n`, i.e. N=99, m=50, k=25, initial
left-original `leftOriginalCount d`, target `n`) to an explicit combinatorial count: the
number of `(L, R)` with `L` a 25-pile of the marked-left deck, `R` a 25-pile of the
marked-right deck, such that
`(leftOriginalCount d - markedInLeft d L) + markedInRight d R = n`.

Chain: fiber product -> (47s) image-fiber sum -> (range-26 domain extension) range-26 sum
-> (integrand match) the Bernoulli-Laplace transition numerator.

We thread `leftOriginalCount d` through every step (no let-shorthand) so that each
sub-lemma matches its statement exactly and no heavy let-vs-explicit unification occurs.
-/

/-- The F3 A3 kernel: the transition count equals the fiber-product count. -/
theorem transitionNumerator_eq_fiberProduct (d : Deck) (n : Nat) :
    transitionNumerator 99 50 25 (leftOriginalCount d) n =
      ((s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n)).card := by
  have hHSame : (fun a =>
      (s50.filter (fun L : Finset (Fin 50) => markedInLeft d L = a)).card *
      (t49.filter (fun R : Finset (Fin 49) => (leftOriginalCount d - a) + markedInRight d R = n)).card) =
      H d (leftOriginalCount d) n := by
    funext a
    dsimp only [H]
  have hstep2 : ((s50 ×ˢ t49).filter
      (fun p : Finset (Fin 50) × Finset (Fin 49) =>
        (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n)).card =
      (s50.image (fun L : Finset (Fin 50) => markedInLeft d L)).sum (H d (leftOriginalCount d) n) := by
    simpa [hHSame] using _Probe47s.pairCountByConstSub s50 t49
      (fun L : Finset (Fin 50) => markedInLeft d L) (fun R : Finset (Fin 49) => markedInRight d R)
      (leftOriginalCount d) n
  have hstep3 : (s50.image (fun L : Finset (Fin 50) => markedInLeft d L)).sum (H d (leftOriginalCount d) n) =
      (Finset.range 26).sum (H d (leftOriginalCount d) n) :=
    fiberSum_extendsTo_range26 (d := d) (x := leftOriginalCount d) (n := n)
  have hstep4 : (Finset.range 26).sum (H d (leftOriginalCount d) n) =
      transitionNumerator 99 50 25 (leftOriginalCount d) n := by
    rw [BernoulliLaplace.transitionNumerator]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [fiberSummand_eq_transitionIntegrand (d := d) (n := n) a ha]
    simp [integrand]
  exact ((hstep2.trans hstep3).trans hstep4).symm

end _Probe47v
end Shufflemath
