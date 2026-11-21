module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath


-- promoted from probe _Probe47s
namespace _Probe47s
open CommanderPermutation
open Finset

/-!
# pairCountByConstSub — count `(x, y) ∈ s ×ˢ t` with `(c - f x) + g y = n`

The combinatorial engine the **per-deck** Bernoulli-Laplace target actually
needs.  Via `newLeftOriginalCount_eq`, counting `(L, R)` with
`(newLeftCards d L R ∩ leftOrigSet).card = n` is counting those with
`(x - markedInLeft d L) + markedInRight d R = n` (where `x = leftOriginalCount d`),
which is exactly this `(c - f p.1) + g p.2 = n` form (with `c = x`).

The fiber is `s.filter(f = a) ×ˢ t.filter ((c - a) + g · = n)` — the `g`-condition
is kept as a raw filter (never *solved* for `g y`), so there is no
Nat-subtraction-solvability trap.  The filtered set is the disjoint big-union
over `a ∈ s.image f`, so
`# = ∑_{a ∈ s.image f} #(s.filter(f = a)) · #(t.filter ((c - a) + g · = n))`.
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The `a`-fiber: pairs whose first coordinate has `f`-value `a` and which
    satisfy `(c - a) + g (second) = n`. -/
def fiberCS (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat) (c n a : Nat) :
    Finset (α × β) :=
  (s.filter (fun x => f x = a)) ×ˢ (t.filter (fun y => (c - a) + g y = n))

/-- The `(c - f) + g = n`-filtered product set equals the big-union of the fibers. -/
theorem filterCS_eq_biUnion (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    (s ×ˢ t).filter (fun p => (c - f p.1) + g p.2 = n) =
      (s.image f).biUnion fun a => fiberCS s t f g c n a := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rcases hp with ⟨⟨hx, hy⟩, hcond⟩
    refine Finset.mem_biUnion.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx, ?_⟩
    simp only [fiberCS, Finset.mem_product, Finset.mem_filter]
    simp [hx, hy, hcond]
  · intro hp
    have h : ∃ a, a ∈ s.image f ∧ p ∈ fiberCS s t f g c n a := by
      simpa using Finset.mem_biUnion.mp hp
    rcases h with ⟨a, _hmem, hxy⟩
    have hpL : p.1 ∈ s.filter (fun x => f x = a) := (Finset.mem_product.mp hxy).1
    have hpR : p.2 ∈ t.filter (fun y => (c - a) + g y = n) := (Finset.mem_product.mp hxy).2
    have hx : p.1 ∈ s := (Finset.mem_filter.mp hpL).1
    have hfa : f p.1 = a := (Finset.mem_filter.mp hpL).2
    have hy : p.2 ∈ t := (Finset.mem_filter.mp hpR).1
    have hcond : (c - a) + g p.2 = n := (Finset.mem_filter.mp hpR).2
    have hprod : p ∈ s ×ˢ t := by simp only [Finset.mem_product]; exact ⟨hx, hy⟩
    have hgoal : (c - f p.1) + g p.2 = n := by rw [hfa]; exact hcond
    exact Finset.mem_filter.mpr ⟨hprod, hgoal⟩

/-- The fibers are pairwise disjoint: different `a`-values give disjoint
    `s.filter(f = ·)` parts, and disjointness propagates through the product. -/
theorem fibersCS_pairwiseDisjoint (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    ((s.image f) : Set Nat).PairwiseDisjoint fun a => fiberCS s t f g c n a := by
  intro a _hmemA b _hmemB hne
  have hdisjL : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x = b)) := by
    rw [Finset.disjoint_left]
    intro x hx
    have hfx : f x = a := (Finset.mem_filter.mp hx).2
    intro hxb
    have hfxb : f x = b := (Finset.mem_filter.mp hxb).2
    exact hne (hfx.symm.trans hfxb)
  change Disjoint (fiberCS s t f g c n a) (fiberCS s t f g c n b)
  simp only [fiberCS]
  rw [Finset.disjoint_product]
  exact Or.inl hdisjL

/-- The count of `(x, y) ∈ s ×ˢ t` with `(c - f x) + g y = n`, decomposed over
    the distinct values of `f`. -/
theorem pairCountByConstSub (s : Finset α) (t : Finset β) (f : α → Nat) (g : β → Nat)
    (c n : Nat) :
    ((s ×ˢ t).filter (fun p => (c - f p.1) + g p.2 = n)).card =
      (s.image f).sum fun a =>
        (s.filter (fun x => f x = a)).card * (t.filter (fun y => (c - a) + g y = n)).card := by
  rw [filterCS_eq_biUnion]
  rw [Finset.card_biUnion (h := fibersCS_pairwiseDisjoint s t f g c n)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberCS, Finset.card_product]

end _Probe47s

-- promoted from probe _Probe47p
namespace _Probe47p
open BernoulliLaplaceGeneral
open CommanderPermutation
open CommanderPhysicalExchange
open FinsetCombinatorics
open Finset

/-!
# Per-deck Bernoulli-Laplace bridge — building blocks (47o part 2)

For a fixed deck `d`, let `x = leftOriginalCount d` (originally-left cards
currently at left positions) and `xR = #(markedRightPos d) = 50 - x` (the
marked cards that crossed to the right).  A 25/25 exchange selects a 25-subset
`L` of the left positions and a 25-subset `R` of the right positions; the new
left-pile originally-left count is

  `newLeftOriginalCount d L R = (x - markedInLeft d L) + markedInRight d R`

(`newLeftOriginalCount_eq`).  This file builds the counting kernel that
discharges `hMembershipExchange` per deck: the number of `(L, R)` pairs with
new count `n` is the 4-fold Vandermonde sum, which equals
`transitionNumerator 99 50 50 25 x n` (r = 50 = the total originally-left /
"red" cards, k = 25).

Building blocks (proved below): the number of 25-subsets of a pile containing
exactly `a` of the marked positions is the hypergeometric number
`choose(#marked, a) * choose(#unmarked, 25 - a)` — the reusable
`powersetCard_markedContent`.
-/

variable (d : Deck) (n : Nat)

/-- The 25/25 selected-set pairs: a 25-subset of the 50 left positions times a
    25-subset of the 49 right positions. -/
noncomputable def leftRight25Pairs : Finset (Finset (Fin 50) × Finset (Fin 49)) :=
  (Finset.univ : Finset (Fin 50)).powersetCard 25 ×ˢ
    (Finset.univ : Finset (Fin 49)).powersetCard 25

/-- The number of 25-subsets `L` of the left pile holding exactly `aL`
    originally-left cards is the hypergeometric number
    `choose(x, aL) * choose(50 - x, 25 - aL)`. -/
theorem leftCountByMarked (aL : Nat) (ha : aL ≤ 25) :
    (((Finset.univ : Finset (Fin 50)).powersetCard 25).filter
      (fun L => markedInLeft d L = aL)).card =
      Nat.choose (leftOriginalCount d) aL * Nat.choose (50 - leftOriginalCount d) (25 - aL) := by
  have hsub : markedLeftPos d ⊆ (Finset.univ : Finset (Fin 50)) := Finset.subset_univ _
  simpa [markedInLeft, markedLeftPos_card d, Finset.inter_comm] using
    powersetCard_markedContent
      (U := (Finset.univ : Finset (Fin 50))) (M := markedLeftPos d) hsub 25 aL ha

/-- The number of 25-subsets `R` of the right pile holding exactly `bR`
    originally-left (crossed) cards is the hypergeometric number
    `choose(xR, bR) * choose(49 - xR, 25 - bR)`, where `xR = 50 - x`. -/
theorem rightCountByMarked (bR : Nat) (ha : bR ≤ 25) :
    (((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => markedInRight d R = bR)).card =
      Nat.choose (markedRightPos d).card bR *
        Nat.choose (49 - (markedRightPos d).card) (25 - bR) := by
  have hsub : markedRightPos d ⊆ (Finset.univ : Finset (Fin 49)) := Finset.subset_univ _
  simpa [markedInRight, Finset.inter_comm] using
    powersetCard_markedContent
      (U := (Finset.univ : Finset (Fin 49))) (M := markedRightPos d) hsub 25 bR ha

end _Probe47p

-- promoted from probe _Probe47t
namespace _Probe47t
open CommanderPermutation
open CommanderPhysicalExchange
open FinsetCombinatorics
open Finset

/-!
# rightFilterGuarded — the `(c - a) + g = n` right-pile count, with guards

The one remaining conceptual piece for the per-deck Bernoulli-Laplace bridge.
Counting `R ∈ (Fin 49).powersetCard 25` with `(x - aL) + markedInRight d R = n`
(where `x = leftOriginalCount d`, `aL` a fixed `markedInLeft` value, and
`bR = n - (x - aL)`), the answer is the hypergeometric number
`choose (markedRightPos d).card bR * choose (49 - (markedRightPos d).card) (25 - bR)`
**exactly when the guards hold** (`x - aL ≤ n` and `bR ≤ 25`) and `0` otherwise.

The nested-`if` guard shape mirrors `transitionNumerator 99 50 25 x n`'s integrand
(`remaining := x - a` guarded by `remaining ≤ y`, then `b := y - remaining` guarded
by `b ≤ k`), so after the `#(markedRightPos d) = 50 - x` substitution this lemma's
RHS is term-for-term `transitionNumerator`'s right-hand factor.
-/

/-- `c ≤ n → (c + k = n ↔ k = n - c)` — the add-then-subtract equivalence the
    guarded right-pile count is built on. -/
lemma haddSub (c n : Nat) (hc : c ≤ n) (k : Nat) : c + k = n ↔ k = n - c := by
  constructor <;> intro h <;> omega

theorem rightFilterGuarded (x aL n : Nat) :
    (((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => (x - aL) + markedInRight d R = n)).card =
      if x - aL ≤ n then
        (if n - (x - aL) ≤ 25 then
          Nat.choose (markedRightPos d).card (n - (x - aL)) *
            Nat.choose (49 - (markedRightPos d).card) (25 - (n - (x - aL)))
        else 0)
      else 0 := by
  let bR := n - (x - aL)
  by_cases h1 : x - aL ≤ n
  · -- x - aL ≤ n:  reduce the outer ite to its then-branch
    rw [if_pos h1]
    by_cases h2 : n - (x - aL) ≤ 25
    · -- h1 ∧ h2:  (x - aL) + markedInRight = n  <->  markedInRight = bR
      rw [if_pos h2]
      have hfin :
          ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
            (fun R => (x - aL) + markedInRight d R = n) =
            ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
            (fun R => markedInRight d R = bR) := by
        apply Finset.ext
        intro R
        simp only [Finset.mem_filter]
        have hequiv : ((x - aL) + markedInRight d R = n) ↔ (markedInRight d R = bR) :=
          haddSub (x - aL) n h1 (markedInRight d R)
        constructor
        · intro hp
          rcases hp with ⟨hmem, hcond⟩
          exact ⟨hmem, hequiv.mp hcond⟩
        · intro hp
          rcases hp with ⟨hmem, hmark⟩
          exact ⟨hmem, hequiv.mpr hmark⟩
      rw [hfin]
      simpa [markedInRight, bR, Finset.inter_comm, Finset.card_univ, Fintype.card_fin] using
        powersetCard_markedContent
          (U := (Finset.univ : Finset (Fin 49))) (M := markedRightPos d) (Finset.subset_univ _) 25 (n - (x - aL)) h2
    · -- h1 ∧ ¬h2 (bR > 25):  markedInRight ≤ 25 < bR, so no such R
      rw [if_neg h2]
      have hempty : ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
        (fun R => (x - aL) + markedInRight d R = n) = ∅ := by
        apply Finset.ext
        intro R
        have hnot : ¬R ∈ ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
          (fun R => (x - aL) + markedInRight d R = n) := by
          intro hmem
          rcases Finset.mem_filter.mp hmem with ⟨hmem2, hcond⟩
          have hmark : markedInRight d R = bR := (haddSub (x - aL) n h1 (markedInRight d R)).mp hcond
          have hR25 : R.card = 25 := (Finset.mem_powersetCard.mp hmem2).2
          have hcard : (markedRightPos d ∩ R).card ≤ 25 := by
            have hsub : markedRightPos d ∩ R ⊆ R := fun _ h => (Finset.mem_inter.mp h).2
            simpa [hR25] using Finset.card_mono hsub
          have hbR25 : bR ≤ 25 := by rw [← hmark]; simpa [markedInRight] using hcard
          exact h2 hbR25
        simp [hnot]
      rw [hempty]
      simp
  · -- ¬h1 (x - aL > n):  (x - aL) + markedInRight ≥ x - aL > n, so no such R
    rw [if_neg h1]
    have hempty : ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
      (fun R => (x - aL) + markedInRight d R = n) = ∅ := by
      apply Finset.ext
      intro R
      have hnot : ¬R ∈ ((Finset.univ : Finset (Fin 49)).powersetCard 25).filter
        (fun R => (x - aL) + markedInRight d R = n) := by
        intro hmem
        rcases Finset.mem_filter.mp hmem with ⟨_hmem2, hcond⟩
        have hlt : n < x - aL := Nat.not_le.mp h1
        have hge : x - aL ≤ (x - aL) + markedInRight d R := Nat.le_add_right _ _
        exact Nat.lt_irrefl n (by simpa [hcond] using Nat.lt_of_lt_of_le hlt hge)
      simp [hnot]
    rw [hempty]
    simp

end _Probe47t

-- promoted from probe _Probe47v
namespace _Probe47v
open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace
open CommanderMarkedRightCount
open Finset

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

-- promoted from probe _Probe47u
namespace _Probe47u
open CommanderPermutation
open CommanderPhysicalExchange
open BernoulliLaplace
open CommanderMarkedRightCount
open Finset

/-!
# perDeckBridge

Connects the physical A3 count
`# { (L, R) : (newLeftCards d L R ∩ leftOrigSet).card = n }`
to the Bernoulli-Laplace numerator `transitionNumerator 99 50 25 (leftOriginalCount d) n`.

Two-step composition:
(1) `newLeftOriginalCount_eq` makes the physical count equal to the marked
    const-sub count `# { (L,R) : (leftOriginalCount d - markedInLeft d L) + markedInRight d R = n }`;
(2) `_Probe47v.transitionNumerator_eq_fiberProduct` (the proved F3 A3 kernel) makes that
    marked const-sub count equal to the transition numerator.
-/

variable {d : Deck}

abbrev s50 : Finset (Finset (Fin 50)) := (Finset.univ : Finset (Fin 50)).powersetCard 25
abbrev t49 : Finset (Finset (Fin 49)) := (Finset.univ : Finset (Fin 49)).powersetCard 25

-- The per-deck bridge: the physical count equals the Bernoulli-Laplace numerator.
theorem perDeckBridge (n : Nat) :
    ((s50 ×ˢ t49).filter
      (fun p : Finset (Fin 50) × Finset (Fin 49) =>
        (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
    transitionNumerator 99 50 25 (leftOriginalCount d) n := by
  -- (1) newLeftCards-count filter  =  marked const-sub filter  (pointwise, via newLeftOriginalCount_eq).
  have hfilt :
      (s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n) =
      (s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, newLeftOriginalCount_eq d p.1 p.2]
  -- (2) count the filter, then apply 47v's proved kernel (marked const-sub count = transition numerator).
  have hcount :
      ((s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (newLeftCards d p.1 p.2 ∩ leftOrigSet).card = n)).card =
      ((s50 ×ˢ t49).filter
        (fun p : Finset (Fin 50) × Finset (Fin 49) =>
          (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = n)).card := by
    simp [hfilt]
  exact hcount.trans (_Probe47v.transitionNumerator_eq_fiberProduct d n).symm

end _Probe47u
end Shufflemath
