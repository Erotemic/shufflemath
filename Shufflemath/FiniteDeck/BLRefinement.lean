module
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceFiber
public import Shufflemath.FiberDisintegration
public import Shufflemath.FiniteDeck.SubsetExchange
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Tactic
@[expose] public section
namespace Shufflemath
namespace FiniteDeck

/-!
The Bernoulli--Laplace refinement of the two-pile subset exchange: the *macro*
state of a deck is the number of marked (initially-left) cards in the left pile.
This module builds the marked-set / count-fiber infrastructure and the count of
each count-fiber, the foundation for the G4 macro-intertwining theorem
(uniform count-fiber ⊳ subsetExchange = blExchange ⊳ uniform count-fiber) and the
discharge of the Commander A3 by specialization at `(99, 50, 50, 25)`.
-/

def markedSet (N r : Nat) (hr : r ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin r)).image (Fin.castLE hr)

theorem markedSet_card (N r : Nat) (hr : r ≤ N) : (markedSet N r hr).card = r := by
  unfold markedSet
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective hr), Finset.card_univ, Fintype.card_fin]

def markedComp (N r : Nat) (hr : r ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)) \ markedSet N r hr

theorem markedComp_card (N r : Nat) (hr : r ≤ N) : (markedComp N r hr).card = N - r := by
  unfold markedComp
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), markedSet_card, Finset.card_univ, Fintype.card_fin]

theorem markedDisjoint (N r : Nat) (hr : r ≤ N) : Disjoint (markedSet N r hr) (markedComp N r hr) := by
  unfold markedComp
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_sdiff_self]

theorem markedCover (N r : Nat) (hr : r ≤ N) :
    (markedSet N r hr) ∪ (markedComp N r hr) = (Finset.univ : Finset (Fin N)) := by
  unfold markedComp
  exact Finset.union_sdiff_of_subset (Finset.subset_univ (markedSet N r hr))

/-- A pile splits as its marked part union its unmarked part. -/
theorem markSplit (N : Nat) (S M : Finset (Fin N)) : S = (S ∩ M) ∪ (S \ M) := by
  apply Finset.ext
  intro a
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ]
  tauto

/-- The unmarked part has size `S.card - (S ∩ M).card`. -/
theorem unmarkedCard (N : Nat) (S M : Finset (Fin N)) :
    (S \ M).card = S.card - (S ∩ M).card := by
  rw [Finset.card_sdiff, ← Finset.inter_comm]

def countFiber (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) : Finset (Finset (Fin N)) :=
  (pileSet N m).filter (fun S => (S ∩ markedSet N r hr).card = x)

theorem countFiber_subset (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) :
    countFiber N m r hm hr x ⊆ pileSet N m := by
  rw [countFiber]
  intro U hU
  exact (Finset.mem_filter.mp hU).1

/-- The marked part of a count-fiber: `x`-subsets of the marked set. -/
def cntLset (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m) : Finset (Finset (Fin N)) :=
  Finset.powersetCard x (markedSet N r hr)

/-- The unmarked part of a count-fiber: `(m - x)`-subsets of the marked complement. -/
def cntRset (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m) : Finset (Finset (Fin N)) :=
  Finset.powersetCard (m - x) (markedComp N r hr)

theorem cntLset_card (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m) :
    (cntLset N m r hm hr x hx).card = Nat.choose r x := by
  rw [cntLset, Finset.card_powersetCard, markedSet_card]

theorem cntRset_card (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m) :
    (cntRset N m r hm hr x hx).card = Nat.choose (N - r) (m - x) := by
  rw [cntRset, Finset.card_powersetCard, markedComp_card]

/-- A `(marked, unmarked)` product element has the expected subset and size facts. -/
theorem cntDecomp (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) :
    p.1 ⊆ markedSet N r hr ∧ p.1.card = x ∧
    p.2 ⊆ markedComp N r hr ∧ p.2.card = m - x := by
  dsimp only [cntLset, cntRset] at hp
  rw [Finset.mem_product] at hp
  rcases hp with ⟨hL, hR⟩
  rw [Finset.mem_powersetCard] at hL hR
  exact ⟨hL.1, hL.2, hR.1, hR.2⟩

/-- The union of a `(marked, unmarked)` pair is an `m`-pile whose marked part has
  size `x`. -/
theorem cntNewpile (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) :
    (p.1 ∪ p.2).card = m ∧ ((p.1 ∪ p.2) ∩ markedSet N r hr).card = x := by
  rcases cntDecomp N m r hm hr x hx p hp with ⟨hle, hlc, hre, hrc⟩
  have hsubM : p.1 ∩ p.2 ⊆ markedSet N r hr := by
    intro z hz
    exact hle (Finset.mem_inter.mp hz |>.1)
  have hsubC : p.1 ∩ p.2 ⊆ markedComp N r hr := by
    intro z hz
    exact hre (Finset.mem_inter.mp hz |>.2)
  have hInt : p.1 ∩ p.2 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    have hzM : z ∈ markedSet N r hr := hsubM hz
    have hzC : z ∈ markedComp N r hr := hsubC hz
    have hznotM : z ∉ markedSet N r hr := by
      rw [markedComp] at hzC
      exact (Finset.mem_sdiff.mp hzC).2
    exact hznotM hzM
  have hDisj : Disjoint p.1 p.2 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact hInt
  have hcard : (p.1 ∪ p.2).card = m := by
    rw [Finset.card_union_of_disjoint hDisj, hlc, hrc, Nat.add_comm]
    exact Nat.sub_add_cancel hx
  have hInter : (p.1 ∪ p.2) ∩ markedSet N r hr = p.1 := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_and, not_not, iff_self]
    have hzB : z ∈ p.2 → z ∉ markedSet N r hr := fun h => (Finset.mem_sdiff.mp (hre h)).2
    tauto
  exact ⟨hcard, by rw [hInter, hlc]⟩

/-- The union of a product element lies in the count-fiber. -/
theorem cntNewpile_mem (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) :
    p.1 ∪ p.2 ∈ countFiber N m r hm hr x := by
  simp only [countFiber, Finset.mem_filter, true_and] at *
  rcases cntNewpile N m r hm hr x hx p hp with ⟨hcard, hmark⟩
  have hSmem : p.1 ∪ p.2 ∈ pileSet N m := by
    simp only [pileSet, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hcard⟩
  exact ⟨hSmem, hmark⟩

/-- Inversion, marked part: `(p.1 ∪ p.2) ∩ markedSet = p.1`. -/
theorem cntInvFirst (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) :
    (p.1 ∪ p.2) ∩ markedSet N r hr = p.1 := by
  rcases cntDecomp N m r hm hr x hx p hp with ⟨hle, _hlc, hre, _hrc⟩
  ext z
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_and, not_not, iff_self]
  have hzB : z ∈ p.2 → z ∉ markedSet N r hr := fun h => (Finset.mem_sdiff.mp (hre h)).2
  tauto

/-- Inversion, unmarked part: `(p.1 ∪ p.2) \ markedSet = p.2`. -/
theorem cntInvSecond (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) :
    (p.1 ∪ p.2) \ markedSet N r hr = p.2 := by
  rcases cntDecomp N m r hm hr x hx p hp with ⟨hle, _hlc, hre, _hrc⟩
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and, not_not, iff_self]
  have hzB : z ∈ p.2 → z ∉ markedSet N r hr := fun h => (Finset.mem_sdiff.mp (hre h)).2
  have hzA (hz : z ∈ p.1) : z ∈ markedSet N r hr := hle hz
  tauto

/- T2 count-fiber cardinality: the number of `m`-piles with exactly `x` marked cards is
   `choose r x * choose (N - r) (m - x)` — choose the `x` marked cards and the
   `m - x` unmarked cards, independently. -/
theorem countFiber_card (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (hx : x ≤ m) :
    (countFiber N m r hm hr x).card = Nat.choose r x * Nat.choose (N - r) (m - x) := by
  have hL : (cntLset N m r hm hr x hx).card = Nat.choose r x := cntLset_card N m r hm hr x hx
  have hR : (cntRset N m r hm hr x hx).card = Nat.choose (N - r) (m - x) :=
    cntRset_card N m r hm hr x hx
  let i (S : Finset (Fin N)) (hS : S ∈ countFiber N m r hm hr x) :
      Finset (Fin N) × Finset (Fin N) := (S ∩ markedSet N r hr, S \ markedSet N r hr)
  let j (p : Finset (Fin N) × Finset (Fin N))
      (hp : p ∈ cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx) : Finset (Fin N) :=
      p.1 ∪ p.2
  have hbij : (countFiber N m r hm hr x).card =
      (cntLset N m r hm hr x hx ×ˢ cntRset N m r hm hr x hx).card := by
    refine Finset.card_bij' i j ?_ ?_ ?_ ?_
    · -- i lands in cntLset ×ˢ cntRset
      intro S hS
      simp only [countFiber, Finset.mem_filter, true_and] at hS
      rcases hS with ⟨hSmem, hmark⟩
      have hcard : S.card = m := by
        simp only [pileSet, Finset.mem_powersetCard] at hSmem
        exact hSmem.2
      have hsubL : S ∩ markedSet N r hr ⊆ markedSet N r hr := Finset.inter_subset_right
      have hsubR : S \ markedSet N r hr ⊆ markedComp N r hr := by
        unfold markedComp
        intro z hz
        rw [Finset.mem_sdiff] at hz
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hz.2⟩
      have hcardR : (S \ markedSet N r hr).card = m - x := by
        rw [unmarkedCard, hcard, hmark]
      rw [Finset.mem_product, cntLset, cntRset, Finset.mem_powersetCard, Finset.mem_powersetCard]
      exact ⟨⟨hsubL, hmark⟩, ⟨hsubR, hcardR⟩⟩
    · -- j lands back in countFiber
      intro p hp
      exact cntNewpile_mem N m r hm hr x hx p hp
    · -- left inverse: j (i S) = S
      intro S hS
      dsimp only [i, j]
      rw [← markSplit]
    · -- right inverse: i (j p) = p
      intro p hp
      dsimp only [i, j]
      ext
      · rw [cntInvFirst N m r hm hr x hx p hp]
      · rw [cntInvSecond N m r hm hr x hx p hp]
  rw [hbij, Finset.card_product, hL, hR]


/-! The **stationary half of the G4 macro-intertwining**: the Bernoulli-Laplace
  stationary macrostate distribution equals the pushforward of the uniform
  distribution over `m`-piles through the marked-card count. `countFiber_card`
  gives `#countFiber(x) = choose r x * choose (N-r) (m-x)`, `blStationary` is
  that same numerator over `choose N m`, and `#pileSet = choose N m`, so the
  two coincide. -/

/-- For an admissible count `x`, the BL stationary mass equals the uniform
  mass of the corresponding count-fiber over the pile space:
  `blStationary x = #countFiber(x) / #pileSet`. This is the stationary half of
  the G4 macro-intertwining. -/
theorem countFiber_blStationary (hm : m ≤ N) (hr : r ≤ N)
    (x : BernoulliLaplaceGeneral.BLState N m r) :
    BernoulliLaplaceGeneral.blStationary N m r x =
      (Finset.card (countFiber N m r hm hr x.val) : Rat) / (Finset.card (pileSet N m) : Rat) := by
  have hxm : x.val ≤ m := by
    have h : x.val ≤ min m r := by
      simpa [BernoulliLaplaceGeneral.blHi_def] using x.2.2
    exact Nat.le_trans h (Nat.min_le_left m r)
  have hPile : (Finset.card (pileSet N m) : Rat) = (Nat.choose N m : Rat) := by
    rw [pileSet, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [BernoulliLaplaceGeneral.blStationary,
      countFiber_card N m r hm hr x.val hxm, hPile]

/-- G4/T4 counting primitive: the marked-count split of a k-subset set. Among the
  k-subsets of a pile S, the number carrying exactly a marked cards (a ≤ k) is
  choose #(S∩M) a * choose #(S\M) (k-a): a k-subset with a marked is uniquely
  (a-subset of S∩M) ∪ ((k-a)-subset of S\M). Used to count the Lset/Rset splits
  of the T4 refinement. -/

theorem pmcDecomp (N : Nat) (S M : Finset (Fin N)) (k a : Nat)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ (Finset.powersetCard a (S ∩ M)) ×ˢ (Finset.powersetCard (k - a) (S \ M))) :
    p.1 ⊆ S ∩ M ∧ p.1.card = a ∧ p.2 ⊆ S \ M ∧ p.2.card = k - a := by
  rw [Finset.mem_product] at hp
  rcases hp with ⟨hL, hR⟩
  rw [Finset.mem_powersetCard] at hL hR
  exact ⟨hL.1, hL.2, hR.1, hR.2⟩

/-- Right-inverse, marked part: for a product pair `(A, B)` with `A ⊆ S∩M` and
  `B ⊆ S\M`, the marked part of their union is `A`. -/
theorem pmcInvFirst (N : Nat) (S M : Finset (Fin N)) (k a : Nat)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ (Finset.powersetCard a (S ∩ M)) ×ˢ (Finset.powersetCard (k - a) (S \ M))) :
    (p.1 ∪ p.2) ∩ M = p.1 := by
  rcases pmcDecomp N S M k a p hp with ⟨hAsub, _hAcard, hBsub, _hBcard⟩
  ext z
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, not_and, not_not, iff_self]
  have hzA : z ∈ p.1 → z ∈ M := fun h => (Finset.mem_inter.mp (hAsub h)).2
  have hzB : z ∈ p.2 → z ∉ M := fun h => (Finset.mem_sdiff.mp (hBsub h)).2
  tauto

/-- Right-inverse, unmarked part: for a product pair `(A, B)` with `A ⊆ S∩M` and
  `B ⊆ S\M`, the unmarked part of their union is `B`. -/
theorem pmcInvSecond (N : Nat) (S M : Finset (Fin N)) (k a : Nat)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ (Finset.powersetCard a (S ∩ M)) ×ˢ (Finset.powersetCard (k - a) (S \ M))) :
    (p.1 ∪ p.2) \ M = p.2 := by
  rcases pmcDecomp N S M k a p hp with ⟨hAsub, _hAcard, hBsub, _hBcard⟩
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_univ, not_and, not_not, iff_self]
  have hzA : z ∈ p.1 → z ∈ M := fun h => (Finset.mem_inter.mp (hAsub h)).2
  have hzB : z ∈ p.2 → z ∉ M := fun h => (Finset.mem_sdiff.mp (hBsub h)).2
  tauto

/-- The marked-count split of a `k`-subset set: among the `k`-subsets of a pile
  `S`, the number carrying exactly `a` marked cards (with `a ≤ k`) is
  `choose #(S∩M) a * choose #(S\M) (k-a)`: a `k`-subset with `a` marked is
  uniquely `(a-subset of S∩M) ∪ ((k-a)-subset of S\M)`. This is the counting
  primitive for the Lset/Rset splits and for the T4 count-count identity. -/
theorem powersetCard_markedSplit (N : Nat) (S M : Finset (Fin N)) (k a : Nat) (ha : a ≤ k) :
    (Finset.filter (fun L => (L ∩ M).card = a) (Finset.powersetCard k S)).card =
      Nat.choose (S ∩ M).card a * Nat.choose (S \ M).card (k - a) := by
  let AM := S ∩ M
  let BM := S \ M
  let Lf := Finset.filter (fun L => (L ∩ M).card = a) (Finset.powersetCard k S)
  let P := (Finset.powersetCard a AM) ×ˢ (Finset.powersetCard (k - a) BM)
  let i (L : Finset (Fin N)) (hL : L ∈ Lf) : Finset (Fin N) × Finset (Fin N) := (L ∩ M, L \ M)
  let j (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ P) : Finset (Fin N) := p.1 ∪ p.2
  have hbij : (Lf).card = (P).card := by
    refine Finset.card_bij' i j ?_ ?_ ?_ ?_
    · -- i lands in the product
      intro L hL
      simp only [Lf, Finset.mem_filter, Finset.mem_powersetCard] at hL
      dsimp only [i, P] at ⊢
      have hA : (L ∩ M).card = a := hL.2
      have hLk : L.card = k := hL.1.2
      have hLsub : L ⊆ S := hL.1.1
      have hsubA : L ∩ M ⊆ AM := by
        intro z hz
        rw [Finset.mem_inter]
        exact ⟨hLsub (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩
      have hsubB : L \ M ⊆ BM := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        rw [Finset.mem_sdiff]
        exact ⟨hLsub hz.1, hz.2⟩
      have hcardB : (L \ M).card = k - a := by
        rw [Finset.card_sdiff, Finset.inter_comm, hA, hLk]
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      change ((L ∩ M) ⊆ AM ∧ (L ∩ M).card = a) ∧ ((L \ M) ⊆ BM ∧ (L \ M).card = k - a)
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact hsubA
      · exact hA
      · exact hsubB
      · exact hcardB
    · -- j lands back in Lf
      intro p hp
      simp only [Lf, Finset.mem_filter, Finset.mem_powersetCard] at ⊢
      dsimp only [P] at hp
      rcases pmcDecomp N S M k a p hp with ⟨hAsub, hAcard, hBsub, hBcard⟩
      have hAsubS : p.1 ⊆ S := by intro z hz; exact (Finset.mem_inter.mp (hAsub hz)).1
      have hBsubS : p.2 ⊆ S := by intro z hz; exact (Finset.mem_sdiff.mp (hBsub hz)).1
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro z hz
          rw [Finset.mem_union] at hz
          rcases hz with hzA | hzB
          · exact hAsubS hzA
          · exact hBsubS hzB
        · have hDisjP : Disjoint p.1 p.2 := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            apply Finset.eq_empty_of_forall_notMem
            intro z hz
            have hzM : z ∈ M := (Finset.mem_inter.mp (hAsub (Finset.mem_inter.mp hz).1)).2
            have hznotM : z ∉ M := (Finset.mem_sdiff.mp (hBsub (Finset.mem_inter.mp hz).2)).2
            exact hznotM hzM
          rw [Finset.card_union_of_disjoint hDisjP, hAcard, hBcard, Nat.add_comm]
          exact Nat.sub_add_cancel ha
      · rw [pmcInvFirst N S M k a p hp, hAcard]
    · -- left inverse: j (i L) = L
      intro L _hL
      dsimp only [i, j]
      ext z
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · -- right inverse: i (j p) = p
      intro p hp
      dsimp only [P] at hp
      dsimp only [i, j, P, AM, BM] at ⊢
      rw [pmcInvFirst N S M k a p hp, pmcInvSecond N S M k a p hp]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]

/-! ### T4 count projection

The map from the membership (subset) level to the macroscopic Bernoulli-Laplace
state: the number of marked cards in an `m`-pile. It lands exactly in the admissible
`BLState N m r` interval `blLo..blHi`. This is the T4 projection that the
count-level transition and the uniform-fiber intertwining are built on.
-/
def countInPileVal (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (S : Membership N m) : Nat :=
  (S.1 ∩ markedSet N r hr).card

theorem countInPile_admissible (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (S : Membership N m) :
    BernoulliLaplaceGeneral.blLo N m r ≤ countInPileVal N m r hm hr S ∧
      countInPileVal N m r hm hr S ≤ BernoulliLaplaceGeneral.blHi N m r := by
  set M := markedSet N r hr
  have hMcard : M.card = r := markedSet_card N r hr
  have hIntMsub : (S.1 ∩ M) ⊆ M := by
    intro z hz
    exact (Finset.mem_inter.mp hz).2
  have hIntM : (S.1 ∩ M).card ≤ r := by
    have h0 : (S.1 ∩ M).card ≤ M.card := Finset.card_le_card hIntMsub
    rwa [hMcard] at h0
  have hSIntMsub : (S.1 ∩ M) ⊆ S.1 := by
    intro z hz
    exact (Finset.mem_inter.mp hz).1
  have hSinter : (S.1 ∩ M).card ≤ m := by
    have h0 : (S.1 ∩ M).card ≤ S.1.card := Finset.card_le_card hSIntMsub
    rwa [S.2] at h0
  have hSD : (M \ S.1).card = r - (S.1 ∩ M).card := by
    rw [Finset.card_sdiff, hMcard, Finset.inter_comm]
  have hCalc : (S.1 ∩ M).card = r - (M \ S.1).card := by
    omega
  have hSsub : (M \ S.1) ⊆ (Finset.univ \ S.1) := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨Finset.mem_univ z, hz.2⟩
  have hUnivS : (Finset.univ \ S.1).card = N - m := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, S.2]
  have hB : (M \ S.1).card ≤ N - m := by
    calc
      (M \ S.1).card ≤ (Finset.univ \ S.1).card := Finset.card_le_card hSsub
      _ = N - m := by rw [hUnivS]
  have hAsub : (M \ S.1) ⊆ M := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    exact hz.1
  have hA : (M \ S.1).card ≤ r := by
    have h0 : (M \ S.1).card ≤ M.card := Finset.card_le_card hAsub
    rwa [hMcard] at h0
  have hMax : max (r - (N - m)) 0 ≤ r - (M \ S.1).card := by
    rw [max_le_iff]
    constructor
    · by_cases hRm : r ≤ N - m
      · have h0 : r - (N - m) = 0 := by omega
        rw [h0]
        exact Nat.zero_le _
      · exact (by omega : r - (N - m) ≤ r - (M \ S.1).card)
    · exact Nat.zero_le _
  have hval : countInPileVal N m r hm hr S = (S.1 ∩ M).card := rfl
  constructor
  · rw [BernoulliLaplaceGeneral.blLo_def, hval, hCalc]
    exact hMax
  · rw [BernoulliLaplaceGeneral.blHi_def, hval]
    exact le_min hSinter hIntM

def countInPile (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (S : Membership N m) :
    BernoulliLaplaceGeneral.BLState N m r :=
  ⟨countInPileVal N m r hm hr S, countInPile_admissible N m r hm hr S⟩

theorem countInPile_val (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (S : Membership N m) :
    (countInPile N m r hm hr S).1 = countInPileVal N m r hm hr S := by
  rfl

/- S has count `x` (as a Bernoulli-Laplace macrostate) iff its underlying `m`-subset
   lies in the `x`-th count-fiber. -/
theorem countInPile_countFiber (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat) (S : Membership N m) :
    (S.1 : Finset (Fin N)) ∈ countFiber N m r hm hr x ↔ (countInPile N m r hm hr S).1 = x := by
  rw [countInPile_val, countInPileVal, countFiber, pileSet]
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨⟨Finset.subset_univ _, S.2⟩, h⟩


/-! ### T4 transitivity backbone

The symmetric group `Perm (Fin N)` acts **transitively on the `m`-subsets**: for any
two `m`-subsets `S, T` there is a permutation mapping `S` onto `T`. This is the
group-action engine behind the T4 count-fiber transitivity (and hence the uniform
count-fiber being a single orbit, so the count-level dynamics closes).

Built on Mathlib's `Set.powersetCard.isPretransitive` (the symmetric group is
pretransitive on `n`-subsets), lifted to a `Finset` statement via the
`SubMulAction` / `smulFinset` machinery.
-/
open scoped Pointwise

theorem permFinsetTransitive (N m : Nat) (hm : m ≤ N) (S T : Finset (Fin N))
    (hS : S.card = m) (hT : T.card = m) :
    ∃ g : Equiv.Perm (Fin N), S.image g = T := by
  have hPre : MulAction.IsPretransitive (Equiv.Perm (Fin N))
      (Set.powersetCard (Fin N) m) :=
    Set.powersetCard.isPretransitive (α := Fin N) (n := m)
  have hs : S ∈ (Set.powersetCard (Fin N) m) := by
    simpa [Set.powersetCard.mem_iff] using hS
  have ht : T ∈ (Set.powersetCard (Fin N) m) := by
    simpa [Set.powersetCard.mem_iff] using hT
  obtain ⟨g, hg⟩ := hPre.exists_smul_eq ⟨S, hs⟩ ⟨T, ht⟩
  -- `hg : g • ⟨S, hs⟩ = ⟨T, ht⟩`  (as powersetCard-subtype elements)
  have hval : ((g • ⟨S, hs⟩ : Set.powersetCard (Fin N) m) : Finset (Fin N)) =
      ((⟨T, ht⟩ : Set.powersetCard (Fin N) m) : Finset (Fin N)) :=
    congrArg (fun (x : Set.powersetCard (Fin N) m) => (x : Finset (Fin N))) hg
  have h1 : Finset.image (fun x => g x) S = T := by
    simpa [Set.powersetCard.coe_smul, Finset.smul_finset_def, Finset.image_congr] using hval
  have h2 : S.image g = Finset.image (fun x => g x) S := by
    ext z
    simp only [Finset.mem_image]
  exact ⟨g, by
    rw [h2]
    exact h1⟩

/- The **count-fiber** `countFiber x` (the m-subsets with exactly x marked cards) is a
   single orbit of the full symmetric group: any two of its members are related by a
   permutation. Immediate from `permFinsetTransitive`, since count-fiber members are
   m-subsets. This is the transitivity half of the G4 macro-intertwining: the uniform
   distribution over a count-fiber is supported on one orbit, so the count-level dynamics
   preserves it. -/
theorem countFiber_transitive (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat)
    (hx : x ≤ m) (S T : Finset (Fin N))
    (hS : S ∈ countFiber N m r hm hr x) (hT : T ∈ countFiber N m r hm hr x) :
    ∃ g : Equiv.Perm (Fin N), S.image g = T := by
  have hScard : S.card = m := by
    simp only [countFiber, pileSet, Finset.mem_filter, Finset.mem_powersetCard] at hS
    exact hS.1.2
  have hTcard : T.card = m := by
    simp only [countFiber, pileSet, Finset.mem_filter, Finset.mem_powersetCard] at hT
    exact hT.1.2
  exact permFinsetTransitive N m hm S T hScard hTcard



/-! ### T4 (A,B) move count (fixed marked counts) -/
theorem countAB (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (k a b : Nat)
    (ha : a ≤ k) (hb : b ≤ k) (S : Membership N m) :
    (Finset.filter (fun A => (A ∩ markedSet N r hr).card = a) (Finset.powersetCard k S.1) ×ˢ
        Finset.filter (fun B => (B ∩ markedSet N r hr).card = b) (Finset.powersetCard k (Finset.univ \ S.1))).card =
      Nat.choose (S.1 ∩ markedSet N r hr).card a *
        Nat.choose (S.1 \ markedSet N r hr).card (k - a) *
        Nat.choose ((Finset.univ \ S.1) ∩ markedSet N r hr).card b *
        Nat.choose ((Finset.univ \ S.1) \ markedSet N r hr).card (k - b) := by
  rw [Finset.card_product,
      powersetCard_markedSplit N S.1 (markedSet N r hr) k a ha,
      powersetCard_markedSplit N (Finset.univ \ S.1) (markedSet N r hr) k b hb]
  ring

/-! ### T4 filter/product helper and move set -/
theorem filterProduct {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s u : Finset α) (t v : Finset β) (hs : u ⊆ s) (ht : v ⊆ t) :
    (s ×ˢ t).filter (fun p => p.1 ∈ u ∧ p.2 ∈ v) = u ×ˢ v := by
  ext p
  constructor
  · intro hL
    rw [Finset.mem_filter] at hL
    rw [Finset.mem_product]
    exact hL.2
  · intro hR
    rw [Finset.mem_product] at hR
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hs hR.1, ht hR.2⟩, hR⟩

def reachMoves (N m k : Nat) (S : Membership N m) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Finset.powersetCard k S.1) ×ˢ (Finset.powersetCard k (Finset.univ \ S.1))

/-! ### T4 product-filter lemma -/
theorem filterCardProduct (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (k a b : Nat)
    (S : Membership N m) :
    ((Finset.powersetCard k S.1) ×ˢ (Finset.powersetCard k (Finset.univ \ S.1))).filter
      (fun p : Finset (Fin N) × Finset (Fin N) =>
        (p.1 ∩ markedSet N r hr).card = a ∧ (p.2 ∩ markedSet N r hr).card = b) =
      (Finset.powersetCard k S.1).filter (fun A : Finset (Fin N) => (A ∩ markedSet N r hr).card = a) ×ˢ
        (Finset.powersetCard k (Finset.univ \ S.1)).filter (fun B : Finset (Fin N) => (B ∩ markedSet N r hr).card = b) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto


/- `pieceCount` ... (T4 counting core: one reachable-move summand). -/
theorem pieceCount (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (k x y a : Nat)
    (ha : a ≤ k) (S : Membership N m)
    (hx : x = (S.1 ∩ markedSet N r hr).card) :
    ((reachMoves N m k S).filter
      (fun p : Finset (Fin N) × Finset (Fin N) =>
        (p.1 ∩ markedSet N r hr).card = a ∧ x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y)).card =
      if x - a ≤ y then
        if y - (x - a) ≤ k then
          Nat.choose (S.1 ∩ markedSet N r hr).card a *
            Nat.choose (S.1 \ markedSet N r hr).card (k - a) *
            Nat.choose ((Finset.univ \ S.1) ∩ markedSet N r hr).card (y - (x - a)) *
            Nat.choose ((Finset.univ \ S.1) \ markedSet N r hr).card (k - (y - (x - a)))
        else 0
      else 0 := by
  set M := markedSet N r hr
  set C := reachMoves N m k S
  set b := y - (x - a)
  set Pa := (C).filter (fun p : Finset (Fin N) × Finset (Fin N) =>
      (p.1 ∩ M).card = a ∧ x - (p.1 ∩ M).card + (p.2 ∩ M).card = y)
  split_ifs with hxy hby
  · -- valid (a,b): land at b; project the product, count via countAB
    have hPred : Pa = (C).filter (fun p : Finset (Fin N) × Finset (Fin N) =>
        (p.1 ∩ M).card = a ∧ (p.2 ∩ M).card = b) := by
      ext p
      by_cases hmem : p ∈ C
      · rw [Finset.mem_filter, Finset.mem_filter] at *
        simp only [hmem]
        by_cases ha2 : (p.1 ∩ M).card = a
        · rw [ha2]
          have hL : x - a + (p.2 ∩ M).card = y ↔ (p.2 ∩ M).card = b := by
            constructor
            · intro h; omega
            · intro h; omega
          simpa [hL]
        · simp only [ha2]
          tauto
      · rw [Finset.mem_filter, Finset.mem_filter] at *
        simp only [hmem]
        tauto
    have hFilter : (C).filter (fun p : Finset (Fin N) × Finset (Fin N) =>
        (p.1 ∩ M).card = a ∧ (p.2 ∩ M).card = b) =
        (Finset.powersetCard k S.1).filter (fun A : Finset (Fin N) => (A ∩ M).card = a) ×ˢ
          (Finset.powersetCard k (Finset.univ \ S.1)).filter (fun B : Finset (Fin N) => (B ∩ M).card = b) := by
      dsimp only [C, reachMoves]
      simpa using filterCardProduct N m r hm hr k a b S
    rw [hPred, hFilter, countAB N m r hm hr k a b ha hby S]
  · -- x-a ≤ y but b > k: (p.2∩M).card = b > k impossible for p ∈ C
    have hEmpty : Pa = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hpA : p ∈ C ∧ (p.1 ∩ M).card = a ∧ x - (p.1 ∩ M).card + (p.2 ∩ M).card = y := by
        simpa [Pa, Finset.mem_filter] using hp
      have hA : (p.1 ∩ M).card = a := hpA.2.1
      have hb : (p.2 ∩ M).card = b := by
        have hland : x - (p.1 ∩ M).card + (p.2 ∩ M).card = y := by simpa [hA] using hpA.2.2
        omega
      have hpC : p ∈ Finset.powersetCard k S.1 ×ˢ Finset.powersetCard k (Finset.univ \ S.1) := by
        simpa [C, reachMoves] using hpA.1
      have hprod : p.1 ∈ Finset.powersetCard k S.1 ∧ p.2 ∈ Finset.powersetCard k (Finset.univ \ S.1) := by
        simpa only [Finset.mem_product] using hpC
      have hk : (p.2).card = k := by
        have hf : p.2 ⊆ (Finset.univ \ S.1) ∧ (p.2).card = k := by
          simpa only [Finset.mem_powersetCard] using hprod.2
        exact hf.2
      have hBle : (p.2 ∩ M).card ≤ k := by
        have h1 : (p.2 ∩ M).card ≤ (p.2).card := by
          apply Finset.card_le_card
          intro z hz
          exact (Finset.mem_inter.mp hz).1
        simpa only [hk] using h1
      rw [hb] at hBle
      exact lt_irrefl b (lt_of_le_of_lt hBle (by omega : k < b))
    rw [hEmpty, Finset.card_empty]
  · -- x-a > y: x-(p.1∩M).card+(p.2∩M).card ≥ x-a > y, so Pa is empty
    have hEmpty : Pa = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hpA : p ∈ C ∧ (p.1 ∩ M).card = a ∧ x - (p.1 ∩ M).card + (p.2 ∩ M).card = y := by
        simpa [Pa, Finset.mem_filter] using hp
      have hA : (p.1 ∩ M).card = a := hpA.2.1
      have hland : x - (p.1 ∩ M).card + (p.2 ∩ M).card = y := by simpa [hA] using hpA.2.2
      have hge : x - a ≤ y := by
        have htmp : x - (p.1 ∩ M).card + (p.2 ∩ M).card ≥ x - a := by simpa [hA]
        simp only [hland] at htmp
        exact htmp
      exact hxy hge
    rw [hEmpty, Finset.card_empty]


/- `markedPileCards` ... (T4: pile/marked cards in x, m-x, r-x, N-m-r+x terms). -/
theorem markedPileCards (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x : Nat) (hx : x = (S.1 ∩ markedSet N r hr).card) :
    (S.1 ∩ markedSet N r hr).card = x ∧
    (S.1 \ markedSet N r hr).card = m - x ∧
    ((Finset.univ \ S.1) ∩ markedSet N r hr).card = r - x ∧
    ((Finset.univ \ S.1) \ markedSet N r hr).card = (N - m) - (r - x) := by
  set M := markedSet N r hr
  have hS1 : S.1.card = m := S.2
  have hInt : (S.1 ∩ M).card = x := hx.symm
  have hMcard : M.card = r := markedSet_card N r hr
  have hInt3 : ((Finset.univ \ S.1) ∩ M).card = r - x := by
    have hEq : (Finset.univ \ S.1) ∩ M = M \ S.1 := by
      ext z
      by_cases hzS : z ∈ S.1
      · by_cases hzM : z ∈ M
        · simp [Finset.mem_sdiff, Finset.mem_inter, hzS, hzM, Finset.mem_univ]
        · simp [Finset.mem_sdiff, Finset.mem_inter, hzS, hzM, Finset.mem_univ]
      · by_cases hzM : z ∈ M
        · simp [Finset.mem_sdiff, Finset.mem_inter, hzS, hzM, Finset.mem_univ]
        · simp [Finset.mem_sdiff, Finset.mem_inter, hzS, hzM, Finset.mem_univ]
    rw [hEq, unmarkedCard N M S.1, hMcard]
    rw [show (M ∩ S.1).card = (S.1 ∩ M).card from by rw [Finset.inter_comm]]
    rw [hInt]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (S.1 ∩ M).card = x
    exact hx.symm
  · -- (S.1 \ M).card = m - x
    rw [unmarkedCard N S.1 M, hS1, hInt]
  · -- ((univ \ S.1) ∩ M).card = r - x
    exact hInt3
  · -- ((univ \ S.1) \ M).card = (N-m) - (r-x)
    have hUnivS : (Finset.univ \ S.1).card = N - m := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, S.2]
    rw [Finset.card_sdiff, hUnivS]
    rw [show (M ∩ (Finset.univ \ S.1)).card = ((Finset.univ \ S.1) ∩ M).card from by rw [Finset.inter_comm]]
    rw [hInt3]


/- T4: `yMoves` (reachable moves landing at macro count `y`) + `yMoves_biUnion`
   (the disjoint union over `a` of the per-`a` landing moves). -/
def yMoves (N m r k : Nat) (hr : r ≤ N) (S : Membership N m) (x y : Nat) :
    Finset (Finset (Fin N) × Finset (Fin N)) :=
  (reachMoves N m k S).filter
    (fun p : Finset (Fin N) × Finset (Fin N) =>
      x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y)

/- `yMoves` is the union, over `a ∈ 0..k`, of the moves that remove exactly
   `a` marked cards from `S` and land at `y`. -/
theorem yMoves_biUnion (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y : Nat) :
    yMoves N m r k hr S x y =
      Finset.biUnion (Finset.Ico 0 (k + 1))
        (fun a => (reachMoves N m k S).filter
          (fun p : Finset (Fin N) × Finset (Fin N) =>
            (p.1 ∩ markedSet N r hr).card = a ∧
              x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y)) := by
  ext p
  have hL : p ∈ yMoves N m r k hr S x y ↔ p ∈ reachMoves N m k S ∧ x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y := by
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hC, hland2⟩
      refine ⟨hC, ?_⟩
      simpa using hland2
    · intro h
      apply Finset.mem_filter.mpr
      have hland3 : x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y := by
        simpa using h.2
      exact ⟨h.1, hland3⟩
  have hR : p ∈ Finset.biUnion (Finset.Ico 0 (k + 1))
        (fun a => (reachMoves N m k S).filter
          (fun p : Finset (Fin N) × Finset (Fin N) =>
            (p.1 ∩ markedSet N r hr).card = a ∧ x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y)) ↔
      ∃ a ∈ Finset.Ico 0 (k + 1), p ∈ reachMoves N m k S ∧
        (p.1 ∩ markedSet N r hr).card = a ∧ x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y := by
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico]
  rw [hL, hR]
  by_cases hland : x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y
  · by_cases hC : p ∈ reachMoves N m k S
    · -- in the product and lands at y: index by a = (p.1∩M).card (≤ k)
      simp only [hland, hC, and_true]
      constructor
      · -- True → ∃ a ∈ Ico 0 (k+1), (p.1∩M).card = a
        intro _
        use (p.1 ∩ markedSet N r hr).card
        have hfC : p.1 ∈ Finset.powersetCard k S.1 ∧
            p.2 ∈ Finset.powersetCard k (Finset.univ \ S.1) := by
          simpa only [reachMoves, Finset.mem_product] using hC
        have hf1 : p.1 ⊆ S.1 ∧ (p.1).card = k := by
          simpa only [Finset.mem_powersetCard] using hfC.1
        have hcard : (p.1).card = k := hf1.2
        have hsub : (p.1 ∩ markedSet N r hr) ⊆ (p.1) := by
          intro z hz
          exact (Finset.mem_inter.mp hz).1
        have hle : (p.1 ∩ markedSet N r hr).card ≤ k := by
          calc
            (p.1 ∩ markedSet N r hr).card ≤ (p.1).card := Finset.card_le_card hsub
            _ = k := hcard
        simp only [Finset.mem_Ico, and_true]
        exact ⟨Nat.zero_le _, by omega⟩
      · -- ∃ ... → True
        intro _
        trivial
    · -- not in the product: both sides false
      simp only [hland, hC, and_false]
      tauto
  · -- does not land at y: both sides false
    simp only [hland, and_false]
    tauto


/- T4: `Pa(a)` (moves removing exactly a marked cards, landing at y) + `Pa_disjoint` -/
def Pa (N m r k : Nat) (hr : r ≤ N) (S : Membership N m) (x y a : Nat) :
    Finset (Finset (Fin N) × Finset (Fin N)) :=
  (reachMoves N m k S).filter
    (fun p : Finset (Fin N) × Finset (Fin N) =>
      (p.1 ∩ markedSet N r hr).card = a ∧
        x - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card = y)

/- Two `Pa a` with different `a` are disjoint (a move has exactly one value of
   `(p.1 ∩ M).card`). -/
theorem Pa_disjoint (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y : Nat) (a b : Nat) (hab : a ≠ b) :
    Disjoint (Pa N m r k hr S x y a) (Pa N m r k hr S x y b) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hpa : p ∈ Pa N m r k hr S x y a := (Finset.mem_inter.mp hp).1
  have hpb : p ∈ Pa N m r k hr S x y b := (Finset.mem_inter.mp hp).2
  have hA : (p.1 ∩ markedSet N r hr).card = a := (Finset.mem_filter.mp hpa).2.1
  have hB : (p.1 ∩ markedSet N r hr).card = b := (Finset.mem_filter.mp hpb).2.1
  exact hab (hA.symm.trans hB)


/- T4: filtering yMoves on (p.1∩M).card = a gives Pa(a). -/
theorem yMoves_fiberCard (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y a : Nat) :
    (yMoves N m r k hr S x y).filter
      (fun p : Finset (Fin N) × Finset (Fin N) => (p.1 ∩ markedSet N r hr).card = a) =
      Pa N m r k hr S x y a := by
  ext p
  simp only [yMoves, Pa, Finset.mem_filter]
  tauto

/- T4: card of a finite disjoint union: `#(s.biUnion t) = ∑ i ∈ s, #(t i)` when
   the fibers `t i` are pairwise disjoint for `i ≠ j`. The general
   `Finset.card_biUnion` asks for `Set.PairwiseDisjoint`, i.e. `∀ i ∈ s, ∀ j ∈
   s, Disjoint (t i) (t j)` including the `i = j` case — too strong when the
   fibers are nonempty. This inductive version only needs `i ≠ j`, which is
   what the `Pa` fibers satisfy (a move has exactly one `(p.1 ∩ M).card`). -/
theorem card_biUnion_pd {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {t : ι → Finset α}
    (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Finset.card (s.biUnion t) = Finset.sum s fun i => Finset.card (t i) := by
  induction s using Finset.induction_on with
  | empty =>
      have hE : (∅ : Finset ι).biUnion t = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨a, ha, _⟩
        exact Finset.notMem_empty a ha
      rw [hE, Finset.card_empty, Finset.sum_empty]
  | insert a s ha IH =>
      have hU : (insert a s).biUnion t = t a ∪ s.biUnion t := by
        ext x
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨a1, ha1, hx⟩
          rw [Finset.mem_insert] at ha1
          rcases ha1 with (heq | hm)
          · subst a1
            rw [Finset.mem_union]
            exact Or.inl hx
          · rw [Finset.mem_union]
            exact Or.inr (Finset.mem_biUnion.mpr ⟨a1, hm, hx⟩)
        · intro h
          rw [Finset.mem_union] at h
          rcases h with (hx | ha)
          · exact Finset.mem_biUnion.mpr ⟨a, (Finset.mem_insert).mpr (Or.inl rfl), hx⟩
          · rcases Finset.mem_biUnion.mp ha with ⟨a1, hm, hx⟩
            exact Finset.mem_biUnion.mpr ⟨a1, (Finset.mem_insert).mpr (Or.inr hm), hx⟩
      rw [hU]
      have hDisj : Disjoint (t a) (s.biUnion t) := by
        rw [Finset.disjoint_left]
        intro p hp hcontra
        rcases Finset.mem_biUnion.mp hcontra with ⟨j, hj, hzj⟩
        have hne : j ≠ a := by
          intro heq
          exact ha (heq ▸ hj)
        exact (Finset.disjoint_left.mp (h j a hne)) hzj hp
      have hIntEmpty : t a ∩ s.biUnion t = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty]
        exact hDisj
      have hIntZero : (t a ∩ s.biUnion t).card = 0 := by
        rw [hIntEmpty, Finset.card_empty]
      rw [Finset.sum_insert ha, IH.symm, ← Finset.card_union_add_card_inter, hIntZero, add_zero]

/- T4: `#yMoves = Σ_{a ∈ 0..k} #Pa(a)` — the count-level transition formula's
   left side: the moves landing at macro count `y` are partitioned, over
   `a ∈ 0..k`, by how many marked cards they remove from `S` (the `Pa` are
   disjoint by `Pa_disjoint`; their union is `yMoves` by `yMoves_biUnion`). -/
theorem yMoves_card_eq_sum (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y : Nat) :
    (yMoves N m r k hr S x y).card =
      Finset.sum (Finset.Ico 0 (k + 1)) fun a => (Pa N m r k hr S x y a).card := by
  have hBi : yMoves N m r k hr S x y =
      Finset.biUnion (Finset.Ico 0 (k + 1)) fun a => Pa N m r k hr S x y a := by
    rw [yMoves_biUnion]
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Pa]
    tauto
  rw [hBi, card_biUnion_pd fun i j hij => Pa_disjoint N m r k hm hr S x y i j hij]

/- T4: `transitionTerm` — the `a`-summand of
   `BernoulliLaplaceGeneral.transitionNumerator N m r k x y`: the moves from
   a membership carrying `x` marked cards landing at `y`, indexed by
   `a = (p.1 ∩ M).card`, the marked cards removed from `S`. The four factors
   are (marked staying in `S`, unmarked staying in `S`, marked arriving from
   the complement, unmarked arriving from the complement). -/
def transitionTerm (N m r k x y a : Nat) : Nat :=
  let remaining := x - a
  if remaining ≤ y then
    let b := y - remaining
    if b ≤ k then
      Nat.choose x a *
        Nat.choose (m - x) (k - a) *
        Nat.choose (r - x) b *
        Nat.choose ((N - m) - (r - x)) (k - b)
    else 0
  else 0

/- `transitionNumerator N m r k x y` is the sum of its `transitionTerm`
   summands over `a ∈ 0..k` (the definition's `let`-bindings unfold
   definitionally, so this is `rfl` after `dsimp`). -/
theorem transitionNumerator_eq_sum_transitionTerm (N m r k x y : Nat) :
    BernoulliLaplaceGeneral.transitionNumerator N m r k x y =
      (Finset.range (k + 1)).sum fun a => transitionTerm N m r k x y a := by
  dsimp only [BernoulliLaplaceGeneral.transitionNumerator, transitionTerm]

/- T4: one `Pa` fiber's count is the corresponding `transitionTerm` summand:
   `pieceCount`'s left side *is* `Pa` (the identical filter on `reachMoves`),
   and `markedPileCards` rewrites the four binomial bases to
   `x, m - x, r - x, (N - m) - (r - x)`. -/
theorem Pa_card_eq_transitionTerm (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y a : Nat) (ha : a ≤ k)
    (hx : x = (S.1 ∩ markedSet N r hr).card) :
    (Pa N m r k hr S x y a).card = transitionTerm N m r k x y a := by
  dsimp only [Pa, transitionTerm]
  rw [pieceCount N m r hm hr k x y a ha S hx]
  by_cases hC1 : x - a ≤ y
  · by_cases hC2 : y - (x - a) ≤ k
    · have h1 := (markedPileCards N m r hm hr S x hx).1
      have h2 := (markedPileCards N m r hm hr S x hx).2.1
      have h3 := (markedPileCards N m r hm hr S x hx).2.2.1
      have h4 := (markedPileCards N m r hm hr S x hx).2.2.2
      rw [ite_eq_left hC1, ite_eq_left hC1, ite_eq_left hC2, ite_eq_left hC2]
      simp only [h1, h2, h3, h4]
    · rw [ite_eq_left hC1, ite_eq_left hC1, ite_eq_right hC2, ite_eq_right hC2]
  · rw [ite_eq_right hC1, ite_eq_right hC1]

/- T4 capstone: the number of reachable `k`-exchange moves from a membership
   carrying `x` marked cards that land at macro count `y` is the
   Bernoulli--Laplace transition numerator: sum the per-`a` `Pa` counts
   (`yMoves_card_eq_sum`), each of which is the corresponding `transitionTerm`
   summand (`Pa_card_eq_transitionTerm`). No admissibility regime is needed:
   the `Nat`-saturated `choose` factors and the two `ite` guards already
   vanish on impossible regimes. -/
theorem yMoves_card_eq_transitionNumerator (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S : Membership N m) (x y : Nat) (hx : x = (S.1 ∩ markedSet N r hr).card) :
    (yMoves N m r k hr S x y).card = BernoulliLaplaceGeneral.transitionNumerator N m r k x y := by
  have hIco : Finset.Ico 0 (k + 1) = Finset.range (k + 1) := by
    ext a
    simp_rw [Finset.mem_Ico, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le a, h⟩⟩
  calc
    (yMoves N m r k hr S x y).card
      = ∑ a ∈ Finset.Ico 0 (k + 1), (Pa N m r k hr S x y a).card :=
        yMoves_card_eq_sum N m r k hm hr S x y
    _ = ∑ a ∈ Finset.range (k + 1), (Pa N m r k hr S x y a).card :=
      Finset.sum_congr hIco fun _ _ => rfl
    _ = ∑ a ∈ Finset.range (k + 1), transitionTerm N m r k x y a := by
      apply Finset.sum_congr rfl
      intro a ha
      have haK : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      exact Pa_card_eq_transitionTerm N m r k hm hr S x y a haK hx
    _ = BernoulliLaplaceGeneral.transitionNumerator N m r k x y :=
      (transitionNumerator_eq_sum_transitionTerm N m r k x y).symm

/- T2 at the (m-pile, x-marked) level: any two `m`-piles holding the same
   number `x` of marked cards are related by a **marked-preserving**
   permutation (one that stabilizes `M = markedSet`). Generalizes
   `Fiber.fibTransitive`, which used arbitrary permutations; the M-invariant
   group is what the T4 fiber-uniform intertwining needs (it conjugates
   moves between two targets in the same count-fiber). -/
theorem markedFiberTransitive (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : Nat)
    (S T : Membership N m) (hS : (S.1 ∩ markedSet N r hr).card = x)
    (hT : (T.1 ∩ markedSet N r hr).card = x) :
    ∃ g : Equiv.Perm (Fin N),
        g '' S.1 = T.1 ∧ g '' (markedSet N r hr) = markedSet N r hr := by
  classical
  let M : Finset (Fin N) := markedSet N r hr
  let MC : Finset (Fin N) := markedComp N r hr
  have hC1 (X : Membership N m) (hX : (X.1 ∩ M).card = x) :
      Fintype.card {a : Fin N // a ∈ M ∧ a ∈ X.1} = x := by
    rw [Fintype.card_subtype (fun a : Fin N => a ∈ M ∧ a ∈ X.1)]
    have hF : (Finset.univ : Finset (Fin N)).filter (fun a => a ∈ M ∧ a ∈ X.1) =
        M ∩ X.1 := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    rw [hF, Finset.inter_comm M X.1]
    exact hX

  have hC2 (X : Membership N m) (hX : (X.1 ∩ M).card = x) :
      Fintype.card {a : Fin N // a ∈ M ∧ a ∉ X.1} = r - x := by
    rw [Fintype.card_subtype (fun a : Fin N => a ∈ M ∧ a ∉ X.1)]
    have hF : (Finset.univ : Finset (Fin N)).filter (fun a => a ∈ M ∧ a ∉ X.1) =
        M \ X.1 := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [hF, Finset.card_sdiff, markedSet_card N r hr, hX]

  have hC3 (X : Membership N m) (hX : (X.1 ∩ M).card = x) :
      Fintype.card {a : Fin N // a ∉ M ∧ a ∈ X.1} = m - x := by
    rw [Fintype.card_subtype (fun a : Fin N => a ∉ M ∧ a ∈ X.1)]
    have hF : (Finset.univ : Finset (Fin N)).filter (fun a => a ∉ M ∧ a ∈ X.1) =
        X.1 \ M := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_not, and_comm]
    rw [hF, unmarkedCard _ X.1 M, X.2, hX]

  have hC4 (X : Membership N m) (hX : (X.1 ∩ M).card = x) :
      Fintype.card {a : Fin N // a ∉ M ∧ a ∉ X.1} = (N - r) - (m - x) := by
    let U : Finset (Fin N) := Finset.univ
    rw [Fintype.card_subtype (fun a : Fin N => a ∉ M ∧ a ∉ X.1)]
    have hF : U.filter (fun a => a ∉ M ∧ a ∉ X.1) = ((U \ M) \ X.1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and, not_not, and_assoc]
    rw [hF, Finset.card_sdiff]
    have hI : (X.1 ∩ (U \ M)) = X.1 \ M := by
      ext a
      constructor
      · intro h
        rw [Finset.mem_inter, Finset.mem_sdiff] at h
        rw [Finset.mem_sdiff]
        exact ⟨h.1, h.2.2⟩
      · intro h
        rw [Finset.mem_sdiff] at h
        rw [Finset.mem_inter, Finset.mem_sdiff]
        exact ⟨h.1, Finset.mem_univ _, h.2⟩
    rw [hI, unmarkedCard _ X.1 M, X.2, hX]
    have hUM : (U \ M).card = N - r := by
      change (markedComp N r hr).card = N - r
      exact markedComp_card N r hr
    rw [hUM]

  have hS1 := hC1 S hS
  have hS2 := hC2 S hS
  have hS3 := hC3 S hS
  have hS4 := hC4 S hS
  have hT1 := hC1 T hT
  have hT2 := hC2 T hT
  have hT3 := hC3 T hT
  have hT4 := hC4 T hT
  let eSM : {a : Fin N // a ∈ M ∧ a ∈ S.1} ≃ {a : Fin N // a ∈ M ∧ a ∈ T.1} :=
      Fintype.equivOfCardEq (by rw [hS1, hT1])
  let eSU : {a : Fin N // a ∈ M ∧ a ∉ S.1} ≃ {a : Fin N // a ∈ M ∧ a ∉ T.1} :=
      Fintype.equivOfCardEq (by rw [hS2, hT2])
  let eUM : {a : Fin N // a ∉ M ∧ a ∈ S.1} ≃ {a : Fin N // a ∉ M ∧ a ∈ T.1} :=
      Fintype.equivOfCardEq (by rw [hS3, hT3])
  let eUU : {a : Fin N // a ∉ M ∧ a ∉ S.1} ≃ {a : Fin N // a ∉ M ∧ a ∉ T.1} :=
      Fintype.equivOfCardEq (by rw [hS4, hT4])
  let g : Fin N → Fin N := fun x => by
    by_cases hxs : x ∈ S.1
    · by_cases hxm : x ∈ M
      · exact (eSM ⟨x, ⟨hxm, hxs⟩⟩).1
      · exact (eUM ⟨x, ⟨hxm, hxs⟩⟩).1
    · by_cases hxm : x ∈ M
      · exact (eSU ⟨x, ⟨hxm, hxs⟩⟩).1
      · exact (eUU ⟨x, ⟨hxm, hxs⟩⟩).1
  -- value lemmas: by_cases adds the branch facts to the context; simp only
  -- [hA, hB, ite_true, ite_false] reduces the if-then-else body of g to the
  -- matching branch value; congrArg + Subtype.ext (proof irrelevance) closes
  -- the matching branch, and the non-matching branches are contradictions.
  have hSMval (x : Fin N) (hM : x ∈ M) (hS : x ∈ S.1) :
      g x = (eSM ⟨x, ⟨hM, hS⟩⟩).1 := by
    by_cases hA : x ∈ S.1
    · by_cases hB : x ∈ M
      · simp only [g, hA, hB, ite_true, ite_false]
        refine congrArg (fun z => (eSM z).1) ?_
        exact Subtype.ext rfl
      · exfalso
        exact hB hM
    · exfalso
      exact hA hS
  have hUMval (x : Fin N) (hM : x ∉ M) (hS : x ∈ S.1) :
      g x = (eUM ⟨x, ⟨hM, hS⟩⟩).1 := by
    by_cases hA : x ∈ S.1
    · by_cases hB : x ∈ M
      · exfalso
        exact hM hB
      · simp only [g, hA, hB, ite_true, ite_false]
        refine congrArg (fun z => (eUM z).1) ?_
        exact Subtype.ext rfl
    · exfalso
      exact hA hS
  have hSUval (x : Fin N) (hM : x ∈ M) (hS : x ∉ S.1) :
      g x = (eSU ⟨x, ⟨hM, hS⟩⟩).1 := by
    by_cases hA : x ∈ S.1
    · exfalso
      exact hS hA
    · by_cases hB : x ∈ M
      · simp only [g, hA, hB, ite_true, ite_false]
        refine congrArg (fun z => (eSU z).1) ?_
        exact Subtype.ext rfl
      · exfalso
        exact hB hM
  have hUUval (x : Fin N) (hM : x ∉ M) (hS : x ∉ S.1) :
      g x = (eUU ⟨x, ⟨hM, hS⟩⟩).1 := by
    by_cases hA : x ∈ S.1
    · exfalso
      exact hS hA
    · by_cases hB : x ∈ M
      · exfalso
        exact hM hB
      · simp only [g, hA, hB, ite_true, ite_false]
        refine congrArg (fun z => (eUU z).1) ?_
        exact Subtype.ext rfl

  -- region-image lemmas: g sends each S-region onto the corresponding T-region
  have hSMimg : ∀ x (hM : x ∈ M) (hS : x ∈ S.1), (eSM ⟨x, ⟨hM, hS⟩⟩).1 ∈ M ∧ (eSM ⟨x, ⟨hM, hS⟩⟩).1 ∈ T.1 :=
      fun x hM hS => (eSM ⟨x, ⟨hM, hS⟩⟩).2
  have hUMimg : ∀ x (hM : x ∉ M) (hS : x ∈ S.1), (eUM ⟨x, ⟨hM, hS⟩⟩).1 ∉ M ∧ (eUM ⟨x, ⟨hM, hS⟩⟩).1 ∈ T.1 :=
      fun x hM hS => (eUM ⟨x, ⟨hM, hS⟩⟩).2
  -- surjective: every z in one of the four T-regions has a preimage in the S-region
  have hSurj : Function.Surjective g := by
    intro z
    by_cases hzM : z ∈ M
    · by_cases hzT : z ∈ T.1
      · obtain ⟨a, ha⟩ := eSM.surjective ⟨z, ⟨hzM, hzT⟩⟩
        have hv : g a.1 = z := by
          rw [hSMval (a.1) a.2.1 a.2.2]
          simpa [ha]
        exact ⟨a.1, hv⟩
      · obtain ⟨a, ha⟩ := eSU.surjective ⟨z, ⟨hzM, hzT⟩⟩
        have hv : g a.1 = z := by
          rw [hSUval (a.1) a.2.1 a.2.2, ha]
        exact ⟨a.1, hv⟩
    · by_cases hzT : z ∈ T.1
      · obtain ⟨a, ha⟩ := eUM.surjective ⟨z, ⟨hzM, hzT⟩⟩
        have hv : g a.1 = z := by
          rw [hUMval (a.1) a.2.1 a.2.2, ha]
        exact ⟨a.1, hv⟩
      · obtain ⟨a, ha⟩ := eUU.surjective ⟨z, ⟨hzM, hzT⟩⟩
        have hv : g a.1 = z := by
          rw [hUUval (a.1) a.2.1 a.2.2, ha]
        exact ⟨a.1, hv⟩
  have hBij : Function.Bijective g := by
    constructor
    · exact Finite.injective_iff_surjective.mpr hSurj
    · exact hSurj
  -- image of S.1 is T.1
  have hImgS : g '' S.1 = T.1 := by
    ext z
    constructor
    · intro hmem
      rcases hmem with ⟨a, haS, rfl⟩
      by_cases haM : a ∈ M
      · rw [hSMval a haM haS]
        exact (eSM ⟨a, ⟨haM, haS⟩⟩).2.2
      · rw [hUMval a haM haS]
        exact (eUM ⟨a, ⟨haM, haS⟩⟩).2.2
    · intro hzT
      by_cases hzM : z ∈ M
      · obtain ⟨a, ha⟩ := eSM.surjective ⟨z, ⟨hzM, hzT⟩⟩
        exact ⟨a.1, a.2.2, by rw [hSMval (a.1) a.2.1 a.2.2, ha]⟩
      · obtain ⟨a, ha⟩ := eUM.surjective ⟨z, ⟨hzM, hzT⟩⟩
        exact ⟨a.1, a.2.2, by rw [hUMval (a.1) a.2.1 a.2.2, ha]⟩
  -- image of M is M
  have hImgM : g '' M = M := by
    ext z
    constructor
    · intro hmem
      rcases hmem with ⟨a, haM, rfl⟩
      by_cases haS : a ∈ S.1
      · rw [hSMval a haM haS]
        exact (eSM ⟨a, ⟨haM, haS⟩⟩).2.1
      · rw [hSUval a haM haS]
        exact (eSU ⟨a, ⟨haM, haS⟩⟩).2.1
    · intro hzM
      by_cases hzT : z ∈ T.1
      · obtain ⟨a, ha⟩ := eSM.surjective ⟨z, ⟨hzM, hzT⟩⟩
        exact ⟨a.1, a.2.1, by rw [hSMval (a.1) a.2.1 a.2.2, ha]⟩
      · obtain ⟨a, ha⟩ := eSU.surjective ⟨z, ⟨hzM, hzT⟩⟩
        exact ⟨a.1, a.2.1, by rw [hSUval (a.1) a.2.1 a.2.2, ha]⟩
  exact ⟨Equiv.ofBijective g hBij, hImgS, hImgM⟩

/-! ## T4 measure half: count projection, count-fiber cardinality, fiber-uniformity

The macrostate of a pile is its count of marked cards, as a `BLState`. The
count-fiber over a macrostate has the hypergeometric cardinality, and the
exchange count `#yMoves` is constant along a fiber: the counting form of the
uniform-fiber-to-BL-kernel intertwining.
-/ 

/-- The macrostate of a pile: its number of marked (initially-left) cards,
    with the admissibility bounds checked. -/
noncomputable def countOf (N m r : Nat) (hr : r ≤ N) (S : Membership N m) :
    BernoulliLaplaceGeneral.BLState N m r := by
  let M := markedSet N r hr
  set x := (S.1 ∩ M).card with hx
  refine ⟨x, ?_, ?_⟩
  · -- lo: x ≥ BernoulliLaplaceGeneral.blLo = max (r - (N - m)) 0
    rw [BernoulliLaplaceGeneral.blLo]
    refine max_le_iff.mpr ⟨?_, by omega⟩
    by_cases hNmr : N - m ≤ r
    · -- max = r - (N - m); show r - x ≤ N - m, i.e. x ≥ r - (N - m)
      have hRsub : (M \ S.1).card = r - x := by
        rw [Finset.card_sdiff, markedSet_card N r hr, hx]
      have hSub : M \ S.1 ⊆ (Finset.univ : Finset (Fin N)) \ S.1 := by
        intro a ha
        rw [Finset.mem_sdiff] at ha ⊢
        exact ⟨Finset.mem_univ a, ha.2⟩
      have hUcard : ((Finset.univ : Finset (Fin N)) \ S.1).card = N - m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.1),
            Finset.card_univ, Fintype.card_fin, S.2]
      have hCap : r - x ≤ N - m := by
        calc
          r - x = (M \ S.1).card := hRsub.symm
          _ ≤ ((Finset.univ : Finset (Fin N)) \ S.1).card := Finset.card_le_card hSub
          _ = N - m := hUcard
      have hle : r ≤ x + (N - m) := by
        rw [Nat.sub_le_iff_le_add] at hCap
        simpa [Nat.add_comm] using hCap
      rw [Nat.sub_le_iff_le_add]
      exact hle
    · -- r < N - m, so r - (N - m) = 0 ≤ x
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hNmr))]
      omega
  · -- hi: x ≤ BernoulliLaplaceGeneral.blHi = min m r
    rw [BernoulliLaplaceGeneral.blHi]
    exact Nat.le_min.mpr ⟨
      by
        calc (S.1 ∩ markedSet N r hr).card ≤ (S.1).card :=
              Finset.card_le_card (Finset.inter_subset_left : S.1 ∩ markedSet N r hr ⊆ S.1)
          _ = m := S.2,
      by
        calc (S.1 ∩ markedSet N r hr).card ≤ (markedSet N r hr).card :=
              Finset.card_le_card (Finset.inter_subset_right : S.1 ∩ markedSet N r hr ⊆ markedSet N r hr)
          _ = r := markedSet_card N r hr⟩

/-- The first projection of `countOf`: the marked-card count. -/
@[simp] theorem countOf_val (N m r : Nat) (hr : r ≤ N) (S : Membership N m) :
    (countOf N m r hr S).val = (S.1 ∩ markedSet N r hr).card := by
  dsimp only [countOf]

/-- The count-fiber over `Membership` (the G1 typed pile): the piles whose
    macrostate is `x`. Distinct from the `pileSet`-based `countFiber` above:
    this one is the fiber the measure-level intertwining sums over; the two
    carry the same hypergeometric cardinality. -/
def countFiberMemb (N m r : Nat) (hr : r ≤ N) (x : BernoulliLaplaceGeneral.BLState N m r) :
    Finset (Membership N m) :=
  (Finset.univ : Finset (Membership N m)).filter (fun S =>
    (S.1 ∩ markedSet N r hr).card = x.val)

/- The fiber is the set of marked-part/unmarked-part choices: a pile in the
   fiber is (up to bijection) a pair (A, B) with A a size-`x` subset of the
   marked set and B a size-`(m - x)` subset of the unmarked set. -/
def countFiberMemb_equiv (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : BernoulliLaplaceGeneral.BLState N m r) :
    ({S : Membership N m // (S.1 ∩ markedSet N r hr).card = x.val} : Type) ≃
      {p : Finset (Fin N) × Finset (Fin N) //
        p.1 ∈ (markedSet N r hr).powersetCard x.val ∧
        p.2 ∈ (markedComp N r hr).powersetCard (m - x.val)} := by
  let M := markedSet N r hr
  let MC := markedComp N r hr
  have hxm : x.val ≤ m := (Nat.le_min.mp x.2.2).1
  have hDis : Disjoint M MC := markedDisjoint N r hr
  have hMC : MC = (Finset.univ : Finset (Fin N)) \ M := rfl
  have hMCempty : M ∩ MC = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDis
  let f : {S : Membership N m // (S.1 ∩ M).card = x.val} →
          {p : Finset (Fin N) × Finset (Fin N) //
            p.1 ∈ M.powersetCard x.val ∧ p.2 ∈ MC.powersetCard (m - x.val)} :=
    fun S =>
      let sF : Finset (Fin N) := S.1
      ⟨⟨sF ∩ M, sF \ M⟩, by
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_powersetCard]
          exact ⟨(Finset.inter_subset_right : sF ∩ M ⊆ M), S.2⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, ?_⟩
          · intro a ha
            rw [Finset.mem_sdiff] at ha
            rw [hMC, Finset.mem_sdiff]
            exact ⟨Finset.mem_univ a, ha.2⟩
          · rw [unmarkedCard _ sF M, S.1.2, S.2]
            ⟩
  let g : {p : Finset (Fin N) × Finset (Fin N) //
            p.1 ∈ M.powersetCard x.val ∧ p.2 ∈ MC.powersetCard (m - x.val)} →
          {S : Membership N m // (S.1 ∩ M).card = x.val} :=
    fun p =>
      let A := p.1.1
      let B := p.1.2
      let hA := (Finset.mem_powersetCard.mp p.2.1 : A ⊆ M ∧ A.card = x.val)
      let hB := (Finset.mem_powersetCard.mp p.2.2 : B ⊆ MC ∧ B.card = m - x.val)
      let hDisAB : Disjoint A B := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext a
        rw [Finset.mem_inter]
        constructor
        · intro h
          have hIn : a ∈ M ∩ MC :=
            Finset.mem_inter.mpr ⟨hA.1 h.1, hB.1 h.2⟩
          rw [hMCempty] at hIn
          exact hIn
        · intro h
          cases h
      let hCardAB : (A ∪ B).card = m := by
        rw [Finset.card_union_of_disjoint hDisAB, hA.2, hB.2,
            Nat.add_comm, Nat.sub_add_cancel hxm]
      let hInter : (A ∪ B) ∩ M = A := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro h
          rcases h.1 with hA' | hB'
          · exact hA'
          · exfalso
            have hIn : a ∈ M ∩ MC := Finset.mem_inter.mpr ⟨h.2, hB.1 hB'⟩
            rw [hMCempty] at hIn
            exact Finset.notMem_empty a hIn
        · intro h
          exact ⟨Or.inl h, hA.1 h⟩
      let hSDiff : (A ∪ B) \ M = B := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro h
          rcases h.1 with hA' | hB'
          · exfalso
            exact h.2 (hA.1 hA')
          · exact hB'
        · intro hb
          exact ⟨Or.inr hb, by
            intro hM
            have hIn : a ∈ M ∩ MC := Finset.mem_inter.mpr ⟨hM, hB.1 hb⟩
            rw [hMCempty] at hIn
            exact Finset.notMem_empty a hIn⟩
      let hFiber : ((A ∪ B) ∩ M).card = x.val := by
        rw [hInter, hA.2]
      ⟨⟨A ∪ B, hCardAB⟩, hFiber⟩
  refine Equiv.mk f g ?_ ?_
  · -- g ∘ f = id: the split parts recombine to S.1 by markSplit
    intro S
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [g, f]
    exact (markSplit _ _ M).symm
  · -- f ∘ g = id: the marked part of A ∪ B is A, the unmarked part is B
    intro T
    let A := T.1.1
    let B := T.1.2
    have hA : A ⊆ M := (Finset.mem_powersetCard.mp T.2.1).1
    have hBMC : B ⊆ MC := (Finset.mem_powersetCard.mp T.2.2).1
    have hInterT : (A ∪ B) ∩ M = A := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h.1 with hA' | hB'
        · exact hA'
        · exfalso
          have hIn : a ∈ M ∩ MC := Finset.mem_inter.mpr ⟨h.2, hBMC hB'⟩
          rw [hMCempty] at hIn
          exact Finset.notMem_empty a hIn
      · exact ⟨Or.inl h, hA h⟩
    have hSDiffT : (A ∪ B) \ M = B := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h.1 with hA' | hB'
        · exfalso
          exact h.2 (hA hA')
        · exact hB'
      · have hNotM : a ∉ M := by
          intro hM
          have hIn : a ∈ M ∩ MC := Finset.mem_inter.mpr ⟨hM, hBMC h⟩
          rw [hMCempty] at hIn
          exact Finset.notMem_empty a hIn
        exact ⟨Or.inr h, hNotM⟩
    apply Subtype.ext
    apply Prod.ext
    · dsimp only [g, f]
      exact hInterT
    · dsimp only [g, f]
      exact hSDiffT

/-- The count-fiber cardinality: the hypergeometric number. -/
theorem countFiberMemb_card (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : BernoulliLaplaceGeneral.BLState N m r) :
    (countFiberMemb N m r hr x).card = Nat.choose r x.val * Nat.choose (N - r) (m - x.val) := by
  let M := markedSet N r hr
  let MC := markedComp N r hr
  have hBridge : (countFiberMemb N m r hr x).card =
      Fintype.card {S : Membership N m // (S.1 ∩ M).card = x.val} :=
    (Fintype.card_of_subtype
        (p := fun S => (S.1 ∩ markedSet N r hr).card = x.val)
        (s := countFiberMemb N m r hr x)
        (H := fun S => by
          simp [countFiberMemb, Finset.mem_filter, Finset.mem_univ])).symm
  have hFiberCard : Fintype.card {S : Membership N m // (S.1 ∩ M).card = x.val} =
      Fintype.card {p : Finset (Fin N) × Finset (Fin N) //
        p.1 ∈ M.powersetCard x.val ∧ p.2 ∈ MC.powersetCard (m - x.val)} :=
    Fintype.card_congr (countFiberMemb_equiv N m r hm hr x)
  have hProd : Fintype.card {p : Finset (Fin N) × Finset (Fin N) //
      p.1 ∈ M.powersetCard x.val ∧ p.2 ∈ MC.powersetCard (m - x.val)} =
      (M.powersetCard x.val ×ˢ MC.powersetCard (m - x.val)).card :=
    Fintype.card_of_subtype
      (p := fun p => p.1 ∈ M.powersetCard x.val ∧ p.2 ∈ MC.powersetCard (m - x.val))
      (s := M.powersetCard x.val ×ˢ MC.powersetCard (m - x.val))
      (H := fun p => by simp only [Finset.mem_product])
  rw [hBridge, hFiberCard, hProd, Finset.card_product,
      Finset.card_powersetCard, Finset.card_powersetCard,
      markedSet_card N r hr, markedComp_card N r hr]

/-- Every admissible macrostate is realized: its count-fiber is nonempty. -/
theorem countFiberMemb_nonempty (N m r : Nat) (hm : m ≤ N) (hr : r ≤ N) (x : BernoulliLaplaceGeneral.BLState N m r) :
    0 < (countFiberMemb N m r hr x).card := by
  rw [countFiberMemb_card N m r hm hr x]
  have hxm : x.val ≤ m := (Nat.le_min.mp x.2.2).1
  have hxr : x.val ≤ r := (Nat.le_min.mp x.2.2).2
  have hNmr : m - x.val ≤ N - r := by
    by_cases hL : N - m ≤ r
    · -- x ≥ r - (N - m) and (N - r) + (r - (N - m)) = m
      have hX1raw : BernoulliLaplaceGeneral.blLo N m r ≤ x.val := x.2.1
      dsimp only [BernoulliLaplaceGeneral.blLo] at hX1raw
      have hMax : (max (r - (N - m)) 0 : Nat) = r - (N - m) := by
        exact max_eq_left (Nat.zero_le _)
      have hX1 : r - (N - m) ≤ x.val := by simpa [hMax] using hX1raw
      have hKey : (N - r) + (r - (N - m)) = m := by
        have hNR : r ≤ N := hr
        have hmN : m ≤ N := hm
        omega
      rw [Nat.sub_le_iff_le_add]
      omega
    · -- r < N - m, so N - r > m
      have hNRlt : m < N - r := by omega
      have hLT : m - x.val < N - r := by
        calc
          m - x.val ≤ m := Nat.sub_le m x.val
          _ < N - r := hNRlt
      exact Nat.le_of_lt hLT
  exact mul_pos (Nat.choose_pos hxr) (Nat.choose_pos hNmr)

/-- The exchange count is constant along a count-fiber (counting form of the
    fiber-uniformity). -/
theorem yMoves_uniformOnFiber (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (S T : Membership N m) (x y : Nat)
    (hS : (S.1 ∩ markedSet N r hr).card = x)
    (hT : (T.1 ∩ markedSet N r hr).card = x) :
    (yMoves N m r k hr S x y).card = (yMoves N m r k hr T x y).card := by
  rw [yMoves_card_eq_transitionNumerator N m r k hm hr S x y hS.symm,
      yMoves_card_eq_transitionNumerator N m r k hm hr T x y hT.symm]

/-- The fiber-pushforward count: the total exchange count out of a whole
    count-fiber into the `y`-fiber is `#fiber · transitionNumerator` — the
    counting form of the uniform-fiber-to-BL-kernel intertwining. -/
theorem fiberPushforward_count (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (x y : BernoulliLaplaceGeneral.BLState N m r) :
    (∑ S ∈ countFiberMemb N m r hr x, (yMoves N m r k hr S x.val y.val).card) =
      (countFiberMemb N m r hr x).card * BernoulliLaplaceGeneral.transitionNumerator N m r k x.val y.val := by
  have hPt : ∀ S ∈ countFiberMemb N m r hr x,
      (yMoves N m r k hr S x.val y.val).card = BernoulliLaplaceGeneral.transitionNumerator N m r k x.val y.val := by
    intro S hS
    dsimp only [countFiberMemb] at hS
    simp only [Finset.mem_filter, Finset.mem_univ] at hS
    have hCard : (S.1 ∩ markedSet N r hr).card = x.val := by tauto
    rw [yMoves_card_eq_transitionNumerator N m r k hm hr S x.val y.val hCard.symm]
  rw [Finset.sum_const_nat hPt]

/-- The macrostate kernel is the pushforward of the fiber-uniform kernel: a
    fiber-uniform start at `x` puts mass `BernoulliLaplaceGeneral.transitionWeight x y` on the `y`-fiber
    after one exchange. -/
theorem uniformFiber_intertwines (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x y : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :
    (∑ S ∈ countFiberMemb p.N p.m p.r p.hrN x,
        ((yMoves p.N p.m p.r p.k p.hrN S x.val y.val).card : Rat) /
          (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat)) /
      ((countFiberMemb p.N p.m p.r p.hrN x).card : Rat) =
      BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val y.val := by
  let hr := p.hrN
  have hEach (S : Membership p.N p.m) (hS : S ∈ countFiberMemb p.N p.m p.r hr x) :
      ((yMoves p.N p.m p.r p.k hr S x.val y.val).card : Rat) /
        (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat) =
        BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val y.val := by
    dsimp only [countFiberMemb] at hS
    simp only [Finset.mem_filter, Finset.mem_univ] at hS
    have hCard : (S.1 ∩ markedSet p.N p.r hr).card = x.val := by tauto
    rw [yMoves_card_eq_transitionNumerator p.N p.m p.r p.k (Nat.le_of_lt p.hmn) hr S x.val y.val hCard.symm,
        BernoulliLaplaceGeneral.transitionWeight]
  have hSum : (∑ S ∈ countFiberMemb p.N p.m p.r hr x,
      ((yMoves p.N p.m p.r p.k hr S x.val y.val).card : Rat) /
        (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat)) =
      (countFiberMemb p.N p.m p.r hr x).card * BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val y.val := by
    rw [Finset.sum_congr rfl (fun S hS => hEach S hS), Finset.sum_const]
    ring
  have hPos : 0 < (countFiberMemb p.N p.m p.r p.hrN x).card :=
    countFiberMemb_nonempty p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN x
  rw [hSum]
  field_simp [hPos.ne']

/-! ### The fiber-uniform membership lift (G4 kernel half)

The "uniform count-fiber membership" kernel: from a `BLState` count it
resamples uniformly over the marked-count fiber. Together with
`subsetExchangeKernel` (T3) and `blExchangeKernel` it is the material for
the G4 macro-intertwining kernel equality
`uniform count-fiber >> subsetExchange = blExchange >> uniform count-fiber`,
the theorem that discharges the Commander A3 by instantiation.
-/

/-- A membership has marked count `x.val` iff it lies in the `countFiberMemb`
    finset (the `countInPile` projection spelled out). -/
theorem countInPile_countFiberMemb
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (S : Membership p.N p.m) :
    (countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S).val = x.val ↔
      S ∈ countFiberMemb p.N p.m p.r p.hrN x := by
  simp [countInPile_val, countInPileVal, countFiberMemb,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- The univ-filter by `countInPile`-count is exactly `countFiberMemb`. -/
theorem uniformCountFiber_univFilter
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :
    (Finset.univ : Finset (Membership p.N p.m)).filter
      (fun S => (countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S).val = x.val) =
      countFiberMemb p.N p.m p.r p.hrN x := by
  ext S
  simpa using countInPile_countFiberMemb p x S

/-- The fiber-uniform membership lift: from a `BLState` count `x` it
    resamples uniformly among the memberships whose marked count is `x.val`,
    zero elsewhere. The denominator is the proven choose-product fiber card
    (`countFiberMemb_card`), so normalisation is a pure finite-cardinality
    computation (the F2 `membershipLift` pattern, generalized to arbitrary
    `N m r`). The "uniform count-fiber membership" half of the G4
    macro-intertwining kernel equality. -/
noncomputable def uniformCountFiberMembership
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel (BernoulliLaplaceGeneral.BLState p.N p.m p.r)
                (Membership p.N p.m) := by
  let hr := p.hrN
  let hm := Nat.le_of_lt p.hmn
  refine fun x => Dist.ofFun
    (fun S : Membership p.N p.m =>
      if (countInPile p.N p.m p.r hm hr S).val = x.val
      then 1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat)
      else 0)
    ?_ ?_
  · -- nonnegativity
    intro S
    split_ifs <;> positivity
  · -- total mass 1: the univ-filter over the `x`-fiber has exactly `#fiber`
    --   members, each of mass `1 / #fiber`, so the sum is `#fiber / #fiber`.
    calc
      (∑ S : Membership p.N p.m,
        if (countInPile p.N p.m p.r hm hr S).val = x.val
        then 1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat) else 0) =
        (∑ S ∈ (Finset.univ : Finset (Membership p.N p.m)),
          if (countInPile p.N p.m p.r hm hr S).val = x.val
          then 1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat) else 0) := by
        rfl
      _ = ((Finset.univ.filter
              (fun S => (countInPile p.N p.m p.r hm hr S).val = x.val)).card : Rat) *
          (1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat)) := by
        rw [FiberDisintegration.sum_if_constant
            (Finset.univ : Finset (Membership p.N p.m))
            (fun S => (countInPile p.N p.m p.r hm hr S).val = x.val)
            (1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat))]
      _ = ((countFiberMemb p.N p.m p.r hr x).card : Rat) *
          (1 / (↑(countFiberMemb p.N p.m p.r hr x).card : Rat)) := by
        rw [uniformCountFiber_univFilter p x]
      _ = 1 := by
        have hpos : 0 < (countFiberMemb p.N p.m p.r hr x).card :=
          countFiberMemb_nonempty p.N p.m p.r (Nat.le_of_lt p.hmn) hr x
        field_simp [hpos.ne']

/-- The subset-exchange kernel viewed on `Membership N m` (the G4 "subsetExchange"
    kernel): from an `m`-member pile it moves by a `k`-exchange to another `m`-member
    pile with the standard T3 weight. It is exactly `subsetExchangeKernel` (T3) on
    the underlying `Finset (Fin N)`, so nonnegativity and the row-sum-1 follow from
    `subsetExchangeKernel_rowOne`. Together with `uniformCountFiberMembership` and
    `blExchangeKernel` it is the other half of the G4 macro-intertwining kernel
    equality. -/
noncomputable def subsetExchangeMembershipKernel
    (p : BernoulliLaplaceGeneral.ExchangeAdmissible) :
    FiniteKernel (Membership p.N p.m) (Membership p.N p.m) := by
  refine fun S => Dist.ofFun
    (fun T => subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S.1 T.1)
    ?_ ?_
  · -- nonneg: the `then` branch is the inverse of a (nonneg) Nat-cast, the
    --   `else` branch is 0
    intro T
    dsimp only [subsetExchangeKernel]
    split_ifs <;> positivity
  · -- row sum 1: the Fintype sum is definitionally the univ Finset sum, which
    --   is 1 by the T3 row-one lemma
    calc
      (∑ T : Membership p.N p.m,
        subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S.1 T.1) =
        (Finset.univ : Finset (Membership p.N p.m)).sum
          (fun T => subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S.1 T.1) := by
        rfl
      _ = 1 := subsetExchangeKernel_rowOne p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S



/- Marked-count change under a k-exchange move `p = (A, B)` out of `S`:
   the target pile `(S \ A) ∪ B` carries
   `#(S∩M) - #(A∩M) + #(B∩M)` marked cards. This is exactly the
   `yMoves` filter rewritten as a statement about the target's count. -/
theorem markedCountChange (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (hk : k ≤ m) (hkm : k ≤ N - m) (S : Membership N m)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S) :
    (((S.1 \ p.1) ∪ p.2) ∩ markedSet N r hr).card =
      (S.1 ∩ markedSet N r hr).card - (p.1 ∩ markedSet N r hr).card + (p.2 ∩ markedSet N r hr).card := by
  let M := markedSet N r hr
  rcases decomp N m k hm hk hkm S p hp with ⟨hsubA, hcardA, hsubB, hcardB⟩
  have hInt : ((S.1 \ p.1) ∩ M) ∩ (p.2 ∩ M) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro hx
      have hxB : x ∈ p.2 := hx.2.1
      have hxBc : x ∉ S.1 := by
        have h : x ∈ Finset.univ \ S.1 := hsubB hxB
        simpa using h
      exact absurd hx.1.1.1 hxBc
    · intro hx
      exfalso
      simp [Finset.mem_sdiff] at hx
  have hDistrib : ((S.1 \ p.1) ∪ p.2) ∩ M = ((S.1 \ p.1) ∩ M) ∪ (p.2 ∩ M) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hIntCard : (((S.1 \ p.1) ∪ p.2) ∩ M).card = ((S.1 \ p.1) ∩ M).card + (p.2 ∩ M).card := by
    rw [hDistrib]
    have hu : (((S.1 \ p.1) ∩ M) ∪ (p.2 ∩ M)).card + (((S.1 \ p.1) ∩ M) ∩ (p.2 ∩ M)).card =
        ((S.1 \ p.1) ∩ M).card + (p.2 ∩ M).card :=
      Finset.card_union_add_card_inter ((S.1 \ p.1) ∩ M) (p.2 ∩ M)
    have hZero : (((S.1 \ p.1) ∩ M) ∩ (p.2 ∩ M)).card = 0 := by rw [hInt, Finset.card_empty]
    rw [hZero, Nat.add_zero] at hu
    exact hu
  have hLrewrite : (S.1 \ p.1) ∩ M = (S.1 ∩ M) \ p.1 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hLcard : ((S.1 \ p.1) ∩ M).card = (S.1 ∩ M).card - (p.1 ∩ M).card := by
    rw [hLrewrite, Finset.card_sdiff]
    have hInter : (p.1 ∩ (S.1 ∩ M)) = (p.1 ∩ M) := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · intro h; exact ⟨h.1, h.2.2⟩
      · intro h
        have hxS : x ∈ S.1 := hsubA h.1
        exact ⟨h.1, hxS, h.2⟩
    simp only [Finset.inter_comm, hInter]
  calc
    (((S.1 \ p.1) ∪ p.2) ∩ M).card = ((S.1 \ p.1) ∩ M).card + (p.2 ∩ M).card := hIntCard
    _ = ((S.1 ∩ M).card - (p.1 ∩ M).card) + (p.2 ∩ M).card := by rw [hLcard]
    _ = (S.1 ∩ M).card - (p.1 ∩ M).card + (p.2 ∩ M).card := by ring


/- The fiber-restricted move/target bijection. The `k`-exchange targets of `S`
   that carry marked-count `y` (the `x`-fiber of the count map) are in bijection with
   the `yMoves` out of `S`: the move `(S.1 \ T.1, T.1 \ S.1)` lands the target `T`
   back, `markedCountChange` is the `y`-landing filter, and `newpile_reach` / the
   inverse-exchange give the two directions. Hence their count is `#yMoves S c y`.
   (See `docs/planning/proof-strategies/2026-11-18-g4-macro-intertwining-plan.md`.)
   -/
/- The k-exchange targets of `S` that carry count `y` are in bijection with the
   moves from `S` landing at `y`, so their count is `#yMoves S c y` (and hence,
   with `c = #count(S)`, the Bernoulli-Laplace transition numerator
   `transitionNumerator c y` by `yMoves_card_eq_transitionNumerator`). -/
theorem reachSetFiberCard_eq_yMoves (N m r k : Nat) (hm : m ≤ N) (hr : r ≤ N)
    (hk : k ≤ m) (hkm : k ≤ N - m) (S : Membership N m)
    (c y : Nat) (hc : c = (S.1 ∩ markedSet N r hr).card)
    (x : BernoulliLaplaceGeneral.BLState N m r) (hx : x.val = y) :
    ((ReachSet N m k hm hk hkm S) ∩ (countFiberMemb N m r hr x)).card =
      (yMoves N m r k hr S c y).card := by
  let M := markedSet N r hr
  let ymReach (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ yMoves N m r k hr S c y) : p ∈ reachMoves N m k S := by
    have hy : p ∈ (reachMoves N m k S).filter (fun q : Finset (Fin N) × Finset (Fin N) => c - (q.1 ∩ M).card + (q.2 ∩ M).card = y) := by
      simpa [yMoves] using hp
    exact (Finset.mem_filter.mp hy).1
  let ymFilter (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ yMoves N m r k hr S c y) :
      c - (p.1 ∩ M).card + (p.2 ∩ M).card = y := by
    have hy : p ∈ (reachMoves N m k S).filter (fun q : Finset (Fin N) × Finset (Fin N) => c - (q.1 ∩ M).card + (q.2 ∩ M).card = y) := by
      simpa [yMoves] using hp
    exact (Finset.mem_filter.mp hy).2
  let i (T : Membership N m) (hT : T ∈ ReachSet N m k hm hk hkm S ∩ countFiberMemb N m r hr x)
      : Finset (Fin N) × Finset (Fin N) := (S.1 \ T.1, T.1 \ S.1)
  let j (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ yMoves N m r k hr S c y) : Membership N m := by
    have hpR := ymReach p hp
    exact ⟨(S.1 \ p.1) ∪ p.2, newpile_card N m k hm hk hkm S p (by simpa [reachMoves, Lset, Rset] using hpR)⟩
  refine Finset.card_bij' i j ?_ ?_ ?_ ?_
  · -- i lands in yMoves (in reachMoves with the y-landing filter)
    intro T hT
    have hInR : T ∈ ReachSet N m k hm hk hkm S := (Finset.mem_inter.mp hT).1
    have hInY : T ∈ countFiberMemb N m r hr x := (Finset.mem_inter.mp hT).2
    have hCountT : (T.1 ∩ M).card = x.val := by simpa [countFiberMemb] using (Finset.mem_filter.mp hInY).2
    have hMove : (S.1 \ T.1, T.1 \ S.1) ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S := by
      rw [Finset.mem_product, Lset, Rset, Finset.mem_powersetCard, Finset.mem_powersetCard]
      simp only [ReachSet, Finset.mem_filter, Finset.mem_univ, true_and] at hInR
      rcases hInR with ⟨hA, hB⟩
      have hsub2 : T.1 \ S.1 ⊆ Finset.univ \ S.1 := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hx.2⟩
      exact ⟨⟨Finset.sdiff_subset, hA⟩, ⟨hsub2, hB⟩⟩
    have hT : ((S.1 ∩ T.1) ∪ (T.1 \ S.1)) = T.1 := by
      ext z
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hmc : (T.1 ∩ M).card = (S.1 ∩ M).card - ((S.1 \ T.1) ∩ M).card + ((T.1 \ S.1) ∩ M).card := by
      simpa [hT] using markedCountChange N m r k hm hr hk hkm S (S.1 \ T.1, T.1 \ S.1) hMove
    have hmc2 : c - ((S.1 \ T.1) ∩ M).card + ((T.1 \ S.1) ∩ M).card = (T.1 ∩ M).card := by
      rw [hc, hmc.symm]
    have hfilter : c - ((S.1 \ T.1) ∩ M).card + ((T.1 \ S.1) ∩ M).card = y := by
      rw [hmc2, hCountT]
      exact hx
    rw [yMoves]
    exact (Finset.mem_filter.mpr ⟨by dsimp [i]; simpa [reachMoves, Finset.mem_product, Lset, Rset, Finset.mem_powersetCard] using hMove, by simpa using hfilter⟩)
  · -- j lands back in ReachSet ∩ the fiber
    intro p hp
    have hpR := ymReach p hp
    have hFilter := ymFilter p hp
    have hpL : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S := by
      simpa [reachMoves, Lset, Rset] using hpR
    have hraw := markedCountChange N m r k hm hr hk hkm S p hpL
    rw [← hc, hFilter] at hraw
    exact Finset.mem_inter.mpr
      ⟨by simpa using newpile_reach N m k hm hk hkm S p hpL,
       by simpa [countFiberMemb, hx] using hraw⟩
  · -- left inverse: j (i T) = T
    intro T hT
    dsimp only [i, j]
    refine Subtype.ext ?_
    change (S.1 \ (S.1 \ T.1)) ∪ (T.1 \ S.1) = T.1
    rw [Finset.sdiff_sdiff_self_left, Finset.inter_comm, Finset.union_comm, Finset.sdiff_union_inter]
  · -- right inverse: i (j p) = p
    intro p hp
    dsimp only [i, j]
    have hpL : p ∈ Lset N m k hm hk hkm S ×ˢ Rset N m k hm hk hkm S := by
      simpa [reachMoves, Lset, Rset] using (ymReach p hp)
    ext
    · rw [inv_first N m k hm hk hkm S p hpL]
    · rw [inv_second N m k hm hk hkm S p hpL]

-- ── G4 capstone mass-body lemmas (extracted; build G4LHS mass-sum collapse) ──
/-- Mass body of the fiber-uniform membership lift (base form, `rfl` unfold). -/
theorem uniformCountFiberMembership_mass (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (j : Membership p.N p.m) :
    (uniformCountFiberMembership p x).mass j =
      (if (countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j).val = x.val
        then (1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card else 0) := by
  dsimp only [uniformCountFiberMembership, Dist.ofFun, Dist.mass]
  rfl

/-- Mass body of the fiber-uniform membership lift, in `ite` form over the marked-count fiber. -/
theorem uniformCountFiberMembership_mass_ite (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (j : Membership p.N p.m) :
    (uniformCountFiberMembership p x).mass j =
      (if (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j) = x.val
        then (1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card else 0) := by
  dsimp only [uniformCountFiberMembership, Dist.ofFun, Dist.mass, countInPile]
  rfl

/-- Mass body of the subset-exchange kernel (base form, `rfl` unfold). -/
theorem subsetExchangeMembershipKernel_mass (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (j : Membership p.N p.m) (S : Membership p.N p.m) :
    (subsetExchangeMembershipKernel p j).mass S =
      subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm j.1 S.1 := by
  dsimp only [subsetExchangeMembershipKernel, Dist.ofFun, Dist.mass]
  rfl

/-- Mass body of the subset-exchange kernel, in `ite` form over the `ReachSet` of S. -/
theorem subsetExchangeMembershipKernel_mass_ite (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (j : Membership p.N p.m) (S : Membership p.N p.m) :
    (subsetExchangeMembershipKernel p j).mass S =
      (if j ∈ ReachSet p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S
        then (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat)⁻¹ else 0) := by
  have hK (j : Membership p.N p.m) (S : Membership p.N p.m) :
      (subsetExchangeMembershipKernel p j).mass S =
        subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm j.1 S.1 := by
    dsimp only [subsetExchangeMembershipKernel, Dist.ofFun, Dist.mass]
    rfl
  rw [hK, subsetExchangeKernel, BernoulliLaplaceGeneral.transitionDenominator]
  dsimp only [ReachSet]
  simp only [Finset.mem_filter, Finset.mem_univ, j.2, S.2, and_true, true_and]
  by_cases h : (j.1 \ S.1).card = p.k ∧ (S.1 \ j.1).card = p.k
  <;> simp [h, and_comm]

/-- Mass body of the Bernoulli-Laplace exchange kernel (transition weight, `rfl` unfold). -/
theorem blExchangeKernel_mass (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (j : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :
    (BernoulliLaplaceGeneral.blExchangeKernel p x).mass j =
      BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val j.val := by
  dsimp only [BernoulliLaplaceGeneral.blExchangeKernel, Dist.ofFun, Dist.mass]
  rfl

/-- `ite(a, x, 0) * ite(b, y, 0) = ite(a ∧ b, x * y, 0)` (0-annihilation in a commutative ring). -/
lemma ite_mul_ite {a b : Prop} [Decidable a] [Decidable b] (x y : Rat) :
    (ite a x 0) * (ite b y 0) = ite (a ∧ b) (x * y) 0 := by
  by_cases ha : a
  · by_cases hb : b
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (And.intro ha hb)]
    · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_right (fun h => hb h.2)]
      rw [mul_zero]
  · by_cases hb : b
    · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_right (fun h => ha h.1)]
      rw [zero_mul]
    · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right (fun h => ha h.1)]
      rw [zero_mul]


-- ── G4 capstone LHS mass-sum collapse (ported from _ProbeG4LHS) ──
/-- G4 capstone LHS sum collapse: `∑_j (UCFM x)(j)·(SE j)(S)` = `TN c (x.val) / (#fiber(x)·D)`
    where `c = #(S∩M)` and `D = BernoulliLaplaceGeneral.transitionDenominator`. -/
theorem g4LHS_mass_sum (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (S : Membership p.N p.m) :
    (∑ j : Membership p.N p.m,
      (uniformCountFiberMembership p x).mass j * (subsetExchangeMembershipKernel p j).mass S) =
      (BernoulliLaplaceGeneral.transitionNumerator p.N p.m p.r p.k
         (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S) x.val : Rat) /
        (↑(countFiberMemb p.N p.m p.r p.hrN x).card * (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat)) := by
  set A := countFiberMemb p.N p.m p.r p.hrN x
  set B := ReachSet p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S
  set c := countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S
  set D := BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k
  set V := (1 : Rat) / ↑A.card * (D : Rat)⁻¹
  have hc : c = (S.1 ∩ markedSet p.N p.r p.hrN).card := by
    dsimp only [c]
    rw [countInPileVal]
  have hApos : 0 < A.card := countFiberMemb_nonempty p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN x
  have hDpos : 0 < D := BernoulliLaplaceGeneral.transitionDenominator_pos p
  have hFib (j : Membership p.N p.m) :
      (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ↔ j ∈ A) := by
    simpa [A, countInPile_val] using countInPile_countFiberMemb p x j
  have hP (j : Membership p.N p.m) :
      (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ∧ j ∈ B) ↔ j ∈ A ∩ B := by
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨Iff.mp (hFib j) h.1, h.2⟩, fun h => ⟨Iff.mpr (hFib j) h.1, h.2⟩⟩
  -- 1. mass bodies
  have hsum :
      (∑ j : Membership p.N p.m, (uniformCountFiberMembership p x).mass j * (subsetExchangeMembershipKernel p j).mass S) =
        (∑ j : Membership p.N p.m,
          (if countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val then (1 : Rat) / ↑A.card else 0) *
          (if j ∈ B then (D : Rat)⁻¹ else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [uniformCountFiberMembership_mass_ite, subsetExchangeMembershipKernel_mass_ite]
  rw [hsum]
  -- 2. ite(a,α,0)·ite(b,γ,0) = ite(a∧b, α·γ, 0)
  have hprod (j : Membership p.N p.m) :
      (if countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val then (1 : Rat) / ↑A.card else 0) *
        (if j ∈ B then (D : Rat)⁻¹ else 0) =
        (if (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ∧ j ∈ B) then V else 0) := by
    simpa [V] using ite_mul_ite ((1 : Rat) / ↑A.card) ((D : Rat)⁻¹)
  have hsum2 :
      (∑ j : Membership p.N p.m,
        (if countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val then (1 : Rat) / ↑A.card else 0) *
        (if j ∈ B then (D : Rat)⁻¹ else 0)) =
      (∑ j : Membership p.N p.m, (if (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ∧ j ∈ B) then V else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hprod j
  rw [hsum2]
  -- 3. ∑_univ ite(P, V, 0) = ∑_filter V + ∑_rest 0 = (A∩B).sum V   (no `·` bullets — applied on the main goal)
  change (Finset.univ : Finset (Membership p.N p.m)).sum
      (fun j => if (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ∧ j ∈ B) then V else 0) = _
  rw [Finset.sum_ite]
  have h2 : (Finset.univ : Finset (Membership p.N p.m)).filter
      (fun j => countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j = x.val ∧ j ∈ B) = A ∩ B := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hP j
  rw [h2]
  simp only [Finset.sum_const_zero, add_zero]
  -- 4. (A∩B).sum V = (A∩B).card * V
  rw [Finset.sum_const]
  -- 5. #(A∩B) = #yMoves S c (x.val)
  have h5 : (A ∩ B).card = (yMoves p.N p.m p.r p.k p.hrN S c x.val).card := by
    rw [Finset.inter_comm,
        reachSetFiberCard_eq_yMoves p.N p.m p.r p.k (Nat.le_of_lt p.hmn) p.hrN p.hkm p.hknm S c x.val hc x rfl]
  rw [h5]
  -- 6. #yMoves = BernoulliLaplaceGeneral.transitionNumerator c (x.val)
  have h6 : (yMoves p.N p.m p.r p.k p.hrN S c x.val).card = BernoulliLaplaceGeneral.transitionNumerator p.N p.m p.r p.k c x.val := by
    rw [yMoves_card_eq_transitionNumerator p.N p.m p.r p.k (Nat.le_of_lt p.hmn) p.hrN S c x.val hc]
  rw [h6]
  -- 7. assemble the quotient: (↑TN) * ((1/↑A.card) * (D:Rat)⁻¹) = ↑TN / (↑A.card * (D:Rat))
  dsimp only [D, V]
  have ha : (↑A.card : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hApos.ne'
  have hd : (↑(D : Nat) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  field_simp [ha, hd]
  ring
  simp [ha, hd, mul_inv_cancel, one_mul, mul_one]
  <;> rfl

-- ── G4 capstone RHS mass-sum collapse (ported from _ProbeG4RHS) ──
/-- G4 capstone RHS sum collapse: `∑_y (blExchangeKernel x)(y)·(uniformCountFiberMembership y)(S)`
    = `transitionNumerator (x.val → c) / (#fiber(c)·D)` where `c = countInPileVal S` and
    `D = BernoulliLaplaceGeneral.transitionDenominator`.  `BLState` is a subtype of `Nat`, so the
    sum runs over the admissible-count interval; the `ite` (on the decidable `c = y.val`) keeps
    only the single count `c`, and because a `BLState` is unique per count the surviving fiber is
    the singleton `⟨c, _⟩`, so the sum collapses to one term. -/
theorem g4RHS_mass_sum (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) (S : Membership p.N p.m) :
    (∑ y : BernoulliLaplaceGeneral.BLState p.N p.m p.r,
      (BernoulliLaplaceGeneral.blExchangeKernel p x).mass y * (uniformCountFiberMembership p y).mass S) =
      (BernoulliLaplaceGeneral.transitionNumerator p.N p.m p.r p.k x.val
         (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S) : Rat) /
        ((BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat) *
          ↑(countFiberMemb p.N p.m p.r p.hrN
              (⟨countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S,
                countInPile_admissible p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S⟩)).card) := by
  set c := countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S
  set hc := countInPile_admissible p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN S
  set yc := (⟨c, hc⟩ : BernoulliLaplaceGeneral.BLState p.N p.m p.r)
  set D := (BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k : Rat)
  set FC := (countFiberMemb p.N p.m p.r p.hrN yc).card
  let A := fun (y : BernoulliLaplaceGeneral.BLState p.N p.m p.r) =>
      BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val y.val /
        ↑(countFiberMemb p.N p.m p.r p.hrN y).card
  have hcval : yc.val = c := rfl
  have hFCpos : 0 < FC := countFiberMemb_nonempty p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN yc
  set Un := (Finset.univ : Finset (BernoulliLaplaceGeneral.BLState p.N p.m p.r))
  -- work in the `Finset.univ` (= admissible-count) representation of the Fintype sum
  change (∑ y ∈ Un, (BernoulliLaplaceGeneral.blExchangeKernel p x).mass y * (uniformCountFiberMembership p y).mass S) = _
  -- the fiber `{y ∈ univ // c = y.val}` is the singleton `{yc}` (a `BLState` is unique per count)
  have hFiber : Un.filter (fun y => c = y.val) = {yc} := by
    apply Finset.ext
    intro y
    constructor
    · intro hf
      have hval : c = y.val := (Finset.mem_filter.mp hf).2
      have hyeq : y = yc := Subtype.ext (hval.symm.trans hcval.symm)
      exact (Finset.mem_singleton.mpr hyeq)
    · intro hs
      have hyeq : y = yc := (Finset.mem_singleton.mp hs)
      have hval : c = y.val := ((congrArg (·.val) hyeq).trans hcval).symm
      exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩)
  -- (1) mass bodies; the product telescopes to `ite(c = y.val, A y, 0)`
  have h1 : (∑ y ∈ Un, (BernoulliLaplaceGeneral.blExchangeKernel p x).mass y * (uniformCountFiberMembership p y).mass S) =
      (∑ y ∈ Un, ite (c = y.val) (A y) 0) := by
    rw [Finset.sum_congr rfl]
    intro y hmem
    rw [blExchangeKernel_mass, uniformCountFiberMembership_mass_ite]
    by_cases h : c = y.val
    · simp [h, c]
      dsimp only [A]
      <;> try field_simp
    · simp [h, c]
      <;> try ring
  -- (2) the ite-weighted sum → the singleton fiber `{yc}` → one term
  have h2 : (∑ y ∈ Un, ite (c = y.val) (A y) 0) = A yc := by
    dsimp only [Un]
    rw [Finset.sum_ite]
    <;> (try (intro _; exact True.intro))
    <;> (try (simp only [Finset.sum_const_zero, add_zero]))
    <;> (try (rw [hFiber]))
    <;> (try (exact (Finset.sum_singleton A yc)))
  -- (3) the surviving term  (`yc.val = c` definitionally, so this is `rfl` after unfolding `A`, `FC`)
  have hA : A yc = BernoulliLaplaceGeneral.transitionWeight p.N p.m p.r p.k x.val c / ↑FC := by
    dsimp only [A, FC]
  have hDpos : 0 < BernoulliLaplaceGeneral.transitionDenominator p.N p.m p.k :=
      BernoulliLaplaceGeneral.transitionDenominator_pos p
  rw [h1, h2, hA, BernoulliLaplaceGeneral.transitionWeight]
  dsimp only [D]
  field_simp [hFCpos.ne', hDpos.ne']
  <;> simp only [c]

/-- **Detailed balance in the count-fiber form (the `hDB` bridge of the G4
    capstone).**  For two admissible macrostates `x`, `y` the flow `x → y`
    weighted by the source count-fiber equals the reverse flow: the product of
    the source fiber cardinality `#countFiberMemb x` and the one-step transition
    numerator `TN(x, y)` equals the same with `x`, `y` swapped.  This is the
    reconciliation between the `#countFiberMemb · transitionNumerator` form used
    by `g4LHS_mass_sum` / `g4RHS_mass_sum` and the already-proved general
    `detailedBalance` (`BernoulliLaplaceFiber`): both sides are the fiber count
    `fiberSum`, and the swap is `fiberSum_swap`.  It makes
    `g4LHS_mass_sum = g4RHS_mass_sum` a `field_simp; ring`, closing the G4
    kernel-equality capstone `g4MacroIntertwining`. -/
theorem g4hDB (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x y : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :
    (countFiberMemb p.N p.m p.r p.hrN x).card *
        BernoulliLaplaceGeneral.transitionNumerator p.N p.m p.r p.k x.val y.val =
      (countFiberMemb p.N p.m p.r p.hrN y).card *
        BernoulliLaplaceGeneral.transitionNumerator p.N p.m p.r p.k y.val x.val := by
  have hm : p.m ≤ p.N := Nat.le_of_lt p.hmn
  simp only [countFiberMemb_card p.N p.m p.r hm p.hrN x,
             countFiberMemb_card p.N p.m p.r hm p.hrN y]
  have hxmem : x.val ∈ BernoulliLaplaceGeneral.stateFinset p.N p.m p.r := Finset.mem_Icc.mpr x.2
  have hymem : y.val ∈ BernoulliLaplaceGeneral.stateFinset p.N p.m p.r := Finset.mem_Icc.mpr y.2
  have hxlo : x.val ≤ p.m := x.2.2.trans (Nat.min_le_left p.m p.r)
  have hylo : y.val ≤ p.m := y.2.2.trans (Nat.min_le_left p.m p.r)
  have hfwd := (BernoulliLaplaceGeneral.fiberSum_eq p x.val y.val hxmem).symm
  have hrev := (BernoulliLaplaceGeneral.fiberSum_eq p y.val x.val hymem).symm
  rw [hfwd, BernoulliLaplaceGeneral.fiberSum_swap p x.val y.val hxlo hylo, hrev]

/-- A symmetric-card-exchange is symmetric: two `m`-subsets `S`, `T` of an `N`-deck
    exchange exactly `k` cards in each direction iff the reverse pair does.  This is
    the seed of the reversible-flow / detailed-balance identity for the
    physical-exchange operator (G4 RHS): the forward and reverse transitions are
    equinumerous, so the flow `x → y` weighted by the source stationary mass equals
    the reverse flow `y → x`.

    `ReachSet S` is `{ T | # (S \ T) = k ∧ # (T \ S) = k }`; the statement says the
    relation is symmetric in its two arguments. -/
theorem reachSet_symm (N m k : Nat) (hm : m ≤ N) (hk : k ≤ m) (hkm : k ≤ N - m)
    (S T : Membership N m) :
    T ∈ ReachSet N m k hm hk hkm S ↔ S ∈ ReachSet N m k hm hk hkm T := by
  simp only [ReachSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end FiniteDeck
end Shufflemath
