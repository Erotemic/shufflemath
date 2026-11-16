module
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.BernoulliLaplaceGeneral
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


end FiniteDeck
end Shufflemath
