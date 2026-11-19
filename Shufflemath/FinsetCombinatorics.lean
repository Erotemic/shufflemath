module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
## `Finset` combinatorial facts for the hypergeometric exchange count (F3)

General counting lemmas used by the F3 item-3 `hMembershipExchange` counting
identity: how many `k`-subsets of a set partitioned into two disjoint parts
`a` and `b` have exactly `i` elements in `a`. The pieces here are the
set-algebra lemmas the counting rests on.
-/
namespace FinsetCombinatorics

/-- If `A ⊆ a` and `B ⊆ b` with `a ∩ b = ∅`, then the union `A ∪ B` is
  *recoverable* by intersecting with the two parts:
  `(A ∪ B) ∩ a = A` and `(A ∪ B) ∩ b = B`. In particular the disjoint-union
  decomposition is unique, which is what lets a `(i`-subset of `a`) ×
  (`(k - i)`-subset of `b`) pair be recovered from its union. -/
theorem union_inter_parts (a b A B : Finset α) [DecidableEq α]
    (ha : A ⊆ a) (hb : B ⊆ b) (hab : a ∩ b = ∅) :
    (A ∪ B) ∩ a = A ∧ (A ∪ B) ∩ b = B := by
  have ha' : ∀ x, x ∈ A → x ∈ a := ha
  have hb' : ∀ x, x ∈ B → x ∈ b := hb
  have hab' : ∀ x, ¬ (x ∈ a ∧ x ∈ b) := fun x h => by
    have hx : x ∈ a ∩ b := by simpa using h
    simpa [hab] using hx
  constructor
  · -- (A ∪ B) ∩ a = A
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  · -- (A ∪ B) ∩ b = B
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto

variable {α : Type*}

/- A valid 25/25 exchange from `S` to `T`: remove a 25-subset `A` of `S`,
   add a 25-subset `B` of the complement, and land exactly on `T`. -/
def isExchangePair (S T A B : Finset α) [Fintype α] [DecidableEq α] : Prop :=
  A ⊆ S ∧ A.card = 25 ∧
  B ⊆ (Finset.univ \ S) ∧ B.card = 25 ∧
  (S \ A) ∪ B = T

private theorem mem_of_subset (s t : Finset α) [DecidableEq α]
    (h : s ⊆ t) (x : α) (hx : x ∈ s) : x ∈ t := by
  simpa using h hx

/-- The added cards of an exchange from `S` to `T` are exactly the cards of
    `T` outside `S`: `B = T \ S`. -/
theorem exchangePair_unique_B [Fintype α] [DecidableEq α]
    (S T A B : Finset α)
    (hAsub : A ⊆ S) (hAcard : A.card = 25)
    (hBcomp : B ⊆ Finset.univ \ S) (hBcard : B.card = 25)
    (hTdef : T = (S \ A) ∪ B) : B = T \ S := by
  have hBnoS (x) (hxB : x ∈ B) : x ∉ S := by
    have hxs : x ∈ Finset.univ \ S := by simpa using hBcomp hxB
    exact (Finset.mem_sdiff.mp hxs).2
  rw [hTdef]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro hxB
    exact ⟨Or.inr hxB, hBnoS x hxB⟩
  · rintro ⟨hxy, hxnS⟩
    by_cases hxSA : x ∈ S \ A
    · exfalso
      exact hxnS (Finset.mem_sdiff.mp hxSA).1
    · simp only [not_not, Finset.mem_sdiff] at hxy hxSA
      tauto

/-- The removed cards of an exchange from `S` to `T` are exactly the cards of
    `S` outside `T`: `A = S \ T`. -/
theorem exchangePair_unique_A [Fintype α] [DecidableEq α]
    (S T A B : Finset α)
    (hAsub : A ⊆ S) (hAcard : A.card = 25)
    (hBcomp : B ⊆ Finset.univ \ S) (_hBcard : B.card = 25)
    (hTdef : T = (S \ A) ∪ B) : A = S \ T := by
  have hBnoS (x) (hxB : x ∈ B) : x ∉ S := by
    have hxs : x ∈ Finset.univ \ S := by simpa using hBcomp hxB
    exact (Finset.mem_sdiff.mp hxs).2
  rw [hTdef]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  have hAinS : x ∈ A → x ∈ S := fun h => mem_of_subset A S hAsub x h
  have hAnotSA : x ∈ A → ¬ x ∈ S \ A :=
    fun hA => fun hSA => (Finset.mem_sdiff.mp hSA).2 hA
  have hBnotS : x ∈ B → x ∉ S := fun hB => hBnoS x hB
  tauto

-- |S\T| = 25 when |S∩T| = 25, |S| = 50
theorem cardSdiffInter [DecidableEq α] (S T : Finset α)
    (h : (S ∩ T).card = 25) (hS : S.card = 50) : (S \ T).card = 25 := by
  have hsub : S ∩ T ⊆ S := by apply Finset.inter_subset_left
  rw [← Finset.sdiff_inter_self_right, Finset.inter_comm,
      Finset.card_sdiff_of_subset hsub, h, hS]

-- |T\S| = 25 when |S∩T| = 25, |T| = 50
theorem cardSdiffInter2 [DecidableEq α] (S T : Finset α)
    (h : (S ∩ T).card = 25) (hT : T.card = 50) : (T \ S).card = 25 := by
  have hsub : S ∩ T ⊆ T := by apply Finset.inter_subset_right
  rw [← Finset.sdiff_inter_self_left, Finset.inter_comm,
      Finset.card_sdiff_of_subset hsub, h, hT]

/-- `S \ (S \ T) = S ∩ T`: removing from `S` the part that misses `T`
    leaves exactly the part of `S` inside `T`.  Pure set algebra (no `Fintype`). -/
theorem sdiff_sdiff_inter [DecidableEq α] (S T : Finset α) :
    (S \ (S \ T)) = S ∩ T := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  -- (x ∈ S ∧ ¬(x ∈ S ∧ ¬x ∈ T)) ↔ (x ∈ S ∧ x ∈ T)
  tauto

/-- `(S \ (S \ T)) ∪ (T \ S) = T`: the part of `S` inside `T` together with
    the part of `T` outside `S` covers exactly `T`.  Pure set algebra.  This is
    the 5th conjunct of `isExchangePair` proved as a standalone lemma so the
    `Fintype`-context 5-conjunct assembly can `exact` it without the `Finset`
    quotient `rw`-in-term-position quirk. -/
theorem sdiff_sdiff_union_eq [DecidableEq α] (S T : Finset α) :
    (S \ (S \ T)) ∪ (T \ S) = T := by
  rw [sdiff_sdiff_inter]
  -- (S ∩ T) ∪ (T \ S) = T
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The canonical exchange pair `(S \ T, T \ S)` is a valid 25/25 exchange from
    `S` to `T` when both piles have 50 cards and overlap in 25: remove the 25
    cards of `S` not in `T`, add the 25 cards of `T` not in `S`, land on `T`. -/
theorem exchangePair_exists [Fintype α] [DecidableEq α] (S T : Finset α)
    (hInter : (S ∩ T).card = 25) (hS : S.card = 50) (hT : T.card = 50) :
    isExchangePair S T (S \ T) (T \ S) := by
  dsimp only [isExchangePair]
  have hAcard : (S \ T).card = 25 := cardSdiffInter S T hInter hS
  have hBcard : (T \ S).card = 25 := cardSdiffInter2 S T hInter hT
  have hAsub : (S \ T) ⊆ S := fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hBcomp : (T \ S) ⊆ Finset.univ \ S := by
    rintro x hx
    have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
    simp only [Finset.mem_sdiff]
    exact ⟨by simp, hxS⟩
  have hTdef : (S \ (S \ T)) ∪ (T \ S) = T := sdiff_sdiff_union_eq S T
  constructor  -- A ⊆ S
  exact hAsub
  constructor  -- A.card = 25
  exact hAcard
  constructor  -- B ⊆ univ \ S
  exact hBcomp
  constructor  -- B.card = 25
  exact hBcard
  -- 5th conjunct: (S \ (S\T)) ∪ (T\S) = T
  exact hTdef




/-- A subset `S ⊆ U` splits uniquely into its `M`-part `S ∩ M` and its
    `M`-complement `S \ M`: the two pieces are disjoint, recombine to `S`, and
    the `M`-complement lies in `U \ M` (when `M ⊆ U`). This is the `U`-
    generalization of the marked/unmarked split behind `countFiberMemb`. -/
theorem sdiff_inter_split {α : Type*} [DecidableEq α] (U M S : Finset α)
    (_hM : M ⊆ U) (hS : S ⊆ U) :
    (S ∩ M) ∪ (S \ M) = S ∧ Disjoint (S ∩ M) (S \ M) ∧ S \ M ⊆ U \ M := by
  refine ⟨?_, ?_, ?_⟩
  · -- the two pieces recombine to `S`
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · -- the two pieces are disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.ext
    intro z
    apply Iff.intro
    · intro hz
      have hzM : z ∈ M := (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2
      have hznotM : z ∉ M := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz).2).2
      contradiction
    · intro hz
      exact False.elim (Finset.notMem_empty z hz)
  · -- the `M`-complement stays inside `U \ M`
    rintro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hz, hznotM⟩
    exact Finset.mem_sdiff.mpr ⟨hS hz, hznotM⟩
/- The counting kernel (F3 A3 pile counts): the `k`-subsets of `U` with exactly
   `a` marked elements (`∩ M`) biject with pairs `(A, B)` where `A` is an
   `a`-subset of `M` and `B` is a `(k - a)`-subset of `U \ M` — the disjoint
   union `S = (S ∩ M) ∪ (S \ M)` recovers both halves, and intersecting a
   recombined `A ∪ B` with the two parts recovers `A` and `B`. This generalizes
   the `Membership`-fiber bijection `countFiberMemb_equiv` to an arbitrary
   `(U, M)` with `M ⊆ U`. -/
def powersetCard_markedContent_equiv {α : Type*} [DecidableEq α]
    (U M : Finset α) (hM : M ⊆ U) (k a : Nat) (ha : a ≤ k) :
    {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} ≃
      {p : Finset α × Finset α //
        p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} := by
  let X := U \ M
  have hXsub : X ⊆ U := Finset.sdiff_subset
  have hMdisjX : M ∩ X = ∅ := by
    ext z
    simp only [X, Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty]
    tauto
  let f : {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} →
          {p : Finset α × Finset α //
            p.1 ∈ M.powersetCard a ∧ p.2 ∈ X.powersetCard (k - a)} :=
    fun S =>
      let sF := S.1
      have hSsub : sF ⊆ U := S.2.1
      have hScard : sF.card = k := S.2.2.1
      have hSmark : (sF ∩ M).card = a := S.2.2.2
      have hAsub : sF ∩ M ⊆ M := Finset.inter_subset_right
      have hBsub : sF \ M ⊆ X := (sdiff_inter_split U M sF hM hSsub).2.2
      have hBcard : (sF \ M).card = k - a := by
        rw [Finset.card_sdiff, Finset.inter_comm, hScard, hSmark]
      ⟨⟨sF ∩ M, sF \ M⟩,
        ⟨Finset.mem_powersetCard.mpr ⟨hAsub, hSmark⟩,
         Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩⟩⟩
  let g : {p : Finset α × Finset α //
            p.1 ∈ M.powersetCard a ∧ p.2 ∈ X.powersetCard (k - a)} →
          {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} :=
    fun p =>
      let A := p.1.1
      let B := p.1.2
      have hA : A ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hAcard : A.card = a := (Finset.mem_powersetCard.mp p.2.1).2
      have hB : B ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      have hBcard : B.card = k - a := (Finset.mem_powersetCard.mp p.2.2).2
      have hABsub : A ∪ B ⊆ U := by
        rintro z hz
        simp only [Finset.mem_union] at hz
        rcases hz with hz | hz
        · exact hM (hA hz)
        · exact hXsub (hB hz)
      have hDisAB : Disjoint A B := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        apply Finset.ext
        intro z
        apply Iff.intro
        · intro hz
          have hzM : z ∈ M := hA (Finset.mem_inter.mp hz).1
          have hzX : z ∈ X := hB (Finset.mem_inter.mp hz).2
          have hInX : z ∈ M ∩ X := Finset.mem_inter.mpr ⟨hzM, hzX⟩
          rw [hMdisjX] at hInX
          exact False.elim (Finset.notMem_empty z hInX)
        · intro hz
          exact False.elim (Finset.notMem_empty z hz)
      have hABcard : (A ∪ B).card = k := by
        have hEmpty : A ∩ B = ∅ := (Finset.disjoint_iff_inter_eq_empty).mp hDisAB
        have hInter : (A ∩ B).card = 0 := by rw [hEmpty, Finset.card_empty]
        have hUnion : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
          Finset.card_union_add_card_inter A B
        rw [hInter, Nat.add_zero, hAcard, hBcard] at hUnion
        omega
      have hAM : (A ∪ B) ∩ M = A := (union_inter_parts M X A B hA hB hMdisjX).1
      have hAmark : ((A ∪ B) ∩ M).card = a := by rw [hAM, hAcard]
      ⟨A ∪ B, ⟨hABsub, hABcard, hAmark⟩⟩
  refine Equiv.mk f g ?_ ?_
  · -- `g ∘ f = id`: the split pieces recombine to `S`.
    intro S
    dsimp only [f, g]
    apply Subtype.ext
    exact (sdiff_inter_split U M S.1 hM S.2.1).1
  · -- `f ∘ g = id`: the recombined `A ∪ B` re-splits to `(A, B)`.
    intro p
    dsimp only [f, g]
    apply Subtype.ext
    apply Prod.ext
    · -- `(A ∪ B) ∩ M = A`
      have hA : p.1.1 ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hB : p.1.2 ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      exact (union_inter_parts M X p.1.1 p.1.2 hA hB hMdisjX).1
    · -- `(A ∪ B) \ M = B`
      have hA : p.1.1 ⊆ M := (Finset.mem_powersetCard.mp p.2.1).1
      have hB : p.1.2 ⊆ X := (Finset.mem_powersetCard.mp p.2.2).1
      have hSdiff : (p.1.1 ∪ p.1.2) \ M = p.1.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        apply Iff.intro
        · intro h
          have hznotM : z ∉ M := h.2
          rcases h.1 with hzA | hzB
          · have hzM : z ∈ M := hA hzA
            contradiction
          · exact hzB
        · intro hzB
          exact ⟨Or.inr hzB, (Finset.mem_sdiff.mp (hB hzB)).2⟩
      exact hSdiff

/- The F3 A3 counting kernel: the number of `k`-subsets of `U` containing
   exactly `a` elements of the marked part `M ⊆ U` is the hypergeometric number
   `choose(M.card, a) · choose(U.card - M.card, k - a)`. This is the reusable
   foundation for the 25/25 exchange pile counts in the Commander A3 discharge. -/
theorem powersetCard_markedContent {α : Type*} [Fintype α] [DecidableEq α]
    (U M : Finset α) (hM : M ⊆ U) (k a : Nat) (ha : a ≤ k) :
    ((U.powersetCard k).filter (fun S => (S ∩ M).card = a)).card =
      Nat.choose M.card a * Nat.choose (U.card - M.card) (k - a) := by
  have hBridge :
      ((U.powersetCard k).filter (fun S => (S ∩ M).card = a)).card =
        Fintype.card {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} :=
    (Fintype.card_of_subtype
        (p := fun S => S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a)
        (s := (U.powersetCard k).filter (fun S => (S ∩ M).card = a))
        (H := fun z => by
          simp only [Finset.mem_filter, Finset.mem_powersetCard, and_assoc])).symm
  have hEquiv :
      Fintype.card {S : Finset α // S ⊆ U ∧ S.card = k ∧ (S ∩ M).card = a} =
        Fintype.card {p : Finset α × Finset α //
          p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} :=
    Fintype.card_congr (powersetCard_markedContent_equiv U M hM k a ha)
  have hProd :
      Fintype.card {p : Finset α × Finset α //
        p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a)} =
        (M.powersetCard a ×ˢ (U \ M).powersetCard (k - a)).card :=
    (Fintype.card_of_subtype
        (p := fun p : Finset α × Finset α =>
          p.1 ∈ M.powersetCard a ∧ p.2 ∈ (U \ M).powersetCard (k - a))
        (s := M.powersetCard a ×ˢ (U \ M).powersetCard (k - a))
        (H := fun p => by simp only [Finset.mem_product]))
  rw [hBridge, hEquiv, hProd, Finset.card_product,
      Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hM]

/-- **Fiber double-count.**  For a function `f : X → Y` between finite types and a
    set of targets `S`, the total size of the fibers over `S` is the size of the
    preimage of `S`: `∑ m ∈ S, #{x : f x = m} = #{x : f x ∈ S}`.  The fibers
    `#{x : f x = m}` (for `m ∈ S`) are pairwise disjoint and their union is exactly
    the preimage `{x : f x ∈ S}`.

    This is the general form of the A3 part-(i) fiber-sum → preimage-sum collapse
    (`Σ_{m : count m = c} #{j : F j = m} = #{j : count (F j) = c}`, with `F` the
    post-exchange membership map and `S` the `c`-fiber of membership counts): the
    total mass of the raw exchange into a membership-count fiber is a count of a
    preimage, which then identifies with the Bernoulli--Laplace transition -/
theorem fiberSum_eq_preimageCard {X : Type*} [Fintype X] [DecidableEq X]
    (Y : Type*) [Fintype Y] [DecidableEq Y] (f : X → Y) (S : Finset Y) :
    Fintype.card {x : X // f x ∈ S} = ∑ m ∈ S, Fintype.card {x : X // f x = m} := by
  classical
  let F (m : Y) : Finset X := (Finset.univ : Finset X).filter (fun x => f x = m)
  -- fiber Fintype-card = its Finset-filter card (bridge via Fintype.card_subtype + ncard)
  have hFiber (m : Y) : Fintype.card {x // f x = m} = (F m).card := by
    simp [F, Fintype.card_subtype]
  -- preimage Fintype-card = its Finset-filter card
  have hPre : Fintype.card {x // f x ∈ S} =
      Finset.card ((Finset.univ : Finset X).filter (fun x => f x ∈ S)) := by
    simp [Fintype.card_subtype]
  -- the biUnion of the fibers over S is exactly the preimage
  have hBiUnion : (S).biUnion F = (Finset.univ : Finset X).filter (fun x => f x ∈ S) := by
    ext x
    simp [F]
  calc
    _ = Finset.card ((Finset.univ : Finset X).filter (fun x => f x ∈ S)) := by rw [hPre]
    _ = Finset.card ((S).biUnion F) := by rw [hBiUnion]
    _ = ∑ m ∈ S, (F m).card := by
      rw [Finset.card_biUnion]
      · -- (S : Set Y).PairwiseDisjoint F : distinct fibers are disjoint
        intro i _ j _ hne
        change Disjoint (F i) (F j)
        rw [Finset.disjoint_left]
        -- goal: ∀ a, a ∈ F i → a ∉ F j
        intro a ha
        by_contra hab
        -- ha : a ∈ F i  =>  f a = i ;  hab : a ∈ F j  =>  f a = j
        have hia : f a = i := by simpa [F, Finset.mem_filter, Finset.mem_univ] using ha
        have hja : f a = j := by simpa [F, Finset.mem_filter, Finset.mem_univ] using hab
        -- i = f a = j, contradicting hne : i ≠ j
        exact hne (hia.symm.trans hja)
    _ = ∑ m ∈ S, Fintype.card {x // f x = m} := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hFiber]

/-- The Fintype-card bridge: two subtypes of a finite type with extensionally-equal predicates
    (forall a, P a <-> Q a) are in bijection, hence their Fintype-cards agree.  Proved here, in
    this shallow module, so it can be applied in deep contexts (e.g. the A3 count-mass bridge) without
    re-running the reduction that a Membership-context subtype `Equiv` would trigger. -/
theorem fintypeCard_subtypeCongr {α : Type*} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ a, P a ↔ Q a) :
    Fintype.card {a : α // P a} = Fintype.card {a : α // Q a} := by
  let e : {a : α // P a} ≃ {a : α // Q a} :=
    ⟨fun x => ⟨x.1, (h x.1).mp x.2⟩,
     fun x => ⟨x.1, (h x.1).mpr x.2⟩,
     by intro x; apply Subtype.ext; rfl,
     by intro x; apply Subtype.ext; rfl⟩
  exact Fintype.card_congr e

end FinsetCombinatorics
