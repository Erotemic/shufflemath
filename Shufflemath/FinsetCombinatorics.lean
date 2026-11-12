module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SDiff
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
    (hBcomp : B ⊆ Finset.univ \ S) (hBcard : B.card = 25)
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


end FinsetCombinatorics
