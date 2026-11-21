module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic
public import Mathlib.Tactic.SetNotationForOrder
public meta import Lean.Meta.DiscrTree

@[expose] public section

namespace Shufflemath

variable {α : Type*} [DecidableEq α]

/- A universe `U` with a distinguished sub-finite subset `T1`.  The `sFiber`
is the set of `x`-subsets of `U` whose intersection with `T1` has size `t`;
`sFiberA` is the subfiber over a fixed `A = S1 ∩ T1`.  These are the pure,
parameter-free form of the marked (S1) and plain (S2) halves of the four-bin
overlap count.  -/

def sFiber (U T1 : Finset α) (x t : ℕ) : Finset (Finset α) :=
  (U.powersetCard x).filter (fun S1 => (S1 ∩ T1).card = t)

def sFiberA (U T1 A : Finset α) (x t : ℕ) : Finset (Finset α) :=
  (U.powersetCard x).filter (fun S1 => S1 ∩ T1 = A)

theorem sFiber_biUnion (U T1 : Finset α) (x t : ℕ) (htx : t ≤ x) :
    sFiber U T1 x t = (T1.powersetCard t).biUnion (fun A => sFiberA U T1 A x t) := by
  ext S1
  dsimp only [sFiber, sFiberA]
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨hS1mem, hI⟩
    set A := S1 ∩ T1 with hAdef
    have hAmem : A ∈ T1.powersetCard t := by
      simp only [hAdef, Finset.inter_subset_right, hI, Finset.mem_powersetCard]
      <;> aesop
    refine ⟨A, hAmem, ?_⟩
    simp only [sFiberA, Finset.mem_filter]
    exact ⟨hS1mem, hAdef.symm⟩
  · rintro ⟨A, hAmem, hmemA⟩
    have hmemA2 : S1 ∈ U.powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [sFiberA, Finset.mem_filter] using hmemA
    rcases hmemA2 with ⟨hS1mem, hI⟩
    refine ⟨hS1mem, ?_⟩
    rw [hI]
    exact (Finset.mem_powersetCard.1 hAmem).2

theorem sFiberA_card (U T1 A : Finset α) (x t : ℕ) (htx : t ≤ x)
    (hT1 : T1 ⊆ U) (hA : A ∈ T1.powersetCard t) :
    (sFiberA U T1 A x t).card = ((U \ T1).powersetCard (x - t)).card := by
  set st := U
  have hAsub : A ⊆ T1 := (Finset.mem_powersetCard.1 hA).1
  have hAcard : A.card = t := (Finset.mem_powersetCard.1 hA).2
  refine Finset.card_bij (fun S1 _ => S1 \ T1) ?_ ?_ ?_
  · -- MapsTo
    intro S1 hS1
    have hS1c : S1 ∈ st.powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [sFiberA, Finset.mem_filter] using hS1
    rcases hS1c with ⟨hS1mem, hI⟩
    have hS1sub : S1 ⊆ st := (Finset.mem_powersetCard.1 hS1mem).1
    have hS1card : S1.card = x := (Finset.mem_powersetCard.1 hS1mem).2
    have hRestsub : S1 \ T1 ⊆ st \ T1 := Finset.sdiff_subset_sdiff hS1sub (by rfl)
    have hRestcard : (S1 \ T1).card = x - t := by
      rw [Finset.card_sdiff, Finset.inter_comm, hI, hAcard, hS1card]
    simpa [hRestsub, hRestcard, Finset.mem_powersetCard]
  · -- InjOn
    intro S1 hS1 S1' hS1' h
    have hS1c : S1 ∈ st.powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [sFiberA, Finset.mem_filter] using hS1
    have hS1c' : S1' ∈ st.powersetCard x ∧ S1' ∩ T1 = A := by
      simpa [sFiberA, Finset.mem_filter] using hS1'
    let hI1 := hS1c.2
    let hI2 := hS1c'.2
    have hUn1 : S1 = A ∪ (S1 \ T1) := by
      ext z
      rw [Finset.mem_union, hI1.symm, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hUn2 : S1' = A ∪ (S1' \ T1) := by
      ext z
      rw [Finset.mem_union, hI2.symm, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hUn1, hUn2, h]
  · -- SurjOn
    intro R hR
    rcases Finset.mem_powersetCard.1 hR with ⟨hRsub, hRcard⟩
    refine ⟨A ∪ R, ?_, ?_⟩
    · -- ha : A ∪ R ∈ sFiberA
      dsimp only [sFiberA]
      have hsub : A ∪ R ⊆ st := by
        intro z hz
        rw [Finset.mem_union] at hz
        rcases hz with hzA | hzR
        · exact hT1 (hAsub hzA)
        · exact (Finset.mem_sdiff.1 (hRsub hzR)).1
      have hARdis : A ∩ R = ∅ := by
        ext z
        rw [Finset.mem_inter]
        constructor
        · intro hz
          have hzT1 := hAsub hz.1
          have hznot := (Finset.mem_sdiff.1 (hRsub hz.2)).2
          exfalso
          exact absurd hzT1 hznot
        · intro hz; cases hz
      have hcard : (A ∪ R).card = x := by
        have h0 : (A ∩ R).card = 0 := by simpa only [hARdis, Finset.card_empty]
        have hsum : (A ∪ R).card + (A ∩ R).card = A.card + R.card :=
          Finset.card_union_add_card_inter _ _
        rw [h0, add_zero, hAcard, hRcard] at hsum
        have hadd : t + (x - t) = x := by rw [Nat.add_comm, Nat.sub_add_cancel htx]
        exact hsum.trans hadd
      have hInt : (A ∪ R) ∩ T1 = A := by
        ext z
        rw [Finset.mem_inter]
        constructor
        · intro hz
          rcases hz with ⟨hzAR, hzT1⟩
          rw [Finset.mem_union] at hzAR
          rcases hzAR with hzA | hzR
          · exact hzA
          · exact absurd hzT1 (Finset.mem_sdiff.1 (hRsub hzR)).2
        · intro hzA
          exact ⟨Finset.mem_union.2 (Or.inl hzA), hAsub hzA⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact And.intro (And.intro hsub hcard) hInt
    · -- i (A ∪ R) = R, i.e. (A ∪ R) \ T1 = R
      ext z
      rw [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hz
        rcases hz with ⟨hzAR, hznotT1⟩
        rcases hzAR with hzA | hzR
        · exfalso
          exact absurd (hAsub hzA) hznotT1
        · exact hzR
      · intro hzR
        exact ⟨Or.inr hzR, (Finset.mem_sdiff.1 (hRsub hzR)).2⟩

theorem sFiber_card (U T1 : Finset α) (x t : ℕ) (htx : t ≤ x) (hT1 : T1 ⊆ U) :
    (sFiber U T1 x t).card =
      (T1.powersetCard t).card * ((U \ T1).powersetCard (x - t)).card := by
  rw [sFiber_biUnion U T1 x t htx]
  have hdis : (T1.powersetCard t : Set (Finset α)).PairwiseDisjoint
      (fun A => sFiberA U T1 A x t) := by
    intro A hA B hB hne
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    ext S1
    dsimp only [sFiberA]
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro hz
      rcases hz with ⟨hleft, hright⟩
      rcases hleft with ⟨hS1in, hAeq1⟩
      rcases hright with ⟨hS2in, hAeq2⟩
      have hAeq : A = B := hAeq1.symm.trans hAeq2
      exact False.elim (hne hAeq)
    · intro hz
      cases hz
  rw [Finset.card_biUnion hdis]
  have hc : ∀ A ∈ T1.powersetCard t,
      (sFiberA U T1 A x t).card = ((U \ T1).powersetCard (x - t)).card := by
    intro A hA
    exact sFiberA_card U T1 A x t htx hT1 hA
  rw [Finset.sum_congr rfl (fun A hA => hc A hA)]
  simp [Finset.sum_const]

/-! The pure closed form: the number of `x`-subsets of `U` with `t`-many
elements in a fixed `T1 ⊆ U` is `choose |T1| t * choose (|U|-|T1|) (x-t)`.
Both the marked (S1) and plain (S2) halves of `overlap_count` are instances.  -/
theorem sFiber_choose (U T1 : Finset α) (x t : ℕ) (htx : t ≤ x) (hT1 : T1 ⊆ U) :
    (sFiber U T1 x t).card =
      Nat.choose T1.card t * Nat.choose (U.card - T1.card) (x - t) := by
  set st := U
  rw [sFiber_card U T1 x t htx hT1]
  rw [Finset.card_powersetCard t T1]
  rw [Finset.card_powersetCard (x - t) (st \ T1)]
  rw [Finset.card_sdiff_of_subset hT1]

end Shufflemath
