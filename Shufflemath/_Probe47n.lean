module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace _Probe47n

open CommanderPermutation
open CommanderPhysicalExchange

variable (d : CommanderPermutation.Deck)

/-- The 50 originally-left card-identities (0..49) as positions in `Fin 99`. -/
noncomputable def leftOrig50 : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image (Fin.castLE (by decide : 50 <= 99))

/-- `leftOrigSet` (the 99-filter) equals the 50-image, so it has 50 elements. -/
theorem leftOrigSet_eq_leftOrig50 : (leftOrigSet : Finset (Fin 99)) = leftOrig50 := by
  unfold leftOrigSet leftOrig50
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨_, hval⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨c.val, hval⟩, Finset.mem_univ _, by simpa [Fin.val_castLE] using hval⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨i, _, heq⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact Finset.mem_univ c
    · subst c
      exact i.isLt

/-- The 50 originally-left card-identities form a 50-element set. -/
theorem leftOrig50_card50 : (leftOrig50 : Finset (Fin 99)).card = 50 := by
  unfold leftOrig50
  rw [Finset.card_image_of_injective]
  · simp
  · exact fun i j h => by simpa [Fin.val_castLE] using h

/-- A position `c` in the 50 originally-left card-identities has `c.val < 50`. -/
theorem leftOrig50_mem_val (c : Fin 99) (hc50 : c ∈ leftOrig50) : c.val < 50 := by
  rcases Finset.mem_image.mp hc50 with ⟨i, _, heq⟩
  subst c
  simp only [Fin.castLE]
  exact i.isLt

/-- The positions holding an originally-left card, i.e. `leftOrig50` mapped by
    `d.symm`: a 50-element set. -/
noncomputable def totalMarkedPos : Finset (Fin 99) := (leftOrig50).image (d.symm)

/-- The total marked positions have 50 elements. -/
theorem totalMarkedPos_card50 : (totalMarkedPos d).card = 50 := by
  unfold totalMarkedPos
  rw [Finset.card_image_of_injective,
    show (leftOrig50 : Finset (Fin 99)).card = 50 from leftOrig50_card50]
  exact d.symm.injective

/-- A left index `l` is marked (its left-position holds an originally-left
    card) iff that left-position lies in the total marked positions. -/
theorem markedLeft_iff_inTotal (l : Fin 50) :
    l ∈ (markedLeftPos d) ↔ leftPosition l ∈ (totalMarkedPos d) := by
  constructor
  · intro hl
    let hval : (d (leftPosition l)).val < 50 := by
      have hcon : True ∧ (d (leftPosition l)).val < 50 := by
        simpa only [markedLeftPos, Finset.mem_filter, Finset.mem_univ] using hl
      exact hcon.2
    have hLO : d (leftPosition l) ∈ leftOrigSet := by
      unfold leftOrigSet
      simpa [Finset.mem_filter] using hval
    have h50 : d (leftPosition l) ∈ leftOrig50 := by
      simpa only [leftOrigSet_eq_leftOrig50] using hLO
    refine Finset.mem_image.mpr ?_
    exact ⟨d (leftPosition l), h50, by simpa [Equiv.symm_apply_apply d]⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨c, hc50, heq⟩
    have hval : (d (leftPosition l)).val < 50 := by
      have hcval : c.val < 50 := leftOrig50_mem_val c hc50
      -- heq : d.symm c = leftPosition l. d (d.symm c) = c.
      have hvalEq : (d (leftPosition l)).val = c.val := by
        have h1 : d (d.symm c) = c := Equiv.apply_symm_apply d c
        have h2 : d (d.symm c) = d (leftPosition l) := by rw [heq]
        have hfin : d (leftPosition l) = c :=
          (h2.symm).trans h1
        simpa only [hfin]
      simpa only [hvalEq] using hcval
    have hcon : True ∧ (d (leftPosition l)).val < 50 := ⟨by simp, hval⟩
    simpa only [markedLeftPos, Finset.mem_filter, Finset.mem_univ] using hcon

/-- A right index `r` is marked iff that right-position lies in the total
    marked positions. -/
theorem markedRight_iff_inTotal (r : Fin 49) :
    r ∈ (markedRightPos d) ↔ rightPosition r ∈ (totalMarkedPos d) := by
  constructor
  · intro hr
    let hval : (d (rightPosition r)).val < 50 := by
      have hcon : True ∧ (d (rightPosition r)).val < 50 := by
        simpa only [markedRightPos, Finset.mem_filter, Finset.mem_univ] using hr
      exact hcon.2
    have hLO : d (rightPosition r) ∈ leftOrigSet := by
      unfold leftOrigSet
      simpa [Finset.mem_filter] using hval
    have h50 : d (rightPosition r) ∈ leftOrig50 := by
      simpa only [leftOrigSet_eq_leftOrig50] using hLO
    refine Finset.mem_image.mpr ?_
    exact ⟨d (rightPosition r), h50, by simpa [Equiv.symm_apply_apply d]⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨c, hc50, heq⟩
    have hval : (d (rightPosition r)).val < 50 := by
      have hcval : c.val < 50 := leftOrig50_mem_val c hc50
      have hvalEq : (d (rightPosition r)).val = c.val := by
        have h1 : d (d.symm c) = c := Equiv.apply_symm_apply d c
        have h2 : d (d.symm c) = d (rightPosition r) := by rw [heq]
        have hfin : d (rightPosition r) = c :=
          (h2.symm).trans h1
        simpa only [hfin]
      simpa only [hvalEq] using hcval
    have hcon : True ∧ (d (rightPosition r)).val < 50 := ⟨by simp, hval⟩
    simpa only [markedRightPos, Finset.mem_filter, Finset.mem_univ] using hcon

/-- The 50 left positions, as a `Fin 99` set. -/
noncomputable def leftUniv50 : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image leftPosition
/-- The 49 right positions, as a `Fin 99` set. -/
noncomputable def rightUniv49 : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 49)).image rightPosition

/-- A position `p` is a left position iff `p.val < 50`. -/
theorem leftPos_iff_val (p : Fin 99) :
    p ∈ leftUniv50 ↔ p.val < 50 := by
  unfold leftUniv50
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨l, _, heq⟩
    subst p
    simp only [leftPosition, Fin.castLE]
    exact l.isLt
  · intro hval
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨p.val, hval⟩, Finset.mem_univ _, by simp [leftPosition]⟩

/-- A position `p` is a right position iff `50 <= p.val`. -/
theorem rightPos_iff_val (p : Fin 99) :
    p ∈ rightUniv49 ↔ 50 <= p.val := by
  unfold rightUniv49
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨r, _, heq⟩
    subst p
    simp only [rightPosition]
    omega
  · intro hval
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨p.val - 50, by omega⟩, Finset.mem_univ _, by
      apply Fin.ext
      simp only [rightPosition]
      omega⟩


/-- The 50 left positions and the 49 right positions cover the full deck. -/
theorem leftUniv50_union_rightUniv49_eq_univ :
    leftUniv50 ∪ rightUniv49 = (Finset.univ : Finset (Fin 99)) := by
  ext p
  rw [Finset.mem_union]
  constructor
  · intro _
    apply Finset.mem_univ
  · intro _
    by_cases hpv : p.val < 50
    · left
      simpa [leftPos_iff_val p] using hpv
    · right
      simp [rightPos_iff_val p]
      omega

/-- A position cannot be both a left position and a right position. -/
theorem leftUniv50_disjoint_rightUniv49 :
    Disjoint leftUniv50 rightUniv49 := by
  rw [Finset.disjoint_left]
  intro p hpL
  have hlt : p.val < 50 := by simpa [leftPos_iff_val p] using hpL
  by_contra hpR
  have hge : 50 <= p.val := by simpa [rightPos_iff_val p] using hpR
  omega

/-- The left-position part of the total marked positions is exactly the image
    of the marked left positions. -/
theorem totalMarked_leftInter_eq_image :
    (totalMarkedPos d) ∩ leftUniv50 = (markedLeftPos d).image leftPosition := by
  ext p
  constructor
  · intro hp
    have hif : p ∈ (totalMarkedPos d) ∩ leftUniv50 ↔
        p ∈ totalMarkedPos d ∧ p ∈ leftUniv50 := Finset.mem_inter
    rcases hif.mp hp with ⟨hp1, hp2⟩
    rw [Finset.mem_image]
    have hpv : p.val < 50 := by simpa [leftPos_iff_val p] using hp2
    let l : Fin 50 := ⟨p.val, hpv⟩
    have hpos : leftPosition l = p := by
      apply Fin.ext
      simp only [leftPosition, Fin.mk]
      rfl
    refine ⟨l, ?_, hpos⟩
    simpa only [markedLeft_iff_inTotal d l, hpos] using hp1
  · intro hp
    simp only [Finset.mem_image] at hp
    rcases hp with ⟨l, hl, heq⟩
    rw [Finset.mem_inter]
    constructor
    · have htot : leftPosition l ∈ totalMarkedPos d := by
        simpa [markedLeft_iff_inTotal d l] using hl
      rwa [heq] at htot
    · unfold leftUniv50
      have hmimg : p ∈ (Finset.univ : Finset (Fin 50)).image leftPosition ↔
          ∃ a ∈ (Finset.univ : Finset (Fin 50)), leftPosition a = p := Finset.mem_image
      exact hmimg.mpr ⟨l, Finset.mem_univ _, heq⟩

/-- The right-position part of the total marked positions is exactly the image
    of the marked right positions. -/
theorem totalMarked_rightInter_eq_image :
    (totalMarkedPos d) ∩ rightUniv49 = (markedRightPos d).image rightPosition := by
  ext p
  constructor
  · intro hp
    have hif : p ∈ (totalMarkedPos d) ∩ rightUniv49 ↔
        p ∈ totalMarkedPos d ∧ p ∈ rightUniv49 := Finset.mem_inter
    rcases hif.mp hp with ⟨hp1, hp2⟩
    rw [Finset.mem_image]
    have hge : 50 <= p.val := by simpa [rightPos_iff_val p] using hp2
    have hsub : p.val - 50 < 49 := by
      have hlt99 : p.val < 99 := p.isLt
      omega
    let r : Fin 49 := ⟨p.val - 50, hsub⟩
    have hpos : rightPosition r = p := by
      apply Fin.ext
      have hrval : r.val = p.val - 50 := by
        unfold r
        rfl
      simp only [rightPosition, hrval]
      omega
    refine ⟨r, ?_, hpos⟩
    simpa only [markedRight_iff_inTotal d r, hpos] using hp1
  · intro hp
    simp only [Finset.mem_image] at hp
    rcases hp with ⟨r, hr, heq⟩
    rw [Finset.mem_inter]
    constructor
    · have htot : rightPosition r ∈ totalMarkedPos d := by
        simpa [markedRight_iff_inTotal d r] using hr
      rwa [heq] at htot
    · unfold rightUniv49
      have hmimg : p ∈ (Finset.univ : Finset (Fin 49)).image rightPosition ↔
          ∃ a ∈ (Finset.univ : Finset (Fin 49)), rightPosition a = p := Finset.mem_image
      exact hmimg.mpr ⟨r, Finset.mem_univ _, heq⟩

/-- The right pile holds `50 - leftOriginalCount d` originally-left cards: the
    50 marked cards split between the 50 left positions and the 49 right
    positions (conservation law). -/
theorem markedRightPos_card :
    (markedRightPos d).card = 50 - leftOriginalCount d := by
  have hCover : leftUniv50 ∪ rightUniv49 = (Finset.univ : Finset (Fin 99)) :=
    leftUniv50_union_rightUniv49_eq_univ
  have hDisjLR : Disjoint leftUniv50 rightUniv49 := leftUniv50_disjoint_rightUniv49
  have hDisjMR : Disjoint ((totalMarkedPos d) ∩ leftUniv50)
      ((totalMarkedPos d) ∩ rightUniv49) := by
    rw [Finset.disjoint_left]
    intro p hML
    have ifML : p ∈ (totalMarkedPos d) ∩ leftUniv50 ↔
        p ∈ totalMarkedPos d ∧ p ∈ leftUniv50 := Finset.mem_inter
    have hpL : p ∈ leftUniv50 := (ifML.mp hML).2
    by_contra hMR
    have ifMR : p ∈ (totalMarkedPos d) ∩ rightUniv49 ↔
        p ∈ totalMarkedPos d ∧ p ∈ rightUniv49 := Finset.mem_inter
    have hpR : p ∈ rightUniv49 := (ifMR.mp hMR).2
    have hnotL : p ∉ leftUniv50 := (Finset.disjoint_right.mp hDisjLR) hpR
    exact hnotL hpL
  have hLeft : ((totalMarkedPos d) ∩ leftUniv50).card = (markedLeftPos d).card := by
    rw [totalMarked_leftInter_eq_image]
    exact Finset.card_image_of_injective (s := markedLeftPos d) (H := leftPosition_injective)
  have hRight : ((totalMarkedPos d) ∩ rightUniv49).card = (markedRightPos d).card := by
    rw [totalMarked_rightInter_eq_image]
    exact Finset.card_image_of_injective (s := markedRightPos d) (H := rightPosition_injective)
  have hA : 50 =
      ((totalMarkedPos d) ∩ leftUniv50).card + ((totalMarkedPos d) ∩ rightUniv49).card := by
    calc
      50 = (totalMarkedPos d).card := by rw [← totalMarkedPos_card50]
      _ = ((totalMarkedPos d) ∩ (leftUniv50 ∪ rightUniv49)).card := by
        rw [hCover, Finset.inter_univ (totalMarkedPos d)]
      _ = (((totalMarkedPos d) ∩ leftUniv50) ∪
            ((totalMarkedPos d) ∩ rightUniv49)).card := by
        rw [Finset.inter_union_distrib_left]
      _ = ((totalMarkedPos d) ∩ leftUniv50).card +
            ((totalMarkedPos d) ∩ rightUniv49).card := by
        rw [Finset.card_union_of_disjoint hDisjMR]
  have hSum : (markedLeftPos d).card + (markedRightPos d).card = 50 := by
    simpa [hLeft, hRight] using hA.symm
  have hGoal : (markedRightPos d).card = 50 - (markedLeftPos d).card := by
    have h50 : 50 = (markedLeftPos d).card + (markedRightPos d).card := hSum.symm
    have hCS : (markedLeftPos d).card + (markedRightPos d).card -
        (markedLeftPos d).card = (markedRightPos d).card := by
      exact Nat.add_sub_cancel_left (markedLeftPos d).card (markedRightPos d).card
    rw [← h50] at hCS
    exact hCS.symm
  simpa only [← markedLeftPos_card d] using hGoal

end _Probe47n
end Shufflemath
