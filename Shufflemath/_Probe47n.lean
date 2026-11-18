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

end _Probe47n
end Shufflemath
