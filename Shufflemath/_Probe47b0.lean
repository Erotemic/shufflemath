module
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Mathlib.Tactic
@[expose] public section
namespace Shufflemath
open CommanderPermutation

def L50 : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image (fun i : Fin 50 => (leftPosition i : Fin 99))

theorem leftOrigSet_eq_L50 : leftOrigSet = L50 := by
  unfold L50
  rw [leftOrigSet_eq_image]
  apply Finset.image_congr
  intro i _
  ext
  rfl

theorem hgL_L50 (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) :
    L50.image (g : Fin 99 → Fin 99) = L50 := by
  rw [← leftOrigSet_eq_L50, hgL, leftOrigSet_eq_L50]

-- TOP-LEVEL hGpart (47ao form): compiles standalone. Main proof references it by name.
theorem hGpart_fwd (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) (hy : y ∈ leftOrigSet) : g y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hyL50 : y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := Finset.mem_image.mpr ⟨y, hyL50, rfl⟩
  simpa [leftOrigSet_eq_L50] using (hL ▸ Himg)

theorem hGpart_bwd (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) (hgy : g y ∈ leftOrigSet) : y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hgyL50 : g y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hgy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := by simpa [hL] using hgyL50
  rcases Finset.mem_image.mp Himg with ⟨z, hz, hgz⟩
  have hzL50 : z ∈ L50 := by simpa [leftOrigSet_eq_L50] using hz
  simpa [leftOrigSet_eq_L50] using (g.injective hgz).symm ▸ hzL50

theorem hGpart (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) : y ∈ leftOrigSet ↔ g y ∈ leftOrigSet :=
  Iff.intro (hGpart_fwd d g hgL y) (hGpart_bwd d g hgL y)

-- MAIN: reference hGpart by name (top-level theorem, light at the call site).
theorem leftOriginalCount_conjugate (d g : Deck)
    (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) :
    leftOriginalCount (d.trans g) = leftOriginalCount d := by
  unfold leftOriginalCount
  -- prove the two Fin 50 filters equal, then the card equality is rfl
  have hEq : (Finset.univ : Finset (Fin 50)).filter (fun i => ((d.trans g) (leftPosition i)).val < 50) =
      (Finset.univ : Finset (Fin 50)).filter (fun i => (d (leftPosition i)).val < 50) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    -- goal: ((d.trans g)(leftPos i)).val < 50 <-> (d (leftPos i)).val < 50
    have htrans : (d.trans g) (leftPosition i) = g (d (leftPosition i)) := by rw [Equiv.trans_apply]
    have hpart : g (d (leftPosition i)) ∈ leftOrigSet ↔ d (leftPosition i) ∈ leftOrigSet :=
      (hGpart d g hgL (d (leftPosition i))).symm
    have hval (x : Fin 99) : x ∈ leftOrigSet ↔ x.val < 50 := by
      simp only [leftOrigSet, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    calc
      ((d.trans g) (leftPosition i)).val < 50
        ↔ (d.trans g) (leftPosition i) ∈ leftOrigSet := (hval _).symm
      _ ↔ g (d (leftPosition i)) ∈ leftOrigSet := by simpa [htrans]
      _ ↔ d (leftPosition i) ∈ leftOrigSet := hpart
      _ ↔ (d (leftPosition i)).val < 50 := hval _
  rw [hEq]

end Shufflemath
