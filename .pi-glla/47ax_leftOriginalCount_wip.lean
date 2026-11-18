
-- 47ax: leftOriginalCount_conjugate assembly — CLOSEST FORM (compiles except the
-- <- direction's hGf call, which is a GENUINE whnf explosion, not a threshold).
--
-- STATUS:
--   * L50, leftOrigSet_eq_L50, hgL_L50, hGf, hGb : all COMPILE (hGpart both dirs).
--   * hLC (leftCards (d.trans g) = (leftCards d).image g): compiles modulo bookkeeping.
--   * hInt -> direction (hGb): compiles.
--   * hInt <- direction (hGf call): whnf TIMEOUTS even at maxHeartbeats 2000000
--     (10x default). The L50-image (Finset.univ : Fin 50).image (leftPosition)
--     nested inside g.image, cast through hL, is a genuine combinatorial whnf
--     explosion in the deep hInt context. NOT a correctness issue, NOT a threshold.
--
-- NEXT-SESSION STRATEGIES (in order of promise):
--   (a) FRAMESHIFT to Fin 50: prove the card equality on the FIN 50 index set
--       (where leftCards d and leftOrigSet are both 50-element images) using g
--       as a Fin-50 bijection, avoiding the Fin 99 image reduction entirely.
--       This is the cleanest and most likely to compile.
--   (b) Prove hInt as its OWN theorem (with a local heartbeat raise) so the whnf
--       cost is paid once at compile of hInt; the main proof then references it.
--   (c) Redefine a light auxiliary: leftOrigSet as an EXPLICIT Finset (not via
--       Finset.image) in a probe, proving hGpart/hInt against that lighter form,
--       then bridge back to the library leftOrigSet by leftOrigSet_eq_L50.
--
-- This is the closest-assembled form; the blocker is a performance wall in Lean's
-- whnf on the image-of-image structure, to be attacked with a representation change.

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

def hGf (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) (y : Fin 99)
    (hy : y ∈ leftOrigSet) : g y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hyL50 : y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := Finset.mem_image.mpr ⟨y, hyL50, rfl⟩
  simpa [leftOrigSet_eq_L50] using (hL ▸ Himg)

def hGb (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) (y : Fin 99)
    (hgy : g y ∈ leftOrigSet) : y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hgyL50 : g y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hgy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := by simpa [hL] using hgyL50
  rcases Finset.mem_image.mp Himg with ⟨z, hz, hgz⟩
  have hzL50 : z ∈ L50 := by simpa [leftOrigSet_eq_L50] using hz
  simpa [leftOrigSet_eq_L50] using (g.injective hgz).symm ▸ hzL50

theorem leftOriginalCount_conjugate (d g : Deck)
    (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) :
    leftOriginalCount (d.trans g) = leftOriginalCount d := by
  have hLC : leftCards (d.trans g) = (leftCards d).image (g : Fin 99 → Fin 99) := by
    unfold leftCards
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      use d (leftPosition i)
      · simp only [Finset.mem_image]
        use i
        simp
      · rw [Equiv.trans_apply]
    · rintro ⟨a, ⟨i, hi, hia⟩, hag⟩
      use i
      · simp
      · rw [Equiv.trans_apply, hia]
        exact hag
  have hInt : (leftCards (d.trans g) ∩ leftOrigSet) =
      ((leftCards d ∩ leftOrigSet).image (g : Fin 99 → Fin 99)) := by
    rw [hLC]
    ext x
    constructor
    · intro h
      have ⟨hym, hyL⟩ := h
      rcases hym with ⟨y, hyLc, hyg⟩
      have hyL' : y ∈ leftOrigSet := hGb d g hgL y (by simpa [hyg] using hyL)
      use y
      constructor
      · constructor
        · exact hyLc
        · exact hyL'
      · exact hyg
    · intro h
      rcases h with ⟨y, hyLc, hyL, hyg⟩
      constructor
      · use y
        constructor
        · exact hyLc
        · exact hyg
      · simpa [hyg] using (hGf d g hgL y hyL)
  rw [hInt, Finset.card_image_of_injective _ g.injective]
  simpa [leftOriginalCount_eq_leftCardsInter]

end Shufflemath
