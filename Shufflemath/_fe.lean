module

public import Shufflemath.FiniteDeck.Fiber
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section
open Classical

namespace Shufflemath
namespace FiniteDeck

-- G2 / T1: the two membership fibers have equal size.
theorem fibersEqual (N m : Nat) (hm : m ≤ N) (A B : Membership N m) :
    Fintype.card (FibType N m hm A) = Fintype.card (FibType N m hm B) := by
  obtain ⟨t, hTB⟩ := fibTransitive_finset N m hm A B
  have hImg : ∀ (e : FibType N m hm A), (leftPositions N m hm).image (fun p => (e.1.trans t) p) = B.1 := by
    intro e
    have h1 := img_comp N t e.1 (leftPositions N m hm)
    simp only [h1, e.2, hTB]
  have hPre : ∀ (f : FibType N m hm B), (leftPositions N m hm).image (fun p => (f.1.trans t.symm) p) = A.1 := by
    intro f
    have h1 := img_comp N t.symm f.1 (leftPositions N m hm)
    have hBack : (B.1).image (fun a => t.symm a) = A.1 := by
      simpa [hTB] using img_symm_img N t A.1
    simp only [h1, f.2, hBack]
  let F : FibType N m hm A → FibType N m hm B := fun e => ⟨e.1.trans t, hImg e⟩
  exact Fintype.card_congr (Equiv.ofBijective F (by
    constructor
    · dsimp only [F]
      intro e₁ e₂ h
      refine Subtype.ext ?_
      apply Equiv.ext
      intro x
      have hE : e₁.1.trans t = e₂.1.trans t := by
        simpa using (congrArg (fun (z : FibType N m hm B) => z.1) h)
      have hE2 : (e₁.1.trans t) x = (e₂.1.trans t) x := by rw [hE]
      have h1 : (e₁.1.trans t) x = t (e₁.1 x) := Equiv.trans_apply e₁.1 t x
      have h2 : (e₂.1.trans t) x = t (e₂.1 x) := Equiv.trans_apply e₂.1 t x
      have hpx : t (e₁.1 x) = t (e₂.1 x) := by simpa [h1, h2] using hE2
      exact (by simpa [Equiv.symm_apply_apply] using (congrArg (fun w => t.symm w) hpx))
    · dsimp only [F]
      intro f
      have hX : (f.1.trans t.symm).trans t = f.1 := by
        ext x
        simp [Equiv.trans_apply, Equiv.apply_symm_apply]
      refine ⟨⟨f.1.trans t.symm, hPre f⟩, ?_⟩
      apply Subtype.ext
      exact hX))
end FiniteDeck
end Shufflemath
