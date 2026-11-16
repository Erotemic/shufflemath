module

public import Shufflemath.FiniteDeck.Fiber
public import Mathlib.Tactic

@[expose] public section
open Classical

namespace Shufflemath
namespace FiniteDeck

-- image of the inverse of the image: for a permutation t, t.symm '' (t '' s) = s.
theorem img_symm_img (N : Nat) (t : Equiv.Perm (Fin N)) (s : Finset (Fin N)) :
    ((s).image (fun p => t p)).image (fun a => t.symm a) = s := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, hAm, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hap⟩ := Finset.mem_image.mp hAm
    have hX : x = p := by
      rw [← hax, ← hap]
      exact Equiv.symm_apply_apply t p
    simpa [hX] using hp
  · intro hx
    have hTx : t x ∈ (s).image (fun p => t p) := Finset.mem_image_of_mem (fun p => t p) hx
    have hX : t.symm (t x) = x := Equiv.symm_apply_apply t x
    simpa [hX] using Finset.mem_image_of_mem (fun a => t.symm a) hTx
end FiniteDeck
end Shufflemath
