module

public import Shufflemath.FiniteDeck.Piles
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

/-!
# G5: per-pile restriction equivariance

A deck permutation `e : Deck N` that maps a position-pile `P i` onto the
corresponding card-pile `C i` (i.e. `(P i).image e = C i`) restricts to a
**bijection** between the two piles, `↥(P i) ≃ ↥(C i)`:

- **Injective** because `e` is a permutation (`e x = e y → x = y`).
- **Surjective** because `e[P i] = C i` (every card in `C i` is the image of some
  position in `P i`).

This is the reusable building block of the general-`k` product-fiber
equivariance: the full `MultiFiber N k posPile cardPile` fiber is a product of
these per-pile equivs, so once each pile `i` is realized,
`Fintype.card (MultiFiber …) = ∏_i (|C i|)!`.  It generalizes the two-pile
`swapFiber_card` (`|C 0|!·|C 1|!`) to arbitrary `k`.

These are deliberately **top-level `def`s with explicit parameters** (not a
`section` with the pile as a free variable): the surjectivity step rewrites the
membership `z.1 ∈ C i` into `z.1 ∈ (P i).image (fun q => e q)` using the
hypothesis `hi`, which only elaborates cleanly when `hi` is a genuine parameter
of the surrounding definition (see the G5 state doc, "pileEquiv" note).
-/

/-- **G5 per-pile restriction map.** Given a pile `i` and a realizing permutation
    `e` with `(P i).image (fun q => e q) = C i`, send a position `x` in pile `i`
    to the card `e x` (which lands in pile `C i`).  This is the forward map of
    the per-pile restriction equiv `pileEquiv`. -/
noncomputable def pileF (N k : Nat) (P C : Fin k → Finset (Fin N)) (i : Fin k) (e : Deck N)
    (hi : (P i).image (fun q => e q) = C i) (x : {x : Fin N // x ∈ P i}) :
    {x : Fin N // x ∈ C i} :=
  ⟨e x.1, by rw [← hi]; exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩

/-- **G5 per-pile restriction equiv.** A deck permutation `e` mapping
    position-pile `P i` onto card-pile `C i` restricts to a **bijection**
    `↥(P i) ≃ ↥(C i)`.  Injective because `e` is; surjective because
    `e[P i] = C i`.  The building block of the general-`k` product-fiber
    equivariance (Wall 2): the full `MultiFiber` fiber is a product of these
    per-pile equivs, whose `Fintype.card` is `∏_i (|P i|)! = ∏_i (|C i|)!`. -/
noncomputable def pileEquiv (N k : Nat) (P C : Fin k → Finset (Fin N)) (i : Fin k) (e : Deck N)
    (hi : (P i).image (fun q => e q) = C i) :
    Equiv {x : Fin N // x ∈ P i} {x : Fin N // x ∈ C i} := by
  let hf := @pileF N k P C i e hi
  have hfInj : Function.Injective hf := by
    intro x y hxy
    dsimp only [hf, pileF] at hxy ⊢
    have he : e x.1 = e y.1 := by simpa using hxy
    exact Subtype.ext (by calc x.1 = e.symm (e x.1) := by rw [Equiv.symm_apply_apply]
                                _ = e.symm (e y.1) := by rw [he]
                                _ = y.1 := by rw [Equiv.symm_apply_apply])
  have hfSurj : Function.Surjective hf := by
    intro z
    have hmem : z.1 ∈ (P i).image (fun q => e q) := by
      rw [hi]
      exact z.2
    rcases Finset.mem_image.mp hmem with ⟨w, hw, hew⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    simp [hf, pileF, hew]
  exact Equiv.ofBijective hf ⟨hfInj, hfSurj⟩

end FiniteDeck
end Shufflemath
