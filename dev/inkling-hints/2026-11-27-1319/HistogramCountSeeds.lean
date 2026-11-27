import Shufflemath.FiniteDeck.FixedPairExchange
import Shufflemath.FiniteDeck.MultiPileFiber

/-! Uncompiled abstract seeds for section B. The same elementary image
criterion handles positions, colors and pile-category cells. No group action
API or new orbit proof. -/
namespace Shufflemath.FiniteDeck.Nov27CountingSeeds
open Classical

-- Characterize simultaneous images of ALL fibers via one pointwise equality.
theorem image_fibers_iff {X I : Type*} [Fintype X] [DecidableEq X] [DecidableEq I]
    (f g : X → I) (e : Equiv.Perm X) :
    (∀ i, (Finset.univ.filter (fun x => f x = i)).image (fun x => e x) =
      Finset.univ.filter (fun x => g x = i)) ↔ ∀ x, g (e x) = f x := by
  constructor
  · intro h x
    have hm : e x ∈ (Finset.univ.filter (fun z => f z = f x)).image (fun z => e z) := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    rw [h (f x)] at hm
    exact (Finset.mem_filter.mp hm).2
  · intro h i
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hxy]
      exact (h x).trans (Finset.mem_filter.mp hx).2
    · intro hy
      refine Finset.mem_image.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hp := h (e.symm y)
      rw [e.apply_symm_apply] at hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm.trans (Finset.mem_filter.mp hy).2⟩

-- Count fibers in Nat, keeping division out of the combinatorial proof.
theorem fiber_card_mul {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (m : Nat) (h : ∀ y, (Finset.univ.filter (fun x : X => f x = y)).card = m) :
    Fintype.card X = Fintype.card Y * m := by
  let e : X ≃ Σ y : Y, {x : X // f x = y} :=
    { toFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
      invFun := fun z => z.2.val
      left_inv := fun x => rfl
      right_inv := by
        rintro ⟨y, x, hx⟩
        subst y
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hc : ∀ y : Y, Fintype.card {x : X // f x = y} = m := by
    intro y
    rw [Fintype.card_subtype]
    exact h y
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

-- A cell-preserving pointwise map implies both color preservation and the
-- intended allocation relabeling. This avoids constructing another sigmaEquiv.
theorem cell_map_imp_relabel {N p c : Nat} {n : Fin p → Nat}
    (color : Fin N → Fin c) (A B : Allocation N p n) (e : Equiv.Perm (Fin N))
    (h : ∀ x, ownerCell color B (e x) = ownerCell color A x) :
    relabel e A = B ∧ ∀ x, color (e x) = color x := by
  constructor
  · apply Subtype.ext
    funext y
    have hy := congrArg Prod.fst (h (e.symm y))
    change B.val (e (e.symm y)) = A.val (e.symm y) at hy
    rw [e.apply_symm_apply] at hy
    exact hy.symm
  · intro x
    exact congrArg Prod.snd (h x)

-- The converse identifies the fiber of a relabeling map without group quotients.
theorem relabel_imp_cell_map {N p c : Nat} {n : Fin p → Nat}
    (color : Fin N → Fin c) (A B : Allocation N p n) (e : Equiv.Perm (Fin N))
    (h : relabel e A = B) (hc : ∀ x, color (e x) = color x) :
    ∀ x, ownerCell color B (e x) = ownerCell color A x := by
  intro x
  have ho := congrArg (fun a : Allocation N p n => a.val (e x)) h
  change A.val (e.symm (e x)) = B.val (e x) at ho
  rw [e.symm_apply_apply] at ho
  exact Prod.ext ho.symm (hc x)

end Shufflemath.FiniteDeck.Nov27CountingSeeds
