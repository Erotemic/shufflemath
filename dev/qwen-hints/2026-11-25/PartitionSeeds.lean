-- Uncompiled generic candidates. These are intentionally independent of N=99.
module

public import Shufflemath.FiniteDeck.Piles
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.Qwen1125

-- Use explicit unique ownership, not another disjoint-union enumeration.
def IsPartition {I X : Type*} (P : I → Finset X) : Prop :=
  (∀ x : X, ∃ i, x ∈ P i) ∧
  (∀ i j x, x ∈ P i → x ∈ P j → i = j)

-- A finite partition's disjoint union of member subtypes is its underlying set.
-- No Fintype/card assumptions are needed for this equivalence itself.
noncomputable def partitionSigmaEquiv {I X : Type*} (P : I → Finset X)
    (hP : IsPartition P) : (Σ i : I, {x : X // x ∈ P i}) ≃ X := by
  classical
  apply Equiv.ofBijective (fun z => z.2.val)
  constructor
  · intro a b h
    rcases a with ⟨i, x⟩
    rcases b with ⟨j, y⟩
    change x.val = y.val at h
    have hy : x.val ∈ P j := by rw [h]; exact y.property
    have hij : i = j := hP.2 i j x.val x.property hy
    subst j
    have hxy : x = y := Subtype.ext h
    subst y
    rfl
  · intro x
    obtain ⟨i, hi⟩ := hP.1 x
    exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩

-- Glue block-local bijections while preserving the block index.
-- If simp on Sigma equality fails, use cases on z, then simp only the
-- appropriate inverse law; the first components are definitionally equal.
def sigmaBlockEquiv {I : Type*} {A B : I → Type*}
    (e : ∀ i, A i ≃ B i) : (Σ i, A i) ≃ (Σ i, B i) where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv z := by rcases z with ⟨i, x⟩; simp
  right_inv z := by rcases z with ⟨i, y⟩; simp

-- This construction is more general than a permutation: the domain and
-- codomain can be different finite sets of equal size, or even arbitrary types.
noncomputable def glueBlocks {I X Y : Type*} (P : I → Finset X) (C : I → Finset Y)
    (hP : IsPartition P) (hC : IsPartition C)
    (e : ∀ i, {x : X // x ∈ P i} ≃ {y : Y // y ∈ C i}) : X ≃ Y :=
  ((partitionSigmaEquiv P hP).symm.trans (sigmaBlockEquiv e)).trans
    (partitionSigmaEquiv C hC)

-- The inverse of the forgetful equivalence is known on each named member.
-- This is the only dependent-index bridge needed for the local formula.
theorem partitionSigmaEquiv_symm_member {I X : Type*} (P : I → Finset X)
    (hP : IsPartition P) (i : I) (x : X) (hx : x ∈ P i) :
    (partitionSigmaEquiv P hP).symm x = ⟨i, ⟨x, hx⟩⟩ := by
  apply (partitionSigmaEquiv P hP).injective
  rw [Equiv.apply_symm_apply]
  rfl

-- The local formula avoids all reasoning about dependent transports during
-- the subsequent image equality and restriction/gluing inverse proofs.
theorem glueBlocks_apply_member {I X Y : Type*} (P : I → Finset X) (C : I → Finset Y)
    (hP : IsPartition P) (hC : IsPartition C)
    (e : ∀ i, {x : X // x ∈ P i} ≃ {y : Y // y ∈ C i})
    (i : I) (x : X) (hx : x ∈ P i) :
    glueBlocks P C hP hC e x = (e i ⟨x, hx⟩).val := by
  unfold glueBlocks
  simp only [Equiv.trans_apply, partitionSigmaEquiv_symm_member P hP i x hx]
  rfl

end Shufflemath.Qwen1125
