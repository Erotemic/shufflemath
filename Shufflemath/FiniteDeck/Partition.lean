module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G5: generic partition / Sigma-gluing interface

A reusable foundation for the multi-pile (G5) theory, independent of `N`, of
`Fin k`, and of positivity assumptions.

* `IsPartition` — a family `P : I → Finset X` is a partition when every element
  has a **unique** owner.  This is the explicit unique-ownership presentation
  (preferred over disjoint-big-union enumerations); empty blocks are allowed,
  so `I` may be `Fin 0`.
* `partitionSigmaEquiv` — the disjoint union of the member subtypes
  `Σ i, {x // x ∈ P i}` is equivalent to `X`.  Injectivity is unique
  ownership + `Subtype.ext`; surjectivity is coverage.  No `Fintype`/card
  assumptions are needed for the equivalence itself.
* `sigmaBlockEquiv` — maps a dependent product of blocks through a supplied
  per-block equivalence, keeping the index.
* `glueBlocks` — composes the three equivalences
  `X ≃ Σ i, P-blocks ≃ Σ i, C-blocks ≃ Y`, producing a global bijection from
  block-local bijections.  This is the "generic partition/Sigma gluing" that
  the B2 fiber equivalence and B3 histogram counting are built on.
* `glueBlocks_apply_member` — the crucial evaluation lemma: when `x ∈ P i`,
  the glued bijection sends `x` to `(e i ⟨x, hx⟩).val`.  Later proofs use this
  pointwise theorem instead of manual `k`-case splits.
-/

/-- A family of finsets `P : I → Finset X` is a **partition** when every
    element of `X` lies in exactly one block: existence and uniqueness of an
    owner.  Empty blocks are allowed (so `I` may be `Fin 0`). -/
def IsPartition {I X : Type*} (P : I → Finset X) : Prop :=
  (∀ x : X, ∃ i, x ∈ P i) ∧
  (∀ i j x, x ∈ P i → x ∈ P j → i = j)

/-- The disjoint union of a partition's member subtypes is its underlying set:
    `Σ i, {x // x ∈ P i} ≃ X`, sending `(i, x)` to `x`.  Injectivity uses
    unique ownership; surjectivity uses coverage.  No `Fintype` or
    cardinality assumptions are required. -/
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

/-- Glue a dependent product of blocks through a supplied per-block
    equivalence, preserving the index: `Σ i, A i ≃ Σ i, B i`. -/
def sigmaBlockEquiv {I : Type*} {A B : I → Type*}
    (e : ∀ i, A i ≃ B i) : (Σ i, A i) ≃ (Σ i, B i) where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv z := by rcases z with ⟨i, x⟩; simp
  right_inv z := by rcases z with ⟨i, y⟩; simp

/-- Given two partitions `P : I → Finset X` and `C : I → Finset Y` and a
    block-local bijection `e i : {x // x ∈ P i} ≃ {y // y ∈ C i}` for every
    block, glue the local bijections into a global `X ≃ Y`.  This is more
    general than a permutation: the domain and codomain may be different types.
    Empty blocks are handled by the Sigma/gluing construction, not by case
    splits. -/
noncomputable def glueBlocks {I X Y : Type*} (P : I → Finset X) (C : I → Finset Y)
    (hP : IsPartition P) (hC : IsPartition C)
    (e : ∀ i, {x : X // x ∈ P i} ≃ {y : Y // y ∈ C i}) : X ≃ Y :=
  ((partitionSigmaEquiv P hP).symm.trans (sigmaBlockEquiv e)).trans
    (partitionSigmaEquiv C hC)

/-- The inverse of the forgetful equivalence is known on each named member:
    `(partitionSigmaEquiv P hP).symm x = ⟨i, ⟨x, hx⟩⟩`.  This is the only
    dependent-index bridge the local gluing formula needs. -/
theorem partitionSigmaEquiv_symm_member {I X : Type*} (P : I → Finset X)
    (hP : IsPartition P) (i : I) (x : X) (hx : x ∈ P i) :
    (partitionSigmaEquiv P hP).symm x = ⟨i, ⟨x, hx⟩⟩ := by
  apply (partitionSigmaEquiv P hP).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The local evaluation formula for the glued bijection: when `x ∈ P i`, the
    glued bijection sends `x` to the value of the local bijection on `⟨x, hx⟩`.
    Later proofs (image equality, restriction/gluing inverses) use this
    pointwise theorem instead of manual `k`-case or dependent-transport
    reasoning. -/
theorem glueBlocks_apply_member {I X Y : Type*} (P : I → Finset X) (C : I → Finset Y)
    (hP : IsPartition P) (hC : IsPartition C)
    (e : ∀ i, {x : X // x ∈ P i} ≃ {y : Y // y ∈ C i})
    (i : I) (x : X) (hx : x ∈ P i) :
    glueBlocks P C hP hC e x = (e i ⟨x, hx⟩).val := by
  unfold glueBlocks
  simp only [Equiv.trans_apply, partitionSigmaEquiv_symm_member P hP i x hx]
  rfl

end FiniteDeck
end Shufflemath
