module

public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# Multi-pile within-pile orbit (the general-`k` T5 membership preservation)

Generalizes the two-pile `WithinPileOrbit` result (`embed_m_imageLeft` /
`act_d_preservesMembership`) to an arbitrary partition of the positions into
`k` piles.

The statement: a global deck obtained by gluing a *family of per-pile
equivalences* `e i : {x // x ∈ P i} ≃ {x // x ∈ P i}` (a permutation within each
pile) sends **each pile to itself**.  Concretely, a within-pile riffle on one
pile — identity on every other pile — cannot move a card across piles, so the
pile membership (and hence the whole allocation / fiber) is preserved.

This is the combinatorial core of the multi-pile "T5 kernel": the within-pile
action group acts on each fiber (fixed allocation) rather than between fibers.
The proof is structural (it uses `glueBlocks_apply_member`, the pointwise gluing
formula) — no `native_decide` and no `99!` enumeration.
-/

/-- A within-pile equiv family `e : ∀ j, {x // x ∈ P j} ≃ {x // x ∈ P j}` (glued
    into a global deck by `glueBlocks`) maps pile `i` onto itself: the image of
    `P i` under the glued deck is `P i`.  The result depends only on `e i` —
    the action on the other piles is irrelevant to pile `i`'s image.  This is
    the general-`k` version of `WithinPileOrbit.embed_m_imageLeft`. -/
theorem glueBlocks_imagePile {N k : Nat} (P : Fin k → Finset (Fin N)) (hP : IsPartition P)
    (i : Fin k) (e : ∀ j, {x : Fin N // x ∈ P j} ≃ {x : Fin N // x ∈ P j}) :
    (P i).image (glueBlocks P P hP hP e) = P i := by
  apply Finset.ext
  intro x
  constructor
  · intro h
    rw [Finset.mem_image] at h
    rcases h with ⟨y, hy, heq⟩
    rw [glueBlocks_apply_member P P hP hP e i y hy] at heq
    · rw [← heq]
      exact (e i ⟨y, hy⟩).property
  · intro hx
    rw [Finset.mem_image]
    obtain ⟨yv, heq⟩ := (e i).surjective ⟨x, hx⟩
    refine ⟨yv.val, ⟨yv.property, ?_⟩⟩
    rw [glueBlocks_apply_member P P hP hP e i yv.val yv.property]
    change (e i yv).val = x
    exact congrArg Subtype.val heq

/-- A within-pile equiv family preserves **every** pile at once: gluing any
    family of per-pile equivalences sends each pile `P j` to itself, so the
    whole allocation (the `IsPartition` fiber) is fixed pointwise. -/
theorem glueBlocks_preservesEveryPile {N k : Nat} (P : Fin k → Finset (Fin N))
    (hP : IsPartition P) (e : ∀ j, {x : Fin N // x ∈ P j} ≃ {x : Fin N // x ∈ P j}) :
    ∀ j, (P j).image (glueBlocks P P hP hP e) = P j := fun j =>
  @glueBlocks_imagePile N k P hP j e

end FiniteDeck
end Shufflemath
