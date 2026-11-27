module

public import Shufflemath.FiniteDeck.HandSecrecy

@[expose] public section

/-!
# The ordered `m`-position law (known-vs-unknown identity extension)

The hand-secrecy arc (`HandSecrecy.lean`) lands the *set*-level statement:
the card set of the first `k` deck positions is uniform over the `k`-subsets.
This module lands the **identity-level** counterpart: the **ordered `m`-tuple
of cards at the first `m` deck positions** is uniform over the injective `m`-tuples —
every ordered tuple `q : Fin m → Fin N` with distinct cards carries mass
`(Nat.factorial (N - m) : Rat) / (Nat.factorial N : Rat)` under the uniform deck law,
the reciprocal of `Nat.choose N m * Nat.factorial m`.  This is the "known vs
unknown card identities" extension of the secrecy story: the hand-set law treats
the hand as *sets* (order discarded); this law treats the hand as an *ordered
tuple of identities*.

Proof shape (mirroring the joint-hand and hand-secrecy laws):
1. **`handTuple`** — the ordered-tuple observation (first `m` positions, order kept).
2. **`tupleEmb`** — the ordered injection `Fin m ↪ {x // x ∈ image q univ}` for
   injective `q` (the `Equiv.ofBijective` idiom).
3. **`tupleEquiv`** — the *specific* ordered-card subtype bijection `q i ↦ q' i`
   (the embedding-composition idiom `qEmb.symm.trans qEmb'`).
4. **`tupleTransitive`** — the `m`-tuple transcomposition sending `q i ↦ q' i`
   (the `glueBlocks` gluing pattern, block 0 the range of `q`, block 1 the
   complement, the complement block via `Fintype.equivOfCardEq`).
5. **`tuple_fiber_card`** — the fibers of the observation for two valid tuples
   are equal (the `d ↦ d.trans τ` bijection).

No ratio of factorials is computed except at the final `field_simp`.
-/

namespace Shufflemath.FiniteDeck

open Classical

/-- The ordered `m`-tuple of cards at the first `m` deck positions. -/
def handTuple (N m : Nat) (hm : m ≤ N) (d : Equiv.Perm (Fin N)) : Fin m → Fin N :=
  fun i => d (Fin.castLE hm i)

/-! ## The ordered-card subtype bijection -/

/-- The ordered injection `Fin m ↪ {x // x ∈ image q univ}` for injective `q`. -/
noncomputable def tupleEmb (q : Fin m → Fin N) (hq : Function.Injective q) :
    Fin m ≃ {x : Fin N // x ∈ Finset.image q Finset.univ} := by
  apply Equiv.ofBijective (fun i => ⟨q i, by
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩⟩)
  · constructor
    · intro a b hab
      have hval : q a = q b := by exact congrArg Subtype.val hab
      exact hq hval
    · intro y
      obtain ⟨i, _, h⟩ := Finset.mem_image.mp y.2
      exact ⟨i, Subtype.ext h⟩

/-- The specific ordered-card subtype bijection: `q i ↦ q' i`. -/
noncomputable def tupleEquiv (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') :
    {x : Fin N // x ∈ Finset.image q Finset.univ}
      ≃ {y : Fin N // y ∈ Finset.image q' Finset.univ} :=
  (tupleEmb q hq).symm.trans (tupleEmb q' hq')

/-- The specific value of the ordered bijection on `q i`. -/
theorem tupleEquiv_apply (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q')
    (i : Fin m) (h : q i ∈ Finset.image q Finset.univ) :
    (tupleEquiv q q' hq hq' ⟨q i, h⟩).val = q' i := by
  have h1 : (tupleEmb q hq).symm ⟨q i, h⟩ = i := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [tupleEquiv, Equiv.trans_apply, h1]
  rfl

/-! ## The `m`-tuple transcomposition -/

/-- The two card-blocks: the range of `q` (block 0) and its complement (block 1). -/
def tupleBlocks (q : Fin m → Fin N) (i : Fin 2) : Finset (Fin N) :=
  match i with
  | 0 => Finset.image q Finset.univ
  | 1 => Finset.univ \ Finset.image q Finset.univ

/-- Membership in the two-block partition. -/
theorem tupleBlocks_mem (q : Fin m → Fin N) (i : Fin 2) (x : Fin N) :
    x ∈ tupleBlocks q i ↔
      (i = 0 ∧ x ∈ Finset.image q Finset.univ) ∨
      (i = 1 ∧ x ∉ Finset.image q Finset.univ) := by
  fin_cases i <;> simp [tupleBlocks, Finset.mem_sdiff]

/-- The two-block partition is a partition. -/
theorem tupleBlocks_isPartition (q : Fin m → Fin N) : IsPartition (tupleBlocks q) := by
  constructor
  · intro x
    by_cases hx : x ∈ Finset.image q Finset.univ
    · exact ⟨0, by simp [tupleBlocks, hx]⟩
    · exact ⟨1, by simp [tupleBlocks, Finset.mem_sdiff, hx]⟩
  · intro i j x hx hj
    fin_cases i <;> fin_cases j <;> simp_all [tupleBlocks, Finset.mem_sdiff]

/-- The complement block holds exactly `N - m` cards. -/
theorem tupleBlocks_complement_card (q : Fin m → Fin N) (hq : Function.Injective q) :
    (Finset.univ \ Finset.image q Finset.univ).card = N - m := by
  have hSq : (Finset.image q Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ hq, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_sdiff, Finset.inter_univ, hSq, Finset.card_univ, Fintype.card_fin]

/-- The per-block bijections: block 0 is the specific ordered bijection
    `tupleEquiv`, block 1 (the complement) is an arbitrary bijection supplied by
    `Fintype.equivOfCardEq`. -/
noncomputable def tupleBlocksEquivs (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') :
    ∀ i : Fin 2, {x : Fin N // x ∈ tupleBlocks q i} ≃ {y : Fin N // y ∈ tupleBlocks q' i} := fun i =>
  match i with
  | 0 => tupleEquiv q q' hq hq'
  | 1 => Fintype.equivOfCardEq (by
      have h1 := tupleBlocks_complement_card q hq
      have h2 := tupleBlocks_complement_card q' hq'
      show Fintype.card ↥(Finset.univ \ Finset.image q Finset.univ) =
        Fintype.card ↥(Finset.univ \ Finset.image q' Finset.univ)
      rw [Fintype.card_coe, Fintype.card_coe, h1, h2])

/-- The `m`-tuple transcomposition: `τ` with `τ (q i) = q' i` for every `i`. -/
noncomputable def tupleTransitive (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') : Equiv.Perm (Fin N) :=
  glueBlocks (tupleBlocks q) (tupleBlocks q')
    (tupleBlocks_isPartition q) (tupleBlocks_isPartition q')
    (tupleBlocksEquivs q q' hq hq')

/-- The `m`-tuple transcomposition moves every `q i` to `q' i`. -/
theorem tupleTransitive_apply_q (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') (i : Fin m) :
    tupleTransitive q q' hq hq' (q i) = q' i := by
  have hx : q i ∈ tupleBlocks q 0 := by
    simp only [tupleBlocks, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  simp only [tupleTransitive]
  rw [glueBlocks_apply_member (tupleBlocks q) (tupleBlocks q')
      (tupleBlocks_isPartition q) (tupleBlocks_isPartition q')
      (tupleBlocksEquivs q q' hq hq') 0 (q i) hx]
  exact tupleEquiv_apply q q' hq hq' i hx

/-! ## The fiber -/

/-- The fiber of an ordered tuple: the decks carrying `q` at the first `m` positions. -/
noncomputable def tupleFiber (N m : Nat) (hm : m ≤ N) (q : Fin m → Fin N) :
    Finset (Equiv.Perm (Fin N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => handTuple N m hm d = q)

/-- The transcomposition acts on the ordered tuple by card-relabeling. -/
theorem handTuple_trans (N m : Nat) (hm : m ≤ N) (τ : Equiv.Perm (Fin N))
    (d : Equiv.Perm (Fin N)) :
    handTuple N m hm (d.trans τ) = (fun i => τ (handTuple N m hm d i)) := by
  ext i
  simp only [handTuple, Equiv.trans_apply]

variable {N m : Nat} {hm : m ≤ N}

/-- The joint-hand image lemma for the ordered fiber: the transcomposition
    carries the fiber of `q` to the fiber of `q'`. -/
theorem tuple_trans_image (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') :
    (tupleFiber N m hm q).image (fun d => d.trans (tupleTransitive q q' hq hq')) =
      tupleFiber N m hm q' := by
  ext e2
  constructor
  · intro he2
    rw [Finset.mem_image] at he2
    obtain ⟨d, hd, hd0⟩ := he2
    simp only [tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp only [tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hd0, handTuple_trans]
    ext i
    rw [hd, tupleTransitive_apply_q q q' hq hq' i]
  · intro he0
    simp only [tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and] at he0
    rw [Finset.mem_image]
    refine ⟨e2.trans (tupleTransitive q q' hq hq').symm, ?_, ?_⟩
    · simp only [tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : ∀ i : Fin m, (tupleTransitive q q' hq hq').symm (q' i) = q i := by
        intro i
        have hm := Equiv.symm_apply_apply (tupleTransitive q q' hq hq') (q i)
        rw [tupleTransitive_apply_q q q' hq hq' i] at hm
        exact hm
      show handTuple N m hm (e2.trans (tupleTransitive q q' hq hq').symm) = q
      rw [handTuple_trans]
      ext i
      rw [he0, h1 i]
    · rw [Equiv.trans_assoc, Equiv.symm_trans_self]
      simp [Equiv.trans_refl]

/-- **Equal-fiber cardinality for ordered tuples.** -/
theorem tuple_fiber_card (q q' : Fin m → Fin N)
    (hq : Function.Injective q) (hq' : Function.Injective q') :
    (tupleFiber N m hm q).card = (tupleFiber N m hm q').card := by
  let τ := tupleTransitive q q' hq hq'
  have hind : Function.Injective (fun d : Equiv.Perm (Fin N) => d.trans τ) := by
    intro a b h
    apply Equiv.ext
    intro x
    have hx := congrArg (fun f => f x) h
    rw [Equiv.trans_apply, Equiv.trans_apply] at hx
    exact Equiv.injective τ hx
  rw [← tuple_trans_image q q' hq hq', Finset.card_image_of_injective _ hind]
/-- **The diagonal / non-injective fiber is empty.** A deck cannot put the
    same card at two distinct positions of the hand, so the fiber of a
    non-injective tuple is empty — every fiber is nonempty only for injective
    tuples. -/
theorem tuple_fiber_empty_of_not_injective (q : Fin m → Fin N)
    (hq : ¬ Function.Injective q) :
    (tupleFiber N m hm q).card = 0 := by
  have hEmpty : tupleFiber N m hm q = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    simp only [tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hq
    have h1 : d (Fin.castLE hm i) = q i := congrArg (fun f : Fin m → Fin N => f i) hd
    have h2 : d (Fin.castLE hm j) = q j := congrArg (fun f : Fin m → Fin N => f j) hd
    have h3 : d (Fin.castLE hm i) = d (Fin.castLE hm j) := calc
      d (Fin.castLE hm i) = q i := h1
      _ = q j := heq
      _ = d (Fin.castLE hm j) := h2.symm
    have h4 : Fin.castLE hm i = Fin.castLE hm j := Equiv.injective d h3
    have h5 : i = j := Fin.castLE_injective hm h4
    exact hij h5
  rw [hEmpty]
  rfl

end Shufflemath.FiniteDeck
