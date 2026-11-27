module

public import Shufflemath.FiniteDeck.HandSecrecy
public import Shufflemath.FiberDisintegration
public import Shufflemath.FiniteDeck.HistogramKernel

@[expose] public section

/-!
# The ordered `m`-position law (known-vs-unknown identity extension)

The hand-secrecy arc (`HandSecrecy.lean`) lands the *set*-level statement:
the card set of the first `k` deck positions is uniform over the `k`-subsets.
This module lands the **identity-level** counterpart: the **ordered `m`-tuple
of cards at the first `m` deck positions** is uniform over the injective `m`-tuples —
every injective ordered tuple `q : Fin m → Fin N` carries mass
`1 / (N.descFactorial m)` under the uniform deck law.  This is the "known vs
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
6. **`tuple_fiber_empty_of_not_injective`** — non-injective tuples have empty fibers.
7. **`tupleExtensionEquiv`** — the extension bijection
   `{q : Fin (k+1) → Fin N // Injective q} ≃ Σ (q : {q' : Fin k → Fin N // Injective q'}), {c : Fin N // c ∉ image q.1 univ}`.
8. **`card_injective`** — the injective-`m`-tuple count
   `Fintype.card {q : Fin m → Fin N // Injective q} = N.descFactorial m`
   (the falling-factorial count; induction via the extension equiv + the complement
   count `N - k`).
9. **`tuple_uniform_law`** — the headline: every injective tuple carries mass
   `1 / N.descFactorial m` under the uniform deck law.

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


/-! ## The extension bijection and the falling-factorial count -/

/-- The last position's card is never in the image of the cast-Succ positions. -/
theorem last_not_in_image (N : Nat) (k : Nat) (q : Fin (k+1) → Fin N) (hq : Function.Injective q) :
    q (Fin.last k) ∉ Finset.image (q ∘ Fin.castSucc) Finset.univ := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have hEq : q (Fin.castSucc i) = q (Fin.last k) := hi
  have := hq hEq
  exact Fin.castSucc_ne_last i this

/-- Extending an injective `k`-tuple by a fresh card yields a fresh injective tuple. -/
theorem extendTuple_injective (N : Nat) (k : Nat) (q : Fin k → Fin N)
    (hq : Function.Injective q) (c : Fin N) (hc : c ∉ Finset.image q Finset.univ) :
    Function.Injective (fun i => Fin.lastCases (motive := fun _ => Fin N) c (fun j => q j) i) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j =>
      have hEq : c = q j := by simpa using hij
      have hmem : c ∈ Finset.image q Finset.univ := by
        rw [Finset.mem_image]
        exact ⟨j, Finset.mem_univ _, hEq.symm⟩
      exact absurd hmem hc
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      have hEq : q i = c := by simpa using hij
      have hmem : c ∈ Finset.image q Finset.univ := by
        rw [Finset.mem_image]
        exact ⟨i, Finset.mem_univ _, hEq⟩
      exact absurd hmem hc
    | cast j =>
      have hEq : q i = q j := by simpa using hij
      have hijs : i = j := hq hEq
      exact congrArg Fin.castSucc hijs

/-- **The extension bijection.** An injective `(k+1)`-tuple is the same as an
    injective `k`-tuple plus a fresh card for the last position — the
    `Fin.lastCases` / `Equiv.ofBijective` idiom. -/
noncomputable def tupleExtensionEquiv (N k : Nat) :
    {q : Fin (k+1) → Fin N // Function.Injective q}
    ≃ Σ (q : {q' : Fin k → Fin N // Function.Injective q'}),
        {c : Fin N // c ∉ Finset.image q.1 Finset.univ} := by
  refine Equiv.ofBijective
    (fun q =>
      (⟨⟨fun i => q.1 (Fin.castSucc i), by
        apply Function.Injective.comp q.2 (Fin.castSucc_injective k)⟩,
       ⟨q.1 (Fin.last k), last_not_in_image N k q.1 q.2⟩⟩))
    ?_
  · constructor
    · intro a b hab
      have hLast : a.1 (Fin.last k) = b.1 (Fin.last k) := by
        have := congrArg (fun x => x.2.1) hab
        exact this
      have hInit' : ∀ i : Fin k, a.1 (Fin.castSucc i) = b.1 (Fin.castSucc i) := by
        have := congrArg (fun x => x.1.1) hab
        intro i
        exact congrFun this i
      have deq : a.1 = b.1 := by
        funext i
        cases i using Fin.lastCases with
        | last => exact hLast
        | cast j => exact hInit' j
      exact Subtype.ext deq
    · intro x
      refine ⟨⟨fun i => Fin.lastCases (motive := fun _ => Fin N) x.2.1 (fun j => x.1.1 j) i,
        ?_⟩, ?_⟩
      · apply extendTuple_injective _ _ _ x.1.2 x.2.1 x.2.2
      · ext
        simp
        dsimp only
        simp [Fin.lastCases]

/-- The complement of the image of an injective `k`-tuple has `N - k` cards. -/
theorem card_complement (N k : Nat) (q : Fin k → Fin N) (hq : Function.Injective q) :
    Fintype.card {c : Fin N // c ∉ Finset.image q Finset.univ} = N - k := by
  rw [Fintype.card_subtype_compl]
  have hCard : Fintype.card {c : Fin N // c ∈ Finset.image q Finset.univ} = k := by
    have h1 : Fin k ≃ {c : Fin N // c ∈ Finset.image q Finset.univ} :=
      Equiv.ofBijective (fun i => ⟨q i, by rw [Finset.mem_image]; exact ⟨i, Finset.mem_univ _, rfl⟩⟩)
        ⟨by intro a b h; exact hq (congrArg Subtype.val h),
         fun y => by
           obtain ⟨i, _, h⟩ := Finset.mem_image.mp y.2
           exact ⟨i, Subtype.ext h⟩⟩
    rw [Fintype.card_congr h1.symm, Fintype.card_fin]
  rw [Fintype.card_fin, hCard]

/-- **The injective-tuple count (the falling factorial).** The number of
    injective `m`-tuples of cards is `N.descFactorial m` — `N` choices for the
    first card, `N - 1` for the second, …, `N - m + 1` for the last. Induction
    via the extension bijection and the complement count `N - k`. -/
theorem card_injective (N m : Nat) :
    Fintype.card {q : Fin m → Fin N // Function.Injective q} = N.descFactorial m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have he : Fintype.card {q : Fin (k+1) → Fin N // Function.Injective q}
        = Fintype.card (Σ (q : {q' : Fin k → Fin N // Function.Injective q'}),
            {c : Fin N // c ∉ Finset.image q.1 Finset.univ}) := by
      rw [Fintype.card_congr (tupleExtensionEquiv N k)]
    rw [he, Fintype.card_sigma]
    have hvals : ∀ q : {q' : Fin k → Fin N // Function.Injective q'},
        Fintype.card {c : Fin N // c ∉ Finset.image q.1 Finset.univ} = N - k := by
      intro q
      exact card_complement N k q.1 q.2
    simp_rw [hvals]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
    rw [ih, Nat.descFactorial_succ]

/-- **The ordered-tuple uniform law (headline).** Under the uniform deck law,
    every injective ordered `m`-tuple of cards at the first `m` positions is
    uniform over the injective `m`-tuples — each carries mass
    `1 / (N.descFactorial m)`. The non-injective tuples have empty fibers; the
    injective tuples number `N.descFactorial m`; the fibers for two injective
    tuples are equal; the sum over all tuples is `N!`. -/
theorem tuple_uniform_law (N : Nat) [Nonempty (Equiv.Perm (Fin N))]
    (m : Nat) (hm : m ≤ N) (q : Fin m → Fin N) (hq : Function.Injective q) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
      (fun d => handTuple N m hm d)) q =
      (1 : Rat) / (N.descFactorial m : Rat) := by
  set K := ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => handTuple N m hm d = q)).card with hK
  have hsumExact : (∑ q' : Fin m → Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handTuple N m hm d = q')).card) = Nat.factorial N := by
    have h := Shufflemath.FiberDisintegration.sum_fiber_card
      (fun d : Equiv.Perm (Fin N) => handTuple N m hm d)
    have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [hcard_eq] at h
    exact_mod_cast h
  have hEmpty : ∀ q' : Fin m → Fin N, ¬ Function.Injective q' →
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => handTuple N m hm d = q')).card = 0 := by
    intro q' hq'
    exact tuple_fiber_empty_of_not_injective q' hq'
  have hcard_filter : (Finset.univ.filter (fun q' : Fin m → Fin N => Function.Injective q')).card =
      N.descFactorial m := by
    rw [← Fintype.card_subtype]
    exact card_injective N m
  have hsumN : (∑ q' : Fin m → Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handTuple N m hm d = q')).card) = N.descFactorial m * K := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun q' : Fin m → Fin N => Function.Injective q')]
    have hNot : ∑ q' ∈ Finset.univ.filter (fun q' : Fin m → Fin N => ¬ Function.Injective q'),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => handTuple N m hm d = q')).card = 0 := by
      apply Finset.sum_eq_zero
      intro q' h'
      exact hEmpty q' (Finset.mem_filter.mp h').2
    rw [hNot, add_zero]
    have hPer : ∑ q' ∈ Finset.univ.filter (fun q' : Fin m → Fin N => Function.Injective q'),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => handTuple N m hm d = q')).card =
        ∑ q' ∈ Finset.univ.filter (fun q' : Fin m → Fin N => Function.Injective q'), K := by
      apply Finset.sum_congr rfl
      intro q' h'
      have hcard' := tuple_fiber_card (hm := hm) q' q (Finset.mem_filter.mp h').2 hq
      have hcard'' : (Finset.univ.filter (fun d => handTuple N m hm d = q')).card = K := by
        calc (Finset.univ.filter (fun d => handTuple N m hm d = q')).card
            = (Finset.univ.filter (fun d => handTuple N m hm d = q)).card := hcard'
          _ = K := hK
      exact hcard''
    rw [hPer, Finset.sum_const, hcard_filter]
    ring
  have hfactN : Nat.factorial N = N.descFactorial m * K := hsumExact.symm.trans hsumN
  have hchoose_pos : 0 < N.descFactorial m := by
    rw [Nat.descFactorial_pos]
    exact hm
  have hchoose_pos_ne : (N.descFactorial m : Rat) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hchoose_pos)
  have hKpos : 0 < K := by
    by_contra h
    have hK0 : K = 0 := by omega
    have hzero : Nat.factorial N = 0 := by
      rw [hfactN, hK0, mul_zero]
    have hNfact : 0 < Nat.factorial N := Nat.factorial_pos N
    omega
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hfactRat : (Nat.factorial N : Rat) = (N.descFactorial m : Rat) * (K : Rat) := by
    exact_mod_cast hfactN
  have hK_ne : (K : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  rw [hcard_eq, hfactRat, ← hK]
  field_simp [hchoose_pos_ne, hK_ne]

end Shufflemath.FiniteDeck
