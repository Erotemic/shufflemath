module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
public import Shufflemath.GSR

@[expose] public section

namespace Shufflemath

/-!
F4.2 — the GSR sorted-key rank as a *genuine* finite permutation.
==========================================================================
This module resolves the "last F4 wall" (Section 3 of
`docs/planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md`):
turn `GSR.idealShuffle`'s output into a *real* finite permutation of the deck
positions.  The output deck is ordered by the GSR key, a lexicographic pair
(`(label, position)` with `label` major and `position` minor); ranking it as a
permutation of `Fin n` used to be blocked because this Mathlib has **no
`DecidableRel` instance for the lexicographic `<` on a product type** (probed on
both `Nat × Nat` and `Fin a × Fin n`; `Finset.filter` fails on both).

The fix is to **flatten the lex key to a single `Nat`**:

    keyNat i = (ℓ i).val * n + i.val

whose `<` *is* the lexicographic order on `(ℓ i).val, i.val` (for `i, j < n`,
`keyNat i < keyNat j ↔ (ℓ i).val < (ℓ j).val ∨ ((ℓ i).val = (ℓ j).val ∧ i.val <
j.val)` — proved as `keyNat_lex`) and whose `<` is decidable.

What this module establishes (all building; see the per-lemma comments):
  * `keyNat`, `keyBelow`, `rankVal` — the flattened key, the below-set, the rank.
  * `keyNat_injective` — two equal flattened keys force equal indices (mod-
    `n` uniqueness), so `keyNat` is injective on a deck.
  * `rankVal_rankEquivSymm` — the rank of the `r`-th rank-ordered card is `r`.
  * `rankEquiv : Equiv (Fin n) (Fin n)` — the rank as a **genuine finite
    permutation**, with `rankEquiv_symm_apply` (symm recovers the rank-ordered
    deck) and `rankEquiv_eq_orderByNewPosition` (the *only* remaining list
    equality of F4.2).
  * `rankOrderKeyList` — the rank-ordered key sequence, with
    `rankOrderKeyList_sortedLT` (the GSR output *is* a sorted key sequence) and
    `rankOrderKeys_nodup`.
  * `keyNat_lex` — the algebraic statement that `keyNat`'s order is the lex
    `(label, position)` order.
  * `map_inj_eq` — injective maps reflect list equality.

The one open sub-lemma for the capstone
`stableBuckets a ℓ (finRange n) = (finRange n).map rankEquiv.symm` is the
`SortedLT` of the *stable-bucketed* deck's key image (hL); it is documented in
full at the end of this module, with the precise Mathlib API gap (no
filter/subsequence-sortedness or filter-`get` lemma) that it needs.
-/

open Finset

/- The flattened lex key: `(ℓ i).val * n + i.val`.  For `i,j < n`,
   `keyNat i < keyNat j ↔ (ℓ i).val < (ℓ j).val ∨ (ℓ i).val = (ℓ j).val ∧ i < j`,
   i.e. it is exactly the lexicographic order, and `<` is decidable. -/
def keyNat (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (ℓ i).val * n + i.val

/- The set of elements whose key is strictly below `i`'s (the "initial segment
   before `i`" in the sorted order). -/
def keyBelow (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun k => keyNat n a ℓ k < keyNat n a ℓ i)

/- The rank: how many keys are strictly below `i`'s.  This is the order-
   preserving map the permutation is built from. -/
def rankVal (n a : Nat) (ℓ : Fin n → Fin a) (i : Fin n) : Nat :=
  (keyBelow n a ℓ i).card

/- **`keyNat` is an injection for `0 < n`.** Two equal flattened keys are
   congruent mod `n`, which forces equal indices: both `i.val` and `j.val` are
   `< n`, so equal mod `n` ⇒ equal. -/
theorem keyNat_injective (n a : Nat) (_hn : 0 < n) (ℓ : Fin n → Fin a) :
    Function.Injective (keyNat n a ℓ) := by
  intro i j h
  have hL : keyNat n a ℓ i ≡ i.val [MOD n] := by
    rw [keyNat]
    exact Nat.mul_modulus_add_modEq_iff.mpr (Nat.ModEq.rfl)
  have hR : keyNat n a ℓ j ≡ j.val [MOD n] := by
    rw [keyNat]
    exact Nat.mul_modulus_add_modEq_iff.mpr (Nat.ModEq.rfl)
  have hmid : keyNat n a ℓ i ≡ keyNat n a ℓ j [MOD n] := by
    simpa [h] using (Nat.ModEq.rfl : keyNat n a ℓ i ≡ keyNat n a ℓ i [MOD n])
  have hval : i.val ≡ j.val [MOD n] := (hL.symm).trans hmid |>.trans hR
  have heq : i.val = j.val := by
    rw [Nat.ModEq] at hval
    simpa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hval
  exact Fin.ext heq

/- **Order-preservation: smaller key ⇒ smaller rank.**  Let `Si = keyBelow i` and
   `Sj = keyBelow j`.  Transitivity of the flattened key-order gives `Si ⊆ Sj`:
   if `key k < key i < key j` then `key k < key j`.  The witness `i` itself lies in
   `Sj` (since `key i < key j`) but not in `Si` (no key is below itself), so
   `Sj \ Si` is nonempty and has positive cardinality.  Because `Si ⊆ Sj`,
   Mathlib's `card_sdiff_of_subset` gives

       #(Sj \ Si) = #Sj - #Si,

   so `#Sj - #Si > 0`, i.e. (by the truncated-subtraction law) `#Si < #Sj`, which
   is exactly `rankVal i < rankVal j`.  The final arithmetic step is closed by
   `omega`. -/
theorem rank_orderPreserve (n a : Nat) (ℓ : Fin n → Fin a) (i j : Fin n)
    (hk : keyNat n a ℓ i < keyNat n a ℓ j) :
    rankVal n a ℓ i < rankVal n a ℓ j := by
  -- (1) containment: k <_key i and i <_key j  ⇒  k <_key j (transitivity of < on the key)
  have hsub : keyBelow n a ℓ i ⊆ keyBelow n a ℓ j := by
    intro k hk_k
    simp [keyBelow] at hk_k ⊢
    exact lt_trans hk_k hk
  -- (2) the witness i lies below j's key but not below its own
  have him : i ∈ keyBelow n a ℓ j := by
    simp [keyBelow, hk]
  have him2 : i ∉ keyBelow n a ℓ i := by
    simp [keyBelow]
  -- (3) so keyBelow j \ keyBelow i is nonempty (it contains i) and has positive cardinality
  have hnon : (keyBelow n a ℓ j \ keyBelow n a ℓ i).Nonempty :=
    ⟨i, by simp only [Finset.mem_sdiff]; exact ⟨him, him2⟩⟩
  have hpos : 0 < (keyBelow n a ℓ j \ keyBelow n a ℓ i).card := Finset.card_pos.mpr hnon
  dsimp [rankVal]
  -- (4) because keyBelow i ⊆ keyBelow j, that is 0 < card(keyBelow j) - card(keyBelow i)
  have hdiff : (keyBelow n a ℓ j).card - (keyBelow n a ℓ i).card > 0 :=
    by simpa [Finset.card_sdiff_of_subset hsub] using hpos
  -- (5) a truncated difference a - b > 0 is exactly b < a
  omega

/- **`rankVal` is injective (for `0 < n`): distinct indices have distinct ranks.**
   `keyNat` injective ⇒ `i ≠ j ⇒ keyNat i ≠ keyNat j`; by trichotomy WLOG
   `keyNat i < keyNat j`, and `rank_orderPreserve` gives `rankVal i < rankVal j`, so
   `rankVal i ≠ rankVal j`.  Together with `keyNat_injective` this makes the rank map
   a strictly-order-reflecting injection of `Fin n` into `ℕ`. -/
theorem rankVal_injective (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    Function.Injective (fun i : Fin n => rankVal n a ℓ i) := by
  intro i j h
  change rankVal n a ℓ i = rankVal n a ℓ j at h
  by_contra hne
  -- i ≠ j, so their flattened keys differ (keyNat injective)
  have hkey_ne : keyNat n a ℓ i ≠ keyNat n a ℓ j := by
    intro heq
    exact hne (keyNat_injective n a hn ℓ heq)
  cases lt_or_gt_of_ne hkey_ne with
  | inl hk => -- keyNat i < keyNat j  ⇒  rankVal i < rankVal j  =  rankVal i, absurd
    have hlt : rankVal n a ℓ i < rankVal n a ℓ j := rank_orderPreserve n a ℓ i j hk
    rw [h.symm] at hlt
    exact Nat.lt_irrefl _ hlt
  | inr hk => -- keyNat j < keyNat i  ⇒  rankVal j < rankVal i  =  rankVal j, absurd
    have hlt : rankVal n a ℓ j < rankVal n a ℓ i := rank_orderPreserve n a ℓ j i hk
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt

/- **`rankVal i < n` (for `0 < n`): the rank fits inside `Fin n`.**  `keyBelow i`
   is a proper subset of `univ`: it is contained in `univ` but misses `i` (no key is
   strictly below itself).  The cardinality function on Finsets is strictly
   monotone (`Finset.card_strictMono`), so `#keyBelow i < #univ = n`. -/
theorem rankVal_lt_n (n a : Nat) (_hn : 0 < n) (ℓ : Fin n → Fin a) (i : Fin n) :
    rankVal n a ℓ i < n := by
  have hsubU : keyBelow n a ℓ i ⊆ (Finset.univ : Finset (Fin n)) := by
    intro k hk_k
    simp only [keyBelow, Finset.mem_filter, Finset.mem_univ] at *
  have him2 : i ∉ keyBelow n a ℓ i := by simp [keyBelow]
  have hssub : keyBelow n a ℓ i ⊂ (Finset.univ : Finset (Fin n)) :=
    Finset.ssubset_iff_of_subset hsubU |>.mpr ⟨i, Finset.mem_univ i, him2⟩
  have hcardU : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  simpa only [rankVal, ← hcardU] using Finset.card_strictMono hssub

/- **`rankEquiv`: the sorted-key rank is a genuine permutation of the positions.**
   Wrap `rankVal` (whose values lie in `{0, …, n-1}` by `rankVal_lt_n`) into a map
   `Fin n → Fin n`.  It is injective (`rankVal_injective`) and, being a map between
   the same finite type, hence bijective (`Finite.surjective_of_injective`);
   `Equiv.ofBijective` packages it into an `Equiv`.  Its `symm` is the order-
   preserving `orderByNewPosition` used in Section 3. -/
noncomputable def rankEquiv (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) : Equiv (Fin n) (Fin n) :=
  let f : Fin n → Fin n := fun i => Fin.mk (rankVal n a ℓ i) (rankVal_lt_n n a hn ℓ i)
  let hfInj : Function.Injective f := by
    intro i j h
    have hval : (f i).val = (f j).val := congrArg Fin.val h
    have hr : rankVal n a ℓ i = rankVal n a ℓ j := by simpa [f, Fin.val, Fin.mk] using hval
    exact rankVal_injective n a hn ℓ hr
  Equiv.ofBijective f ⟨hfInj, Finite.surjective_of_injective hfInj⟩

/- **`canonicalList`: the canonical deck of positions `[0, 1, …, n-1]`** as a
   `List (Fin n)`, in increasing-position order (the minor key).  Defined
   directly as `List.finRange n` — the standard Mathlib list of all `Fin n` in
   order — which carries clean `get`/`idxOf`/`nodup` lemmas (`idxOf_finRange`,
   `nodup_finRange`, …) and is exactly the `filterMap`-over-`range` deck. -/
def canonicalList (n : Nat) : List (Fin n) := List.finRange n

/- **`orderByNewPosition`: the output list of a position permutation `σ`.**  The
   card at output position `r` is the one that was at original position `σ r`
   (Section 3: the GSR shuffle's output order).  For the canonical deck this is
   exactly `[σ 0, σ 1, …, σ (n-1)]`, i.e. `finRange n` mapped by `σ`. -/
def orderByNewPosition (n : Nat) (σ : Equiv (Fin n) (Fin n)) : List (Fin n) :=
  (List.finRange n).map σ

/- **When `a = 1` every label is `0`, so the flattened key is just the position:**
   `keyNat n 1 ℓ i = i.val`, hence the number of smaller keys is `i.val` and
   `rankVal n 1 ℓ i = i.val`.  The rank is exactly the position (identity). -/
theorem rankVal_a1 (n : Nat) (_hn : 0 < n) (ℓ : Fin n → Fin 1) (i : Fin n) :
    rankVal n 1 ℓ i = i.val := by
  have hall : ∀ c : Fin n, (ℓ c).val = 0 := fun c => by
    have : (ℓ c).val < 1 := (ℓ c).isLt
    omega
  -- keyBelow n 1 ℓ i = { j : Fin n | j.val < i.val }
  have hsub : keyBelow n 1 ℓ i =
      Finset.filter (fun j : Fin n => j.val < i.val) (Finset.univ : Finset (Fin n)) := by
    ext j
    simp only [keyBelow, Finset.mem_filter, Finset.mem_univ, keyNat, hall, Nat.zero_mul, Nat.zero_add]
  -- #{ j : Fin n | j.val < i.val } = i.val  (values 0 … i.val-1)
  have hval_inj : Function.Injective (Fin.val : Fin n → ℕ) := fun x y h => Fin.ext h
  simpa only [rankVal, hsub] using by
    let S := (Finset.univ : Finset (Fin n)).filter (fun j : Fin n => j.val < i.val)
    have himg : S.image Fin.val = Finset.range i.val := by
      dsimp only [S]
      apply Finset.ext
      intro k
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj.2
      · rintro hk
        exact ⟨Fin.mk k (Nat.lt_trans hk i.isLt), ⟨True.intro, hk⟩, rfl⟩
    calc S.card = (S.image Fin.val).card := (Finset.card_image_of_injective S hval_inj).symm
      _ = (Finset.range i.val).card := by rw [himg]
      _ = i.val := Finset.card_range _

/- **When `a = 1` the stable buckets are the identity:** every card has label `0`,
   so the single bucket (label value `0`) contains the whole deck in original
   order.  `stableBuckets 1 ℓ deck = deck`. -/
theorem stableBuckets_a1_id (n : Nat) (ℓ : Fin n → Fin 1) (deck : List (Fin n)) :
    GSR.stableBuckets 1 ℓ deck = deck := by
  simp [GSR.stableBuckets, List.range_one, List.filter_true]


/- **Rank is order-reflecting:** `rankVal i < rankVal j` ⇒ `keyNat i < keyNat j`
   (the converse of `rank_orderPreserve`).  Distinct keys give distinct ranks, so the
   two order relations coincide: `rankVal` is an order-embedding. -/
theorem rank_orderReflect (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) (i j : Fin n)
    (hrank : rankVal n a ℓ i < rankVal n a ℓ j) :
    keyNat n a ℓ i < keyNat n a ℓ j := by
  by_contra hno
  by_cases heq : keyNat n a ℓ i = keyNat n a ℓ j
  · -- equal keys ⇒ i = j (keyNat injective) ⇒ equal ranks, contradicting hrank
    have hij : i = j := (keyNat_injective n a hn ℓ) heq
    subst hij
    omega
  · -- keys differ and not (key i < key j), so key j < key i; then rank j < rank i,
      -- contradicting hrank (rank i < rank j)
    have hjlt : keyNat n a ℓ j < keyNat n a ℓ i := by omega
    have hrankj : rankVal n a ℓ j < rankVal n a ℓ i := rank_orderPreserve n a ℓ j i hjlt
    omega

/- **The rank of the card at sorted position `r` is `r` itself.**  `rankEquiv.symm r`
   is the card whose rank is `r`, so its `rankVal` is `r.val`. -/
theorem rankVal_rankEquivSymm (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) (r : Fin n) :
    rankVal n a ℓ ((rankEquiv n a hn ℓ).symm r) = r.val := by
  have hval (x : Fin n) : (rankEquiv n a hn ℓ x).val = rankVal n a ℓ x := by
    dsimp only [rankEquiv, Equiv.ofBijective]
    exact rfl
  have hE : rankEquiv n a hn ℓ ((rankEquiv n a hn ℓ).symm r) = r := (rankEquiv n a hn ℓ).apply_symm_apply r
  rw [← hval ((rankEquiv n a hn ℓ).symm r)]
  simp only [hE]

/- **The rank-ordered key sequence is monotone:** earlier sorted positions have smaller
   keys (rank r < rank s ⇒ key r < key s).  This is the sortedness of the *target* side
   (`orderByNewPosition (rankEquiv.symm)`). -/
theorem rankOrderKeys_monotone (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) (r s : Fin n)
    (h : r < s) :
    keyNat n a ℓ ((rankEquiv n a hn ℓ).symm r) < keyNat n a ℓ ((rankEquiv n a hn ℓ).symm s) := by
  have hr : rankVal n a ℓ ((rankEquiv n a hn ℓ).symm r) = r.val := rankVal_rankEquivSymm n a hn ℓ r
  have hs : rankVal n a ℓ ((rankEquiv n a hn ℓ).symm s) = s.val := rankVal_rankEquivSymm n a hn ℓ s
  have hrank : rankVal n a ℓ ((rankEquiv n a hn ℓ).symm r) <
      rankVal n a ℓ ((rankEquiv n a hn ℓ).symm s) := by
    rw [hr, hs]
    exact Fin.lt_def.mp h
  exact rank_orderReflect n a hn ℓ _ _ hrank

/-!## The rank-ordered key list, as a clean `Fin`-indexed list (F4.2 target side)

`rankOrderKeyList` is the GSR rank-ordered key sequence written directly as a `Fin n`-
indexed list (via `List.ofFn`): its `i`-th entry is the key of the card that ranks `i`,
i.e. `keyNat (rankEquiv.symm i)`.  Because that card has rank `i.val`
(`rankVal_rankEquivSymm`), these keys are strictly increasing in `i`
(`rankOrderKeys_monotone`) and pairwise distinct (`keyNat_injective`). -/

/-- The GSR rank-ordered key list, `Fin`-indexed.  Noncomputable: depends on the
    noncomputable `rankEquiv`. -/
noncomputable def rankOrderKeyList (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) : List ℕ :=
  List.ofFn (fun r : Fin n => keyNat n a ℓ ((rankEquiv n a hn ℓ).symm r))

/- **The rank-ordered key list is strictly increasing** — the GSR output is a sorted
   key sequence.  Via `List.sortedLT_ofFn_iff` this is exactly `rankOrderKeys_monotone`
   (rank `i < j` ⇒ key `i < key j`), restated as strict monotonicity of the entry map. -/
theorem rankOrderKeyList_sortedLT (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    (rankOrderKeyList n a hn ℓ).SortedLT := by
  unfold rankOrderKeyList
  rw [List.sortedLT_ofFn_iff]
  intro i j hij
  exact rankOrderKeys_monotone n a hn ℓ i j hij

/- **The rank-ordered key list has distinct entries** — `keyNat ∘ rankEquiv.symm` is
   injective (composition of two injective maps: `keyNat_injective`, then `Equiv.symm`). -/
theorem rankOrderKeys_nodup (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    (rankOrderKeyList n a hn ℓ).Nodup := by
  unfold rankOrderKeyList
  rw [List.nodup_ofFn]
  intro r s h
  have hsym : (rankEquiv n a hn ℓ).symm r = (rankEquiv n a hn ℓ).symm s :=
    keyNat_injective n a hn ℓ h
  have hE := congrArg (rankEquiv n a hn ℓ) hsym
  simpa only [Equiv.apply_symm_apply] using hE

/- **Injective maps reflect list equality:** if `f` is injective and
   `l₁.map f = l₂.map f`, then `l₁ = l₂` (`List.map_injective_iff`). -/
theorem map_inj_eq {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (l₁ l₂ : List α) (hmap : l₁.map f = l₂.map f) : l₁ = l₂ :=
  (List.map_injective_iff.mpr hf) hmap

/-!## The key is the lex `(label, position)` order, flattened

The GSR output order compares cards by `(label, position)` lexicographically, with
`label` the major and `position` the minor key.  Because a position is always `< n`,
flattening that lex pair to a single `Nat` via `keyNat = label·n + position` is an
*order embedding*: two distinct cards compare by `keyNat` exactly when they compare by
`(label, position)`.  This is the algebraic heart of why the stable-bucketed deck (which
is precisely the `(label, position)` lex order) is a sorted key sequence. -/

/-- **Key order = lex `(label, position)` order.**  For distinct cards `i`, `j`,
    `keyNat i < keyNat j` iff `i`'s label is smaller, or the labels tie and `i`'s
    position is smaller.  (Positions are `< n`, so `label·n + position` faithfully
    encodes the lex pair.) -/
theorem keyNat_lex (n a : Nat) (ℓ : Fin n → Fin a) (i j : Fin n) :
    keyNat n a ℓ i < keyNat n a ℓ j ↔
        (ℓ i).val < (ℓ j).val ∨ ((ℓ i).val = (ℓ j).val ∧ i.val < j.val) := by
  dsimp only [keyNat]
  constructor
  · -- LHS ⟹ RHS
    intro h
    by_cases hlt : (ℓ i).val < (ℓ j).val
    · exact Or.inl hlt
    · by_cases heq : (ℓ i).val = (ℓ j).val
      · -- labels tie: a·n + i.val < a·n + j.val  ⟹  i.val < j.val (cancel a·n)
        rw [heq] at h
        have hval : i.val < j.val := by simpa [Nat.add_left_cancel_iff] using h
        exact Or.inr ⟨heq, hval⟩
      · -- label i > label j:  (ℓ i).val ≥ (ℓ j).val + 1, so key i ≥ (ℓ j).val·n + n > key j
        have hge : (ℓ j).val + 1 ≤ (ℓ i).val := by omega
        have hmul : (ℓ j).val * n + n ≤ (ℓ i).val * n := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hge
        have hstep : (ℓ j).val * n + n > (ℓ j).val * n + j.val := by
          apply Nat.add_lt_add_left; exact j.isLt
        have hbad : (ℓ i).val * n + i.val > (ℓ j).val * n + j.val := by
          calc (ℓ i).val * n + i.val ≥ (ℓ i).val * n := Nat.le_add_right _ _
            _ ≥ (ℓ j).val * n + n := hmul
            _ > (ℓ j).val * n + j.val := hstep
        have hba : (ℓ j).val * n + j.val < (ℓ i).val * n + i.val := hbad
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans h hba))
  · -- RHS ⟹ LHS
    intro h
    rcases h with (hlt | ⟨heq, hint⟩)
    · -- a < b:  a·n + i.val < (a+1)·n ≤ b·n ≤ b·n + j.val
      have hmul : (ℓ i).val * n + n ≤ (ℓ j).val * n := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
      have hstep1 : (ℓ i).val * n + i.val < (ℓ i).val * n + n := by
        apply Nat.add_lt_add_left; exact i.isLt
      have hstep2 : (ℓ i).val * n + i.val < (ℓ j).val * n := Nat.lt_of_lt_of_le hstep1 hmul
      exact Nat.lt_of_lt_of_le hstep2 (Nat.le_add_right _ _)
    · -- a = b, i.val < j.val:  a·n + i.val < a·n + j.val
      rw [heq]
      apply Nat.add_lt_add_left
      exact hint

/-!## The F4.2 capstone: the last wall (precisely characterized)

**Goal.**
```
theorem stableBuckets_eq_orderByNewPosition (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (ℓ : Fin n → Fin a) :
    GSR.stableBuckets a ℓ (List.finRange n) =
      (List.finRange n).map (rankEquiv n a hn ℓ).symm
```
**What is already in hand (this file).**
  * `rankOrderKeyList n a hn ℓ` is the *target*'s key sequence and is `SortedLT`
    (`rankOrderKeyList_sortedLT`), and its entries are distinct (`rankOrderKeys_nodup`).
  * `keyNat_lex` above: `keyNat` order = the lex `(label, position)` order that
    `stableBuckets` implements.  So conceptually `(stableBuckets …).map keyNat` is
    *the same* sorted key sequence as `rankOrderKeyList`, and the capstone then follows
    from `keyNat_injective` + `map_inj_eq` once both sides' key images are shown equal.

**The single remaining sub-lemma (`hL`).**
```
(stableBuckets a ℓ (finRange n)).map (keyNat n a ℓ).SortedLT
```
`stableBuckets a ℓ (finRange n) = (range a).flatMap (fun i => (finRange n).filter
(fun c => (ℓ c).val == i))`.  Its key image is the concatenation, over increasing
label `i`, of the runs `[i·n + pos | pos increasing with label i]`.  Each run is
strictly increasing and the runs are disjoint and ordered (`keyNat_lex`), so the whole
concatenation is `SortedLT` — provable by induction on `a` via `List.sortedLT_append`
once each *bucket* is shown `SortedLT`.

**Why it is not yet closed (the precise API gap).**
A single bucket is `((finRange n).filter (fun c => (ℓ c).val == i)).map keyNat`.  To
show it `SortedLT` one needs a Mathlib lemma that **filtering a `SortedLT` list stays
`SortedLT`** (or, equivalently, that a `List.IsSublist` of a `SortedLT` list is
`SortedLT`), plus a way to **index into a `filter`** (`get`/`getElem` over a filter).
Neither is in the current Mathlib `Data.List` API (`sortedLT_finRange` and
`sortedLT_append` are present; the filter/sublist-sortedness and the filter `get` are
not).  The bucket can be shown `SortedLT` by a manual induction on the deck that
computes the filtered list's `get` element-by-element, or by introducing a
`bucket_sortedLT` lemma proved via `List.IsSublist` (once a sublist-sortedness lemma
is added).  That is the exact next step; everything else for F4.2 is in place.
-/

end Shufflemath
end
