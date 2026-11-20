module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
public import Shufflemath.GSR

@[expose] public section

namespace Shufflemath

/-!
F4.2 last-wall WIP — the sorted-key rank as a *genuine* finite permutation.
==========================================================================
The "last F4 wall" (Section 3 of `docs/planning/proof-strategies/
2026-11-20-deep-structural-hints-for-qwen.md`): turn `GSR.idealShuffle`'s output
into a real finite permutation of the deck positions and preserve the law.

Root blocker: this Mathlib has **no `DecidableRel` instance for the
lexicographic `<` on a product type** — probed both `Nat × Nat` and
`Fin a × Fin n`, and `Finset.filter` fails on both.  The fix is to **flatten the
lex key to a single `Nat`**:

    keyNat i = (ℓ i).val * n + i.val

whose `<` *is* the lexicographic order on `(ℓ i).val, i.val` (for `i,j < n`,
`keyNat i < keyNat j ↔ (ℓ i).val < (ℓ j).val ∨ (ℓ i).val = (ℓ j).val ∧ i < j`),
and whose `<` is decidable.  Everything below is built on that.

Progress:
  * `keyNat`, `keyBelow`, `rankVal` — defs (build clean).
  * **`keyNat_injective`** — two equal flattened keys are congruent mod `n`
    (`Nat.mul_modulus_add_modEq_iff`), which forces equal indices (both `< n`,
    via `Nat.mod_eq_of_lt`).
  * **`rank_orderPreserve`** — smaller key ⇒ smaller rank, by the proper-
    subset cardinality law `card_sdiff_of_subset` (the witness `i` sits in
    `keyBelow j \ keyBelow i`), with the final truncated-subtraction step by `omega`.
Then the next layer: `rankEquiv` (`Equiv.ofBijective` +
`Finite.surjective_of_injective`), then `stableBuckets a ℓ (List.range n) =
orderByNewPosition (rank_ℓ.symm)`, then `ν_{n,a}` as the pushforward of
`GSR.uniformLabels`, then the deck-level law via `CommanderDeckGSR.pileRelabelEquiv`.
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
   `List (Fin n)`, in increasing-position order (the minor key). -/
def canonicalList (n : Nat) : List (Fin n) :=
  (List.range n).filterMap fun k => (if hk : k < n then some (Fin.mk k hk) else none)

/- **`orderByNewPosition`: the output list of a position permutation `σ`.**  The
   card at output position `r` is the one that was at original position `σ r`
   (Section 3: the GSR shuffle's output order).  For the canonical deck this is
   exactly `[σ 0, σ 1, …, σ (n-1)]`. -/
def orderByNewPosition (n : Nat) (σ : Equiv (Fin n) (Fin n)) : List (Fin n) :=
  (canonicalList n).map σ

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

end Shufflemath
end
