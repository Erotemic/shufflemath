module

public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Basic
public import Shufflemath.GSR
public import Shufflemath.GSRF42

@[expose] public section

namespace Shufflemath

-- ---- hL sub-lemma: filter-then-map-by-per-label-monotone stays SortedLT
theorem bucketKeys_sortedLT (n a : Nat) (_hn : 0 < n) (ℓ : Fin n → Fin a) (i : Nat)
    (l : List (Fin n)) (hl : l.SortedLT) :
    ((l.filter (fun c => (ℓ c).val == i)).map (keyNat n a ℓ)).SortedLT := by
  induction l with
  | nil => exact List.sortedLT_nil
  | cons x r ih =>
      have hxr : ∀ y ∈ r, x < y := (List.sortedLT_cons.mp hl).1
      have hIh : ((r.filter (fun c => (ℓ c).val == i)).map (keyNat n a ℓ)).SortedLT :=
        ih (List.sortedLT_cons.mp hl).2
      by_cases hb : ((ℓ x).val == i) = true
      · have hfilter : (x :: r).filter (fun c => (ℓ c).val == i) =
              x :: r.filter (fun c => (ℓ c).val == i) := by simp [List.filter, hb]
        rw [hfilter, List.map]
        apply List.sortedLT_cons.mpr
        constructor
        · intro y hy
          obtain ⟨z, hz, rfl⟩ := (List.mem_map.1 hy)
          have hzr : z ∈ r := List.mem_of_mem_filter hz
          have hzx : x.val < z.val := hxr z hzr
          have hxlab : (ℓ x).val = i := by simpa using hb
          have hzlab : (ℓ z).val = i := by simpa using List.of_mem_filter hz
          rw [keyNat, keyNat, hxlab, hzlab]
          exact Nat.add_lt_add_left hzx (i * n)
        · exact hIh
      · have hfilter : (x :: r).filter (fun c => (ℓ c).val == i) =
              r.filter (fun c => (ℓ c).val == i) := by simp [List.filter, hb]
        rw [hfilter]
        exact hIh

-- ---- the stable-buckets key image is SortedLT (induct on the bucket counter)
private theorem stableBuckets_partialSortedLT (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a)
    (m : Nat) :
    (((List.range m).flatMap (fun j : ℕ =>
      (List.finRange n).filter (fun z : Fin n => (ℓ z).val == j))).map (keyNat n a ℓ)).SortedLT := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.flatMap_nil, List.map_nil]
      exact List.sortedLT_nil
  | succ m im =>
      let cb := (List.finRange n).filter (fun z : Fin n => (ℓ z).val == m)
      have hdecomp :
          (((List.range (m+1)).flatMap (fun j : ℕ =>
            (List.finRange n).filter (fun z : Fin n => (ℓ z).val == j))).map (keyNat n a ℓ)) =
            (((List.range m).flatMap (fun j : ℕ =>
              (List.finRange n).filter (fun z : Fin n => (ℓ z).val == j))).map (keyNat n a ℓ)) ++
            cb.map (keyNat n a ℓ) := by
        simp only [List.range_succ, List.flatMap_append, List.map_append, cb]
        · -- [m].flatMap (fun j => bucket j).map keyNat = bucket m.map keyNat
          simp [List.flatMap]
      rw [hdecomp]
      apply List.sortedLT_append.mpr
      constructor
      · exact im
      · constructor
        · exact bucketKeys_sortedLT n a hn ℓ m (List.finRange n) (List.sortedLT_finRange _)
        · -- cross-gap: every prefix key < every suffix key
          intro x hx y hy
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
          obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
          have hcl : (ℓ c).val < m := by
            obtain ⟨j, hj, hjc⟩ := List.mem_flatMap.1 hc
            have hjc2 : (ℓ c).val = j := by simpa using List.of_mem_filter hjc
            simpa [hjc2, List.mem_range] using hj
          have hdl : (ℓ d).val = m := by simpa using List.of_mem_filter hd
          rw [keyNat, keyNat, hdl]
          have hinc : (ℓ c).val * n + c.val < (ℓ c).val * n + n :=
            Nat.add_lt_add_left c.isLt _
          have hstep : (ℓ c).val * n + n ≤ m * n := by
            simpa [Nat.succ_mul] using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hcl)
          exact Nat.lt_of_lt_of_le hinc (Nat.le_trans hstep (Nat.le_add_right _ _))

-- Public wrapper: the stable-buckets deck (a labels) has a SortedLT key image.
theorem stableBuckets_keySortedLT (n a : Nat) (_ha : 0 < a) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    ((GSR.stableBuckets a ℓ (List.finRange n)).map (keyNat n a ℓ)).SortedLT := by
  simpa only [GSR.stableBuckets] using stableBuckets_partialSortedLT n a hn ℓ a

-- ---- R.map keyNat = rankOrderKeyList -------------------------------------
theorem rankOrderKeyList_eq_Rmap (n a : Nat) (hn : 0 < n) (ℓ : Fin n → Fin a) :
    ((List.finRange n).map (rankEquiv n a hn ℓ).symm).map (keyNat n a ℓ) =
      (rankOrderKeyList n a hn ℓ) := by
  simp [rankOrderKeyList, List.map_map, List.ofFn_eq_map]

-- ---- THE F4.2 SORTING IDENTITY -----------------------------------------
-- The keys emitted by the stable-bucket ordering are exactly the keys in rank
-- order.  Since `rankEquiv` is the *unique* ordering by (label, position) =
-- (key, position), this is precisely "stableBuckets = order by new position"
-- at the key level:  both orderings agree on every key.
--
-- Proof:  both key-images are SortedLT (stableBuckets via the bucket-induction,
-- `rankOrderKeyList` by construction) and they contain exactly the same keys
-- (both decks contain every card, and `keyNat` is a fixed bijection of cards
-- to keys);  two SortedLT lists with the same membership are equal.

-- Every card of `Fin n` sits in `finRange n` (it is the full enumeration).
private theorem card_in_finRange {n : ℕ} (c : Fin n) :
    c ∈ (List.finRange n : List (Fin n)) := by
  simp only [← List.ofFn_id, List.mem_ofFn', Set.mem_range]
  exact ⟨c, rfl⟩

theorem stableBuckets_keys_eq_rankOrderKeyList (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (ℓ : Fin n → Fin a) :
    (GSR.stableBuckets a ℓ (List.finRange n)).map (keyNat n a ℓ) =
      (rankOrderKeyList n a hn ℓ) := by
  let L := GSR.stableBuckets a ℓ (List.finRange n)
  let R := (List.finRange n).map (rankEquiv n a hn ℓ).symm
  have hL : (L.map (keyNat n a ℓ)).SortedLT := stableBuckets_keySortedLT n a ha hn ℓ
  have hR : (R.map (keyNat n a ℓ)).SortedLT := by
    simpa only [R, rankOrderKeyList_eq_Rmap] using rankOrderKeyList_sortedLT n a hn ℓ
  -- same membership on the key image
  have hmem : ∀ k, k ∈ L.map (keyNat n a ℓ) ↔ k ∈ R.map (keyNat n a ℓ) := by
    intro k
    constructor
    -- k ∈ L.map keyNat  ⇒  k = keyNat c for some card c  ⇒  k ∈ R.map keyNat
    --                  (witness the same card c;  c lies in R at rank rankEquiv c)
    · intro hk
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hk
      refine List.mem_map.mpr ⟨c, ?_, ?_⟩
      · refine List.mem_map.mpr ⟨(rankEquiv n a hn ℓ) c, ?_, ?_⟩
        · exact (card_in_finRange ((rankEquiv n a hn ℓ) c))
        · exact (rankEquiv n a hn ℓ).symm_apply_apply c
      · rfl
    -- k ∈ R.map keyNat  ⇒  k = keyNat r for some card r  ⇒  r ∈ L  ⇒  k ∈ L.map keyNat
    · intro hk
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hk
      refine List.mem_map.mpr ⟨r, ?_, ?_⟩
      · dsimp only [L]
        exact (GSR.stableBuckets_set a ℓ (List.finRange n) r).mpr (card_in_finRange r)
      · rfl
  have hLR : L.map (keyNat n a ℓ) = R.map (keyNat n a ℓ) :=
    List.SortedLT.eq_of_mem_iff hL hR hmem
  simpa only [R, rankOrderKeyList_eq_Rmap] using hLR

-- ---- THE F4.2 DECK-LEVEL PERMUTATION CAPSTONE ----------------------------
-- The stable-bucketed deck IS the deck re-ordered by new position (rank).
-- This is the final F4.2 capstone:  `stableBuckets a ℓ (finRange n) =
-- (finRange n).map rankEquiv.symm` as a genuine *card-list* equality (not just
-- at the key level).  Proof:  both sides map under the *injective* key `keyNat`
-- to the same key list (stable-bucket key image = `rankOrderKeyList` = the
-- rank-ordered deck's key image), so by `map_inj_eq` the card lists are equal.
theorem stableBuckets_eq_orderByNewPosition (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (ℓ : Fin n → Fin a) :
    GSR.stableBuckets a ℓ (List.finRange n) =
      (List.finRange n).map (rankEquiv n a hn ℓ).symm := by
  -- both sides map under `keyNat` to the same key list
  have hmap :
      (GSR.stableBuckets a ℓ (List.finRange n)).map (keyNat n a ℓ) =
        ((List.finRange n).map (rankEquiv n a hn ℓ).symm).map (keyNat n a ℓ) := by
    rw [stableBuckets_keys_eq_rankOrderKeyList n a ha hn ℓ,
        ← (rankOrderKeyList_eq_Rmap n a hn ℓ)]
  -- `keyNat` is injective, so equal key-images force equal card lists
  exact (map_inj_eq (keyNat n a ℓ) (keyNat_injective n a hn ℓ)
       (GSR.stableBuckets a ℓ (List.finRange n))
       ((List.finRange n).map (rankEquiv n a hn ℓ).symm) hmap)

end Shufflemath
