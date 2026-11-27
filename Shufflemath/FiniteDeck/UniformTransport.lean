module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.FiniteDeck.BlockPartition
public import Shufflemath.FiniteDeck.UniformExchange
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.FiniteDeck

open Classical

/-!
# G7 arithmetic core — uniform transport between allocation carriers

The G7 changing-capacities arc needs a uniform-law transport theorem across
*different* allocation carriers, and the arithmetic identity that makes it
possible without any ratio of factorials — a **biregular relation**: a
relation with constant outgoing degree and constant incoming degree.  These
are the two generic facts the transfer-allocation kernel is built on:

1. `uniform_transport_of_colsum` — a rectangular stochastic kernel with
   constant column sums transports the uniform law to the uniform law.  No
   symmetry or equal-sized state spaces is assumed.
2. `biregular_count` — the same relation counted once in each direction.  The
   outgoing and incoming degrees of the transfer relation relate the old and
   new allocation space sizes, with no factorials.
-/

/-- A rectangular stochastic kernel with constant column sums transports
uniform to uniform. No symmetry or equal-sized state spaces is assumed. -/
theorem uniform_transport_of_colsum {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [DecidableEq X] [DecidableEq Y]
    (K : FiniteKernel X Y)
    (h : ∀ y, (∑ x : X, Dist.mass (K x) y) =
      (Fintype.card X : Rat) / (Fintype.card Y : Rat)) :
    FiniteKernel.apply (GSR.uniformDist X) K = GSR.uniformDist Y := by
  classical
  ext y
  change Dist.mass (FiniteKernel.apply (GSR.uniformDist X) K) y =
    Dist.mass (GSR.uniformDist Y) y
  rw [FiniteKernel.apply_mass, GSR.mass_uniformDist y]
  have he : (∑ x : X, Dist.mass (GSR.uniformDist X) x * Dist.mass (K x) y) =
    (Fintype.card X : Rat)⁻¹ * ∑ x : X, Dist.mass (K x) y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [GSR.mass_uniformDist]
  rw [he, h]
  have hx : (Fintype.card X : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hy : (Fintype.card Y : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hx, hy]

/-- Counting a biregular relation two ways. Use this instead of factorial
arithmetic to relate the old and new allocation space sizes. -/
theorem biregular_count {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [∀ x y, Decidable (R x y)] (outdeg indeg : Nat)
    (hout : ∀ x, (Finset.univ.filter (R x)).card = outdeg)
    (hin : ∀ y, (Finset.univ.filter (fun x => R x y)).card = indeg) :
    Fintype.card X * outdeg = Fintype.card Y * indeg := by
  classical
  have ha (x : X) : (∑ y : Y, if R x y then (1 : Nat) else 0) = outdeg := by
    rw [← Finset.sum_filter]
    simpa using hout x
  have hb (y : Y) : (∑ x : X, if R x y then (1 : Nat) else 0) = indeg := by
    rw [← Finset.sum_filter]
    simpa using hin y
  calc
    _ = ∑ x : X, ∑ y : Y, if R x y then (1 : Nat) else 0 := by simp [ha]
    _ = ∑ y : Y, ∑ x : X, if R x y then (1 : Nat) else 0 := Finset.sum_comm
    _ = _ := by simp [hb]


/-! ### The transfer kernel — G7 changing-capacities core

Given two distinct piles `i j` of the allocation carrier and a transfer size
`t ≤ n i`, the **transfer** moves an arbitrary `t`-subset `U` of pile `i` —
chosen uniformly — into pile `j`.  The target capacities are
`n' i = n i - t`, `n' j = n j + t`, the rest unchanged, so the total is
preserved.  The row at source `A` is the uniform law over the `t`-subsets of
pile `i` (the **transfer choices**) pushed through the reassignment.  The
different transfer choices give different target allocations, so the
outgoing degree at `A` is the number of transfer choices,
`Nat.choose (n i) t`.
-/

variable {N p : Nat} {n : Fin p → Nat} {i j : Fin p} {t : Nat}

/-- The `i`-th pile of an allocation as a finset of cards. -/
def pileCard (A : Allocation N p n) (i : Fin p) : Finset (Fin N) :=
  Finset.univ.filter (fun x => A.val x = i)

theorem pileCard_card (A : Allocation N p n) (i : Fin p) :
    (pileCard A i).card = n i := A.property i

/-- Two distinct piles of an allocation are disjoint. -/
theorem pileCard_disjoint (A : Allocation N p n) {i j : Fin p} (hij : i ≠ j) :
    Disjoint (pileCard A i) (pileCard A j) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  subst hab
  exact hij (ha.symm.trans hb)

/-- The target capacities after transferring `t` cards from pile `i` to pile `j`:
pile `i` loses `t` cards, pile `j` gains them, the rest are unchanged. -/
def transferCap (n : Fin p → Nat) (i j : Fin p) (t : Nat) : Fin p → Nat :=
  fun k => if k = i then n i - t else if k = j then n j + t else n k

/-- The owner function after transferring the cards of `U` from pile `i` into
pile `j`: cards in `U` move to pile `j`; every other card keeps its pile. -/
def transferOwner (A : Allocation N p n) (U : Finset (Fin N)) (j : Fin p) (x : Fin N) : Fin p :=
  if x ∈ U then j else A.val x

/-- The `t`-subsets of the `i`-th pile of `A`: the transfer choices. -/
def TransferChoices (A : Allocation N p n) (i : Fin p) (t : Nat) : Type :=
  {U : Finset (Fin N) // U ∈ (pileCard A i).powersetCard t}

instance (A : Allocation N p n) (i : Fin p) (t : Nat) : Fintype (TransferChoices A i t) :=
  Fintype.subtype ((pileCard A i).powersetCard t) (fun _ => Iff.rfl)

/-- The number of transfer choices is `Nat.choose (n i) t`. -/
theorem TransferChoices.card (A : Allocation N p n) (i : Fin p) (t : Nat) :
    Fintype.card (TransferChoices A i t) = Nat.choose (n i) t := by
  classical
  have hSub : Fintype.card (TransferChoices A i t) =
      ((pileCard A i).powersetCard t).card := by
    simp only [TransferChoices]
    exact Fintype.card_coe _
  rw [hSub, Finset.card_powersetCard, pileCard_card]

/-- The nonemptiness of the transfer choices when `t` fits in the pile. -/
theorem TransferChoices.nonempty (A : Allocation N p n) (i : Fin p) (t : Nat)
    (ht : t ≤ n i) : Nonempty (TransferChoices A i t) := by
  have hcard : t ≤ (pileCard A i).card := by rw [pileCard_card]; exact ht
  obtain ⟨U, hU⟩ := Finset.powersetCard_nonempty_of_le hcard
  exact ⟨⟨U, hU⟩⟩

/-- The subtype `U ∈ (pileCard A i).powersetCard t` is exactly the property
`U ⊆ pileCard A i ∧ U.card = t`. -/
theorem TransferChoices.subtype_iff {A : Allocation N p n} (i : Fin p) (t : Nat) {U : Finset (Fin N)} :
    (U ∈ (pileCard A i).powersetCard t) ↔ U ⊆ pileCard A i ∧ U.card = t :=
  Finset.mem_powersetCard

/-! ### Capacity preservation

The new pile-`k` card-set at the transfer owner, split into the three
branches.  Each is a small `ext` computation. -/

/-- For `k = i`: the new pile-`i` is the old pile with `U` removed. -/
theorem transferOwner_filter_pile_i (A : Allocation N p n) (i j : Fin p)
    (U : Finset (Fin N)) (hij : i ≠ j) :
    (Finset.univ.filter (fun x => transferOwner A U j x = i)) =
      pileCard A i \ U := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, pileCard,
    Finset.mem_filter]
  simp only [transferOwner]
  by_cases hxU : x ∈ U
  · rw [ite_eq_left hxU]
    tauto
  · rw [ite_eq_right hxU]
    tauto

/-- For `k = j` (distinct from `i`): the new pile-`j` is the old pile with `U` added. -/
theorem transferOwner_filter_pile_j (A : Allocation N p n) (i j : Fin p)
    (U : Finset (Fin N)) (hij : i ≠ j) (hU : U ∈ (pileCard A i).powersetCard t) :
    (Finset.univ.filter (fun x => transferOwner A U j x = j)) =
      pileCard A j ∪ U := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_filter,
    pileCard]
  simp only [transferOwner]
  by_cases hxU : x ∈ U
  · rw [ite_eq_left hxU]
    tauto
  · rw [ite_eq_right hxU]
    tauto

/-- For `k` distinct from both `i` and `j`: the new pile-`k` is unchanged. -/
theorem transferOwner_filter_other (A : Allocation N p n) (i j : Fin p)
    (U : Finset (Fin N)) (hij : i ≠ j) (k : Fin p)
    (hk_ne_i : k ≠ i) (hk_ne_j : k ≠ j) (hU : U ∈ (pileCard A i).powersetCard t) :
    (Finset.univ.filter (fun x => transferOwner A U j x = k)) = pileCard A k := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_filter, pileCard]
  simp only [transferOwner]
  have hUsub : U ⊆ pileCard A i := (Finset.mem_powersetCard.mp hU).1
  by_cases hxU : x ∈ U
  · rw [ite_eq_left hxU]
    have h1 : A.val x = i := by
      have hmem := hUsub hxU
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    rw [h1]
    tauto
  · rw [ite_eq_right hxU]

/-- The transfer preserves every pile's card count. -/
theorem transfer_capacity (A : Allocation N p n) (i j : Fin p) (t : Nat)
    (U : Finset (Fin N)) (hU : U ∈ (pileCard A i).powersetCard t)
    (hij : i ≠ j) (k : Fin p) :
    (Finset.univ.filter (fun x => transferOwner A U j x = k)).card =
      transferCap n i j t k := by
  have hsub : U ⊆ pileCard A i := (Finset.mem_powersetCard.mp hU).1
  have hUcard : U.card = t := (Finset.mem_powersetCard.mp hU).2
  by_cases hk : k = i
  · rw [hk]
    rw [transferOwner_filter_pile_i A i j U hij,
      Finset.card_sdiff_of_subset hsub, pileCard_card, hUcard]
    rw [transferCap, ite_eq_left rfl]
  · by_cases hj : k = j
    · rw [hj]
      have hDisj : Disjoint (pileCard A j) U :=
        (Finset.disjoint_of_subset_left hsub (pileCard_disjoint A hij)).symm
      rw [transferOwner_filter_pile_j A i j U hij hU,
        Finset.card_union_of_disjoint hDisj, pileCard_card, hUcard]
      rw [transferCap, ite_eq_right (fun h => hij (h.symm)), ite_eq_left rfl]
    · have hkNEi : k ≠ i := hk
      have hkNEJ : k ≠ j := hj
      rw [transferOwner_filter_other A i j U hij k hkNEi hkNEJ hU, pileCard_card]
      rw [transferCap, ite_eq_right hk, ite_eq_right hj]


/-! ### The transferred allocation, the transfer map, and the transfer kernel

The `i`-th pile loses the chosen `t` cards `U` (moved into pile `j`), pile `j`
gains them; every other pile is unchanged.  The new allocation is built from
the `transferOwner` owner function, whose per-pile card counts are exactly
`transferCap n i j t` — proved by `transfer_capacity` above.  The outgoing
targets are distinct: different `U` give different targets (the `i`-th pile
of the target is uniquely determined by `U`), so the outgoing degree at `A`
is `choose (n i) t` — the number of transfer choices. -/

/-- The transferred allocation: cards of `U` move from pile `i` to pile `j`;
every other card keeps its pile. -/
noncomputable def transferAllocation (A : Allocation N p n) (U : Finset (Fin N))
    (j : Fin p) (t : Nat) (hU : U ∈ (pileCard A i).powersetCard t) (hij : i ≠ j) :
    Allocation N p (transferCap n i j t) :=
  ⟨transferOwner A U j, fun k => transfer_capacity A i j t U hU hij k⟩

/-- Different transfer choices give different target allocations (fixed `A`):
the `i`-th pile of the target determines `U`. -/
theorem transferAllocation_injective (A : Allocation N p n) (i j : Fin p) (t : Nat)
    (hij : i ≠ j) :
    Function.Injective (fun U : TransferChoices A i t =>
      transferAllocation A U.1 j t U.2 hij) := by
  rintro ⟨U₁, hU₁⟩ ⟨U₂, hU₂⟩ h
  have hval : (transferAllocation A U₁ j t hU₁ hij).val =
      (transferAllocation A U₂ j t hU₂ hij).val := congrArg Subtype.val h
  have hOwner : transferOwner A U₁ j = transferOwner A U₂ j := by
    simpa only [transferAllocation] using hval
  have hU₁sub : U₁ ⊆ pileCard A i := (Finset.mem_powersetCard.mp hU₁).1
  have hU₂sub : U₂ ⊆ pileCard A i := (Finset.mem_powersetCard.mp hU₂).1
  have hval_eq (x : Fin N) : transferOwner A U₁ j x = transferOwner A U₂ j x :=
    congrFun hOwner x
  have hEq : U₁ = U₂ := by
    ext x
    constructor
    · intro hx
      have hx₁ : transferOwner A U₁ j x = j := by
        simp only [transferOwner]
        rw [if_pos hx]
      have hx₂ : transferOwner A U₂ j x = j := hval_eq x ▸ hx₁
      by_cases hxU₂ : x ∈ U₂
      · exact hxU₂
      · exfalso
        have htr : transferOwner A U₂ j x = A.val x := by
          simp only [transferOwner]
          rw [if_neg hxU₂]
        rw [htr] at hx₂
        have hxi : A.val x = i := by
          have hmem := hU₁sub hx
          simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          exact hmem
        rw [hxi] at hx₂
        exact hij hx₂
    · intro hx
      have hx₂ : transferOwner A U₂ j x = j := by
        simp only [transferOwner]
        rw [if_pos hx]
      have hx₁ : transferOwner A U₁ j x = j := hval_eq x ▸ hx₂
      by_cases hxU₁ : x ∈ U₁
      · exact hxU₁
      · exfalso
        have htr : transferOwner A U₁ j x = A.val x := by
          simp only [transferOwner]
          rw [if_neg hxU₁]
        rw [htr] at hx₁
        have hxi : A.val x = i := by
          have hmem := hU₂sub hx
          simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          exact hmem
        rw [hxi] at hx₁
        exact hij hx₁
  exact Subtype.ext hEq

/-- The transfer kernel: move `t` cards chosen uniformly from pile `i` into
pile `j`.  The row at `A` is the uniform law over the transfer choices
pushed through the transfer. -/
noncomputable def transferKernel (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (ht : t ≤ n i) :
    FiniteKernel (Allocation N p n) (Allocation N p (transferCap n i j t)) :=
  fun A => letI := TransferChoices.nonempty A i t ht
    (GSR.uniformDist (TransferChoices A i t)).map
      (fun U => transferAllocation A U.1 j t U.2 hij)

/-- With the kernel fixed, the row mass at a target `B`: at most one transfer
choice maps to `B` (injectivity), so the mass is `1 / card (TransferChoices A i t)`
when `B` is reachable and `0` otherwise. -/
theorem transferKernel_mass (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (ht : t ≤ n i)
    (A : Allocation N p n) (B : Allocation N p (transferCap n i j t)) :
    Dist.mass (transferKernel i j t hij ht A) B =
      if ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B
      then (Fintype.card (TransferChoices A i t) : Rat)⁻¹ else 0 := by
  classical
  haveI := TransferChoices.nonempty A i t ht
  rw [transferKernel]
  rw [GSR.map_injective_uniform_mass
    (fun U : TransferChoices A i t => transferAllocation A U.1 j t U.2 hij)
    (transferAllocation_injective A i j t hij) B]


/-- The reverse owner function: cards in `S` (returned to pile `i` from `B`'s
    pile `j`) go to pile `i`; pile `B i` cards stay in pile `i`; pile `B j`
    cards not in `S` stay in pile `j`; other cards keep their pile. -/
def revOwner (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N)) (x : Fin N) : Fin p :=
  if x ∈ S then i
  else if x ∈ pileCard B i then i
  else if x ∈ pileCard B j then j
  else B.val x

theorem revOwner_filter_pile_i (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hij : i ≠ j) :
    Finset.univ.filter (fun x => revOwner B S x = i) = S ∪ pileCard B i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  simp only [revOwner]
  split_ifs with hxS hxi hjb
  · simp [hxS]
  · simp [hxi]
  · have hRs : ¬ (x ∈ S ∨ x ∈ pileCard B i) := by simp [hxS, hxi]
    have hLi : ¬ (j = i) := fun h => hij h.symm
    constructor
    · intro h
      exact (hLi h).elim
    · intro h
      exact (hRs h).elim
  · simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hxS]

theorem revOwner_filter_pile_j (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hij : i ≠ j) :
    Finset.univ.filter (fun x => revOwner B S x = j) = pileCard B j \ S := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  simp only [revOwner]
  split_ifs with hxS hxi hjb
  · simp [hxS, hij]
  · have hNe : x ∉ pileCard B j := (Finset.disjoint_left.mp (pileCard_disjoint B hij)) hxi
    simp [hxS, hNe, hij]
  · simp [hjb, hxS]
  · simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hxS, hjb]

theorem revOwner_filter_other (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hSi : S ⊆ pileCard B j) (hij : i ≠ j) (k : Fin p) (hkNi : k ≠ i) (hkNj : k ≠ j) :
    Finset.univ.filter (fun x => revOwner B S x = k) = pileCard B k := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, pileCard, Finset.mem_filter]
  simp only [revOwner]
  split_ifs with hxS hxi hjb
  · have hbij : B.val x = j := by
      have hmem := hSi hxS
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    refine ⟨fun h => (hkNi h.symm).elim, fun h => (hkNj (h.symm.trans hbij)).elim⟩
  · have hbij : B.val x = i := by
      have hmem := hxi
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    simp [hkNi, hbij]
  · have hbij : B.val x = j := by
      have hmem := hjb
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    simp [hkNj, hbij]
  · rfl



noncomputable def revAllocation (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hSi : S ⊆ pileCard B j) (hcard : S.card = t) (ht : t ≤ n i) (hij : i ≠ j) :
    Allocation N p n := by
  refine ⟨revOwner B S, fun k => ?_⟩
  by_cases hki : k = i
  · rw [hki]
    rw [revOwner_filter_pile_i B S hij]
    have hdisj : Disjoint S (pileCard B i) :=
      Finset.disjoint_of_subset_left hSi (pileCard_disjoint B hij).symm
    have hcap : (pileCard B i).card = n i - t := by
      rw [pileCard_card B i, transferCap, ite_eq_left rfl]
    rw [Finset.card_union_of_disjoint hdisj, hcard, hcap]
    omega
  · by_cases hkj : k = j
    · rw [hkj]
      rw [revOwner_filter_pile_j B S hij, Finset.card_sdiff_of_subset hSi]
      have hcap : (pileCard B j).card = n j + t := by
        rw [pileCard_card B j, transferCap]
        split_ifs with hji hjj <;> simp_all
      rw [hcap, hcard]
      omega
    · have hki' : k ≠ i := hki
      have hkj' : k ≠ j := hkj
      rw [revOwner_filter_other B S hSi hij k hki' hkj']
      rw [pileCard_card B k, transferCap, ite_eq_right hki', ite_eq_right hkj']



theorem pileCard_revAllocation_i (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hSi : S ⊆ pileCard B j) (hcard : S.card = t) (ht : t ≤ n i) (hij : i ≠ j) :
    pileCard (revAllocation B S hSi hcard ht hij) i = S ∪ pileCard B i := by
  have : (revAllocation B S hSi hcard ht hij).val = revOwner B S := rfl
  simp only [pileCard]
  rw [this]
  exact revOwner_filter_pile_i B S hij

theorem pileCard_revAllocation_j (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hSi : S ⊆ pileCard B j) (hcard : S.card = t) (ht : t ≤ n i) (hij : i ≠ j) :
    pileCard (revAllocation B S hSi hcard ht hij) j = pileCard B j \ S := by
  have : (revAllocation B S hSi hcard ht hij).val = revOwner B S := rfl
  simp only [pileCard]
  rw [this]
  exact revOwner_filter_pile_j B S hij

theorem pileCard_revAllocation_other (B : Allocation N p (transferCap n i j t)) (S : Finset (Fin N))
    (hSi : S ⊆ pileCard B j) (hcard : S.card = t) (ht : t ≤ n i) (hij : i ≠ j) (k : Fin p)
    (hkNi : k ≠ i) (hkNj : k ≠ j) :
    pileCard (revAllocation B S hSi hcard ht hij) k = pileCard B k := by
  have : (revAllocation B S hSi hcard ht hij).val = revOwner B S := rfl
  simp only [pileCard]
  rw [this]
  exact revOwner_filter_other B S hSi hij k hkNi hkNj

/-- Forward-from-reverse: the transfer of the returned set from the reverse
    allocation gives back the original target. -/
theorem transferAllocation_revAllocation (B : Allocation N p (transferCap n i j t))
    (S : Finset (Fin N)) (hSi : S ⊆ pileCard B j) (hcard : S.card = t)
    (ht : t ≤ n i) (hij : i ≠ j) :
    transferAllocation (revAllocation B S hSi hcard ht hij) S j t
      (Finset.mem_powersetCard.mpr ⟨by
        rw [pileCard_revAllocation_i B S hSi hcard ht hij]
        exact Finset.subset_union_left, hcard⟩) hij = B := by
  refine Subtype.ext ?_
  funext x
  simp only [transferAllocation, revAllocation, transferOwner, revOwner]
  split_ifs with hxS hxi hjb
  · have hmem := hSi hxS
    simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.symm
  · have hmem := hxi
    simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.symm
  · have hmem := hjb
    simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.symm
  · rfl


/-- The target's pile `i` is the source's pile `i` with `U` removed. -/
theorem pileCard_transferAllocation_i (A : Allocation N p n) (U : Finset (Fin N))
    (j : Fin p) (t : Nat) (hU : U ∈ (pileCard A i).powersetCard t) (hij : i ≠ j) :
    pileCard (transferAllocation A U j t hU hij) i = pileCard A i \ U := by
  have hval : (transferAllocation A U j t hU hij).val = transferOwner A U j := rfl
  simp only [pileCard]
  rw [hval]
  exact transferOwner_filter_pile_i A i j U hij

/-- The target's pile `j` is the source's pile `j` with `U` added. -/
theorem pileCard_transferAllocation_j (A : Allocation N p n) (U : Finset (Fin N))
    (j : Fin p) (t : Nat) (hU : U ∈ (pileCard A i).powersetCard t) (hij : i ≠ j) :
    pileCard (transferAllocation A U j t hU hij) j = pileCard A j ∪ U := by
  have hval : (transferAllocation A U j t hU hij).val = transferOwner A U j := rfl
  simp only [pileCard]
  rw [hval]
  exact transferOwner_filter_pile_j A i j U hij hU

/-- The reverse-from-forward equality: the reverse construction on the target
    recovers the original source allocation. -/
theorem revAllocation_ext (A : Allocation N p n) (U : TransferChoices A i t)
    (B : Allocation N p (transferCap n i j t))
    (hB : transferAllocation A U.1 j t U.2 hij = B)
    (hSi : U.1 ⊆ pileCard B j) (hcard : U.1.card = t)
    (ht : t ≤ n i) (hij : i ≠ j) :
    revAllocation B U.1 hSi hcard ht hij = A := by
  refine Subtype.ext ?_
  funext x
  have hval : (revAllocation B U.1 hSi hcard ht hij).val = revOwner B U.1 := rfl
  rw [hval]
  simp only [revOwner]
  by_cases hxU : x ∈ U.1
  · rw [ite_eq_left hxU]
    have hmem := (Finset.mem_powersetCard.mp U.2).1 hxU
    simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.symm
  · rw [ite_eq_right hxU]
    by_cases hxi : x ∈ pileCard B i
    · rw [ite_eq_left hxi]
      have hBJ : pileCard B i = pileCard A i \ U.1 := by
        have hC := congrArg (fun z => pileCard z i) hB
        rw [pileCard_transferAllocation_i A U.1 j t U.2 hij] at hC
        exact hC.symm
      have hxmem : x ∈ pileCard A i := by
        rw [hBJ] at hxi
        exact (Finset.mem_sdiff.mp hxi).1
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hxmem
      exact hxmem.symm
    · rw [ite_eq_right hxi]
      by_cases hjb : x ∈ pileCard B j
      · rw [ite_eq_left hjb]
        have hBJ : pileCard B j = pileCard A j ∪ U.1 := by
          have hC := congrArg (fun z => pileCard z j) hB
          rw [pileCard_transferAllocation_j A U.1 j t U.2 hij] at hC
          exact hC.symm
        rw [hBJ] at hjb
        rcases Finset.mem_union.mp hjb with hxA | hxU'
        · simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
          exact hxA.symm
        · exact absurd hxU' hxU
      · rw [ite_eq_right hjb]
        have hval : B.val = transferOwner A U.1 j := by
          have hC := congrArg Subtype.val hB
          exact hC.symm
        rw [hval]
        simp only [transferOwner]
        rw [ite_eq_right hxU]

/-- The return set of an allocation with the given transfer: the cards
    both in the source's pile `i` and the target's pile `j`. -/
def returnSet (B : Allocation N p (transferCap n i j t)) (g : Allocation N p n) :
    Finset (Fin N) :=
  pileCard g i ∩ pileCard B j

/-- The return set is a subset of the target's pile `j`. -/
theorem returnSet_subset (B : Allocation N p (transferCap n i j t)) (g : Allocation N p n) :
    returnSet B g ⊆ pileCard B j :=
  Finset.inter_subset_right

/-- The return set is exactly the transfer's return set. -/
theorem returnSet_eq (B : Allocation N p (transferCap n i j t)) (g : Allocation N p n)
    (U : TransferChoices g i t) (hU : transferAllocation g U.1 j t U.2 hij = B) (hij : i ≠ j) :
    returnSet B g = U.1 := by
  have hBJ : pileCard B j = pileCard g j ∪ U.1 := by
    have hC := congrArg (fun z => pileCard z j) hU
    rw [pileCard_transferAllocation_j g U.1 j t U.2 hij] at hC
    exact hC.symm
  have hdisj : Disjoint (pileCard g i) (pileCard g j) := pileCard_disjoint g hij
  ext x
  constructor
  · intro hx
    have hx_i : x ∈ pileCard g i := (Finset.mem_inter.mp hx).1
    have hx_B : x ∈ pileCard B j := (Finset.mem_inter.mp hx).2
    rw [hBJ] at hx_B
    rcases Finset.mem_union.mp hx_B with hxj | hxU
    · exfalso
      exact absurd hxj (Finset.disjoint_left.mp hdisj hx_i)
    · exact hxU
  · intro hxU
    have hx_i : x ∈ pileCard g i := (Finset.mem_powersetCard.mp U.2).1 hxU
    have hx_B : x ∈ pileCard B j := by
      rw [hBJ]
      exact Finset.mem_union_right _ hxU
    exact Finset.mem_inter.mpr ⟨hx_i, hx_B⟩

/-- The reverse construction: an `Equiv` between the reachable return sets
    (`t`-subsets of `pileCard B j`) and the source allocations with `i` as the
    source pile and the transfer summing to `B`. -/
noncomputable def reverseEquiv (B : Allocation N p (transferCap n i j t))
    (ht : t ≤ n i) (hij : i ≠ j) :
    {S : Finset (Fin N) // S ⊆ pileCard B j ∧ S.card = t} ≃
      {A : Allocation N p n // ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B} := by
  classical
  refine {
    toFun := fun S => ⟨revAllocation B S.1 S.2.1 S.2.2 ht hij,
      ⟨⟨S.1, Finset.mem_powersetCard.mpr ⟨by
        rw [pileCard_revAllocation_i B S.1 S.2.1 S.2.2 ht hij]
        exact Finset.subset_union_left, S.2.2⟩⟩,
        transferAllocation_revAllocation B S.1 S.2.1 S.2.2 ht hij⟩⟩
    invFun := fun g => by
      have hEx : ∃ U : TransferChoices g.1 i t, transferAllocation g.1 U.1 j t U.2 hij = B := g.2
      refine ⟨returnSet B g.1, ⟨returnSet_subset B g.1, ?_⟩⟩
      have hU := Classical.choose_spec hEx
      have hEq : returnSet B g.1 = (Classical.choose hEx).1 :=
        returnSet_eq B g.1 (Classical.choose hEx) hU hij
      rw [hEq]
      exact (Finset.mem_powersetCard.mp (Classical.choose hEx).2).2
    left_inv := fun S => by
      have hval : returnSet B (revAllocation B S.1 S.2.1 S.2.2 ht hij) = S.1 := by
        rw [returnSet, pileCard_revAllocation_i B S.1 S.2.1 S.2.2 ht hij]
        have hdisj : Disjoint (pileCard B i) (pileCard B j) := pileCard_disjoint B hij
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro hx
          rcases hx.1 with hx1 | hx2
          · exact hx1
          · exact absurd hx.2 (Finset.disjoint_left.mp hdisj hx2)
        · intro hx1
          exact ⟨Or.inl hx1, S.2.1 hx1⟩
      apply Subtype.ext
      exact hval
    right_inv := fun g => by
      have hEx : ∃ U : TransferChoices g.1 i t, transferAllocation g.1 U.1 j t U.2 hij = B := g.2
      have hU := Classical.choose_spec hEx
      have hSi : (Classical.choose hEx).1 ⊆ pileCard B j := by
        have hBJ : pileCard B j = pileCard g.1 j ∪ (Classical.choose hEx).1 := by
          have hC := congrArg (fun z => pileCard z j) hU
          rw [pileCard_transferAllocation_j g.1 (Classical.choose hEx).1 j t (Classical.choose hEx).2 hij] at hC
          exact hC.symm
        rw [hBJ]
        exact Finset.subset_union_right
      have hcard : (Classical.choose hEx).1.card = t := (Finset.mem_powersetCard.mp (Classical.choose hEx).2).2
      have hReq := revAllocation_ext g.1 (Classical.choose hEx) B hU hSi hcard ht hij
      have hEq : returnSet B g.1 = (Classical.choose hEx).1 :=
        returnSet_eq B g.1 (Classical.choose hEx) hU hij
      apply Subtype.ext
      apply Subtype.ext
      show revOwner B (returnSet B g.1) = g.1.val
      rw [hEq]
      exact congrArg Subtype.val hReq
  }

/-- The incoming degree: the number of source allocations reaching `B` is the
    number of `t`-subsets of the target's pile `j`. -/
theorem sources_card (B : Allocation N p (transferCap n i j t)) (ht : t ≤ n i) (hij : i ≠ j) :
    Fintype.card {A : Allocation N p n // ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B} =
      Nat.choose ((pileCard B j).card) t := by
  have hcard := Fintype.card_congr (reverseEquiv B ht hij)
  calc
    Fintype.card {A : Allocation N p n // ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B}
        = Fintype.card {S : Finset (Fin N) // S ⊆ pileCard B j ∧ S.card = t} :=
          hcard.symm
    _ = ((pileCard B j).powersetCard t).card := by
          rw [Fintype.card_subtype]
          have hE : ({S : Finset (Fin N) | S ⊆ pileCard B j ∧ S.card = t} : Finset (Finset (Fin N))) =
              (pileCard B j).powersetCard t := by
            apply Finset.ext
            intro S
            simp
          rw [hE]
    _ = Nat.choose ((pileCard B j).card) t := Finset.card_powersetCard _ _


/-! ### Total capacities are preserved and the constant degree of the transfer

The transfer moves `t` cards from pile `i` to pile `j`; the target capacities
are `transferCap n i j t`.  The arithmetic preservation of the total —
`∑ k, transferCap n i j t k = N` — is the total-capstone for `nonemptyOfSumCapacities`
on the target carrier.  The transfer relation is **biregular**: its outgoing
degree at `A` is `choose (n i) t` (injectivity), and its incoming degree at `B`
is `choose (n j + t) t` (the reverse construction).  Biregularity is what makes
the transfer kernel transport the uniform law. -/

/-- Total capacities are preserved by a transfer: pile `i` loses `t` cards,
pile `j` gains them, every other pile is unchanged, so the total stays `N`. -/
theorem transferCap_sum (hsum : (∑ k, n k) = N) (ht : t ≤ n i) (hij : i ≠ j) :
    (∑ k, transferCap n i j t k) = N := by
  have hi_mem : i ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ i
  have hji_mem : j ∈ (Finset.univ.erase i) :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hrest : (∑ k ∈ (Finset.univ.erase i).erase j, transferCap n i j t k) =
      ∑ k ∈ (Finset.univ.erase i).erase j, n k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hk
    simp only [transferCap, ite_eq_right hk.2.1, ite_eq_right hk.1]
  have htotal : (∑ k, n k) = (∑ k ∈ (Finset.univ.erase i).erase j, n k) + n i + n j := by
    rw [← Finset.sum_erase_add _ _ hi_mem, ← Finset.sum_erase_add _ _ hji_mem]
    omega
  have hiCap : transferCap n i j t i = n i - t := by
    rw [transferCap, ite_eq_left rfl]
  have hjCap : transferCap n i j t j = n j + t := by
    rw [transferCap, ite_eq_right (fun h => hij (h.symm)), ite_eq_left rfl]
  have h3 : (∑ k, transferCap n i j t k) = (∑ k ∈ (Finset.univ.erase i).erase j, n k) + (n i - t) + (n j + t) := by
    rw [← Finset.sum_erase_add _ _ hi_mem]
    rw [← Finset.sum_erase_add _ _ hji_mem]
    rw [hrest, hiCap, hjCap]
    ring
  rw [h3, ← hsum, htotal]
  omega

/-- The uniform law over the post-transfer allocation carrier (feasible
capacities, total preserved by `transferCap_sum`). -/
noncomputable def uniformTransferAlloc (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (hsum : (∑ k, n k) = N) (ht : t ≤ n i) :
    Dist (Allocation N p (transferCap n i j t)) := by
  letI : Nonempty (Allocation N p (transferCap n i j t)) :=
    nonemptyOfSumCapacities N p (transferCap n i j t) (transferCap_sum hsum ht hij)
  exact GSR.uniformDist (Allocation N p (transferCap n i j t))

/-- The constant incoming degree of the transfer relation: the number of
source allocations reaching any target `B` equals the number of `t`-subsets
of the target's pile `j` — and pile `j` always holds exactly `n j + t`
cards, so the degree is `choose (n j + t) t`. -/
theorem transferKernel_incoming_degree (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (ht : t ≤ n i) (B : Allocation N p (transferCap n i j t)) :
    (Finset.univ.filter (fun A : Allocation N p n =>
      ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card =
      Nat.choose (n j + t) t := by
  classical
  have hbridge : (Finset.univ.filter (fun A : Allocation N p n =>
      ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card =
      Fintype.card {A : Allocation N p n // ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B} := by
    simpa only [Fintype.card_subtype]
  rw [hbridge, sources_card B ht hij]
  congr 1
  have hcap : (pileCard B j).card = n j + t := by
    rw [pileCard_card B j, transferCap, ite_eq_right (fun h => hij (h.symm)), ite_eq_left rfl]
  rw [hcap]

/-- The outgoing degree: the number of distinct targets reachable from `A`
equals the number of transfer choices, `choose (n i) t` (injectivity). -/
theorem transferKernel_outgoing_degree (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (A : Allocation N p n) :
    (Finset.univ.filter (fun B : Allocation N p (transferCap n i j t) =>
      ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card =
      Nat.choose (n i) t := by
  classical
  have hval : (Finset.univ.filter (fun B : Allocation N p (transferCap n i j t) =>
      ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)) =
      (Finset.univ : Finset (TransferChoices A i t)).image
        (fun U => transferAllocation A U.1 j t U.2 hij) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [hval, Finset.card_image_of_injOn (transferAllocation_injective A i j t hij).injOn]
  rw [Finset.card_univ, TransferChoices.card]

/-- The transfer relation is biregular: outgoing degree `choose (n i) t`,
incoming degree `choose (n j + t) t`. -/
theorem transferKernel_biregular (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (ht : t ≤ n i) :
    Fintype.card (Allocation N p n) * Nat.choose (n i) t =
      Fintype.card (Allocation N p (transferCap n i j t)) * Nat.choose (n j + t) t := by
  classical
  have hout : ∀ A : Allocation N p n,
      (Finset.univ.filter (fun B : Allocation N p (transferCap n i j t) =>
        ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card =
        Nat.choose (n i) t :=
    fun A => transferKernel_outgoing_degree i j t hij A
  have hin : ∀ B : Allocation N p (transferCap n i j t),
      (Finset.univ.filter (fun A : Allocation N p n =>
        ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card =
        Nat.choose (n j + t) t :=
    fun B => transferKernel_incoming_degree i j t hij ht B
  exact biregular_count (fun A B => ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)
    (Nat.choose (n i) t) (Nat.choose (n j + t) t) hout hin

/-- The transfer kernel transports the uniform law on the source carrier to
the uniform law on the target carrier — the G7 changing-capacities capstone.
The column sum at a target `B` is the constant `choose (n j + t) t / choose
(n i) t`, which by the biregular count equals the ratio of the two carrier
sizes. -/
theorem uniform_transport_transferKernel (i j : Fin p) (t : Nat) (hij : i ≠ j)
    (ht : t ≤ n i)
    (hsum : (∑ k, n k) = N) :
    FiniteKernel.apply (uniformAlloc hsum) (transferKernel i j t hij ht) =
      uniformTransferAlloc i j t hij hsum ht := by
  classical
  letI : Nonempty (Allocation N p n) := nonemptyOfSumCapacities N p n hsum
  letI : Nonempty (Allocation N p (transferCap n i j t)) :=
    nonemptyOfSumCapacities N p (transferCap n i j t) (transferCap_sum hsum ht hij)
  have hcolsum : ∀ B : Allocation N p (transferCap n i j t),
      (∑ A : Allocation N p n, Dist.mass (transferKernel i j t hij ht A) B) =
        (Fintype.card (Allocation N p n) : Rat) / (Fintype.card (Allocation N p (transferCap n i j t)) : Rat) := by
    intro B
    have hper : ∀ A : Allocation N p n, Dist.mass (transferKernel i j t hij ht A) B =
        if ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B
        then ((Nat.choose (n i) t : Rat))⁻¹ else 0 := fun A => by
      rw [transferKernel_mass i j t hij ht A B, TransferChoices.card]
    have hcol : (∑ A : Allocation N p n, Dist.mass (transferKernel i j t hij ht A) B) =
        ((Finset.univ.filter fun A : Allocation N p n =>
          ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card *
          ((Nat.choose (n i) t : Rat))⁻¹ := by
      calc
        (∑ A : Allocation N p n, Dist.mass (transferKernel i j t hij ht A) B)
            = ∑ A : Allocation N p n, (if ∃ U : TransferChoices A i t,
                transferAllocation A U.1 j t U.2 hij = B then ((Nat.choose (n i) t : Rat))⁻¹ else 0) := by
              exact Finset.sum_congr rfl (fun A _ => hper A)
        _ = ∑ A ∈ (Finset.univ.filter fun A : Allocation N p n =>
              ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B),
              ((Nat.choose (n i) t : Rat))⁻¹ := by
              rw [← Finset.sum_filter]
        _ = ((Finset.univ.filter fun A : Allocation N p n =>
              ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B)).card *
              ((Nat.choose (n i) t : Rat))⁻¹ := by
              rw [Finset.sum_const]
              simp only [nsmul_eq_mul]
    rw [hcol]
    have hin : (Finset.univ.filter fun A : Allocation N p n =>
          ∃ U : TransferChoices A i t, transferAllocation A U.1 j t U.2 hij = B).card =
        Nat.choose (n j + t) t :=
      transferKernel_incoming_degree i j t hij ht B
    rw [hin]
    have h : Fintype.card (Allocation N p n) * Nat.choose (n i) t =
        Fintype.card (Allocation N p (transferCap n i j t)) * Nat.choose (n j + t) t :=
      transferKernel_biregular i j t hij ht
    have hcardR : (Fintype.card (Allocation N p n) : Rat) * (Nat.choose (n i) t : Rat) =
        (Fintype.card (Allocation N p (transferCap n i j t)) : Rat) * (Nat.choose (n j + t) t : Rat) := by
      exact_mod_cast h
    have hni : (Nat.choose (n i) t : Rat) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos ht)
    have hy : (Fintype.card (Allocation N p (transferCap n i j t)) : Rat) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [eq_div_iff hy]
    field_simp [hni]
    rw [show (Nat.choose (n j + t) t : Rat) * (Fintype.card (Allocation N p (transferCap n i j t)) : Rat) =
        (Fintype.card (Allocation N p (transferCap n i j t)) : Rat) * (Nat.choose (n j + t) t : Rat) by ring]
    rw [← hcardR]
    ring
  exact uniform_transport_of_colsum _ hcolsum

end Shufflemath.FiniteDeck
