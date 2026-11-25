module

public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

/-!
# G5 / T5 — A1: the allocation carrier (arbitrary number of piles)

The **state** of a multi-pile exchange is the *allocation* — which named card
sits in which pile — not the order.  This module defines the A1 carrier
`Allocation (N p n)`: an owner function `Fin N → Fin p` assigning each of the
`N` named cards to one of `p` piles, with the `i`-th pile holding exactly
`n i` cards.

The carrier is built on the **owner-function** representation (not a dependent
product of `Finset`s), whose ambient type `Fin N → Fin p` carries an ordinary
finite-product `Fintype`.  The subtype of valid owners is therefore a genuine
finite type: `Fintype (Allocation N p n)` is given explicitly by
`Fintype.subtype` over the filter of the universal owner set, with **no
Finset-family `Fintype` wall**.  Inhabitation is by a positional partition:
for any `IsPartition P`, the allocation whose `i`-th pile is `P i` (capacities
`n i = (P i).card`) is a witness.

This is a reusable arbitrary-finite-deck foundation: the carrier, its finite
structure, and its inhabitation are all stated for a general `N` and an
arbitrary number `p` of piles with capacities `n`.
-/

/-- The per-pile card-count predicate on an owner function: pile `i` holds
    exactly `n i` cards. -/
def pAlloc {N p : Nat} (n : Fin p → Nat) (o : Fin N → Fin p) : Prop :=
  ∀ i, (Finset.univ.filter (fun x : Fin N => o x = i)).card = n i

/-- The **allocation** of `N` named cards into `p` piles with capacities
    `n`: the owner function `Fin N → Fin p` satisfying `pAlloc`. -/
def Allocation (N p : Nat) (n : Fin p → Nat) : Type :=
  { owner : Fin N → Fin p // pAlloc n owner }

variable {N p : Nat} {n : Fin p → Nat}

/-- The allocation carrier is a genuine finite type: the valid owners are the
    filter of the universal owner set, and `Fintype.subtype` gives its
    `Fintype` from the ambient `Fintype (Fin N → Fin p)` — no Finset-family
    `Fintype` wall. -/
noncomputable instance : Fintype (Allocation N p n) :=
  Fintype.subtype (Finset.univ.filter (pAlloc n)) (fun o =>
    by simp [Finset.mem_univ])

/-- The `i`-th pile of an allocation holds exactly `n i` cards. -/
theorem Allocation.pileCard (A : Allocation N p n) (i : Fin p) :
    (Finset.univ.filter (fun x => A.val x = i)).card = n i := A.property i

/-- The unique pile owning a card `x` in a partition: the index `i` with
    `x ∈ P i`.  Well-defined by the unique-ownership clause of `IsPartition`. -/
noncomputable def pileOwner (P : Fin p → Finset (Fin N)) (hP : IsPartition P)
    (x : Fin N) : Fin p :=
  Classical.choose (hP.1 x)

/-- `pileOwner P hP x = i` iff `x ∈ P i`: the chosen owner is the unique pile
    containing `x`. -/
theorem pileOwner_iff (P : Fin p → Finset (Fin N)) (hP : IsPartition P)
    (x : Fin N) (i : Fin p) : pileOwner P hP x = i ↔ x ∈ P i := by
  constructor
  · intro h
    have hexists : x ∈ P (pileOwner P hP x) := Classical.choose_spec (hP.1 x)
    simpa only [h] using hexists
  · intro hx
    have hexists : x ∈ P (pileOwner P hP x) := Classical.choose_spec (hP.1 x)
    have h := hP.2 (pileOwner P hP x) i x hexists hx
    simpa [h] using hexists

/-- The `i`-th pile of the owner function of a partition is exactly `P i`. -/
theorem pileOwner_preimage (P : Fin p → Finset (Fin N)) (hP : IsPartition P)
    (i : Fin p) :
    Finset.univ.filter (fun x => pileOwner P hP x = i) = P i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pileOwner_iff P hP x i

/-- **Inhabitation by a positional partition.**  For any `IsPartition P`, the
    owner function of `P` is an allocation with capacities `n i = (P i).card`.
    This witnesses a powerful arbitrary-capacity result without constructing a
    partition from a list of capacities. -/
noncomputable def Allocation.ofPartition (P : Fin p → Finset (Fin N))
    (hP : IsPartition P) :
    Allocation N p (fun i => (P i).card) := by
  refine ⟨fun x => pileOwner P hP x, fun i => ?_⟩
  rw [pileOwner_preimage P hP i]

/-- The allocation carrier is nonempty for any capacities realized by a
    partition (in particular the positional / all-in-one-pile cases). -/
theorem Allocation.nonemptyOfPartition
    (P : Fin p → Finset (Fin N)) (hP : IsPartition P) :
    Nonempty (Allocation N p (fun i => (P i).card)) :=
  ⟨Allocation.ofPartition P hP⟩

/-! ### A1.3 — the exchange: swapping two cards' piles

The elementary **exchange** of the multi-pile state swaps the *piles* of two
named cards `a` and `b` (leaving the order inside each pile untouched, since
the state records only ownership).  This is the finite-deck analogue of the
two-pile `PileEquiv.swap`.  We show it is a well-defined **self-map of the
allocation carrier**: `swapOwner A a b` is again an `Allocation`, because it is
`A.val` composed with the transposition `a ↔ b`, a bijection, and a bijection
preserves every fiber's cardinality.

All statements are for a general `N` and arbitrary pile count `p` with
capacities `n` — a reusable arbitrary-finite-deck foundation.
-/ 

/-- The owner function after swapping the piles of two cards `a` and `b`:
    card `a` takes `b`'s pile, card `b` takes `a`'s, all other cards fixed. -/
def swapOwner (A : Allocation N p n) (a b : Fin N) (x : Fin N) : Fin p :=
  if x = a then A.val b else if x = b then A.val a else A.val x

/-- The transposition of two card indices: the map that swaps `a` and `b`
    and fixes every other card. -/
def cardTransposition (a b : Fin N) (x : Fin N) : Fin N :=
  if x = a then b else if x = b then a else x

/-- `cardTransposition` is an involution: applying it twice is the identity. -/
theorem cardTransposition_involution (a b : Fin N) (x : Fin N) :
    cardTransposition a b (cardTransposition a b x) = x := by
  by_cases hab : a = b
  · subst hab
    by_cases hx : x = a
    · subst hx
      simp [cardTransposition]
    · simp [cardTransposition, hx]
  · by_cases ha : x = a
    · subst ha
      simp [cardTransposition, hab]
    · by_cases hb : x = b
      · subst hb
        simp [cardTransposition, hab]
      · simp [cardTransposition, ha, hb]

/-- The transposition is a genuine equivalence (bijection). -/
noncomputable def transposition (a b : Fin N) : Fin N ≃ Fin N := by
  classical
  refine Equiv.ofBijective (cardTransposition a b) ?_
  constructor
  · intro x y h
    have h1 := congrArg (cardTransposition a b) h
    simp [cardTransposition_involution] at h1
    exact h1
  · intro y
    exact ⟨cardTransposition a b y, by simp [cardTransposition_involution]⟩

/-- Swapping the piles of two cards is `A.val` composed with the pointwise
    transposition `cardTransposition`: card `x` takes the pile that `cardTransposition a b x` had. -/
theorem swapOwner_eq_cardTransposition (A : Allocation N p n) (a b x : Fin N) :
    swapOwner A a b x = A.val (cardTransposition a b x) := by
  dsimp only [swapOwner, cardTransposition]
  split_ifs <;> simp_all

/-- The transposition equivalence applies as the pointwise `cardTransposition`. -/
theorem transposition_apply (a b x : Fin N) : (transposition a b) x = cardTransposition a b x := by
  dsimp [transposition]
  rfl

/-! ### A1.4 core — conjugation of a transposition by a relabeling

The next layer of the A1 program is **relabel-invariance**: the multi-pile exchange
structure should not depend on the arbitrary names we have given the cards.  The
foundational equivariance fact is that a permutation `σ` of the card indices
*conjugates* the transposition of `a, b` to the transposition of their images `σ a, σ b`.
This is what makes swapping two cards' piles commute with relabeling, and (via the
uniform `(a, b)`-choice being relabel-invariant) what makes the uniform swap kernel
invariant under relabeling.  Stated for a general `N`; `σ` may be any permutation, and
no allocation is involved. -/

/-- Conjugation: a permutation `σ` conjugates the transposition of `a, b` to the
    transposition of their images `σ a, σ b`. -/
theorem conjugate_transposition (σ : Equiv.Perm (Fin N)) (a b x : Fin N) :
    σ (cardTransposition a b (σ.symm x)) = cardTransposition (σ a) (σ b) x := by
  by_cases ha : x = σ a
  · subst ha
    simp [cardTransposition, Equiv.symm_apply_apply]
  · by_cases hb : x = σ b
    · subst hb
      simp [cardTransposition, Equiv.symm_apply_apply, ha]
    · have hna : σ.symm x ≠ a := by
        intro h
        have hx : x = σ a := by rw [(σ.apply_symm_apply x).symm, h]
        contradiction
      have hnb : σ.symm x ≠ b := by
        intro h
        have hx : x = σ b := by rw [(σ.apply_symm_apply x).symm, h]
        contradiction
      simp [cardTransposition, hna, hnb, ha, hb, Equiv.apply_symm_apply]

/-! ### A1.4 — the relabeling action and its commutation with the exchange

A **relabeling** of the card indices is a permutation `σ : Fin N ≃ Fin N`.  It acts on
the allocation carrier by precomposing the owner function with `σ.symm` (card `x` of the
relabelled allocation holds the card that `σ.symm x` held before).  The action is a
genuine bijection, and — by conjugation — it commutes with the exchange: swapping the
two images `σ a, σ b` of the relabelled state is the relabelling of swapping `a, b`.  This
is the equivariance needed to show the uniform swap kernel is invariant under relabeling
(see `UniformExchange.swapKernel_equivariant`). -/

/-- The relabeling action: a permutation `σ` of the card indices acts on an
    allocation by precomposing its owner function with `σ.symm`.  The result is again a
    valid allocation (each i-fiber is in bijection, via `σ.symm`, with the corresponding
    fiber of the original, so its cardinality is `n i`). -/
def relabel (σ : Equiv.Perm (Fin N)) (A : Allocation N p n) : Allocation N p n :=
  ⟨fun x => A.val (σ.symm x), fun i => by
      set τ : Fin N ≃ Fin N := σ.symm
      have hcomp : ∀ x, A.val (σ.symm x) = A.val (τ x) := fun x => rfl
      classical
      have hE : {x : Fin N // A.val (σ.symm x) = i} ≃ {y : Fin N // A.val y = i} :=
        Equiv.ofBijective (fun z => ⟨τ z.val, by simpa [hcomp] using z.property⟩)
          (⟨fun z w h =>
              Subtype.ext (by simpa [Equiv.symm_apply_apply]
                using (congrArg (τ.symm) (congrArg (·.val) h))),
           fun w =>
             ⟨⟨τ.symm w.val, by simpa [hcomp, Equiv.apply_symm_apply] using w.property⟩,
              by simpa [Equiv.symm_apply_apply]⟩⟩)
      have h1 : (Finset.univ.filter (fun x => A.val (σ.symm x) = i)).card =
          Fintype.card {x : Fin N // A.val (σ.symm x) = i} := by
        simpa only [Fintype.card_subtype]
      have h2 : Fintype.card {x : Fin N // A.val (σ.symm x) = i} =
          Fintype.card {y : Fin N // A.val y = i} := by
        simpa using Fintype.card_congr hE
      have h3 : Fintype.card {y : Fin N // A.val y = i} =
          (Finset.univ.filter (fun y => A.val y = i)).card := by
        simpa only [Fintype.card_subtype]
      rw [h1, h2, h3, A.property i]⟩

/-- Relabeling is invertible: `relabel (σ.symm) (relabel σ A) = A` — hence the
    action is a genuine bijection of the allocation carrier. -/
theorem relabel_symm_relabel (σ : Equiv.Perm (Fin N)) (A : Allocation N p n) :
    relabel (σ.symm) (relabel σ A) = A := by
  apply Subtype.ext
  funext x
  simp [relabel, Equiv.symm_symm, Equiv.symm_apply_apply]

/-! ### A1.4 — the exchange commutes with relabeling

Swapping the two *images* `σ a, σ b` of the relabelled allocation `relabel σ A` gives
the same owner at `x` as relabelling the allocation obtained by swapping `a, b`.  This
is the owner-function form of the commutation `relabel σ ∘ swapPiles(a,b) =
swapPiles(σ a, σ b) ∘ relabel σ`, and is the one that elaborates in this module (it
names only the single `noncomputable` def `relabel`, not both `relabel` and `swapPiles`). -/

/-- Relabeling and the exchange commute at the owner level: swapping the images
    `σ a, σ b` of the relabelled state has, at `x`, the owner that the original state
    had at the card that both the swap and the relabelling send `x` to — i.e. the owner
    `A.val (cardTransposition a b (σ.symm x))`.  A direct consequence of the conjugation
    of a transposition by `σ`. -/
theorem relabel_commute_owner (σ : Equiv.Perm (Fin N)) (A : Allocation N p n) (a b x : Fin N) :
    swapOwner (relabel σ A) (σ a) (σ b) x = A.val (cardTransposition a b (σ.symm x)) := by
  -- the left side, by the transposition form of the swap, is the relabelled owner at the
  -- transposed index; unfolding `relabel` beta-reduces it to `A.val` at `σ.symm` of that index
  have hUnf : (relabel σ A).val (cardTransposition (σ a) (σ b) x) =
      A.val (σ.symm (cardTransposition (σ a) (σ b) x)) := by
    dsimp only [relabel]
  rw [swapOwner_eq_cardTransposition, hUnf]
  -- now both sides are `A.val` of two indices; fold the relabelling into the transposition
  -- using the conjugation `σ ∘ τ_{a,b} ∘ σ⁻¹ = τ_{σ a, σ b}`
  have hc : σ.symm (cardTransposition (σ a) (σ b) x) = cardTransposition a b (σ.symm x) := by
    have h := congrArg (σ.symm) (conjugate_transposition σ a b x)
    simpa [Equiv.symm_apply_apply] using h.symm
  rw [hc]

/-- `relabel σ` is a **bijection** (its two-sided inverse is `relabel σ.symm`, by
    `relabel_symm_relabel`), so it is injective: it sends equal allocations to equal
    allocations and conversely.  Equivalently, for any two allocations `B` and `Y`,
    `relabel σ B = relabel σ Y ↔ B = Y`.  This is the term-by-term bridge the A1.4
    kernel-equivariance `swapKernel_equivariant` uses to match its two fiber sums over
    the *same* index pairs (no reindexing): instantiate `Y := swapPiles A a b`. -/
theorem relabel_eq_iff (σ : Equiv.Perm (Fin N)) (B Y : Allocation N p n) :
    relabel σ B = relabel σ Y ↔ B = Y := by
  constructor
  · intro h
    -- apply the inverse relabeling `relabel (σ.symm)` to both sides, then fold
    have h1 := congrArg (fun z => (relabel (σ.symm) z)) h
    simpa [relabel_symm_relabel] using h1
  · intro h
    simpa [h]

/-- **The exchange is a well-defined self-map of the allocation carrier:**
    swapping two cards' piles preserves every pile's size (so the result is
    again an `Allocation`).  Reason: `swapOwner = A.val ∘ σ` for the
    transposition `σ`, a bijection, and a bijection preserves each fiber's
    cardinality (counted here via `Fintype.card` of the fibers, which is
    invariant under the transposition). -/
theorem swapOwner_capacity (A : Allocation N p n) (a b : Fin N) (i : Fin p) :
    (Finset.univ.filter (fun x => swapOwner A a b x = i)).card = n i := by
  set σ : Fin N ≃ Fin N := (transposition a b)
  have hcomp : ∀ x, swapOwner A a b x = A.val (σ x) := fun x => by
    rw [swapOwner_eq_cardTransposition, ← transposition_apply]
  classical
  -- the i-fiber of (A.val ∘ σ) is in bijection with the i-fiber of A.val, via x ↦ σ x
  have hE : {x : Fin N // swapOwner A a b x = i} ≃ {y : Fin N // A.val y = i} :=
    Equiv.ofBijective (fun z => ⟨σ z.val, by simpa [hcomp] using z.property⟩)
      (⟨fun z w h =>
          Subtype.ext (by simpa [Equiv.symm_apply_apply]
            using (congrArg (σ.symm) (congrArg (·.val) h))),
        fun w =>
          ⟨⟨σ.symm w.val, by simpa [hcomp, Equiv.apply_symm_apply] using w.property⟩,
           by simpa [Equiv.symm_apply_apply]⟩⟩)
  have h1 : (Finset.univ.filter (fun x => swapOwner A a b x = i)).card =
      Fintype.card {x : Fin N // swapOwner A a b x = i} := by
    simpa only [Fintype.card_subtype]
  have h2 : Fintype.card {x : Fin N // swapOwner A a b x = i} =
      Fintype.card {y : Fin N // A.val y = i} := by
    simpa using Fintype.card_congr hE
  have h3 : Fintype.card {y : Fin N // A.val y = i} =
      (Finset.univ.filter (fun y => A.val y = i)).card := by
    simpa only [Fintype.card_subtype]
  rw [h1, h2, h3, A.property i]

/-- Swapping two cards' piles yields a valid allocation (the exchange
    operation, packaged as a self-map of the carrier). -/
noncomputable def swapPiles (A : Allocation N p n) (a b : Fin N) : Allocation N p n :=
  ⟨fun x => swapOwner A a b x, fun i => swapOwner_capacity A a b i⟩

end FiniteDeck
end Shufflemath
