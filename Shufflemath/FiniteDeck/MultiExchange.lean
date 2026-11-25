module

public import Shufflemath.FiniteDeck.Partition
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
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

variable {N p : Nat} (n : Fin p → Nat)

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

end FiniteDeck
end Shufflemath
