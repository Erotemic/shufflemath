module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
## `Finset` combinatorial facts for the hypergeometric exchange count (F3)

General counting lemmas used by the F3 item-3 `hMembershipExchange` counting
identity: how many `k`-subsets of a set partitioned into two disjoint parts
`a` and `b` have exactly `i` elements in `a`. The pieces here are the
set-algebra lemmas the counting rests on.
-/
namespace FinsetCombinatorics

/-- If `A ⊆ a` and `B ⊆ b` with `a ∩ b = ∅`, then the union `A ∪ B` is
  *recoverable* by intersecting with the two parts:
  `(A ∪ B) ∩ a = A` and `(A ∪ B) ∩ b = B`. In particular the disjoint-union
  decomposition is unique, which is what lets a `(i`-subset of `a`) ×
  (`(k - i)`-subset of `b`) pair be recovered from its union. -/
theorem union_inter_parts (a b A B : Finset α) [DecidableEq α]
    (ha : A ⊆ a) (hb : B ⊆ b) (hab : a ∩ b = ∅) :
    (A ∪ B) ∩ a = A ∧ (A ∪ B) ∩ b = B := by
  have ha' : ∀ x, x ∈ A → x ∈ a := ha
  have hb' : ∀ x, x ∈ B → x ∈ b := hb
  have hab' : ∀ x, ¬ (x ∈ a ∧ x ∈ b) := fun x h => by
    have hx : x ∈ a ∩ b := by simpa using h
    simpa [hab] using hx
  constructor
  · -- (A ∪ B) ∩ a = A
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  · -- (A ∪ B) ∩ b = B
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto

end FinsetCombinatorics
