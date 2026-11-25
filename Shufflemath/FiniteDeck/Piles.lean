module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.Fiber
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G5: multi-pile algebra — the pile-partition type definitions

Generalizes the two-pile fiber theory (G2) from a left/right split to an
arbitrary number `k` of piles.  A **pile partition** is a family
`posPile : Fin k → Finset (Fin N)` of pairwise-disjoint position sets covering
the deck; a **card allocation** `cardPile : Fin k → Finset (Fin N)` is the
analogous partition of the card universe.  A deck `d` **realizes** the
allocation when each pile's positions map onto the corresponding card pile.

This file establishes the reusable multi-pile type (`MultiFiber`) together
with the **two-pile instantiation** (`twoPilePos`, `twoPileCard`), whose pile
`0` / pile `1` are exactly the G2 left and right piles.  The two-pile/two-color
reduction (a two-pile allocation's fiber equals the G2 `FibType`) and the
general-`k` product-factorial fiber count are the next increments; this
increment fixes the shared type definitions they build on.
-/

/-- A deck `d` **realizes** the card allocation `cardPile` relative to the
    positional partition `posPile` when every pile's positions map onto the
    corresponding card pile. -/
def realizesAllocation (N k : Nat)
    (posPile cardPile : Fin k → Finset (Fin N)) (d : Deck N) : Prop :=
  ∀ p, (posPile p).image (fun q => d q) = cardPile p

/-- The **fiber** over a card allocation: all decks realizing it. -/
abbrev MultiFiber (N k : Nat) (posPile cardPile : Fin k → Finset (Fin N)) : Type :=
  {d : Deck N // realizesAllocation N k posPile cardPile d}

variable (N m : Nat) (hm : m ≤ N)

/-- The two-pile positional partition: pile `0` is the left pile, pile `1`
    the right pile. -/
noncomputable def twoPilePos (N m : Nat) (hm : m ≤ N) : Fin 2 → Finset (Fin N) :=
  fun p => if p.val = 0 then leftPositions N m hm else rightPositions N m hm

/-- The two-pile card allocation: pile `0` is the card set `A`, pile `1` its
    complement. -/
noncomputable def twoPileCard (N m : Nat) (A : Membership N m) : Fin 2 → Finset (Fin N) :=
  fun p => if p.val = 0 then A.1 else Finset.univ \ A.1

/-- Pile `0` is the left pile. -/
theorem twoPilePos0 (N m : Nat) (hm : m ≤ N) : twoPilePos N m hm 0 = leftPositions N m hm := by
  simp [twoPilePos]

/-- Pile `1` is the right pile. -/
theorem twoPilePos1 (N m : Nat) (hm : m ≤ N) : twoPilePos N m hm 1 = rightPositions N m hm := by
  simp [twoPilePos]

/-- Pile `0` of the card allocation is the card set `A`. -/
theorem twoPileCard0 (N m : Nat) (A : Membership N m) : twoPileCard N m A 0 = A.1 := by
  simp [twoPileCard]

/-- Pile `1` of the card allocation is the complement of `A`. -/
theorem twoPileCard1 (N m : Nat) (A : Membership N m) : twoPileCard N m A 1 = Finset.univ \ A.1 := by
  simp [twoPileCard]

/-- The image of the whole deck is the whole card universe: a permutation's
    image is onto. -/
theorem univImage_eq_univ (N : Nat) (e : Deck N) :
    (Finset.univ : Finset (Fin N)).image (fun p => e p) = Finset.univ := by
  apply Finset.ext
  intro y
  rw [Finset.mem_image]
  constructor
  · intro _; exact Finset.mem_univ _
  · intro _; exact ⟨e.symm y, Finset.mem_univ _, Equiv.apply_symm_apply e y⟩

/-- **G5 two-pile reduction.** A deck `e` whose left pile maps onto `A` (the G2
    fiber condition) automatically maps its right pile onto the complement of
    `A`: for a bijection the two-pile allocation predicate is equivalent to the
    single left-image condition.  This is the `k = 2` instance of the general
    pile-partition realization, and is what lets the two-pile `MultiFiber` be
    identified with the G2 `FibType`. -/
theorem twoPile_pred_iff (N m : Nat) (hm : m ≤ N) (A : Membership N m) (e : Deck N) :
    ((leftPositions N m hm).image (fun p => e p) = A.1 ∧
       (rightPositions N m hm).image (fun p => e p) = Finset.univ \ A.1) ↔
    (leftPositions N m hm).image (fun p => e p) = A.1 := by
  classical
  have hUniv : (Finset.univ : Finset (Fin N)).image (fun p => e p) = Finset.univ :=
    univImage_eq_univ N e
  constructor
  · intro h; exact h.1
  · intro hL
    constructor
    · exact hL
    · unfold rightPositions
      rw [Finset.image_sdiff (f := fun p => e p) _ _ e.injective, hUniv, hL]

/- A `Fin 2` element is either `0` or `1`. -/
theorem finTwo_cases (p : Fin 2) : p = 0 ∨ p = 1 := by
  by_cases h : p.val = 0
  · left
    exact Fin.ext h
  · have h1 : p.val = 1 := by
      have hlt : p.val < 2 := p.isLt
      omega
    right
    exact Fin.ext h1

/-- **G5 two-pile/two-color reduction (bijection).** The two-pile `MultiFiber`
    over the allocation `(A, univ \ A)` is in **bijection** with the G2 `FibType`
    over `A`: the left-image condition already forces the right-image one (a
    permutation's image is onto, so the complement of the left image is exactly
    the right image).  Thus the two-pile fiber IS the G2 fiber — the two-color
    generalization recovers the G2 counting and disintegration (G2-G4) exactly,
    with no `N!` enumeration. -/
theorem twoPile_equivFiber (N m : Nat) (hm : m ≤ N) (A : Membership N m) :
    Nonempty (Equiv (MultiFiber N 2 (twoPilePos N m hm) (twoPileCard N m A))
                   (FibType N m hm A)) := by
  refine ⟨Equiv.ofBijective ?toFun ?_⟩
  · -- toFun : the 2-pile fiber maps to the G2 fiber (its left-image condition)
    intro x
    exact ⟨x.1, by simpa [twoPilePos0, twoPileCard0] using x.2 0⟩
  · constructor
    · -- injective on the underlying deck
      intro x y h
      exact Subtype.ext (by simpa using congrArg (fun z => z.1) h)
    · -- surjective: a G2 fiber deck satisfies the 2-pile allocation
      intro y
      refine ⟨⟨y.1, ?_⟩, Subtype.ext rfl⟩
      intro p
      rcases finTwo_cases p with hp0 | hp1
      · subst hp0
        simpa [twoPilePos0, twoPileCard0] using y.2
      · subst hp1
        simpa [twoPilePos1, twoPileCard1] using (twoPile_pred_iff N m hm A y.1).2 y.2 |>.2

end FiniteDeck
end Shufflemath
