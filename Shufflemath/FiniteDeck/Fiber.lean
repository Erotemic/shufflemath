module

public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Shufflemath.FiniteDeck.TwoPileFiber
public import Mathlib.Tactic

-- The generic two-pile `k`-exchange fiber machinery (roadmap item G2/T1).
-- A deck `Deck N` is a bijection of `Fin N`; for a left pile `A : Membership N m`
-- its fiber is the decks sending the left positions onto `A`. Restricting such a
-- deck to the left (resp. right) positions gives a bijection to `A` (resp. to the
-- complement of `A`). This module proves the left-restriction bijection; the
-- right-restriction bijection and the fiber count follow.
@[expose] public section

namespace Shufflemath
namespace FiniteDeck

def FibType (N m : Nat) (hm : m ≤ N) (A : Membership N m) :=
  {e : Equiv.Perm (Fin N) // (leftPositions N m hm).image (fun p => e p) = A.1}
def LType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (leftPositions N m hm)}
def RType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (rightPositions N m hm)}
def AAType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ A.1}
def BBType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ (Finset.univ \ A.1)}

-- The restriction of a fiber permutation to the left pile is a bijection L ≃ A.
noncomputable def fiberRestrictL (N m : Nat) (hm : m ≤ N) (A : Membership N m) (e : FibType N m hm A) :
    LType N m hm ≃ AAType N m hm A := by
  have hmem : ∀ (l : LType N m hm), e.1 (l.1) ∈ A.1 := by
    intro l
    simpa [e.2, Finset.mem_image] using (Finset.mem_image_of_mem (fun p => e.1 p) l.2)
  apply Equiv.ofBijective (fun l => ⟨e.1 (l.1), hmem l⟩)
  · constructor
    · -- injective: e is a bijection, so it is injective on the left positions
      intro l₁ l₂ h
      have hEq : e.1 (l₁.1) = e.1 (l₂.1) := by
        simpa using (congrArg (fun (z : AAType N m hm A) => z.1) h)
      exact Subtype.ext ((Equiv.injective (e.1)) hEq)
    · -- surjective: e's left-image is exactly A, so every a ∈ A is e p for a left p
      intro a
      have hA : ∃ p ∈ (leftPositions N m hm), e.1 p = a.1 := by
        rw [← Finset.mem_image]
        rw [e.2]
        exact a.2
      rcases hA with ⟨p, hp, heq⟩
      exact ⟨⟨p, hp⟩, Subtype.ext heq⟩

-- The restriction of a fiber permutation to the right positions is a bijection
-- to the complement of the left pile `A`: the right-image of a fiber deck is
-- exactly `univ \ A`, because the deck is a bijection and its left-image is `A`.
noncomputable def fiberRestrictR (N m : Nat) (hm : m ≤ N) (A : Membership N m) (e : FibType N m hm A) :
    RType N m hm ≃ BBType N m hm A := by
  have hmem : ∀ (r : RType N m hm), e.1 (r.1) ∈ (Finset.univ \ A.1) := by
    intro r
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · -- e.1 (r.1) ∉ A.1: if it were, its left-preimage would equal r.1, a left position
      intro h
      have hImg : e.1 (r.1) ∈ (leftPositions N m hm).image (fun p => e.1 p) := by
        simpa [e.2] using h
      rcases Finset.mem_image.mp hImg with ⟨p, hp, heq⟩
      have hInj : p = r.1 := (Equiv.injective (e.1)) heq
      have hLeft : r.1 ∈ leftPositions N m hm := by
        simpa [hInj] using hp
      have hNotLeft : r.1 ∉ leftPositions N m hm := by
        have hr2 : r.1 ∈ rightPositions N m hm := r.2
        dsimp only [rightPositions] at hr2
        rw [Finset.mem_sdiff] at hr2
        exact hr2.2
      exact hNotLeft hLeft
  apply Equiv.ofBijective (fun r => ⟨e.1 (r.1), hmem r⟩)
  · constructor
    · intro r₁ r₂ h
      have hEq : e.1 (r₁.1) = e.1 (r₂.1) := by
        simpa using (congrArg (fun (z : BBType N m hm A) => z.1) h)
      exact Subtype.ext ((Equiv.injective (e.1)) hEq)
    · -- surjective: b.1 ∉ A.1, so its unique preimage under the bijection e.1 is a right position
      intro b
      let q := (e.1).symm (b.1)
      have hq : e.1 q = b.1 := Equiv.apply_symm_apply (e.1) (b.1)
      have hNotLeft : q ∉ leftPositions N m hm := by
        intro h
        have hImg : e.1 q ∈ (leftPositions N m hm).image (fun p => e.1 p) := by
          simpa [Finset.mem_image] using h
        have hInA : e.1 q ∈ A.1 := by
          simpa [e.2] using hImg
        have hb2 : b.1 ∈ Finset.univ \ A.1 := b.2
        rw [Finset.mem_sdiff] at hb2
        exact hb2.2 (by simpa [hq] using hInA)
      have hRight : q ∈ rightPositions N m hm := by
        rw [rightPositions, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hNotLeft⟩
      exact ⟨⟨q, hRight⟩, Subtype.ext hq⟩

theorem fibTransitive (N m : Nat) (hm : m ≤ N) (A B : Membership N m) :
    ∃ g : Equiv.Perm (Fin N), g '' A.1 = B.1 := by
  classical
  set Ac : Finset (Fin N) := Finset.univ \ A.1
  set Bc : Finset (Fin N) := Finset.univ \ B.1
  have hA : Fintype.card {x : Fin N // x ∈ A.1} = m := fintype_card_pile N m hm A
  have hB : Fintype.card {x : Fin N // x ∈ B.1} = m := fintype_card_pile N m hm B
  have hAc : Fintype.card {x : Fin N // x ∈ Ac} = N - m := by simpa [Ac] using fintype_card_complementPile N m hm A
  have hBc : Fintype.card {x : Fin N // x ∈ Bc} = N - m := by simpa [Bc] using fintype_card_complementPile N m hm B
  have hAB : Fintype.card {x : Fin N // x ∈ A.1} = Fintype.card {x : Fin N // x ∈ B.1} := by rw [hA, hB]
  have hAcBc : Fintype.card {x : Fin N // x ∈ Ac} = Fintype.card {x : Fin N // x ∈ Bc} := by rw [hAc, hBc]
  let eA : {x : Fin N // x ∈ A.1} ≃ {x : Fin N // x ∈ B.1} := Fintype.equivOfCardEq hAB
  let eAc : {x : Fin N // x ∈ Ac} ≃ {x : Fin N // x ∈ Bc} := Fintype.equivOfCardEq hAcBc
  let g : Fin N → Fin N := fun x => by
    by_cases hx : x ∈ A.1
    · exact (eA ⟨x, hx⟩).1
    · exact (eAc ⟨x, by
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hx⟩⟩).1
  -- value on A (then-branch of g, the else-branch is pruned by hx)
  have hAval : ∀ x (hx : x ∈ A.1), g x = (eA ⟨x, hx⟩).1 := by
    intro x hx
    dsimp only [g]
    split_ifs
    · refine congrArg (fun (z : {a : Fin N // a ∈ A.1}) => (eA z).1) ?_
      exact Subtype.ext rfl
  -- value on A^c (else-branch of g, the then-branch is pruned by hx)
  have hAcval : ∀ x (hx : x ∉ A.1), g x = (eAc ⟨x, by
      rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hx⟩⟩).1 := by
    intro x hx
    dsimp only [g]
    split_ifs
    · refine congrArg (fun (z : {a : Fin N // a ∈ Ac}) => (eAc z).1) ?_
      exact Subtype.ext rfl
  -- image membership, via the value lemmas
  have hAimg : ∀ x (hx : x ∈ A.1), g x ∈ B.1 := by
    intro x hx
    rw [hAval x hx]
    exact (eA ⟨x, hx⟩).2
  have hAcimg : ∀ x (hx : x ∉ A.1), g x ∈ Bc := by
    intro x hx
    rw [hAcval x hx]
    simpa [Finset.mem_sdiff] using (eAc ⟨x, by
      rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hx⟩⟩).2
  -- value of g on an A^c-element, proved directly (bypasses the proof-mismatch
  -- that hAcval would introduce): g x = (eAc a).1 when x = a.1, a ∈ A^c.
  have hAcval2 (a : {w : Fin N // w ∈ Ac}) : g a.1 = (eAc a).1 := by
    dsimp only [g]
    split_ifs with hThen
    · -- then-branch: hThen : a.1 ∈ A.1, but a.1 ∈ Ac means a.1 ∉ A.1
      have ha : a.1 ∈ Ac := a.2
      dsimp only [Ac] at ha
      rw [Finset.mem_sdiff] at ha
      exfalso
      exact ha.2 hThen
    · -- else-branch: a.1 ∉ A.1, so g (a.1) = (eAc ⟨a.1, p⟩).1
      refine congrArg (fun (w : {v : Fin N // v ∈ Ac}) => (eAc w).1) ?_
      exact Subtype.ext rfl
  -- surjective: B-part via eA, B^c-part via eAc
  have hSurj : Function.Surjective g := by
    intro z
    by_cases hz : z ∈ B.1
    · obtain ⟨a, ha2⟩ := eA.surjective ⟨z, hz⟩
      have hgoal : g (a.1) = (eA a).1 := by
        rw [hAval (a.1) a.2]
      have hval : g (a.1) = z := by
        rw [hgoal]
        simpa [ha2]
      exact ⟨a.1, hval⟩
    · obtain ⟨a, ha2⟩ := eAc.surjective ⟨z, by
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, hz⟩⟩
      have hgoal : g (a.1) = (eAc a).1 := hAcval2 a
      have hval : g (a.1) = z := by
        rw [hgoal]
        simpa [ha2]
      exact ⟨a.1, hval⟩
  -- surjective endomap on a fintype is bijective
  have hBij : Function.Bijective g := by
    constructor
    · exact Finite.injective_iff_surjective.mpr hSurj
    · exact hSurj
  -- image of A is B
  have hImg : g '' A.1 = B.1 := by
    ext z
    constructor
    · intro hmem
      rcases hmem with ⟨x, hx, rfl⟩
      exact hAimg x hx
    · intro hz
      obtain ⟨a, ha2⟩ := eA.surjective ⟨z, hz⟩
      have hgoal : g (a.1) = (eA a).1 := by
        rw [hAval (a.1) a.2]
      have hval : g (a.1) = z := by
        rw [hgoal]
        simpa [ha2]
      exact ⟨a.1, a.2, hval⟩
  exact ⟨Equiv.ofBijective g hBij, hImg⟩

-- ============================================================================
-- NEXT STEP (G2/T1 capstone) — the fiber count  #Fiber(A) = m! * (N - m)!
-- ============================================================================
-- CORRECT STRATEGY (avoids the pointwise-glue wall): use the TRANSITIVE group
-- action of G = Perm (Fin N) on the pile set P = {s : Finset (Fin N) // #s = m}
-- by pushforward  g . s := g '' s.  The fiber  Fib(A) := {g // g '' L = A}
-- (L = leftPositions) is the "translation set" sending the fixed base pile L to
-- A.  Facts:
--   (i)   the Fib(A) over A in P are pairwise disjoint and their union is G
--         (every g sends L to exactly one m-pile);
--   (ii)  by transitivity of the action (membershipFiber_transitive, already
--         established generically / in the Commander case), a group element
--         mapping A to B gives a bijection Fib(A) -> Fib(B), so all Fib(A)
--         have EQUAL cardinality;
--   (iii)  hence  #P * #Fib(A) = #G,  i.e.  (choose N m) * #Fib(A) = N!,  so
--         #Fib(A) = N! / choose N m = N! / (N!/(m!(N-m)!)) = m! * (N - m)!.
-- This is a pure orbit/fiber count: no pointwise `glue` function (whose
-- `if x ∈ L ... else ...` else-branch cannot name its own negation — the
-- term-mode `if`/`by_cases` opacity wall).  The only `Finset`s needed are
-- Fib(A) itself and the pile set P.
--
-- 0. fibTransitive  : DONE (proven above).  The pushforward action is transitive —
--      for any A, B in P, ∃ g : Perm (Fin N), g '' A.1 = B.1.  Built in TACTIC mode
--      (a theorem's `by`), where `by_cases hx : x ∈ A.1` gives a usable
--      `¬(x ∈ A.1)` in the else-branch (unlike a `def`).  Glues equicardinal bijections
--      A→B and Aᶜ→Bᶜ (Fintype.equivOfCardEq on the subtypes) into a full Perm;
--      surjectivity is proved (2 cases: B-part via the A-bijection, Bᶜ-part via the
--      complement-bijection) and bijectivity follows from Finite.injective_iff_surjective
--      (equal-card endomap).  The value lemmas use
--      `dsimp only [g]; split_ifs; congrArg (fun z => (eA z).1); exact Subtype.ext rfl`
--      to bridge the subtype proof-mismatch.  KEY GOTCHAS: (a) a `set`-bound Ac is
--      NOT rw-able — use `dsimp only [Ac]`; (b) `Surjective g` is a 2-field
--      `⟨w, h⟩` existential (no membership conjunct), but `z ∈ g '' A` is
--      `∃ x, x ∈ A ∧ g x = z` (3 fields); (c) `simpa [ha2]` bridges `↑(eA a) = z`
--      from `eA a = ⟨z, hz⟩`; (d) the A-branch value `g (a.1) = (eA a).1` closes by
--      `rw [hAval (a.1) a.2]` alone (a.2 IS a's proof, so ⟨a.1, a.2⟩ = a is rfl);
--      the Aᶜ-branch needs the direct hAcval2 (proof-mismatch).
-- 1. fibersPartition : the Fib(A) form a pairwise-disjoint cover of G.
-- 2. fibersEqual     : #Fib(A) is independent of A  (from 0, via a fiber-bijection).
-- 3. fiberCount      : (choose N m) * #Fib(A) = N!  ⟹  #Fib(A) = m! * (N-m)!.
--      (from 1+2+membershipCount + N! = (choose N m) * m! * (N-m)!, i.e. the
--      factorial form of the binomial coefficient.)
-- ============================================================================
end FiniteDeck
end Shufflemath
