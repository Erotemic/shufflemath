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

abbrev FibType (N m : Nat) (hm : m ≤ N) (A : Membership N m) :=
  {e : Equiv.Perm (Fin N) // (leftPositions N m hm).image (fun p => e p) = A.1}
abbrev LType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (leftPositions N m hm)}
abbrev RType (N m : Nat) (hm : m ≤ N) := {p : Fin N // p ∈ (rightPositions N m hm)}
abbrev AAType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ A.1}
abbrev BBType (N m : Nat) (hm : m ≤ N) (A : Membership N m) := {a : Fin N // a ∈ (Finset.univ \ A.1)}

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

theorem img_comp (N : Nat) (t e : Equiv.Perm (Fin N)) (s : Finset (Fin N)) :
    (s).image (fun p => (e.trans t) p) = ((s).image (fun p => e p)).image (fun a => t a) := by
  apply Finset.ext
  intro x
  constructor
  · -- -> : x in (t ∘ e)''s  =>  x in t''(e''s)
    intro hx
    obtain ⟨p, hp, htx⟩ := Finset.mem_image.mp hx
    have hE : e p ∈ (s).image (fun q => e q) := Finset.mem_image_of_mem (fun q => e q) hp
    have hX : t (e p) = x := (Equiv.trans_apply e t p).symm.trans htx
    simpa [hX] using Finset.mem_image_of_mem (fun a => t a) hE
  · -- <- : x in t''(e''s)  =>  x in (t ∘ e)''s
    intro hx
    obtain ⟨a, hAm, htax⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hea⟩ := Finset.mem_image.mp hAm
    have hX : (e.trans t) p = x := by
      calc (e.trans t) p = t (e p) := by rw [Equiv.trans_apply]
        _ = t a := by rw [hea]
        _ = x := htax
    simpa [hX] using Finset.mem_image_of_mem (fun p => (e.trans t) p) hp

theorem img_symm_img (N : Nat) (t : Equiv.Perm (Fin N)) (s : Finset (Fin N)) :
    ((s).image (fun p => t p)).image (fun a => t.symm a) = s := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, hAm, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hap⟩ := Finset.mem_image.mp hAm
    have hX : x = p := by
      rw [← hax, ← hap]
      exact Equiv.symm_apply_apply t p
    simpa [hX] using hp
  · intro hx
    have hTx : t x ∈ (s).image (fun p => t p) := Finset.mem_image_of_mem (fun p => t p) hx
    have hX : t.symm (t x) = x := Equiv.symm_apply_apply t x
    simpa [hX] using Finset.mem_image_of_mem (fun a => t.symm a) hTx

theorem fibTransitive_finset (N m : Nat) (hm : m ≤ N) (A B : Membership N m) :
    ∃ t : Equiv.Perm (Fin N), (A.1).image (fun a => t a) = B.1 := by
  obtain ⟨t, hTB⟩ := fibTransitive N m hm A B
  refine ⟨t, ?_⟩
  apply Finset.ext
  intro x
  rw [← Finset.mem_coe, ← Finset.mem_coe]
  -- now: x ∈ ↑((A.1).image (fun a => t a))  ↔  x ∈ ↑B.1   (both Set)
  have hL : ↑((A.1).image (fun a => t a)) = (⇑t) '' ↑A.1 := by
    have h1 : ↑((A.1).image (fun a => t a)) = (fun a => t a) '' ↑A.1 := by
      simpa using Finset.coe_image (fun a => t a) A.1
    have h2 : (fun a => t a) '' ↑A.1 = (⇑t) '' ↑A.1 := by
      apply Set.ext; intro y; simp only [Set.mem_image]
    simpa [h1, h2]
  rw [hL]
  simpa [hTB]

-- G2 / T1: the two membership fibers have equal size.
theorem fibersEqual (N m : Nat) (hm : m ≤ N) (A B : Membership N m) :
    Fintype.card (FibType N m hm A) = Fintype.card (FibType N m hm B) := by
  obtain ⟨t, hTB⟩ := fibTransitive_finset N m hm A B
  have hImg : ∀ (e : FibType N m hm A), (leftPositions N m hm).image (fun p => (e.1.trans t) p) = B.1 := by
    intro e
    have h1 := img_comp N t e.1 (leftPositions N m hm)
    simp only [h1, e.2, hTB]
  have hPre : ∀ (f : FibType N m hm B), (leftPositions N m hm).image (fun p => (f.1.trans t.symm) p) = A.1 := by
    intro f
    have h1 := img_comp N t.symm f.1 (leftPositions N m hm)
    have hBack : (B.1).image (fun a => t.symm a) = A.1 := by
      simpa [hTB] using img_symm_img N t A.1
    simp only [h1, f.2, hBack]
  let F : FibType N m hm A → FibType N m hm B := fun e => ⟨e.1.trans t, hImg e⟩
  exact Fintype.card_congr (Equiv.ofBijective F (by
    constructor
    · dsimp only [F]
      intro e₁ e₂ h
      refine Subtype.ext ?_
      apply Equiv.ext
      intro x
      have hE : e₁.1.trans t = e₂.1.trans t := by
        simpa using (congrArg (fun (z : FibType N m hm B) => z.1) h)
      have hE2 : (e₁.1.trans t) x = (e₂.1.trans t) x := by rw [hE]
      have h1 : (e₁.1.trans t) x = t (e₁.1 x) := Equiv.trans_apply e₁.1 t x
      have h2 : (e₂.1.trans t) x = t (e₂.1 x) := Equiv.trans_apply e₂.1 t x
      have hpx : t (e₁.1 x) = t (e₂.1 x) := by simpa [h1, h2] using hE2
      exact (by simpa [Equiv.symm_apply_apply] using (congrArg (fun w => t.symm w) hpx))
    · dsimp only [F]
      intro f
      have hX : (f.1.trans t.symm).trans t = f.1 := by
        ext x
        simp [Equiv.trans_apply, Equiv.apply_symm_apply]
      refine ⟨⟨f.1.trans t.symm, hPre f⟩, ?_⟩
      apply Subtype.ext
      exact hX))

-- G2 / T1: the image of the left pile under any permutation is again an
-- m-pile (it has m distinct cards), so it is a valid membership.
theorem leftImageIsMembership (N m : Nat) (hm : m ≤ N) (g : Equiv.Perm (Fin N)) :
    ((leftPositions N m hm).image (fun p => g p)).card = m := by
  have hInjOn : Set.InjOn (fun p => g p) (↑(leftPositions N m hm)) := by
    intro a ha b hb hab
    have h1 : g.symm (g a) = a := Equiv.symm_apply_apply g a
    have h2 : g.symm (g b) = b := Equiv.symm_apply_apply g b
    have h3 : g.symm (g a) = g.symm (g b) := congrArg (fun w => g.symm w) hab
    simpa [h1, h2] using h3
  rw [Finset.card_image_of_injOn hInjOn, leftPositions_card N m hm]

-- G2 / T1: a permutation sends the left pile to a UNIQUE pile, so it lies in
-- at most one membership fiber (the disjointness half of the partition).
theorem fibersUnique (N m : Nat) (hm : m ≤ N) (A B : Membership N m) (g : Equiv.Perm (Fin N)) :
    (leftPositions N m hm).image (fun p => g p) = A.1 →
    (leftPositions N m hm).image (fun p => g p) = B.1 →
    A.1 = B.1 := by
  intro hgA hgB
  simpa [hgA] using hgB

/-- The finset of decks whose left-pile image is exactly `A` — the fiber of `A`
  as an explicit finset of the full permutation space. -/
def fiberSet (N m : Nat) (hm : m ≤ N) (A : Membership N m) : Finset (Equiv.Perm (Fin N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun g => (leftPositions N m hm).image (fun p => g p) = A.1)

/-- `# fiberSet A = Fintype.card (FibType A)`: the finset of fiber decks and the
  fiber-deck subtype have the same size (the value projection is the bijection).
  First building block of the G2/T1 fiber count: it lets the later argument work
  with finsets (and `Finset.card_biUnion` for the partition) instead of the
  dependent `Fintype` sum. -/
theorem fiberSet_card (N m : Nat) (hm : m ≤ N) (A : Membership N m) :
    (fiberSet N m hm A).card = Fintype.card (FibType N m hm A) := by
  let f : FibType N m hm A → Equiv.Perm (Fin N) := fun x => (x : Equiv.Perm (Fin N))
  have hInj : Function.Injective f := by
    intro x y h
    exact Subtype.ext h
  have hImg : (Finset.univ : Finset (FibType N m hm A)).image f = fiberSet N m hm A := by
    dsimp only [fiberSet]
    apply Finset.ext
    intro g
    simp only [f, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, FibType]
    constructor
    · intro h
      rcases h with ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨g, h⟩, rfl⟩
  rw [← hImg, Finset.card_image_of_injective (Finset.univ : Finset (FibType N m hm A)) hInj]
  exact Finset.card_univ

/-- The fiber of a pile `S` (no membership wrapper): the decks imaging the left
  pile to exactly `S`. -/
def fiberSetPile (N m : Nat) (hm : m ≤ N) (S : Finset (Fin N)) : Finset (Equiv.Perm (Fin N)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun g => (leftPositions N m hm).image (fun p => g p) = S)

/-- `fiberSet A` is just the fiber of its pile `A.1`. -/
theorem fiberSet_eq_pile (N m : Nat) (hm : m ≤ N) (A : Membership N m) :
    fiberSet N m hm A = fiberSetPile N m hm A.1 := rfl

/-- The finset of all m-piles (the concrete index for the fiber partition). -/
def pileSet (N m : Nat) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard m

/-- Cover half of the fiber partition: the pile-fibers bi-union to the whole
  permutation space (each deck images the left pile to some m-pile). -/
theorem fiberCover (N m : Nat) (hm : m ≤ N) :
    (pileSet N m).biUnion (fun S => fiberSetPile N m hm S) =
    (Finset.univ : Finset (Equiv.Perm (Fin N))) := by
  ext g
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    have hS : ((leftPositions N m hm).image (fun p => g p)).card = m := leftImageIsMembership N m hm g
    have hIn : (leftPositions N m hm).image (fun p => g p) ∈ pileSet N m := by
      rw [pileSet, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hS⟩
    refine ⟨(leftPositions N m hm).image (fun p => g p), hIn, ?_⟩
    dsimp only [fiberSetPile]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Disjointness half of the fiber partition: distinct piles have disjoint
  fibers (a deck images the left pile to exactly one pile). -/
theorem fiberDisjoint (N m : Nat) (hm : m ≤ N) :
    (pileSet N m : Set (Finset (Fin N))).PairwiseDisjoint (fun S => fiberSetPile N m hm S) := by
  intros S1 _ S2 _ hne
  change Disjoint (fiberSetPile N m hm S1) (fiberSetPile N m hm S2)
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb heq
  dsimp only [fiberSetPile] at ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hIm : (leftPositions N m hm).image (fun p => a p) =
      (leftPositions N m hm).image (fun p => b p) :=
    congrArg (fun x : Equiv.Perm (Fin N) => (leftPositions N m hm).image (fun p => x p)) heq
  exact hne (by rw [← ha, ← hb]; exact hIm)

/-- The total permutation count is the sum of the pile-fiber counts: the
  pile-fibers partition the permutation space. -/
theorem fiberSum_eq_permCard (N m : Nat) (hm : m ≤ N) :
    Fintype.card (Equiv.Perm (Fin N)) = (pileSet N m).sum (fun S => (fiberSetPile N m hm S).card) := by
  have hDisj : (pileSet N m : Set (Finset (Fin N))).PairwiseDisjoint (fun S => fiberSetPile N m hm S) :=
    fiberDisjoint N m hm
  calc Fintype.card (Equiv.Perm (Fin N))
      = (Finset.univ : Finset (Equiv.Perm (Fin N))).card := Finset.card_univ
    _ = ((pileSet N m).biUnion (fun S => fiberSetPile N m hm S)).card :=
      congrArg Finset.card (fiberCover N m hm).symm
    _ = (pileSet N m).sum (fun S => (fiberSetPile N m hm S).card) := Finset.card_biUnion hDisj

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
-- DONE: fibTransitive, fibersEqual, leftImageIsMembership (cover half of the
--   partition), fibersUnique (disjointness half).
-- REMAINING — fiberCount : Fintype.card (FibType N m hm A) = Nat.factorial m * Nat.factorial (N - m).
--   Two assembly routes (all building blocks above + membershipCount + Fintype.card_perm are ready):
--   (a) Sigma route:  Perm ≃ Σ A : Membership, Fib A  via  fwd g = (sentPile g, g),  bwd s = s.2.1.
--       Injective via  congrArg (fun x => x.2.1);  surjective witness  s.2.1  with  Sigma.ext.
--       THEN  Fintype.card_sigma  ->  Finset.sum_const  ->  Nat.choose_mul_factorial_mul_factorial
--       ->  Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hm).
--       BLOCKED: the second subgoal of  Sigma.ext  is a  Subtype.cast  (≍ / HEq-based) of the
--       dependent  FibType  second component;  apply/refine Subtype.ext  will not unify with it.
--       The cast trivializes only if the  FibType  index is the  Finset  A.1  (not the membership A).
--   (b) Finset-fiber route (RECOMMENDED, no dependent types):  fiberSet A =
--       (univ : Finset (Equiv.Perm (Fin N))).filter (fun g => sentPile g = A).  Prove  #fiberSet A =
--       Fintype.card (FibType A)  (Finset.card_bij), that the  fiberSet  partition  (univ : Finset
--       (Equiv.Perm (Fin N)))  (from  leftImageIsMembership  +  fibersUnique,  via  Finset.card_biUnion
--       +  PairwiseDisjoint),  hence  Fintype.card (Equiv.Perm (Fin N)) =
--       (univ : Finset (Membership N m)).sum (fun A => #fiberSet A) = Nat.choose N m * #Fib(A),
--       then  Fintype.card_perm (Fin N) = Nat.factorial N  and  cancel  Nat.choose N m.
--   Gotchas:  Nat.factorial  (the  !  postfix does not parse in this module context);  explicit
--   N m hm params;  Fintype.card_sigma  bridges  ∑ i  <->  Finset.univ.sum  by  rfl;  the  Finset
--   sum -> product step needs  Finset.sum_const  +  Nat.smul_eq_mul;  cancellation uses
--   Nat.choose_pos hm  (0 < choose N m).
-- ============================================================================
end FiniteDeck
end Shufflemath
