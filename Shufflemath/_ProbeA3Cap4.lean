module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPerDeckKernel
public import Shufflemath.CommanderA3ExchangeCard
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open CommanderPermutation
open CommanderPhysicalExchange
open CommanderMembershipKernels
open CommanderMembershipExchange
open CommanderMarkedRightCount
open BernoulliLaplace
open Finset

/-! **f4 equinumerosity — Fintype route (74th session; the A3 count-bridge wall is CRACKED).**
    The A3 count-fiber equinumerosity, proved at the Fintype level without ever computing
    `Finset.univ` (no elaboration recursion).  Every count-fiber subtype gets an explicit
    `Fintype.subtype` instance:  the  s50 ×ˢ t49  fiber over its fiber Finset (membership
    reduces through  `Finset.mem_filter`/`Finset.mem_product`,  with  `s50`/`t49`  left
    `abbrev`-opaque so no  powerset  univ  is  computed),  and  each  exchangeChoice  fiber
    over  `(Finset.univ : Finset exchangeChoice).filter  Q`  (membership  reduces  through
    `Finset.mem_univ`,  not  the  univ  itself).  Then  `Fintype.card_congr`  (through  an
    explicit  subtype  `Equiv`),  `Fintype.subtype_card`  (the  s50 ×ˢ t49  fiber  card), and
    `_Probe47v.transitionNumerator_eq_fiberProduct`  (a  `Nat.choose`  count)  close  the
    bridge.  All  predicates  are  `abbrev`s  so  they  stay  decidable-  and  univ-transparent.

    This  breaks  the  wall  that  blocked  the  pure-Finset  `image`-push  route  (4b–4l):
    that  route  required  a  `Finset.ext`  pointwise  membership  on  the  `×ˢ`-of-powerset
    side  that  forced  the  univ  compute  (elaboration  recursion).  The  Fintype  route
    replaces  that  step  with  `Fintype.card_congr`  on  a  structural  `Equiv`,  which  never
    touches  the  univ. -/

/-- The  marked-count  predicate  on  a  flat  (L, R)  product  element  —  the  fiber  condition. -/
abbrev countPred (d : Deck) (c : Nat) (p : Finset (Fin 50) × Finset (Fin 49)) : Prop :=
  (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = c

/-- The  marked-count  predicate  on  an  exchange  choice  (via  its  (L, R)  projection). -/
abbrev Qex (d : Deck) (c : Nat) (j : exchangeChoice) : Prop :=
  countPred d c (j.1.1, j.2.1)

abbrev αtype := Finset (Fin 50) × Finset (Fin 49)

/-- A  (L, R)  element  of  the  count  fiber:  in  the  25-subset  families  and  satisfying
    the  marked-count  condition. -/
abbrev αpred (d : Deck) (c : Nat) (x : αtype) : Prop :=
  x.1 ∈ _Probe47v.s50 ∧ x.2 ∈ _Probe47v.t49 ∧ countPred d c x

/-- The  s50 ×ˢ t49  count  fiber  (a  subtype). -/
abbrev αfiber (d : Deck) (c : Nat) := {x : αtype // αpred d c x}
/-- The  exchangeChoice  marked-count  fiber  (a  subtype). -/
abbrev cntfiber (d : Deck) (c : Nat) := {j : exchangeChoice // Qex d c j}

/-- The  membershipCount  (pre-marked)  count  predicate  —  the  P  side  of  the  A3  bridge. -/
abbrev Pmem (d : Deck) (c : Nat) (j : exchangeChoice) : Prop :=
  membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c

/-- The  exchangeChoice  membershipCount  fiber  (a  subtype). -/
abbrev pfiber (d : Deck) (c : Nat) := {j : exchangeChoice // Pmem d c j}

/- The  membershipCount  fiber  as  a  Finset  (for  its  `Fintype.subtype`  instance). -/
abbrev pfilter (d : Deck) (c : Nat) : Finset exchangeChoice :=
  (Finset.univ : Finset exchangeChoice).filter (fun j => Pmem d c j)
/- The  marked-count  fiber  as  a  Finset  (for  its  `Fintype.subtype`  instance). -/
abbrev cnts (d : Deck) (c : Nat) : Finset exchangeChoice :=
  (Finset.univ : Finset exchangeChoice).filter (fun j => Qex d c j)
/- The  s50 ×ˢ t49  count  fiber  as  a  Finset  —  literally  the  47v  fiber  Finset  (same  `s50`,
    `t49`,  same  `countPred`),  so  its  card  is  `rfl`-equal  to  `_Probe47v`'s  (no  univ  unfold). -/
abbrev αs (d : Deck) (c : Nat) : Finset αtype :=
  (_Probe47v.s50 ×ˢ _Probe47v.t49).filter
    (fun x => (leftOriginalCount d - markedInLeft d x.1) + markedInRight d x.2 = c)

/- Membership  bridges  for  the  three  fiber  Finsets. -/
def αH (d : Deck) (c : Nat) : ∀ x, x ∈ αs d c ↔ αpred d c x := by
  intro x
  simp [αs, αpred, Finset.mem_filter, Finset.mem_product, and_assoc]

def cntH (d : Deck) (c : Nat) : ∀ j, j ∈ cnts d c ↔ Qex d c j := by
  intro j
  simp [Finset.mem_filter, Finset.mem_univ]

def pH (d : Deck) (c : Nat) : ∀ j, j ∈ pfilter d c ↔ Pmem d c j := by
  intro j
  simp [Finset.mem_filter, Finset.mem_univ]

/- Explicit  `Fintype.subtype`  instances  for  the  three  fiber  subtypes. -/
def fintypePFiber (d : Deck) (c : Nat) : Fintype (pfiber d c) :=
  Fintype.subtype (pfilter d c) (pH d c)

def fintypeCountFiber (d : Deck) (c : Nat) : Fintype (cntfiber d c) :=
  Fintype.subtype (cnts d c) (cntH d c)

def fintypeAlphaFiber (d : Deck) (c : Nat) : Fintype (αfiber d c) :=
  Fintype.subtype (αs d c) (αH d c)

/- Pointwise  P  <->  Q  (the  membershipCount  =  markedCount  identity). -/
theorem hPQ (d : Deck) (c : Nat) (j : exchangeChoice) : Pmem d c j ↔ Qex d c j := by
  dsimp only [Pmem, Qex, countPred]
  have h := count_exchangeChoice_eq_markedCount d j
  constructor
  · intro hc; rw [h] at hc; exact hc
  · intro hc; rw [← h] at hc; exact hc

/- The  P  <->  Q  subtype  equiv  (same  exchangeChoice,  the  predicate  flips). -/
def pQ_equiv (d : Deck) (c : Nat) : pfiber d c ≃ cntfiber d c := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro j; exact ⟨j.1, (hPQ d c j.1).mp j.2⟩
  · intro j; exact ⟨j.1, (hPQ d c j.1).mpr j.2⟩
  · intro j; apply Subtype.ext; rfl
  · intro j; apply Subtype.ext; rfl

/- The  projLR  equiv  between  the  exchangeChoice  marked-count  fiber  and  the  s50 ×ˢ t49
    count  fiber:  a  marked-count  choice  projects  to  a  count-fiber  (L, R)  pair  and  back. -/
def fiberEquiv (d : Deck) (c : Nat) : cntfiber d c ≃ αfiber d c := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · -- toFun:  exchange  choice  ->  (L, R)  count-fiber  element
    intro j
    exact ⟨⟨j.1.1.1, j.1.2.1⟩, ⟨j.1.1.2, j.1.2.2, by simpa [countPred, Qex] using j.2⟩⟩
  · -- invFun:  (L, R)  count-fiber  element  ->  exchange  choice
    intro x
    exact ⟨⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2.1⟩⟩, by simpa [countPred, Qex, αpred] using x.2.2.2⟩
  · -- leftInv
    intro j
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  · -- rightInv
    intro x
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-! **f4  —  the  exchangeChoice  marked-count  fiber  has  exactly  `transitionNumerator`
    elements.**  `Q`-fiber  =  s50 ×ˢ t49  count  fiber  (`Fintype.card_congr`  on  `fiberEquiv`),
    =  the  fiber  Finset  card  (`Fintype.subtype_card`),  =  `transitionNumerator`  (`_Probe47v`). -/
theorem probe_f4_equiv (d : Deck) (c : Nat) :
    @Fintype.card (cntfiber d c) (Fintype.subtype (cnts d c) (cntH d c)) =
      transitionNumerator 99 50 25 (leftOriginalCount d) c := by
  have h1 : @Fintype.card (cntfiber d c) (Fintype.subtype (cnts d c) (cntH d c)) =
      @Fintype.card (αfiber d c) (Fintype.subtype (αs d c) (αH d c)) :=
    @Fintype.card_congr (cntfiber d c) (αfiber d c) (Fintype.subtype (cnts d c) (cntH d c))
      (Fintype.subtype (αs d c) (αH d c)) (fiberEquiv d c)
  have h2 : @Fintype.card (αfiber d c) (Fintype.subtype (αs d c) (αH d c)) =
      Finset.card (αs d c) :=
    Fintype.subtype_card (αs d c) (αH d c)
  have h3 : Finset.card (αs d c) = transitionNumerator 99 50 25 (leftOriginalCount d) c :=
    (_Probe47v.transitionNumerator_eq_fiberProduct d c).symm
  exact (h1.trans h2).trans h3

/-! **THE  A3  COUNT-BRIDGE  (74th  session  —  f4  WALL  CRACKED).**  The  full  count-fiber
    equinumerosity:  the  membershipCount  count-fiber  of  exchange  choices  has  exactly
    `transitionNumerator`  elements.  Chain:  P-fiber  =  Q-fiber  (the  pointwise  `P<->Q`  equiv,
    `Fintype.card_congr`)  =  `transitionNumerator`  (`probe_f4_equiv`).  Explicit  `Fintype.subtype`
    instances  throughout,  so  it  composes  instance-transparently  and  never  computes  a  univ. -/
theorem a3_countBridge (d : Deck) (c : Nat) :
    @Fintype.card (pfiber d c) (Fintype.subtype (pfilter d c) (pH d c)) =
      transitionNumerator 99 50 25 (leftOriginalCount d) c := by
  have h1 : @Fintype.card (pfiber d c) (Fintype.subtype (pfilter d c) (pH d c)) =
      @Fintype.card (cntfiber d c) (Fintype.subtype (cnts d c) (cntH d c)) :=
    @Fintype.card_congr (pfiber d c) (cntfiber d c) (Fintype.subtype (pfilter d c) (pH d c))
      (Fintype.subtype (cnts d c) (cntH d c)) (pQ_equiv d c)
  have h2 : @Fintype.card (cntfiber d c) (Fintype.subtype (cnts d c) (cntH d c)) =
      transitionNumerator 99 50 25 (leftOriginalCount d) c :=
    probe_f4_equiv d c
  exact (h1.trans h2)

end Shufflemath
end
