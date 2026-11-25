module

public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.Histograms
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Finset Finset.Nat

/-!
# Multi-pile pairwise exchange count (the general-`k` B4, allocation level)

The two-pile B4 (`SubsetExchange.subsetExchangeCount`) exchanges `k` cards
between the left pile `S` (size `m`) and the right pile `T` (the complement,
size `N - m`): the reachable allocations are in bijection with
`(k-subsets of S) × (k-subsets of T)`, so there are `choose m k * choose
(N-m) k` of them.

This module generalizes that to an **arbitrary pair of disjoint piles** `A`
(size `m`) and `B` (size `n`) of an `N`-card deck — the allocation-level
pairwise exchange that appears in the multi-pile `G5` program.  A `k`-exchange
between them swaps `k` cards each way: given `oi ⊆ A` (the cards leaving `A`)
and `oj ⊆ B` (the cards leaving `B`), the exchanged pair is

    `exchangePair A B oi oj = ((A \ oi) ∪ oj, (B \ oj) ∪ oi)`.

The reconstruction identity `A \ ((A \ oi) ∪ oj) = oi` (and symmetrically for
`B`), which uses only the disjointness of the two piles, makes the exchange
map **injective** on `(k-subsets of A) × (k-subsets of B)`: the exchanged pair
determines `(oi, oj)` by `oi = A \ A'`, `oj = B \ B'`.  Hence the number of
reachable exchanged pairs is the count of the domain,

    `choose m k * choose n k` — the allocation-level denominator of the T5
    histogram kernel.

The two-pile result is the special case `B = univ \ A` (`n = N - m`).  The
proof is structural (membership `ext` + `tauto` over disjointness); there is no
`native_decide` and no enumeration of the full deck.

## Involutivity / reversibility (proven here)
`exchangePair_involution` shows the exchange is an involution up to the swap of
the two leaving sets: applying it again to the exchanged pair, with the leaving
sets `(oj, oi)` (the cards each pile *borrowed*), recovers the original pair:
`exchangePair ((A\oi)∪oj) ((B\oj)∪oi) oj oi = (A, B)`.  Hence the allocation-level
pairwise-exchange kernel is a **reversible symmetric kernel** — the T5 "unique
`(out_i, out_j)` argument" at the allocation level (roadmap T5 line 167).

That statement is made precise by `exchangeTargets_symmetric` (the kernel-symmetry
section at the end of this file): the swap `(oi, oj) ↦ (oj, oi)` is a bijection
from the set of `k`-exchanges `(A,B) → (A',B')` to the set `(A',B') → (A,B)`, so
the two **counts are equal** — the kernel is symmetric, and on a finite allocation
space the uniform distribution is stationary under a single exchange move.  The
proof reuses the involutivity above plus the disjoint-pile membership bookkeeping
(no `native_decide`, no deck enumeration).

## Remaining next step (documented, not yet proven here)
- **Histogram lumping:** lump the allocation chain over colors to obtain the
  multivariate-hypergeometric T5 transition and prove its stationarity (note the
  color-level kernel's reversibility is *not* a formal consequence of the
  allocation-level symmetry above — lumping can break it); then the `G5capstone`
  multi-pile exchange kernel-equality (the full headline).
-/

/-- The exchanged pair: `oi` cards leave `A` (entering `B`), `oj` cards leave
    `B` (entering `A`). -/
def exchangePair (N : Nat) (A B oi oj : Finset (Fin N)) :
    Finset (Fin N) × Finset (Fin N) := ((A \ oi) ∪ oj, (B \ oj) ∪ oi)

/-- A card that lies in both `A` and `B` is impossible when they are disjoint. -/
private theorem disjoint_notMem {N : Nat} (A B : Finset (Fin N)) (hDis : Disjoint A B)
    (y : Fin N) : y ∈ A → y ∈ B → False := by
  rintro hyA hyB
  have hInt : y ∈ A ∩ B := Finset.mem_inter.mpr ⟨hyA, hyB⟩
  simpa [Finset.disjoint_iff_inter_eq_empty.mp hDis] using hInt

/-- Finset subset gives the corresponding membership implication. -/
private theorem subset_mem {N : Nat} (A B : Finset (Fin N)) (h : A ⊆ B) (y : Fin N) :
    y ∈ A → y ∈ B := by
  intro hy
  rw [Finset.subset_def] at h
  simpa using h (by simpa using hy)

/-- The exchange map is injective on `(k-subsets of A) × (k-subsets of B)`:
    the exchanged pair determines `(oi, oj)` by `oi = A \ A'`, `oj = B \ B'`. -/
theorem exchangePair_injOn (N : Nat) (A B : Finset (Fin N)) (k : Nat)
    (hDis : Disjoint A B) (s : Finset (Finset (Fin N) × Finset (Fin N)))
    (hs : s ⊆ Finset.powersetCard k A ×ˢ Finset.powersetCard k B) :
    Set.InjOn (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2) s := by
  intro p hp q hq heq
  have hpm : p ∈ Finset.powersetCard k A ×ˢ Finset.powersetCard k B := hs hp
  have hqm : q ∈ Finset.powersetCard k A ×ˢ Finset.powersetCard k B := hs hq
  have hpA : p.1 ⊆ A := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hpm).1)).1
  have hpB : p.2 ⊆ B := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hpm).2)).1
  have hqA : q.1 ⊆ A := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hqm).1)).1
  have hqB : q.2 ⊆ B := (Finset.mem_powersetCard.mp ((Finset.mem_product.mp hqm).2)).1
  -- Membership implications (the leaving subsets sit inside their piles).
  have hpa (y : Fin N) : y ∈ p.1 → y ∈ A := subset_mem p.1 A hpA y
  have hpb (y : Fin N) : y ∈ p.2 → y ∈ B := subset_mem p.2 B hpB y
  have hqa (y : Fin N) : y ∈ q.1 → y ∈ A := subset_mem q.1 A hqA y
  have hqb (y : Fin N) : y ∈ q.2 → y ∈ B := subset_mem q.2 B hqB y
  -- Reconstruction: a leaving subset is recovered by removing the exchanged pile.
  have hP1 : A \ ((A \ p.1) ∪ p.2) = p.1 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ p.1 → y ∈ A := hpa y
    have h2 : y ∈ p.1 → y ∉ p.2 := fun hy hb => disjoint_notMem A B hDis y (hpa y hy) (hpb y hb)
    tauto
  have hP2 : B \ ((B \ p.2) ∪ p.1) = p.2 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ p.2 → y ∈ B := hpb y
    have h2 : y ∈ p.2 → y ∉ p.1 := fun hy hb => disjoint_notMem A B hDis y (hpa y hb) (hpb y hy)
    tauto
  have hQ1 : A \ ((A \ q.1) ∪ q.2) = q.1 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ q.1 → y ∈ A := hqa y
    have h2 : y ∈ q.1 → y ∉ q.2 := fun hy hb => disjoint_notMem A B hDis y (hqa y hy) (hqb y hb)
    tauto
  have hQ2 : B \ ((B \ q.2) ∪ q.1) = q.2 := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have h1 : y ∈ q.2 → y ∈ B := hqb y
    have h2 : y ∈ q.2 → y ∉ q.1 := fun hy hb => disjoint_notMem A B hDis y (hqa y hb) (hqb y hy)
    tauto
  have hAeq : (A \ p.1) ∪ p.2 = (A \ q.1) ∪ q.2 := congrArg Prod.fst heq
  have hBeq : (B \ p.2) ∪ p.1 = (B \ q.2) ∪ q.1 := congrArg Prod.snd heq
  refine Prod.ext ?_ ?_
  · calc
      p.1 = A \ ((A \ p.1) ∪ p.2) := hP1.symm
      _ = A \ ((A \ q.1) ∪ q.2) := by rw [hAeq]
      _ = q.1 := hQ1
  · calc
      p.2 = B \ ((B \ p.2) ∪ p.1) := hP2.symm
      _ = B \ ((B \ q.2) ∪ q.1) := by rw [hBeq]
      _ = q.2 := hQ2

/-- The pairwise multi-pile exchange count: from disjoint piles `A` (size `m`)
    and `B` (size `n`), a `k`-exchange between them reaches exactly
    `choose m k * choose n k` pairs.  This is the allocation-level denominator
    of the T5 histogram kernel and the multi-pile generalization of
    `SubsetExchange.subsetExchangeCount` (which is the case `B = univ \ A`). -/
theorem pairwiseExchangeCount (N m n k : Nat)
    (A B : Finset (Fin N)) (hA : A.card = m) (hB : B.card = n) (hDis : Disjoint A B) :
    (Finset.image (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2)
        (Finset.powersetCard k A ×ˢ Finset.powersetCard k B)).card =
      Nat.choose m k * Nat.choose n k := by
  let D := Finset.powersetCard k A ×ˢ Finset.powersetCard k B
  have hInj : Set.InjOn (fun (p : Finset (Fin N) × Finset (Fin N)) => exchangePair N A B p.1 p.2) D :=
    exchangePair_injOn N A B k hDis D (Finset.Subset.refl _)
  rw [Finset.card_image_of_injOn hInj, Finset.card_product,
      Finset.card_powersetCard, hA, Finset.card_powersetCard, hB]

/-!
## B4 involutivity / reversibility (allocation-level, T5 "reversible symmetric
kernel")

The `k`-exchange is an involution up to the swap of the two leaving sets:
applied again to the exchanged pair, with the leaving sets `(oj, oi)` (the
cards each pile *borrowed*), it recovers the original pair.  Hence the
allocation-level pairwise-exchange kernel is a **reversible symmetric kernel** —
the T5 "unique `(out_i, out_j)` argument" (roadmap T5 line 167), at the
allocation level.
-/
theorem exchangePair_involution (N : Nat) (A B oi oj : Finset (Fin N))
    (hOi : oi ⊆ A) (hOj : oj ⊆ B) (hDis : Disjoint A B) :
    exchangePair N ((A \ oi) ∪ oj) ((B \ oj) ∪ oi) oj oi = (A, B) := by
  refine Prod.ext ?_ ?_
  · -- ((A \ oi) ∪ oj) \ oj ∪ oi = A
    ext x
    simp only [exchangePair, Finset.mem_sdiff, Finset.mem_union]
    have fOiA : x ∈ oi → x ∈ A := subset_mem oi A hOi x
    have fOjB : x ∈ oj → x ∈ B := subset_mem oj B hOj x
    have fAnotOj : x ∈ A → x ∉ oj := by rintro hA hOjX; exact disjoint_notMem A B hDis x hA (fOjB hOjX)
    have fOjnotA : x ∈ oj → x ∉ A := by rintro hOjX hA; exact disjoint_notMem A B hDis x hA (fOjB hOjX)
    have fOjnotOi : x ∈ oj → x ∉ oi := by rintro hOjX hOiX; exact disjoint_notMem A B hDis x (fOiA hOiX) (fOjB hOjX)
    have fOinotOj : x ∈ oi → x ∉ oj := by rintro hOiX hOjX; exact disjoint_notMem A B hDis x (fOiA hOiX) (fOjB hOjX)
    tauto
  · -- ((B \ oj) ∪ oi) \ oi ∪ oj = B
    ext x
    simp only [exchangePair, Finset.mem_sdiff, Finset.mem_union]
    have fOiA : x ∈ oi → x ∈ A := subset_mem oi A hOi x
    have fOjB : x ∈ oj → x ∈ B := subset_mem oj B hOj x
    have fBnotOi : x ∈ B → x ∉ oi := by rintro hB hOiX; exact disjoint_notMem A B hDis x (fOiA hOiX) hB
    have fOinotB : x ∈ oi → x ∉ B := by rintro hOiX hB; exact disjoint_notMem A B hDis x (fOiA hOiX) hB
    have fOinotOj : x ∈ oi → x ∉ oj := by rintro hOiX hOjX; exact disjoint_notMem A B hDis x (fOiA hOiX) (fOjB hOjX)
    have fOjnotOi : x ∈ oj → x ∉ oi := by rintro hOjX hOiX; exact disjoint_notMem A B hDis x (fOiA hOiX) (fOjB hOjX)
    tauto

/-!
## Histogram-level transition denominator (multivariate Vandermonde)

`histAllocSum xs k` sums, over every allocation of `k` cards across the category
counts `xs = [X_0, …, X_{c-1}]`, the product of the per-category binomial
coefficients `∏_i C(X_i, a_i)` — the *numerator* of the T5 histogram-level
transition (lumping the allocation chain).  The theorem below is the
**multivariate Vandermonde identity** `histAllocSum xs k = C(∑ xs, k)`, proved
by induction on `xs` with each cons-step an application of Mathlib's 2-way
`Nat.add_choose_eq`; the antidiagonal form is used throughout, so no
range↔antidiagonal transport is required.
-/
def histAllocSum (xs : List Nat) (k : Nat) : Nat :=
  match xs with
  | [] => if k = 0 then 1 else 0
  | a :: rest => ∑ ij ∈ antidiagonal k, (a.choose ij.1) * histAllocSum rest (ij.2)

theorem histAllocSum_choose (xs : List Nat) :
    ∀ k, histAllocSum xs k = Nat.choose (xs.sum) k := by
  induction xs with
  | nil =>
      intro k
      simp only [histAllocSum]
      cases k <;> simp
  | cons x xs ih =>
      intro k
      rw [histAllocSum, List.sum_cons, Nat.add_choose_eq]
      refine Finset.sum_congr rfl fun ij _ ↦ ?_
      rw [ih (ij.2)]

/-!
## Kernel symmetry: the exchange is a reversible symmetric kernel (allocation level)

`exchangeTargets N A B A' B' k` is the set of `(oi, oj)` `k`-exchanges — `oi` a
`k`-subset of `A`, `oj` a `k`-subset of `B` — that land exactly on the target
`(A', B')`.  `exchangeTargets_symmetric` shows that swapping the two leaving
sets is a **bijection** from the exchanges `(A,B) → (A',B')` to the exchanges
`(A',B') → (A,B)`, so the two counts are equal: the allocation-level pairwise
exchange is a reversible symmetric kernel (the T5 "unique `(out_i, out_j)`
argument").  On a finite allocation space this is the foundation for the
uniform distribution being stationary under a single exchange move.  The proof
is purely combinatorial — it reuses the involutivity (`exchangePair_involution`)
and the injectivity structure of the exchange map; there is no `native_decide`
and no enumeration of the full deck.
-/

/-- The set of `(oi, oj)` `k`-exchanges from allocation `(A, B)` that reach the
    target `(A', B')`: `oi` a `k`-subset of `A`, `oj` a `k`-subset of `B`, and
    `exchangePair A B oi oj = (A', B')`. -/
def exchangeTargets (N : Nat) (A B A' B' : Finset (Fin N)) (k : Nat) :
    Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Finset.powersetCard k A ×ˢ Finset.powersetCard k B).filter
    (fun p => exchangePair N A B p.1 p.2 = (A', B'))

private def swapP (N : Nat) (p : Finset (Fin N) × Finset (Fin N)) : Finset (Fin N) × Finset (Fin N) :=
  (p.2, p.1)

/- A `k`-exchange landing on `(X', Y')` from `(X, Y)`, read backwards with the
   leaving sets swapped, lands back on `(X, Y)`: the swap maps the forward
   target-set into the backward one. -/
private theorem swapLands (N : Nat) (X Y X' Y' : Finset (Fin N)) (k : Nat) (hXY : Disjoint X Y)
    (p : Finset (Fin N) × Finset (Fin N))
    (hp : p ∈ (Finset.powersetCard k X ×ˢ Finset.powersetCard k Y).filter
        (fun q => exchangePair N X Y q.1 q.2 = (X', Y'))) :
    swapP N p ∈ (Finset.powersetCard k X' ×ˢ Finset.powersetCard k Y').filter
      (fun q => exchangePair N X' Y' q.1 q.2 = (X, Y)) := by
  have hDom : p ∈ Finset.powersetCard k X ×ˢ Finset.powersetCard k Y := Finset.mem_filter.mp hp |>.1
  have hoiX : p.1 ⊆ X := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hDom).1).1
  have hojY : p.2 ⊆ Y := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hDom).2).1
  have hoiK : p.1.card = k := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hDom).1).2
  have hojK : p.2.card = k := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hDom).2).2
  have hEq : exchangePair N X Y p.1 p.2 = (X', Y') := Finset.mem_filter.mp hp |>.2
  have hX' : X' = (X \ p.1) ∪ p.2 := by
    simpa [exchangePair, Prod.fst] using (congrArg Prod.fst hEq).symm
  have hY' : Y' = (Y \ p.2) ∪ p.1 := by
    simpa [exchangePair, Prod.snd] using (congrArg Prod.snd hEq).symm
  have hp2in : p.2 ∈ Finset.powersetCard k X' := by
    rw [hX']
    refine Finset.mem_powersetCard.mpr ⟨?_, hojK⟩
    intro y hy
    exact Finset.mem_union.mpr (Or.inr hy)
  have hp1in : p.1 ∈ Finset.powersetCard k Y' := by
    rw [hY']
    refine Finset.mem_powersetCard.mpr ⟨?_, hoiK⟩
    intro y hy
    exact Finset.mem_union.mpr (Or.inr hy)
  have hDom' : swapP N p ∈ Finset.powersetCard k X' ×ˢ Finset.powersetCard k Y' := by
    simp only [swapP]
    exact Finset.mem_product.mpr ⟨hp2in, hp1in⟩
  have hLands : exchangePair N X' Y' (swapP N p).1 (swapP N p).2 = (X, Y) := by
    simp only [swapP]
    simpa only [hX', hY'] using exchangePair_involution N X Y p.1 p.2 hoiX hojY hXY
  exact Finset.mem_filter.mpr ⟨hDom', hLands⟩

/- The kernel is symmetric: swapping the leaving sets is a bijection from the
   set of `k`-exchanges `(A,B) → (A',B')` to the set `(A',B') → (A,B)`, so the
   two counts are equal. -/
theorem exchangeTargets_symmetric (N : Nat) (A B A' B' : Finset (Fin N)) (k : Nat)
    (hDis : Disjoint A B) (hDis' : Disjoint A' B') :
    (exchangeTargets N A B A' B' k).card = (exchangeTargets N A' B' A B k).card := by
  let S  := exchangeTargets N A B A' B' k
  let S' := exchangeTargets N A' B' A B k
  let f (p : Finset (Fin N) × Finset (Fin N)) := swapP N p
  have hFwd (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ S) : f p ∈ S' :=
    swapLands N A B A' B' k hDis p hp
  have hFwd' (p : Finset (Fin N) × Finset (Fin N)) (hp : p ∈ S') : f p ∈ S :=
    swapLands N A' B' A B k hDis' p hp
  have hInv (p : Finset (Fin N) × Finset (Fin N)) : f (f p) = p := by simp [f, swapP]
  have hInj : Set.InjOn f (S : Set _) := by
    intro p _ q _ heq
    have h1 : p.1 = q.1 := by simpa [f, swapP] using congrArg Prod.snd heq
    have h2 : p.2 = q.2 := by simpa [f, swapP] using congrArg Prod.fst heq
    exact Prod.ext h1 h2
  have hImg : S.image f = S' := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
      exact hFwd m hm
    · intro hp'
      have hmid : f p ∈ S := hFwd' p hp'
      exact Finset.mem_image.mpr ⟨f p, hmid, hInv p⟩
  have h1 : S.card = (S.image f).card := (Finset.card_image_of_injOn hInj).symm
  have h2 : (S.image f).card = S'.card := by rw [hImg]
  exact h1.trans h2

/-! ## T5: the two-pile exchange kernel is well-defined on the allocation-level
     state space, and its normalized transition is stochastic

A pile with per-category card counts `X : List Nat` exchanges `k` cards with a
second pile `Y`: the transition is counted by the product of the two piles' 
per-category Vandermonde totals (`histAllocSum`), and the sum of the numerator
over every valid pair of category selections is the *universal* denominator
`choose (∑ X) k * choose (∑ Y) k` (independent of the category counts).  Hence
the normalized two-pile T5 transition kernel has row-sum `1` for every 
histogram — it is a valid Markov transition and a stationary-law candidate.

The **well-definedness** step is the `FiberMP` state space below: a `k`-
exchange of two disjoint `(m,n)`-piles lands again on a disjoint `(m,n)`-pair
(`exchangePairFiberMP`), so the exchange kernel is a self-map of the
allocation-level state space.  This is the prerequisite for the remaining T5 
steps — the column-sum / reversibility (Fintype-walled) and the 
multivariate-hypergeometric stationary law. -/

/- The allocation-level state space of the two-pile exchange: the disjoint
    `(m,n)`-pairs of piles in an `N`-card deck. -/
def FiberMP (N m n : Nat) : Type :=
  { p : Finset (Fin N) × Finset (Fin N) // p.1.card = m ∧ p.2.card = n ∧ Disjoint p.1 p.2 }

/- **Well-definedness on the state space.**  A `k`-exchange of two disjoint
    `(m,n)`-piles lands again on a disjoint `(m,n)`-pair: the exchanged pair 
    preserves both pile sizes (the moved `k`-subsets have equal cardinality) and 
    disjointness (each card stays in exactly one of the two piles), so the 
    exchange kernel maps the allocation-level state space to itself. -/
theorem exchangePairFiberMP (N m n k : Nat) (A' B' oi oj : Finset (Fin N))
    (hA' : A'.card = m) (hB' : B'.card = n) (hDis' : Disjoint A' B')
    (hOi : oi ⊆ A') (hoiK : oi.card = k) (hOj : oj ⊆ B') (hojK : oj.card = k) :
    ∃ p : FiberMP N m n, p.val = exchangePair N A' B' oi oj := by
  have hKm : k ≤ m := by rw [←hoiK, ←hA']; exact Finset.card_le_card hOi
  have hKn : k ≤ n := by rw [←hojK, ←hB']; exact Finset.card_le_card hOj
  have hOiA : Disjoint (A' \ oi) oj := by
    rw [Finset.disjoint_iff_ne]
    intro x hxA' y hxo hxy
    have hxInA : x ∈ A' := (Finset.mem_sdiff.mp hxA').1
    have hyInB : y ∈ B' := hOj hxo
    exact (Finset.disjoint_iff_ne.mp hDis' x hxInA y hyInB) hxy
  have hOjB : Disjoint (B' \ oj) oi := by
    rw [Finset.disjoint_iff_ne]
    intro x hxB' y hyo hxy
    have hyInA : y ∈ A' := hOi hyo
    have hxInB : x ∈ B' := (Finset.mem_sdiff.mp hxB').1
    exact (Finset.disjoint_iff_ne.mp hDis' y hyInA x hxInB) hxy.symm
  have hSizeA : (exchangePair N A' B' oi oj).1.card = m := by
    rw [exchangePair, Finset.card_union_of_disjoint hOiA, Finset.card_sdiff_of_subset hOi, hA', hoiK]
    omega
  have hSizeB : (exchangePair N A' B' oi oj).2.card = n := by
    rw [exchangePair, Finset.card_union_of_disjoint hOjB, Finset.card_sdiff_of_subset hOj, hB', hojK]
    omega
  have hDis : Disjoint (exchangePair N A' B' oi oj).1 (exchangePair N A' B' oi oj).2 := by
    rw [exchangePair, Finset.disjoint_iff_ne]
    intro x hxA y hyB hxy
    have hxAu : x ∈ A' \ oi ∨ x ∈ oj := Finset.mem_union.mp hxA
    have hyBu : x ∈ B' \ oj ∨ x ∈ oi := by rw [←hxy] at hyB; exact Finset.mem_union.mp hyB
    rcases hxAu with hxA'' | hOjx
    · rcases hyBu with hyB'' | hyO
      · -- x in A'\oi and x in B'\oj  =>  x in A' and x in B'
        have hxA' : x ∈ A' := (Finset.mem_sdiff.mp hxA'').1
        have hyB' : x ∈ B' := (Finset.mem_sdiff.mp hyB'').1
        exact (Finset.disjoint_iff_ne.mp hDis' x hxA' x hyB') rfl
      · -- x in A'\oi and x in oi  =>  contradiction (x notin oi)
        exact (Finset.mem_sdiff.mp hxA'').2 (hyO)
    · rcases hyBu with hyB'' | hyO
      · -- x in oj and x in B'\oj  =>  contradiction (x notin oj)
        exact (Finset.mem_sdiff.mp hyB'').2 (hOjx)
      · -- x in oj and x in oi  =>  x in B' and x in A'
        have hyInB : x ∈ B' := hOj hOjx
        have hxInA : x ∈ A' := hOi hyO
        exact (Finset.disjoint_iff_ne.mp hDis' x hxInA x hyInB) rfl
  exact ⟨⟨exchangePair N A' B' oi oj, ⟨hSizeA, hSizeB, hDis⟩⟩, rfl⟩

/-!
# T5: the two-pile multi-category transition is stochastic

A pile with per-category card counts `X : List Nat` exchanges `k` cards with a
second pile `Y`: the transition is counted by the product of the two piles' 
per-category Vandermonde totals (`histAllocSum`), and the sum of the numerator
over every valid pair of category selections is the *universal* denominator
`choose (∑ X) k * choose (∑ Y) k` (independent of the category counts).  Hence
the normalized two-pile T5 transition kernel has row-sum `1` for every 
histogram — it is a valid Markov transition and a stationary-law candidate.  The
column-sum / reversibility (allocation-level fiber symmetry, Fintype-walled) and
the multivariate-hypergeometric stationary law are the remaining T5 steps.
-/ 

/-- **T5 two-pile transition stochasticity (numerator form).**  The total
    number of category-counted `k`-exchanges between two piles whose per-category
    counts are `X`, `Y` equals the universal denominator `choose (∑ X) k ·
    choose (∑ Y) k`: summing the multivariate-hypergeometric numerator over every
    valid category selection from each pile recovers the total number of ways to
    choose `k` cards from each pile. -/
theorem twoPileExchangeTotal (X Y : List Nat) (k : Nat) :
    histAllocSum X k * histAllocSum Y k =
      Nat.choose (X.sum) k * Nat.choose (Y.sum) k := by
  rw [histAllocSum_choose X k, histAllocSum_choose Y k]

/-- **T5 two-pile transition stochasticity (normalized form).**  For legal `k`
    (`k ≤` each pile size), the normalized two-pile T5 transition kernel has
    row-sum `1`: the transition mass out of any histogram is exactly the
    denominator, so the normalized row-sum is `1` (universal, independent of the
    category counts). -/
theorem twoPileTransitionStochastic (X Y : List Nat) (k : Nat)
    (hX : k ≤ X.sum) (hY : k ≤ Y.sum) :
    ((histAllocSum X k * histAllocSum Y k : Nat) : Rat) /
      ((Nat.choose (X.sum) k * Nat.choose (Y.sum) k : Nat) : Rat) = 1 := by
  have hnz : (Nat.choose (X.sum) k * Nat.choose (Y.sum) k : Nat) ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.ne_of_gt (Nat.choose_pos hX))
      (Nat.ne_of_gt (Nat.choose_pos hY))
  rw [twoPileExchangeTotal X Y k]
  field_simp [hnz]

end FiniteDeck
end Shufflemath
