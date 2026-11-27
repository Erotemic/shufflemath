module

public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.FiniteDeck.UniformTransport
public import Shufflemath.GSR
public import Shufflemath.Markov
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

variable {N p : Nat} {n : Fin p → Nat}

/-!
# Fixed-pair k-subset exchange kernel (G5capstone foundation — D1/D2)

Two distinct piles `i` and `j` exchange `k` cards each way: the `k` cards picked
from pile `i` move into pile `j` and vice versa.  The choice type is the
allocation-independent `Pick (s k)` — the `k`-subsets of `Fin s` — so the noise
`Pick (n i) k × Pick (n j) k` depends only on the capacities, never on the
allocation (the documented `G5capstone` D1 route).
-/

/-- The `k`-subsets of `Fin s` (an allocation-independent choice type). -/
def Pick (s k : Nat) : Type :=
  {u : Finset (Fin s) // u ∈ (Finset.univ : Finset (Fin s)).powersetCard k}

instance (s k : Nat) : Fintype (Pick s k) :=
  Fintype.subtype ((Finset.univ : Finset (Fin s)).powersetCard k) (fun _ => Iff.rfl)

theorem Pick.card (s k : Nat) : Fintype.card (Pick s k) = Nat.choose s k := by
  have hSub : Fintype.card (Pick s k) =
      ((Finset.univ : Finset (Fin s)).powersetCard k).card := by
    simp only [Pick]
    exact Fintype.card_coe _
  rw [hSub, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem Pick.nonempty (s k : Nat) (h : k ≤ s) : Nonempty (Pick s k) := by
  have hcard : k ≤ (Finset.univ : Finset (Fin s)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact h
  obtain ⟨U, hU⟩ := Finset.powersetCard_nonempty_of_le hcard
  exact ⟨⟨U, hU⟩⟩

/-- The fixed size-bijection for one pile: the subtype of the pile's cards. -/
noncomputable def pileEquivOf (A : Allocation N p n) (i : Fin p) :
    Equiv (Fin (n i)) {x : Fin N // x ∈ pileCard A i} := by
  have hcard : Fintype.card (Fin (n i)) =
      Fintype.card {x : Fin N // x ∈ pileCard A i} := by
    simp [Fintype.card_coe, pileCard_card]
  exact Fintype.equivOfCardEq hcard

/-- The card set of a pick, mapped through the pile bijection. -/
noncomputable def mapPick (A : Allocation N p n) (i : Fin p) (u : Pick (n i) k) : Finset (Fin N) :=
  u.1.image (fun x => (pileEquivOf A i x).val)

theorem mapPick_card (A : Allocation N p n) (i : Fin p) (u : Pick (n i) k) :
    (mapPick A i u).card = k := by
  have hinj : Set.InjOn (fun x => (pileEquivOf A i x).val) ↑u.1 := by
    intro a _ b _ hval
    have hsub : pileEquivOf A i a = pileEquivOf A i b := Subtype.ext hval
    exact (pileEquivOf A i).injective hsub
  have hcard : (mapPick A i u).card = u.1.card := Finset.card_image_of_injOn hinj
  rw [hcard, (Finset.mem_powersetCard.mp u.2).2]

theorem mapPick_subset (A : Allocation N p n) (i : Fin p) (u : Pick (n i) k) :
    mapPick A i u ⊆ pileCard A i := by
  intro x hx
  simp only [mapPick, Finset.mem_image] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact (pileEquivOf A i v).property

/-- **pickOfCardSet** — reverse direction of the mapPick bijection:
the pick whose card set is exactly `W` (a `k`-subset of the pile `i`'s cards). -/
noncomputable def pickOfCardSet {N p : Nat} {n : Fin p → Nat} (A : Allocation N p n)
    (i : Fin p) (W : Finset (Fin N)) (hsub : ∀ x ∈ W, x ∈ pileCard A i) :
    Pick (n i) W.card := by
  classical
  have hinj : Set.InjOn (fun p : {x : Fin N // x ∈ W} =>
      (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)
      ↑(Finset.univ : Finset {x : Fin N // x ∈ W}) := by
    intro a ha b hb heq
    have hval : (pileEquivOf A i).symm ⟨a.1, hsub a.1 a.2⟩ =
      (pileEquivOf A i).symm ⟨b.1, hsub b.1 b.2⟩ := heq
    have hvals := (pileEquivOf A i).symm.injective hval
    exact Subtype.ext (congrArg (fun y : ↥(pileCard A i) => y.val) hvals)
  have hcard' : ((Finset.univ : Finset {x : Fin N // x ∈ W}).image
      (fun p : {x : Fin N // x ∈ W} => (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)).card
      = W.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_coe]
  exact ⟨(Finset.univ : Finset {x : Fin N // x ∈ W}).image
    (fun p : {x : Fin N // x ∈ W} => (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard'⟩⟩

/-- **pickOfCardSet'** — the reverse direction with the card hypothesis instead of the card suffix:
     same underlying construction as `pickOfCardSet`, but the resulting pick is annotated with
     the known card `k` (via `hcard : W.card = k`) rather than `W.card`.  This restatement is what
     lets the full reverse identity `pickOfCardSet' A i (mapPick A i u) hsub (mapPick_card A i u) = u`
     land without the dependent-subtype cast friction (the `Equiv.cast` projection does not reduce
     definitionally — verified across several routes). -/
noncomputable def pickOfCardSet' {N p : Nat} {n : Fin p → Nat} (A : Allocation N p n)
    (i : Fin p) (W : Finset (Fin N)) (hsub : ∀ x ∈ W, x ∈ pileCard A i)
    (hcard : W.card = k) : Pick (n i) k := by
  classical
  have hinj : Set.InjOn (fun p : {x : Fin N // x ∈ W} =>
      (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)
      ↑(Finset.univ : Finset {x : Fin N // x ∈ W}) := by
    intro a ha b hb heq
    have hval : (pileEquivOf A i).symm ⟨a.1, hsub a.1 a.2⟩ =
      (pileEquivOf A i).symm ⟨b.1, hsub b.1 b.2⟩ := heq
    have hvals := (pileEquivOf A i).symm.injective hval
    exact Subtype.ext (congrArg (fun y : ↥(pileCard A i) => y.val) hvals)
  have hcard' : ((Finset.univ : Finset {x : Fin N // x ∈ W}).image
      (fun p : {x : Fin N // x ∈ W} => (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)).card
      = W.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_coe]
  exact ⟨(Finset.univ : Finset {x : Fin N // x ∈ W}).image
    (fun p : {x : Fin N // x ∈ W} => (pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard'.trans hcard⟩⟩

/-- **Full reverse identity (card-hypothesis form).**  Building the pick from the mapped card set
     recovers the original pick.  The underlying construction is the same as `pickOfCardSet`, but
     the card annotation comes from the card equation `hcard`, so the two sides are picks of the
     same type — no subtype cast is needed.  Proved via `ext` + the same image-image membership
     chain as the finset-level identity. -/
theorem pickOfCardSet'_mapPick {N p : Nat} {n : Fin p → Nat}
    (A : Allocation N p n) (i : Fin p) (k : Nat) (u : Pick (n i) k) :
    pickOfCardSet' A i (mapPick A i u) (fun x hx => mapPick_subset A i u hx)
      (mapPick_card A i u) = u := by
  apply Subtype.ext
  ext x
  simp only [pickOfCardSet', mapPick, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hy
    obtain ⟨p, hp, hyx⟩ := hy
    have hsymm : (pileEquivOf A i) ((pileEquivOf A i).symm ⟨p.1, mapPick_subset A i u p.2⟩)
        = (pileEquivOf A i) x := congrArg (pileEquivOf A i) hyx
    rw [Equiv.apply_symm_apply] at hsymm
    have hval : p.1 = ((pileEquivOf A i) x).val := by
      have h := congrArg (fun y : ↥(pileCard A i) => y.val) hsymm
      exact h
    have hmem : p.1 ∈ mapPick A i u := p.2
    simp only [mapPick, Finset.mem_image] at hmem
    obtain ⟨y, hyu, hyval⟩ := hmem
    have hvv : ((pileEquivOf A i) x).val = ((pileEquivOf A i) y).val := by
      rw [← hval]; exact hyval.symm
    have hxy : (pileEquivOf A i) x = (pileEquivOf A i) y := Subtype.ext hvv
    exact (pileEquivOf A i).injective hxy ▸ hyu
  · intro hx
    have hmem : (pileEquivOf A i x).val ∈ mapPick A i u :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    refine ⟨⟨(pileEquivOf A i x).val, hmem⟩, Finset.mem_univ _, ?_⟩
    have h2 : (⟨(pileEquivOf A i x).val, mapPick_subset A i u hmem⟩ : ↥(pileCard A i))
        = pileEquivOf A i x := Subtype.ext rfl
    rw [h2]
    exact Equiv.symm_apply_apply _ _

/-- **Round trip (card-hypothesis form).**  The card set of the pick built from `W` by
     `pickOfCardSet'` is `W` itself. -/
theorem mapPick_pickOfCardSet' {N p : Nat} {n : Fin p → Nat}
    (A : Allocation N p n) (i : Fin p) (W : Finset (Fin N))
    (hsub : ∀ x ∈ W, x ∈ pileCard A i) (hcard : W.card = k) :
    mapPick A i (pickOfCardSet' A i W hsub hcard) = W := by
  ext x
  simp only [mapPick, pickOfCardSet']
  rw [Finset.image_image]
  rw [Finset.image_congr (fun p _ => by
    change (pileEquivOf A i ((pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)).val = p.1
    rw [Equiv.apply_symm_apply, Subtype.coe_mk])]
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact p.2
  · intro hx
    refine Finset.mem_image.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    exact Finset.mem_univ _

/-- The pile card sets: the `k`-subsets of pile `i`'s cards. -/
def pileCardSet (A : Allocation N p n) (i : Fin p) (k : Nat) : Type :=
  {W : Finset (Fin N) // W ⊆ pileCard A i ∧ W.card = k}

/-- **The two-sided transport.**  `mapPick` (pick → card set) and
     `pickOfCardSet'` (card set → pick) are inverse bijections between the picks
     of pile `i` and its `k`-card subsets. -/
noncomputable def mapPickEquiv (A : Allocation N p n) (i : Fin p) (k : Nat) :
    Equiv (Pick (n i) k) (pileCardSet A i k) :=
  Equiv.mk
    (fun u : Pick (n i) k => (⟨mapPick A i u, mapPick_subset A i u, mapPick_card A i u⟩ : pileCardSet A i k))
    (fun W => pickOfCardSet' A i W.1 (fun x hx => W.2.1 hx) W.2.2)
    (fun u => pickOfCardSet'_mapPick A i k u)
    (fun W => by
      apply Subtype.ext
      exact mapPick_pickOfCardSet' A i W.1 (fun x hx => W.2.1 hx) W.2.2)

/-- **The two-sided transport is injective.**  The forward map (a pick's card set)
     determines the pick — the two-sided bijection's injectivity, derived directly
     from the `Equiv`. -/
theorem mapPickEquiv_injective {N p : Nat} {n : Fin p → Nat}
    (A : Allocation N p n) (i : Fin p) (k : Nat) :
    Function.Injective (mapPickEquiv A i k) :=
  Equiv.injective _

/-- **Card set determines the pick** (two-sided, by the bijection): two picks whose card sets
     are equal are equal. -/
theorem mapPick_eq_of_card_eq {N p : Nat} {n : Fin p → Nat}
    (A : Allocation N p n) (i : Fin p) (k : Nat)
    (u v : Pick (n i) k) (h : (mapPickEquiv A i k u).1 = (mapPickEquiv A i k v).1) :
    u = v := by
  have h2 : (mapPickEquiv A i k u) = (mapPickEquiv A i k v) := Subtype.ext h
  exact Equiv.injective (mapPickEquiv A i k) h2

/-- **Round trip** — the card set of a pick built from `W` is `W`. -/
theorem mapPick_pickOfCardSet {N p : Nat} {n : Fin p → Nat} (A : Allocation N p n)
    (i : Fin p) (W : Finset (Fin N)) (hsub : ∀ x ∈ W, x ∈ pileCard A i) :
    mapPick A i (pickOfCardSet A i W hsub) = W := by
  ext x
  simp only [mapPick, pickOfCardSet]
  rw [Finset.image_image]
  rw [Finset.image_congr (fun p _ => by
    change (pileEquivOf A i ((pileEquivOf A i).symm ⟨p.1, hsub p.1 p.2⟩)).val = p.1
    rw [Equiv.apply_symm_apply, Subtype.coe_mk])]
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact p.2
  · intro hx
    refine Finset.mem_image.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    exact Finset.mem_univ _

/-- **Injectivity** — the card map is injective on picks: two picks with the
    same card set are equal. -/
theorem mapPick_injective {N p : Nat} {n : Fin p → Nat} (A : Allocation N p n)
    (i : Fin p) (k : Nat) :
    Function.Injective (mapPick A i (k := k)) := by
  intro u v huhv
  apply Subtype.ext
  simp only [mapPick] at huhv
  have hinj' : Function.Injective (fun y : Fin (n i) => (pileEquivOf A i y).val) := by
    intro a b h
    have hval : pileEquivOf A i a = pileEquivOf A i b := Subtype.ext h
    exact (pileEquivOf A i).injective hval
  exact (Finset.image_inj hinj').mp huhv

/-- **Reverse of the round trip (finset level).**  The underlying index finset of the pick
    built from `mapPick A i u` is the original index finset `u.1`.  This is the
    finset-level content of the reverse identity `pickOfCardSet A i (mapPick A i u) hsub = u`
    (the full subtype-identity as stated stays parked — the card annotation
    `(mapPick A i u).card` of the constructed pick cannot be rewritten into the target
    `Pick (n i) k` type — the documented dependent-subtype friction); the underlying
    finset equality is the load-bearing half and is fully landed. -/
theorem pickOfCardSet_mapPick_underlying {N p : Nat} {n : Fin p → Nat}
    (A : Allocation N p n) (i : Fin p) (k : Nat) (u : Pick (n i) k) :
    (pickOfCardSet A i (mapPick A i u) (fun x hx => mapPick_subset A i u hx)).1 = u.1 := by
  ext x
  simp only [pickOfCardSet, mapPick, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hy
    obtain ⟨p, hp, hyx⟩ := hy
    have hsymm : (pileEquivOf A i) ((pileEquivOf A i).symm ⟨p.1, mapPick_subset A i u p.2⟩)
        = (pileEquivOf A i) x := congrArg (pileEquivOf A i) hyx
    rw [Equiv.apply_symm_apply] at hsymm
    have hval : p.1 = ((pileEquivOf A i) x).val := by
      have h := congrArg (fun y : ↥(pileCard A i) => y.val) hsymm
      exact h
    have hmem : p.1 ∈ mapPick A i u := p.2
    simp only [mapPick, Finset.mem_image] at hmem
    obtain ⟨y, hyu, hyval⟩ := hmem
    have hvv : ((pileEquivOf A i) x).val = ((pileEquivOf A i) y).val := by
      rw [← hval]; exact hyval.symm
    have hxy : (pileEquivOf A i) x = (pileEquivOf A i) y := Subtype.ext hvv
    exact (pileEquivOf A i).injective hxy ▸ hyu
  · intro hx
    have hmem : (pileEquivOf A i x).val ∈ mapPick A i u :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    refine ⟨⟨(pileEquivOf A i x).val, hmem⟩, Finset.mem_univ _, ?_⟩
    have h2 : (⟨(pileEquivOf A i x).val, mapPick_subset A i u hmem⟩ : ↥(pileCard A i))
        = pileEquivOf A i x := Subtype.ext rfl
    rw [h2]
    exact Equiv.symm_apply_apply _ _

/-- The raw owner function of the fixed-pair exchange: `U` (picked from pile `i`,
    mapped to cards) moves to pile `j`; `V` (picked from pile `j`) moves to pile
    `i`; every other card keeps its pile. -/
noncomputable def fixedPairOwner (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (z : Pick (n i) k × Pick (n j) k) (x : Fin N) : Fin p :=
  if x ∈ mapPick A i z.1 then j
  else if x ∈ mapPick A j z.2 then i
  else A.val x

/-! ### The pile sets of the exchanged allocation -/

/-- **Pile `i` after the exchange** — the old pile minus the picked cards,
    plus the picked card set coming in from pile `j`. -/
theorem fixedPairOwner_filter_i (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = i)) =
      (pileCard A i \ mapPick A i z.1) ∪ mapPick A j z.2 := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
    pileCard]
  constructor
  · intro hx
    dsimp only [fixedPairOwner] at hx
    by_cases hU : x ∈ mapPick A i z.1
    · rw [ite_eq_left hU] at hx
      exact (hij hx.symm).elim
    · rw [ite_eq_right hU] at hx
      by_cases hV : x ∈ mapPick A j z.2
      · exact Or.inr hV
      · rw [ite_eq_right hV] at hx
        exact Or.inl ⟨hx, hU⟩
  · intro hx
    obtain ⟨hval, hnot⟩ | hV := hx
    · by_cases hU : x ∈ mapPick A i z.1
      · exact absurd hU hnot
      · have hnotU : x ∉ mapPick A i z.1 := hU
        by_cases hV' : x ∈ mapPick A j z.2
        · dsimp only [fixedPairOwner]
          rw [ite_eq_right hnotU, ite_eq_left hV']
        · dsimp only [fixedPairOwner]
          rw [ite_eq_right hnotU, ite_eq_right hV']
          exact hval
    · have hdisj : x ∉ mapPick A i z.1 := by
        intro hU
        have hU' : x ∈ pileCard A i := mapPick_subset A i z.1 hU
        have hV' : x ∈ pileCard A j := mapPick_subset A j z.2 hV
        exact (Finset.disjoint_left.mp (pileCard_disjoint A hij) hU') hV'
      dsimp only [fixedPairOwner]
      rw [ite_eq_right hdisj, ite_eq_left hV]

/-- **Pile `j` after the exchange** — the old pile minus the picked cards,
    plus the picked card set coming in from pile `i`. -/
theorem fixedPairOwner_filter_j (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = j)) =
      (pileCard A j \ mapPick A j z.2) ∪ mapPick A i z.1 := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
    pileCard]
  constructor
  · intro hx
    dsimp only [fixedPairOwner] at hx
    by_cases hU : x ∈ mapPick A i z.1
    · rw [ite_eq_left hU] at hx
      exact Or.inr hU
    · rw [ite_eq_right hU] at hx
      by_cases hV : x ∈ mapPick A j z.2
      · rw [ite_eq_left hV] at hx
        exact (hij hx).elim
      · rw [ite_eq_right hV] at hx
        exact Or.inl ⟨hx, hV⟩
  · intro hx
    obtain ⟨hval, hnot⟩ | hU := hx
    · by_cases hU2 : x ∈ mapPick A i z.1
      · dsimp only [fixedPairOwner]
        rw [ite_eq_left hU2]
      · by_cases hV : x ∈ mapPick A j z.2
        · exact absurd hV hnot
        · dsimp only [fixedPairOwner]
          rw [ite_eq_right hU2, ite_eq_right hV]
          exact hval
    · have hdisj : x ∉ mapPick A j z.2 := by
        intro hV
        have hV' : x ∈ pileCard A j := mapPick_subset A j z.2 hV
        have hU' : x ∈ pileCard A i := mapPick_subset A i z.1 hU
        exact (Finset.disjoint_left.mp (pileCard_disjoint A hij) hU') hV'
      dsimp only [fixedPairOwner]
      rw [ite_eq_left (by assumption : x ∈ mapPick A i z.1)]

/-- **Pile `l` after the exchange** — unchanged for `l \notin {i, j}`. -/
theorem fixedPairOwner_filter_other (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (_hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k)
    (l : Fin p) (hli : l ≠ i) (hlj : l ≠ j) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = l)) =
      pileCard A l := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_filter, pileCard]
  constructor
  · intro hx
    have hU : x ∉ mapPick A i z.1 := by
      intro h
      dsimp only [fixedPairOwner] at hx
      rw [ite_eq_left h] at hx
      exact (hlj hx.symm).elim
    have hV : x ∉ mapPick A j z.2 := by
      intro h
      dsimp only [fixedPairOwner] at hx
      rw [ite_eq_right hU, ite_eq_left h] at hx
      exact (hli hx.symm).elim
    dsimp only [fixedPairOwner] at hx
    rw [ite_eq_right hU, ite_eq_right hV] at hx
    exact hx
  · intro hx
    have hsub : x ∈ pileCard A l := by simpa only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hval : A.val x = l := by
      simp only [pileCard, Finset.mem_filter, Finset.mem_univ, true_and] at hsub
      exact hsub
    have hU : x ∉ mapPick A i z.1 := by
      intro h
      have hU' : x ∈ pileCard A i := mapPick_subset A i z.1 h
      exact (Finset.disjoint_right.mp (pileCard_disjoint A hli) hU') hsub
    have hV : x ∉ mapPick A j z.2 := by
      intro h
      have hV' : x ∈ pileCard A j := mapPick_subset A j z.2 h
      exact (Finset.disjoint_right.mp (pileCard_disjoint A hlj) hV') hsub
    dsimp only [fixedPairOwner]
    rw [ite_eq_right hU, ite_eq_right hV]
    exact hval

/-! ### The exchanged allocation (well-defined capacities) -/

theorem fixedPairOwner_card_i (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = i)).card = n i := by
  have hsubU : mapPick A i z.1 ⊆ pileCard A i := mapPick_subset A i z.1
  have hsubV : mapPick A j z.2 ⊆ pileCard A j := mapPick_subset A j z.2
  have hUcard : (mapPick A i z.1).card = k := mapPick_card A i z.1
  have hVcard : (mapPick A j z.2).card = k := mapPick_card A j z.2
  have hDisj : Disjoint (pileCard A i \ mapPick A i z.1) (mapPick A j z.2) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    have hasub : a ∈ pileCard A i := (Finset.mem_sdiff.mp ha).1
    have hb' : b ∈ pileCard A j := mapPick_subset A j z.2 hb
    intro heq; subst heq
    exact (Finset.disjoint_left.mp (pileCard_disjoint A hij) hasub) hb'
  have hKle : k ≤ n i := by
    have hcard : (z.1.1).card = k := (Finset.mem_powersetCard.mp z.1.2).2
    have hcardU : (z.1.1).card ≤ (Finset.univ : Finset (Fin (n i))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at hcardU
    omega
  rw [fixedPairOwner_filter_i A i j k hij z, Finset.card_union_of_disjoint hDisj,
    Finset.card_sdiff_of_subset hsubU, pileCard_card, hUcard, hVcard]
  omega

theorem fixedPairOwner_card_j (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = j)).card = n j := by
  have hsubU : mapPick A i z.1 ⊆ pileCard A i := mapPick_subset A i z.1
  have hsubV : mapPick A j z.2 ⊆ pileCard A j := mapPick_subset A j z.2
  have hUcard : (mapPick A i z.1).card = k := mapPick_card A i z.1
  have hVcard : (mapPick A j z.2).card = k := mapPick_card A j z.2
  have hDisj : Disjoint (pileCard A j \ mapPick A j z.2) (mapPick A i z.1) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    have hasub : a ∈ pileCard A j := (Finset.mem_sdiff.mp ha).1
    have hb' : b ∈ pileCard A i := mapPick_subset A i z.1 hb
    intro heq; subst heq
    exact (Finset.disjoint_right.mp (pileCard_disjoint A hij) hasub) hb'
  have hKle : k ≤ n j := by
    have hcard : (z.2.1).card = k := (Finset.mem_powersetCard.mp z.2.2).2
    have hcardU : (z.2.1).card ≤ (Finset.univ : Finset (Fin (n j))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at hcardU
    omega
  rw [fixedPairOwner_filter_j A i j k hij z, Finset.card_union_of_disjoint hDisj,
    Finset.card_sdiff_of_subset hsubV, pileCard_card, hVcard, hUcard]
  omega

/-- The card counts are preserved by the fixed-pair exchange: every pile `l`
    keeps exactly `n l` cards. -/
theorem fixedPairOwner_card (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) (l : Fin p) :
    (Finset.univ.filter (fun x => fixedPairOwner A i j k z x = l)).card = n l := by
  by_cases hli : l = i
  · rw [hli]
    exact fixedPairOwner_card_i A i j k hij z
  · by_cases hlj : l = j
    · rw [hlj]
      exact fixedPairOwner_card_j A i j k hij z
    · have hli' : l ≠ i := hli
      have hlj' : l ≠ j := hlj
      rw [fixedPairOwner_filter_other A i j k hij z l hli' hlj', pileCard_card]

/-- The exchanged allocation: cards of `U` move into pile `j`, cards of `V`
    move into pile `i`; every other card keeps its pile. -/
noncomputable def fixedPairAlloc (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (z : Pick (n i) k × Pick (n j) k) : Allocation N p n :=
  ⟨fixedPairOwner A i j k z, fun l => fixedPairOwner_card A i j k hij z l⟩


/-- The X-side extraction: from the exchanged-allocation pile-`i` equality, recover the
    picked card sets. -/
theorem sdiff_out (X a : Finset (Fin N)) (hsub : a ⊆ X) :
    X \ (X \ a) = a := by
  rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hsub]

theorem fixedPairAlloc_injective (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) :
    Function.Injective (fun z : Pick (n i) k × Pick (n j) k =>
      fixedPairAlloc A i j k hij z) := by
  intro z1 z2 h
  have hval : fixedPairOwner A i j k z1 = fixedPairOwner A i j k z2 := by
    have h' := congrArg (fun a : Allocation N p n => a.val) h
    exact h'
  have hpile :
      (Finset.univ.filter (fun x => fixedPairOwner A i j k z1 x = i)) =
        (Finset.univ.filter (fun x => fixedPairOwner A i j k z2 x = i)) :=
    congrArg (fun w => Finset.univ.filter (fun x => w x = i)) hval
  rw [fixedPairOwner_filter_i A i j k hij z1, fixedPairOwner_filter_i A i j k hij z2] at hpile
  have hVeq : mapPick A j z1.2 = mapPick A j z2.2 := by
    ext x
    constructor
    · intro hx
      have this : x ∈ (pileCard A i \ mapPick A i z1.1) ∪ mapPick A j z1.2 :=
        Finset.mem_union.mpr (Or.inr hx)
      rw [hpile] at this
      simp only [Finset.mem_union, Finset.mem_sdiff] at this
      have hxnot : x ∉ pileCard A i :=
        Finset.disjoint_right.mp (pileCard_disjoint A hij) (mapPick_subset A j z1.2 hx)
      rcases this with ⟨hxX, -⟩ | hx2
      · exact absurd hxX hxnot
      · exact hx2
    · intro hx
      have this : x ∈ (pileCard A i \ mapPick A i z2.1) ∪ mapPick A j z2.2 :=
        Finset.mem_union.mpr (Or.inr hx)
      rw [hpile.symm] at this
      simp only [Finset.mem_union, Finset.mem_sdiff] at this
      have hxnot : x ∉ pileCard A i :=
        Finset.disjoint_right.mp (pileCard_disjoint A hij) (mapPick_subset A j z2.2 hx)
      rcases this with ⟨hxX, -⟩ | hx1
      · exact absurd hxX hxnot
      · exact hx1
  have hEq : pileCard A i \ mapPick A i z1.1 = pileCard A i \ mapPick A i z2.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxX, hxU₁⟩ := Finset.mem_sdiff.mp hx
      have this : x ∈ (pileCard A i \ mapPick A i z1.1) ∪ mapPick A j z1.2 :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxX, hxU₁⟩))
      rw [hpile] at this
      simp only [Finset.mem_union, Finset.mem_sdiff] at this
      rcases this with ⟨_, hxU₂⟩ | hx2
      · exact Finset.mem_sdiff.mpr ⟨hxX, hxU₂⟩
      · have hxY : x ∈ pileCard A j := mapPick_subset A j z2.2 hx2
        exact absurd hxX (Finset.disjoint_right.mp (pileCard_disjoint A hij) hxY)
    · intro hx
      obtain ⟨hxX, hxU₂⟩ := Finset.mem_sdiff.mp hx
      have this : x ∈ (pileCard A i \ mapPick A i z2.1) ∪ mapPick A j z2.2 :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxX, hxU₂⟩))
      rw [hpile.symm] at this
      simp only [Finset.mem_union, Finset.mem_sdiff] at this
      rcases this with ⟨_, hxU₁⟩ | hx1
      · exact Finset.mem_sdiff.mpr ⟨hxX, hxU₁⟩
      · have hxY : x ∈ pileCard A j := mapPick_subset A j z1.2 hx1
        exact absurd hxX (Finset.disjoint_right.mp (pileCard_disjoint A hij) hxY)
  have hU1e2 : mapPick A i z1.1 = mapPick A i z2.1 := by
    have h' : pileCard A i \ (pileCard A i \ mapPick A i z1.1) =
        pileCard A i \ (pileCard A i \ mapPick A i z2.1) := by rw [hEq]
    rw [sdiff_out _ _ (mapPick_subset A i z1.1), sdiff_out _ _ (mapPick_subset A i z2.1)] at h'
    exact h'
  have hinj : Function.Injective (fun x => (pileEquivOf A i x).val) := by
    intro a b hvalx
    have hsub : pileEquivOf A i a = pileEquivOf A i b := Subtype.ext hvalx
    exact (pileEquivOf A i).injective hsub
  have hUidx : z1.1.1 = z2.1.1 := (Finset.image_inj hinj).mp hU1e2
  have hH1 : z1.1 = z2.1 := Subtype.ext hUidx
  have hinjV : Function.Injective (fun x => (pileEquivOf A j x).val) := by
    intro a b hvalx
    have hsub : pileEquivOf A j a = pileEquivOf A j b := Subtype.ext hvalx
    exact (pileEquivOf A j).injective hsub
  have hVidx : z1.2.1 = z2.2.1 := (Finset.image_inj hinjV).mp hVeq
  have hH2 : z1.2 = z2.2 := Subtype.ext hVidx
  exact Prod.ext hH1 hH2

theorem fixedPair_nonempty (_A : Allocation N p n) (i j : Fin p) (k : Nat)
    (_hj : i ≠ j) (hk : k ≤ n i) (hk' : k ≤ n j) :
    Nonempty (Pick (n i) k × Pick (n j) k) := by
  have h1 : Nonempty (Pick (n i) k) := Pick.nonempty (n i) k hk
  have h2 : Nonempty (Pick (n j) k) := Pick.nonempty (n j) k hk'
  exact ⟨⟨Classical.choice h1, Classical.choice h2⟩⟩

/-- The fixed-pair exchange kernel — the normalized two-pile `k`-subset swap,
    as a pushforward of the uniform law over the (allocation-independent) noise
    through the exchanged-allocation map. -/
noncomputable def fixedPairKernel (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) :
    Dist (Allocation N p n) := by
  haveI : Nonempty (Pick (n i) k × Pick (n j) k) :=
    fixedPair_nonempty A i j k hij hki hkj
  exact (GSR.uniformDist (Pick (n i) k × Pick (n j) k)).map
    (fun z => fixedPairAlloc A i j k hij z)

/-- The mass of the fixed-pair kernel is the injective-map workhorse: `1 / card Noise`
    at the points in the range of the exchanged-allocation map, `0` elsewhere. -/
theorem fixedPairKernel_mass (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) (B : Allocation N p n) :
    Dist.mass (fixedPairKernel A i j k hij hki hkj) B =
      if ∃ z, fixedPairAlloc A i j k hij z = B then
        (Fintype.card (Pick (n i) k × Pick (n j) k) : Rat)⁻¹
      else 0 := by
  haveI : Nonempty (Pick (n i) k × Pick (n j) k) :=
    fixedPair_nonempty A i j k hij hki hkj
  show Dist.mass ((GSR.uniformDist (Pick (n i) k × Pick (n j) k)).map
    (fun z => fixedPairAlloc A i j k hij z)) B = _
  exact GSR.map_injective_uniform_mass _ (fixedPairAlloc_injective A i j k hij) B

/-- **The kernel is a genuine probability law** — total mass `1` (the row-sum
    over the whole allocation carrier is exactly `1`). -/
theorem fixedPairKernel_rowSum (A : Allocation N p n) (i j : Fin p) (k : Nat)
    (hij : i ≠ j) (hki : k ≤ n i) (hkj : k ≤ n j) :
    ∑ B : Allocation N p n, Dist.mass (fixedPairKernel A i j k hij hki hkj) B = 1 :=
  Dist.sum_mass _

end FiniteDeck

end Shufflemath
