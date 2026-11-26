module

public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.FiniteDeck.UniformExchange
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.GenericQuotient

/-! The generic reachable-quotient API: for any observation function `f : X → Y`,
the **observable range** is the finite? no — the reachability subtype
`ReachObs f = { y : Y // ∃ x, f x = y }`, carrying a genuine normalized quotient
kernel `quotient f K` over it.  Strong lumpability (`∀ x x', f x = f x' →
(K x).map f = (K x').map f`) yields a genuine, non-scalar kernel whose law is
exactly the pushforward of the raw kernel through `observe`.  All lemmas are
fully general: no Fintype, DecidableEq, Nonempty, or enumeration of the raw
observation type.  -/

/-- Only attainable observation values are states. -/
def ReachObs {X Y : Type*} (f : X → Y) := {y : Y // ∃ x : X, f x = y}

def observe {X Y : Type*} (f : X → Y) (x : X) : ReachObs f :=
  ⟨f x, ⟨x, rfl⟩⟩

noncomputable def representative {X Y : Type*} (f : X → Y)
    (y : ReachObs f) : X := Classical.choose y.property

theorem observe_representative {X Y : Type*} (f : X → Y) (y : ReachObs f) :
    observe f (representative f y) = y := by
  apply Subtype.ext
  exact Classical.choose_spec y.property

theorem observe_surjective {X Y : Type*} (f : X → Y) :
    Function.Surjective (observe f) := fun y =>
  ⟨representative f y, observe_representative f y⟩

/-- An explicit left inverse to the inclusion, defined only when there is a
reachable default. Off the range its value is immaterial. -/
noncomputable def retract {X Y : Type*} (f : X → Y) (d : ReachObs f)
    (y : Y) : ReachObs f := by
  classical
  exact if h : ∃ x : X, f x = y then ⟨y, h⟩ else d

theorem retract_val {X Y : Type*} (f : X → Y) (d z : ReachObs f) :
    retract f d z.val = z := by
  classical
  unfold retract
  exact dite_eq_left z.property

/-- Equality of pushforwards can be cancelled using a left inverse, without
point masses or a Fintype instance. -/
theorem cancel_map_leftInverse {X Y : Type*} (g : X → Y) (r : Y → X)
    (hr : Function.LeftInverse r g) (μ ν : Dist X)
    (h : μ.map g = ν.map g) : μ = ν := by
  have hm := congrArg (fun w : Dist Y => w.map r) h
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map] at hm
  have hi : (fun x => r (g x)) = id := funext hr
  rw [hi, Convexity.StdSimplex.map_id, Convexity.StdSimplex.map_id] at hm
  exact hm

/-- Raw equality of observed rows implies equality on the reachable carrier.
The essential bridge from a strong-lumpability proof to a genuine quotient. -/
theorem reachable_map_eq {X Y : Type*} (f : X → Y) (μ ν : Dist X)
    (d : ReachObs f) (h : μ.map f = ν.map f) :
    μ.map (observe f) = ν.map (observe f) := by
  apply cancel_map_leftInverse (fun z : ReachObs f => z.val) (retract f d)
    (retract_val f d)
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  exact h

/-- A normalized quotient row by representative choice. -/
noncomputable def quotient {X Y : Type*} (f : X → Y) (K : FiniteKernel X X) :
    FiniteKernel (ReachObs f) (ReachObs f) :=
  fun y => (K (representative f y)).map (observe f)

theorem quotient_at {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f) (x : X) :
    quotient f K (observe f x) = (K x).map (observe f) := by
  apply reachable_map_eq f _ _ (observe f x)
  exact hl _ _ (Classical.choose_spec (observe f x).property)

/-- The actual commuting square, not a row-sum identity. -/
theorem quotient_intertwines {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f) :
    FiniteKernel.comp K (FiniteKernel.deterministic (observe f)) =
      FiniteKernel.comp (FiniteKernel.deterministic (observe f)) (quotient f K) := by
  funext x
  change FiniteKernel.apply (K x) (FiniteKernel.deterministic (observe f)) =
    FiniteKernel.apply (Dist.pointMass (observe f x)) (quotient f K)
  rw [GSR.apply_deterministic, FiniteKernel.apply_pointMass]
  exact (quotient_at f K hl x).symm

/-- Generic commuting-square transport, no finite sums. -/
theorem apply_observation {X Y : Type*} (f : X → Y)
    (K : FiniteKernel X X) (Q : FiniteKernel Y Y)
    (h : FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) (μ : Dist X) :
    (FiniteKernel.apply μ K).map f = FiniteKernel.apply (μ.map f) Q := by
  calc
    _ = FiniteKernel.apply (FiniteKernel.apply μ K) (FiniteKernel.deterministic f) :=
      (GSR.apply_deterministic _ _).symm
    _ = FiniteKernel.apply μ (FiniteKernel.comp K (FiniteKernel.deterministic f)) :=
      FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply μ (FiniteKernel.comp (FiniteKernel.deterministic f) Q) := by rw [h]
    _ = FiniteKernel.apply (FiniteKernel.apply μ (FiniteKernel.deterministic f)) Q :=
      (FiniteKernel.apply_comp _ _ _).symm
    _ = _ := by rw [GSR.apply_deterministic]

theorem quotient_stationary {X Y : Type*} (f : X → Y) (K : FiniteKernel X X)
    (hl : ∀ x x', f x = f x' → (K x).map f = (K x').map f)
    (μ : Dist X) (hμ : FiniteKernel.apply μ K = μ) :
    FiniteKernel.apply (μ.map (observe f)) (quotient f K) = μ.map (observe f) := by
  have h := apply_observation (observe f) K (quotient f K)
    (quotient_intertwines f K hl) μ
  rw [hμ] at h
  exact h.symm

/-- Exact simulation of all `t` steps, not just one step or stationary starts. -/
theorem run_observation {X Y : Type*} (f : X → Y)
    (K : FiniteKernel X X) (Q : FiniteKernel Y Y)
    (h : FiniteKernel.comp K (FiniteKernel.deterministic f) =
      FiniteKernel.comp (FiniteKernel.deterministic f) Q) (t : Nat) (μ : Dist X) :
    (FiniteKernel.run K t μ).map f = FiniteKernel.run Q t (μ.map f) := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
    rw [FiniteKernel.run_rec_eq, FiniteKernel.run_rec_eq,
      ih, apply_observation f K Q h]

end Shufflemath.GenericQuotient
namespace Shufflemath.GenericPairObservation

/-! Generic pair-observation laws: the law of a pair of independent uniform
draws depends only on the fiber counts of the two coordinate maps.  These are
the pair-reparametrization tools behind the strong-lumpability argument. -/

variable {X Y Z : Type*} [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq Y]

/-- Uniform pushforward via cardinality, valid even when `Y` is not a Fintype. -/
theorem uniformMap_mass_card (f : X → Y) (y : Y) :
    Dist.mass ((GSR.uniformDist X).map f) y =
      ((Finset.univ.filter (fun x : X => f x = y)).card : Rat) /
        (Fintype.card X : Rat) := by
  classical
  rw [GSR.map_uniform_mass, ← Finset.mul_sum]
  have hfilter : (Finset.univ : Finset X).filter (fun x => y = f x) =
      Finset.univ.filter (fun x => f x = y) := by
    ext x
    simp [eq_comm]
  have hcount : (∑ x : X, if y = f x then (1 : Rat) else 0) =
      ((Finset.univ.filter (fun x : X => f x = y)).card : Rat) := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [hcount, div_eq_mul_inv, mul_comm]

/-- Cardinality of the fiber of a pair observation splits as the product of the
fiber cardinalities of the coordinates. -/
theorem pairFiber_card (f : X → Y) (z : Y × Y) :
    ((Finset.univ : Finset (X × X)).filter
      (fun ab => (f ab.1, f ab.2) = z)).card =
      (Finset.univ.filter (fun a : X => f a = z.1)).card *
      (Finset.univ.filter (fun b : X => f b = z.2)).card := by
  classical
  have h : (Finset.univ : Finset (X × X)).filter
      (fun ab => (f ab.1, f ab.2) = z) =
      (Finset.univ.filter (fun a : X => f a = z.1)) ×ˢ
      (Finset.univ.filter (fun b : X => f b = z.2)) := by
    ext ab
    rcases ab with ⟨a, b⟩
    rcases z with ⟨u, v⟩
    simp [Finset.mem_product]
  rw [h, Finset.card_product]

/-- Generic deterministic factorization of a uniform experiment. -/
theorem uniformPair_factor (f : X → Y) (step : Y × Y → Z) (out : X × X → Z)
    (h : ∀ ab, out ab = step (f ab.1, f ab.2)) :
    (GSR.uniformDist (X × X)).map out =
      ((GSR.uniformDist (X × X)).map (fun ab => (f ab.1, f ab.2))).map step := by
  rw [Convexity.StdSimplex.map_map]
  apply congrArg _ (funext fun ab => h ab)

/-- The law of a pair of observed cells depends only on their cardinalities. -/
theorem uniformPairMap_eq_of_counts (f g : X → Y)
    (h : ∀ y : Y, (Finset.univ.filter (fun x : X => f x = y)).card =
      (Finset.univ.filter (fun x : X => g x = y)).card) :
    (GSR.uniformDist (X × X)).map (fun ab => (f ab.1, f ab.2)) =
      (GSR.uniformDist (X × X)).map (fun ab => (g ab.1, g ab.2)) := by
  classical
  ext z
  change Dist.mass ((GSR.uniformDist (X × X)).map
      (fun ab => (f ab.1, f ab.2))) z =
    Dist.mass ((GSR.uniformDist (X × X)).map
      (fun ab => (g ab.1, g ab.2))) z
  rw [uniformMap_mass_card, uniformMap_mass_card, pairFiber_card, pairFiber_card,
    h z.1, h z.2]

end Shufflemath.GenericPairObservation
namespace Shufflemath.FiniteDeck

/-! The signed histogram on the allocation carrier and its strong lumpability
under the uniform-transposition kernel.  The signed form is what makes the
update identity underflow-free; it is not itself the state carrier. -/

variable {N p c : Nat} {n : Fin p → Nat}

/-- The canonical finite card-cell map on the owner carrier. -/
def ownerCell (color : Fin N → Fin c) (A : Allocation N p n) (x : Fin N) : Fin p × Fin c :=
  (A.val x, color x)

def ownerHist (color : Fin N → Fin c) (A : Allocation N p n) (z : Fin p × Fin c) : Nat :=
  (Finset.univ.filter (fun x : Fin N => ownerCell color A x = z)).card

/-- The histogram is a signed function in the update lemma only. It need not
be used as the finite histogram carrier. `Dist.map` accepts arbitrary types. -/
def signedHist (color : Fin N → Fin c) (A : Allocation N p n) (z : Fin p × Fin c) : Int :=
  Int.ofNat (ownerHist color A z)

def unitCell (z u : Fin p × Fin c) : Int := if z = u then 1 else 0

/-- Simultaneous signed update: handles even `a = b`, same-pile, and same-color
cases without Nat subtraction underflow. -/
def signedSwapStep (H : (Fin p × Fin c) → Int) (uv : (Fin p × Fin c) × (Fin p × Fin c))
    (z : Fin p × Fin c) : Int :=
  H z - unitCell z uv.1 - unitCell z uv.2 +
    unitCell z (uv.2.1, uv.1.2) + unitCell z (uv.1.1, uv.2.2)

/-- The elementary signed update identity: a two-card swap moves the histogram
in signed coordinates by the four-cell swap rectangle, in a difference-free
(subtractable) form that remains meaningful even when `a = b`.  This replaces
the Nat-level subtraction that would underflow for overlapping cells. -/
theorem signedHist_swap_update (color : Fin N → Fin c)
    (A : Allocation N p n) (a b : Fin N) :
    signedHist color (swapPiles A a b) = signedSwapStep (signedHist color A)
      (ownerCell color A a, ownerCell color A b) := by
  classical
  funext z
  -- step 1: a histogram is a sum of unit cells over cards
  have hsum : ∀ (C : Allocation N p n),
      signedHist color C z = ∑ x : Fin N, unitCell z (ownerCell color C x) := by
    intro C
    show Int.ofNat ((Finset.univ.filter (fun x => (C.val x, color x) = z)).card) = _
    rw [Int.ofNat_eq_natCast, Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    simp only [unitCell, ownerCell, eq_comm]
    rfl
  -- step 2: on the deleted-pair core S, the cells are unchanged
  have hac : ∀ x ∈ (Finset.univ.erase a).erase b,
      ownerCell color (swapPiles A a b) x = ownerCell color A x := by
    intro x hx
    have h1 := Finset.mem_erase.mp hx
    have hxb : x ≠ b := h1.1
    have hxa : x ≠ a := (Finset.mem_erase.mp h1.2).1
    simp [ownerCell, swapPiles, swapOwner, hxa, hxb]
  -- step 3: rewrite both sides via the deleted-pair core S
  simp only [signedSwapStep, unitCell]
  rw [hsum (swapPiles A a b)]
  rw [hsum A]
  by_cases hab : a = b
  · -- identity swap
    subst hab
    have hid : swapPiles A a a = A := by
      apply Subtype.ext
      funext x
      by_cases hx : x = a
      · subst hx
        simp [swapPiles, swapOwner]
      · simp [swapPiles, swapOwner, hx]
    rw [hid]
    simp only [unitCell]
    ring
  · -- general case: a ≠ b
    set S := (Finset.univ.erase a).erase b with hS
    have huniv : (∑ x : Fin N, unitCell z (ownerCell color (swapPiles A a b) x)) =
        (∑ x ∈ S, unitCell z (ownerCell color (swapPiles A a b) x)) +
          unitCell z (ownerCell color (swapPiles A a b) b) +
          unitCell z (ownerCell color (swapPiles A a b) a) := by
      have h1 : (∑ x : Fin N, unitCell z (ownerCell color (swapPiles A a b) x)) =
          ∑ x ∈ Finset.univ.erase a, unitCell z (ownerCell color (swapPiles A a b) x) +
            unitCell z (ownerCell color (swapPiles A a b) a) := by
        rw [← Finset.sum_erase_add _ _ (show a ∈ Finset.univ by simp)]
      have h2mem : b ∈ Finset.univ.erase a := by
        simp only [Finset.mem_erase, Finset.mem_univ]
        exact ⟨Ne.symm hab, trivial⟩
      have h2 : (∑ x ∈ Finset.univ.erase a, unitCell z (ownerCell color (swapPiles A a b) x)) =
          ∑ x ∈ S, unitCell z (ownerCell color (swapPiles A a b) x) +
            unitCell z (ownerCell color (swapPiles A a b) b) := by
        rw [← Finset.sum_erase_add _ _ h2mem]
      rw [h1, h2]
    have hcelA : ownerCell color (swapPiles A a b) a = (A.val b, color a) := by
      simp only [ownerCell, swapPiles, swapOwner]
      split_ifs <;> simp_all
    have hcelB : ownerCell color (swapPiles A a b) b = (A.val a, color b) := by
      simp only [ownerCell, swapPiles, swapOwner]
      split_ifs <;> simp_all
    rw [huniv, hcelA, hcelB]
    have hS : (∑ x ∈ S, unitCell z (ownerCell color (swapPiles A a b) x)) =
        ∑ x ∈ S, unitCell z (ownerCell color A x) :=
      Finset.sum_congr rfl (fun x hx => by rw [hac x hx])
    rw [hS]
    have hunivA : (∑ x : Fin N, unitCell z (ownerCell color A x)) =
        (∑ x ∈ S, unitCell z (ownerCell color A x)) +
          unitCell z (ownerCell color A b) +
          unitCell z (ownerCell color A a) := by
      have h1 : (∑ x : Fin N, unitCell z (ownerCell color A x)) =
          ∑ x ∈ Finset.univ.erase a, unitCell z (ownerCell color A x) +
            unitCell z (ownerCell color A a) := by
        rw [← Finset.sum_erase_add _ _ (show a ∈ Finset.univ by simp)]
      have h2mem : b ∈ Finset.univ.erase a := by
        simp only [Finset.mem_erase, Finset.mem_univ]
        exact ⟨Ne.symm hab, trivial⟩
      have h2 : (∑ x ∈ Finset.univ.erase a, unitCell z (ownerCell color A x)) =
          ∑ x ∈ S, unitCell z (ownerCell color A x) +
            unitCell z (ownerCell color A b) := by
        rw [← Finset.sum_erase_add _ _ h2mem]
      rw [h1, h2]
    rw [hunivA]
    simp only [unitCell, ownerCell]
    simp [add_assoc, add_comm, add_left_comm]
    rfl

/-- Once the elementary signed update identity is proved, this gives strong
lumpability of the raw signed observation by a two-line pushforward argument. -/
theorem signedHist_lumpable_of_update (hN : 0 < N) (color : Fin N → Fin c)
    (hstep : ∀ (A : Allocation N p n) (a b : Fin N),
      signedHist color (swapPiles A a b) = signedSwapStep (signedHist color A)
        (ownerCell color A a, ownerCell color A b))
    (A B : Allocation N p n) (h : ownerHist color A = ownerHist color B) :
    (swapKernel hN A).map (signedHist color) = (swapKernel hN B).map (signedHist color) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hpair := GenericPairObservation.uniformPairMap_eq_of_counts (ownerCell color A) (ownerCell color B)
    (fun z => congrFun h z)
  have hH : signedHist color A = signedHist color B := by
    funext z
    exact congrArg Int.ofNat (congrFun h z)
  change ((GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => swapPiles A ab.1 ab.2)).map (signedHist color) =
    ((GSR.uniformDist (Fin N × Fin N)).map
      (fun ab => swapPiles B ab.1 ab.2)).map (signedHist color)
  simp only [Convexity.StdSimplex.map_map]
  have hA := GenericPairObservation.uniformPair_factor (ownerCell color A) (signedSwapStep (signedHist color A))
    (fun ab => signedHist color (swapPiles A ab.1 ab.2)) (fun ab => hstep A ab.1 ab.2)
  have hB := GenericPairObservation.uniformPair_factor (ownerCell color B) (signedSwapStep (signedHist color B))
    (fun ab => signedHist color (swapPiles B ab.1 ab.2)) (fun ab => hstep B ab.1 ab.2)
  change (GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => signedHist color (swapPiles A ab.1 ab.2)) =
    (GSR.uniformDist (Fin N × Fin N)).map
      (fun ab => signedHist color (swapPiles B ab.1 ab.2))
  rw [hA, hB, hpair, hH]

/-- Strong lumpability of the raw signed observation, with the elementary
update identity discharged by `signedHist_swap_update`. -/
theorem signedHist_lumpable (hN : 0 < N) (color : Fin N → Fin c)
    (A B : Allocation N p n) (h : ownerHist color A = ownerHist color B) :
    (swapKernel hN A).map (signedHist color) = (swapKernel hN B).map (signedHist color) :=
  signedHist_lumpable_of_update hN color
    (fun A a b => signedHist_swap_update color A a b) A B h

/-- Strong lumpability in the pointwise form used by the quotient instantiation:
equal signed histograms give equal pushforwards. -/
theorem signedHist_strong_lumpable (hN : 0 < N) (color : Fin N → Fin c)
    (A B : Allocation N p n) (h : signedHist color A = signedHist color B) :
    (swapKernel hN A).map (signedHist color) = (swapKernel hN B).map (signedHist color) := by
  apply signedHist_lumpable hN color A B
  funext z
  exact Int.ofNat.inj (congrFun h z)

/-- The reachable-quotient observation of the signed histogram: the observation
takes a signed histogram to its subtype inhabitant. -/
def histObserve (N p c : Nat) (n : Fin p → Nat) (color : Fin N → Fin c) :
    Allocation N p n →
      @GenericQuotient.ReachObs (Allocation N p n) (Fin p × Fin c → Int) (signedHist color) :=
  GenericQuotient.observe (signedHist color)

/-- The normalized reachable histogram quotient kernel: the genuine
two-pile/two-color/multi-pile transposition kernel of the finite-deck campaign. -/
noncomputable def histSwapKernel (N p c : Nat) (n : Fin p → Nat) (hN : 0 < N) (color : Fin N → Fin c) :
    FiniteKernel (@GenericQuotient.ReachObs (Allocation N p n) (Fin p × Fin c → Int) (signedHist color))
      (@GenericQuotient.ReachObs (Allocation N p n) (Fin p × Fin c → Int) (signedHist color)) :=
  GenericQuotient.quotient (signedHist color) (swapKernel hN)

/-- The uniform-transposition kernel with its allocation domain pinned as a
`FiniteKernel` for statements. -/
noncomputable def swapKernel_kernel (N p : Nat) (n : Fin p → Nat) (hN : 0 < N) :
    FiniteKernel (Allocation N p n) (Allocation N p n) :=
  swapKernel hN

/-- The stationary pushforward of the uniform allocation law. -/
noncomputable def histStationary (N p c : Nat) (n : Fin p → Nat)
    (hsum : (∑ i, n i) = N) (color : Fin N → Fin c) :
    Dist (@GenericQuotient.ReachObs (Allocation N p n) (Fin p × Fin c → Int) (signedHist color)) :=
  (uniformAlloc hsum).map (histObserve N p c n color)

/-- **M1a export — the commuting square**: the transposition kernel pushed
through the histogram observation equals the observation pushed through the
quotient kernel. -/
theorem histSwap_comp_square {N p c : Nat} {n : Fin p → Nat} (hN : 0 < N) (color : Fin N → Fin c) :
    FiniteKernel.comp (swapKernel_kernel N p n hN)
        (FiniteKernel.deterministic (histObserve N p c n color)) =
      FiniteKernel.comp (FiniteKernel.deterministic (histObserve N p c n color))
        (histSwapKernel N p c n hN color) := by
  exact GenericQuotient.quotient_intertwines (signedHist color) (swapKernel hN)
    (fun A B h => signedHist_strong_lumpable hN color A B h)

/-- **M1 export — stationarity of the quotient pushforward**: the uniform
allocation law pushed through `histObserve` is stationary under
`histSwapKernel`. -/
theorem histStationary_stationary {N p c : Nat} {n : Fin p → Nat} (hN : 0 < N)
    (hsum : (∑ i, n i) = N) (color : Fin N → Fin c) :
    FiniteKernel.apply (histStationary N p c n hsum color) (histSwapKernel N p c n hN color) =
      histStationary N p c n hsum color := by
  have hμ : FiniteKernel.apply (uniformAlloc hsum) (swapKernel hN) = uniformAlloc hsum := by
    ext A
    exact swapKernel_uniformStationary hN hsum A
  exact GenericQuotient.quotient_stationary (signedHist color) (swapKernel hN)
    (fun A B h => signedHist_strong_lumpable hN color A B h) (uniformAlloc hsum) hμ

/-- **M1 export — all-step projection**: the histogram law after `t` steps of
the transposition kernel is the `t`-step run of the quotient kernel from the
projected start. -/
theorem histObserve_run {N p c : Nat} {n : Fin p → Nat} (hN : 0 < N) (color : Fin N → Fin c)
    (t : Nat) (μ : Dist (Allocation N p n)) :
    (FiniteKernel.run (swapKernel_kernel N p n hN) t μ).map (histObserve N p c n color) =
      FiniteKernel.run (histSwapKernel N p c n hN color) t (μ.map (histObserve N p c n color)) := by
  exact GenericQuotient.run_observation (histObserve N p c n color) (swapKernel hN)
    (histSwapKernel N p c n hN color) (histSwap_comp_square hN color) t μ

end Shufflemath.FiniteDeck
