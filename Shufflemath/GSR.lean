module

public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace GSR

/-!
# Inverse GSR shuffles via finite labels

An `a`-shuffle assigns a label in `Fin a` independently to each card, then
stably groups the deck by that label. The deck is a list of distinct card
identities (`Fin n`); the operation also makes sense on arbitrary lists,
which makes the stable-grouping identity simple to state.

Two consecutive label sortings, with alphabet sizes `a` and `b`, agree
pointwise with a single lexicographic sorting by a pair of labels
`(major : Fin b, minor : Fin a)`. The pair alphabet has `b*a` entries.
This identity does not depend on uniformity: it applies to biased and
correlated *per-round* label laws too, provided the two rounds are sampled
independently. The shuffle kernel below specializes it to uniform labels.

This file does not yet identify `Fin b × Fin a` with `Fin (b*a)` or derive the
Bayer--Diaconis rising-sequence probability formula. It does prove the
product-*alphabet* composition law, including the probabilistic kernels.
-/

variable {α : Type*}

/-- Sort in ascending label order, preserving the order of equal-label cards.
Every bucket filters the **original** deck, so the grouping is stable. -/
def stableBuckets (a : Nat) (labels : α → Fin a) (deck : List α) : List α :=
  (List.range a).flatMap fun i =>
    deck.filter (fun card => (labels card).val == i)

/-- Lexicographic stable grouping by `(major, minor)` labels. -/
def lexBuckets (a b : Nat) (minor : α → Fin a) (major : α → Fin b)
    (deck : List α) : List α :=
  (List.range b).flatMap fun j =>
    (List.range a).flatMap fun i =>
      deck.filter (fun card => ((major card).val == j) && ((minor card).val == i))

theorem filter_flatMap {β : Type*} (p : α → Bool)
    (xs : List β) (f : β → List α) :
    (xs.flatMap f).filter p = xs.flatMap (fun x => (f x).filter p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap, Function.comp_def]

theorem filter_filter (p q : α → Bool) (xs : List α) :
    (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih]

/-- Deterministic product-label composition. The later label is the major
key, and the earlier label is the minor key. Swapping these is wrong for
inverse riffles; this theorem fixes the convention in Lean. -/
theorem stableBuckets_comp (a b : Nat) (minor : α → Fin a) (major : α → Fin b)
    (deck : List α) :
    stableBuckets b major (stableBuckets a minor deck) =
      lexBuckets a b minor major deck := by
  simp [stableBuckets, lexBuckets, filter_flatMap]

/-- The lexicographically ordered pair alphabet has `b*a` labels.
The explicit numeric encoding and its sorting compatibility are future work. -/
theorem productAlphabet_card (a b : Nat) :
    Fintype.card (Fin b × Fin a) = b * a := by
  simp

/-!
## Bayer--Diaconis product-alphabet encoding (F4.1, single-label core)

A `Fin (a*b)` label decomposes lexicographically into a `Fin b` *major* and a
`Fin a` *minor* component: the numeric value `m*a + n` has major `m` and minor
`n`. The decomposition is a bijection (a monotone reindexing), which is what
makes a single `a*b`-alphabet GSR shuffle the same shuffle as an independent
`b`-alphabet and `a`-alphabet product-label shuffle.
-/ 

/-- Lexicographic decomposition of a `Fin (a*b)` label into its `(major, minor)`
  components: numeric `m*a + n` has major `m : Fin b` and minor `n : Fin a`. -/
noncomputable def encodeLabel {a b : Nat} (ha : 0 < a) (k : Fin (a*b)) :
    Fin b × Fin a :=
  (Fin.mk (k.val / a) (Nat.div_lt_of_lt_mul k.isLt),
   Fin.mk (k.val % a) (Nat.mod_lt k.val ha))

/-- The inverse of `encodeLabel`: the `Fin (a*b)` label with major `m` and
  minor `n` has numeric value `m*a + n`. -/
noncomputable def decodeLabel {a b : Nat} (ha : 0 < a) (hb : 0 < b) (p : Fin b × Fin a) :
    Fin (a*b) :=
  Fin.mk (p.1.val * a + p.2.val) (by
    have h1 : p.1.val < b := p.1.isLt
    have h2 : p.2.val < a := p.2.isLt
    calc
      p.1.val * a + p.2.val < p.1.val * a + a := Nat.add_lt_add_left h2 (p.1.val * a)
      _ = (p.1.val + 1) * a := by ring
      _ ≤ b * a := Nat.mul_le_mul_right a (Nat.succ_le_of_lt h1)
      _ = a * b := Nat.mul_comm _ _)

/-- `decodeLabel` is a left inverse of `encodeLabel`. -/
theorem decodeLabel_encodeLabel {a b : Nat} (ha : 0 < a) (hb : 0 < b) (k : Fin (a*b)) :
    decodeLabel ha hb (encodeLabel ha k) = k := by
  simp only [encodeLabel, decodeLabel]
  rw [Fin.ext_iff]
  simpa [Nat.mul_comm] using Nat.div_add_mod k.val a

/-- `encodeLabel` is a left inverse of `decodeLabel`. -/
theorem encodeLabel_decodeLabel {a b : Nat} (ha : 0 < a) (hb : 0 < b) (p : Fin b × Fin a) :
    encodeLabel ha (decodeLabel ha hb p) = p := by
  have hdecval : (decodeLabel ha hb p).val = p.1.val * a + p.2.val := rfl
  have h2 : p.2.val < a := p.2.isLt
  have h2m : p.2.val % a = p.2.val := Nat.mod_eq_of_lt h2
  have hcarry : (p.1.val * a) % a + p.2.val % a < a := by
    simp only [Nat.mul_comm, Nat.mul_mod_right, Nat.zero_add, h2m]
    exact h2
  have hmaj : (decodeLabel ha hb p).val / a = p.1.val := by
    rw [hdecval, Nat.add_div_eq_of_add_mod_lt hcarry]
    rw [show (p.1.val * a) / a = p.1.val by
      rw [Nat.mul_comm, Nat.mul_div_cancel_left _ ha]]
    rw [Nat.div_eq_of_lt h2, Nat.add_zero]
  have hmin : (decodeLabel ha hb p).val % a = p.2.val := by
    rw [hdecval, Nat.add_mod]
    have hmul : (p.1.val * a) % a = 0 := by
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right _ _
    rw [hmul, Nat.zero_add, Nat.mod_mod]
    exact h2m
  apply Prod.ext
  · -- major component
    apply Fin.ext
    simp only [encodeLabel]
    exact hmaj
  · -- minor component
    apply Fin.ext
    simp only [encodeLabel]
    exact hmin

/-! ## Exact probability law, with `StdSimplex` as the sole distribution authority -/

/-- Uniform distribution on any inhabited finite type, in exact rationals. -/
noncomputable def uniformDist (β : Type*) [Fintype β] [Nonempty β] : Dist β :=
  Dist.ofFun
    (fun _ => (Fintype.card β : Rat)⁻¹)
    (fun _ => by positivity)
    (by
      classical
      have hcard : (Fintype.card β : Rat) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
      simp [nsmul_eq_mul, hcard])

/-- Independent uniform `a`-ary labels for the `n` card identities. -/
noncomputable def uniformLabels (n a : Nat) (ha : 0 < a) :
    Dist (Fin n → Fin a) := by
  letI : Nonempty (Fin n → Fin a) := ⟨fun _ => ⟨0, ha⟩⟩
  exact uniformDist (Fin n → Fin a)

/-- A stable-label shuffle with any specified finite label law. This
includes uniform GSR and nonuniform independent-card labels as special
cases. The output is a well-formed distribution by `StdSimplex.map`. -/
noncomputable def labelShuffle (a : Nat) (source : Dist (Fin n → Fin a)) :
    FiniteKernel (List (Fin n)) (List (Fin n)) :=
  fun deck => source.map (fun labels => stableBuckets a labels deck)

/-- A probabilistic inverse GSR `a`-shuffle, on a deck of `n` named cards.
A positive alphabet size is required for the uniform label source. -/
noncomputable def idealShuffle (n a : Nat) (ha : 0 < a) :
    FiniteKernel (List (Fin n)) (List (Fin n)) :=
  labelShuffle a (uniformLabels n a ha)

/-- A single refinement with independent minor and major label sources.
This is the product-alphabet shuffle, with alphabet size `b*a`. -/
noncomputable def productLabelShuffle (a b : Nat)
    (minorSource : Dist (Fin n → Fin a)) (majorSource : Dist (Fin n → Fin b)) :
    FiniteKernel (List (Fin n)) (List (Fin n)) :=
  fun deck => FiniteKernel.apply minorSource (fun minor =>
    majorSource.map (fun major => lexBuckets a b minor major deck))

theorem apply_deterministic {β γ : Type*} (mu : Dist β) (f : β → γ) :
    FiniteKernel.apply mu (FiniteKernel.deterministic f) = mu.map f := by
  change (mu.map (fun x => Convexity.StdSimplex.single (f x))).join = mu.map f
  rw [Dist.join_sConvexComb]
  calc
    _ = ((mu.map f).map Convexity.StdSimplex.single).sConvexComb := by
      rw [Convexity.StdSimplex.map_map]
    _ = mu.map f := Convexity.StdSimplex.iConvexComb_single (mu.map f)

theorem comp_deterministic_left {β γ δ : Type*}
    (f : β → γ) (K : FiniteKernel γ δ) :
    FiniteKernel.comp (FiniteKernel.deterministic f) K = fun x => K (f x) := by
  funext x
  change FiniteKernel.apply (Dist.pointMass (f x)) K = K (f x)
  exact FiniteKernel.apply_pointMass (f x) K

/-- **Product-alphabet composition law for inverse riffles.** Running an
`a`-label stable shuffle and then a `b`-label stable shuffle has *exactly*
the same probability law as independently sampling both labels and sorting
by the combined lexicographic `(b,a)` label. The proof holds for arbitrary
per-round label distributions and does not enumerate any permutations. -/
theorem labelShuffle_comp (a b : Nat)
    (minorSource : Dist (Fin n → Fin a)) (majorSource : Dist (Fin n → Fin b)) :
    FiniteKernel.comp (labelShuffle a minorSource) (labelShuffle b majorSource) =
      productLabelShuffle a b minorSource majorSource := by
  funext deck
  let sortMinor : (Fin n → Fin a) → List (Fin n) :=
    fun labels => stableBuckets a labels deck
  change FiniteKernel.apply (minorSource.map sortMinor) (labelShuffle b majorSource) =
    productLabelShuffle a b minorSource majorSource deck
  calc
    FiniteKernel.apply (minorSource.map sortMinor) (labelShuffle b majorSource) =
        FiniteKernel.apply
          (FiniteKernel.apply minorSource (FiniteKernel.deterministic sortMinor))
          (labelShuffle b majorSource) := by
      rw [apply_deterministic]
    _ = FiniteKernel.apply minorSource
          (FiniteKernel.comp (FiniteKernel.deterministic sortMinor)
            (labelShuffle b majorSource)) :=
      FiniteKernel.apply_comp _ _ _
    _ = FiniteKernel.apply minorSource
          (fun minor => majorSource.map
            (fun major => lexBuckets a b minor major deck)) := by
      rw [comp_deterministic_left]
      congr 1
      funext minor
      change majorSource.map
        (fun major => stableBuckets b major (stableBuckets a minor deck)) =
        majorSource.map (fun major => lexBuckets a b minor major deck)
      congr 1
      funext major
      exact stableBuckets_comp a b minor major deck
    _ = productLabelShuffle a b minorSource majorSource deck := rfl

/-- Uniform-GSR specialization of the product-alphabet composition theorem.
The two random label assignments are independent; the combined label has
`a*b` possibilities per card. -/
theorem idealShuffle_comp (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    FiniteKernel.comp (idealShuffle n a ha) (idealShuffle n b hb) =
      productLabelShuffle a b (uniformLabels n a ha) (uniformLabels n b hb) :=
  labelShuffle_comp a b (uniformLabels n a ha) (uniformLabels n b hb)

end GSR
end Shufflemath
end
