module

public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace GSR

/-!
## Small `Bool` helpers

`Bool` facts used by the F4.1 sorting-compatibility `Bool`/`==`/`&&` filter
bridge.
-/

-- `(x && y) = true` holds exactly when both are `true`. A clean `Iff` form
-- (the `=`-of-`Prop` `Bool.and_eq_true_eq_eq_true_and_eq_true` is an `Eq` of
-- props, not an `Iff`, and does not compose with the `↔` from
-- `Bool.eq_iff_iff`).
theorem and_true_iff (x y : Bool) : (x && y) = true ↔ (x = true) ∧ (y = true) := by
  by_cases hx : x = true <;> by_cases hy : y = true <;> simp


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

/-! ## Mixed-radix uniqueness without division (F4.1, sorting-compatibility core)

The `Nat.div`/`Nat.mod`-free statement that a two-digit mixed-radix expansion
with *no carry* is unique: if `x*a + y = j*a + i` with both low digits `y < a`
and `i < a`, then the digits agree, `x = j` and `y = i`. This is exactly the
predicate equivalence that makes sorting by the combined label `major*a + minor`
agree with sorting by the `(major, minor)` pair, and it is stated without any
`div`/`mod` so that `List`-level reindexing does not trigger rewrite loops.
-/ 

/-- No-carry mixed-radix uniqueness: `x*a + y = j*a + i` with `y < a` and
  `i < a` forces `x = j` and `y = i`. The proof only uses the residue of the
  two sides modulo `a` (the low digit is the residue) and then cancels the
  common `·*a` term; no `div`/`mod` of the full number is taken. -/
theorem mixedRadix_unique {a x y j i : Nat} (ha : 0 < a) (hy : y < a) (hi : i < a)
    (h : x * a + y = j * a + i) : x = j ∧ y = i := by
  -- the low digit (residue mod a) of each side is its minor part: adding a
  -- multiple of `a` does not change the residue, and the minor part is < a.
  have hymod : (x * a + y) % a = y := by
    have h0 : (x * a + y) % a = ((x * a) % a + y % a) % a := Nat.add_mod (x * a) y a
    rw [h0]
    have hxamod : (x * a) % a = 0 := by
      rw [Nat.mul_comm, Nat.mul_mod_right]
    rw [hxamod]
    have hy2 : y % a = y := Nat.mod_eq_of_lt hy
    rw [hy2, Nat.zero_add]
    exact Nat.mod_eq_of_lt hy
  have himod : (j * a + i) % a = i := by
    have h0 : (j * a + i) % a = ((j * a) % a + i % a) % a := Nat.add_mod (j * a) i a
    rw [h0]
    have hjamod : (j * a) % a = 0 := by
      rw [Nat.mul_comm, Nat.mul_mod_right]
    rw [hjamod]
    have hi2 : i % a = i := Nat.mod_eq_of_lt hi
    rw [hi2, Nat.zero_add]
    exact Nat.mod_eq_of_lt hi
  -- the two sides are equal, so their low digits (residues) agree
  have hyi : y = i := by
    have h1 : (x * a + y) % a = (j * a + i) % a := by rw [h]
    simpa [hymod, himod] using h1
  -- with the low digits equal, the common `·*a` term cancels
  have hxy : x = j := by
    have h1 : x * a + i = j * a + i := by simpa [hyi] using h
    -- cancel the `+ i` (on the right) via commutativity + left cancellation
    have h1c : i + x * a = i + j * a := by simpa [Nat.add_comm] using h1
    have h2 : x * a = j * a := (Nat.add_right_inj).mp h1c
    have h2' : a * x = a * j := by simpa [Nat.mul_comm] using h2
    exact Nat.mul_left_cancel ha h2'
  exact ⟨hxy, hyi⟩

/-- The per-card sorting-compatibility predicate (F4.1): a card lands in the
  lexicographic bucket `(major = j, minor = i)` exactly when its combined
  `major*a + minor` label equals `j*a + i`. This is `mixedRadix_unique` applied
  per card, and it is the pointwise bridge between the combined-label sort
  (`stableBuckets (a*b) (combineLabels …)`) and the lexicographic sort
  (`lexBuckets`). The bounds on the *given* bucket indices `j < b` and `i < a`
  are all that is needed; the card's own components are in range by `Fin`. -/
theorem combinedLabel_pred {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (c : Fin n) (j i : Nat)
    (hi : i < a) :
    (major c).val * a + (minor c).val = j * a + i ↔
      (major c).val = j ∧ (minor c).val = i := by
  have hnc : (minor c).val < a := (minor c).isLt
  constructor
  · intro h
    rcases mixedRadix_unique ha hnc hi h with ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

-- Arithmetic lemmas for the mixed-radix sorting-compatibility: a number in the
-- block `a*b' .. a*b' + a - 1` divides by `a` to `b'` with remainder the offset.
theorem div_block (a b' x : Nat) (ha : 0 < a) (hx : x < a) : (a * b' + x) / a = b' := by
  have hle : (a*b' + x)/a ≤ b' := by
    have hgoal : a*b' + x ≤ b'*a + a - 1 := by
      have hlt : x + 1 ≤ a := Nat.succ_le_of_lt hx
      have hcomm : b'*a = a*b' := by ring
      omega
    exact (Nat.div_le_iff_le_mul ha).mpr hgoal
  have hge : b' ≤ (a*b' + x)/a := by
    by_contra hnot
    have hlt : (a*b' + x)/a < b' := Nat.lt_of_not_ge hnot
    rw [Nat.div_lt_iff_lt_mul ha] at hlt
    have hcomm : b'*a = a*b' := by ring
    rw [hcomm] at hlt
    exact absurd hlt (Nat.not_lt_of_ge (Nat.le_add_right (a*b') x))
  exact le_antisymm hle hge

theorem mod_block (a b' x : Nat) (ha : 0 < a) (hx : x < a) : (a * b' + x) % a = x := by
  have h1 : (a*b' + x) % a = ((a*b') % a + x % a) % a := by rw [Nat.add_mod]
  rw [h1]
  have h2 : (a*b') % a = 0 := by
    have hcomm : a*b' = b'*a := by ring
    rw [hcomm]
    exact Nat.mul_mod_left b' a
  have h3 : x % a = x := Nat.mod_eq_of_lt hx
  rw [h2, h3, Nat.zero_add]
  exact Nat.mod_eq_of_lt hx

-- The (div, mod) sequence over `range (a*b)` is exactly the nested (j, i)
-- sequence over `range b x range a` in lexicographic order: iterating the
-- numeric values `0 .. a*b - 1` and splitting each as `j*a + i` (j = k/a,
-- i = k % a) walks the (j, i) grid in exactly the lexBuckets order.
theorem rangeMap_divmod_eq_nested (a b : Nat) (ha : 0 < a) :
    (List.range (a * b)).map (fun k => (k / a, k % a)) =
      (List.range b).flatMap (fun j => (List.range a).map (fun i => (j, i))) := by
  induction b with
  | zero =>
      simp [List.range_zero]
  | succ b' ih =>
    -- LHS: split the last block (a*b' .. a*b' + a - 1)
    have hLHS : (List.range (a * Nat.succ b')).map (fun k => (k / a, k % a)) =
        (List.range (a * b')).map (fun k => (k / a, k % a)) ++
          (List.range a).map (fun i => (b', i)) := by
      simp only [Nat.mul_succ]
      rw [List.range_add]
      rw [List.map_append]
      rw [List.map_map]
      have hp : (List.range a).map ((fun k => (k/a, k%a)) ∘ fun x => a*b' + x) =
          (List.range a).map (fun i => (b', i)) := by
        rw [List.map_eq_map_iff]
        intro x hx
        have hlt : x < a := List.mem_range.mp hx
        have h1 : (a * b' + x) / a = b' := div_block a b' x ha hlt
        have h2 : (a * b' + x) % a = x := mod_block a b' x ha hlt
        simp only [h1, h2, Function.comp_apply]
      rw [hp]
    -- RHS: split off the last major index b'
    have hRHS : (List.range (Nat.succ b')).flatMap (fun j => (List.range a).map (fun i => (j, i))) =
        (List.range b').flatMap (fun j => (List.range a).map (fun i => (j, i))) ++
          (List.range a).map (fun i => (b', i)) := by
      rw [List.range_succ, List.flatMap_append]
      simp
    rw [hLHS, hRHS, ih]

/-!
## The label reparameterization (F4.1)

A `Fin (a*b)` label array decomposes, per card, into an independent `Fin b`
major and `Fin a` minor array. This is a bijection on label arrays, which is
what lets a single `(a*b)`-alphabet GSR shuffle be read as a product of a
`b`-alphabet and an `a`-alphabet shuffle.
-/ 

/-- The forward reparameterization: combine a `Fin a` minor array and a `Fin b`
  major array into a single `Fin (a*b)` array (per card). -/
noncomputable def combineLabels {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) : Fin n → Fin (a*b) :=
  fun i => decodeLabel ha hb (major i, minor i)

/-- The inverse reparameterization: split a `Fin (a*b)` array into its `Fin a`
  minor and `Fin b` major components (per card). -/
noncomputable def splitLabels {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (labels : Fin n → Fin (a*b)) : (Fin n → Fin a) × (Fin n → Fin b) :=
  (fun i => (encodeLabel ha (labels i)).2, fun i => (encodeLabel ha (labels i)).1)

/-- `splitLabels ∘ combineLabels = id`: re-splitting a recombined pair recovers
  the original minor and major arrays. -/
theorem splitLabels_combineLabels {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) :
    splitLabels ha hb (combineLabels ha hb minor major) = (minor, major) := by
  apply Prod.ext
  · -- first component (minor): (splitLabels (combineLabels minor major)).1 = minor
    funext i
    apply Fin.ext
    simp only [combineLabels, splitLabels, Prod.snd]
    have h : encodeLabel ha (decodeLabel ha hb (major i, minor i)) = (major i, minor i) :=
      encodeLabel_decodeLabel ha hb (major i, minor i)
    simpa [h] using rfl
  · -- second component (major): (splitLabels (combineLabels minor major)).2 = major
    funext i
    apply Fin.ext
    simp only [combineLabels, splitLabels, Prod.fst]
    have h : encodeLabel ha (decodeLabel ha hb (major i, minor i)) = (major i, minor i) :=
      encodeLabel_decodeLabel ha hb (major i, minor i)
    simpa [h] using rfl

/-- `combineLabels ∘ splitLabels = id`: recombining a split label array
  recovers the original array. -/
theorem combineLabels_splitLabels {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (labels : Fin n → Fin (a*b)) :
    combineLabels ha hb (splitLabels ha hb labels).1 (splitLabels ha hb labels).2 = labels := by
  funext i
  simp only [combineLabels, splitLabels]
  have hpair : ((encodeLabel ha (labels i)).1, (encodeLabel ha (labels i)).2) =
      encodeLabel ha (labels i) := rfl
  rw [hpair]
  exact decodeLabel_encodeLabel ha hb (labels i)

-- Per card, its combined numeric value equals `k` iff its major/minor are
-- exactly the `(div, mod)` decomposition of `k`. This is the `=`/`Prop`-world
-- per-card bridge for the sorting-compatibility (the `Bool`/`==`/`&&` filter
-- predicate is its `Nat.beq_eq` lift). Proven without `simp` on `decodeLabel`
-- (which recurses) — `change`/`rfl` for the value, `rw` for the rest.
theorem combineVal_pred_eq {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (c : Fin n) (k : Nat) :
    (combineLabels ha hb minor major c).val = k ↔
      (major c).val = k/a ∧ (minor c).val = k%a := by
  have hval : (combineLabels ha hb minor major c).val = (major c).val * a + (minor c).val := by
    change (decodeLabel ha hb (major c, minor c)).val = (major c).val * a + (minor c).val
    change (major c).val * a + (minor c).val = (major c).val * a + (minor c).val
    rfl
  have hk : k = (k/a)*a + k%a := by simpa [Nat.mul_comm] using (Nat.div_add_mod k a).symm
  constructor
  · intro h
    rw [hval, hk] at h
    exact (combinedLabel_pred ha hb minor major c (k/a) (k%a) (Nat.mod_lt k ha)).mp h
  · rintro ⟨h1, h2⟩
    rw [hval, hk, h1, h2]

/-- The `combineLabels`/`splitLabels` reparameterization is a bijection: a
  single `(a*b)`-alphabet label array is the same data as an independent `Fin a`
  minor array and a `Fin b` major array. -/
noncomputable def labelReparam {n a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (Fin n → Fin a) × (Fin n → Fin b) ≃ (Fin n → Fin (a*b)) where
  toFun := fun p => combineLabels ha hb p.1 p.2
  invFun := splitLabels ha hb
  left_inv := fun p => splitLabels_combineLabels ha hb p.1 p.2
  right_inv := fun labels => combineLabels_splitLabels ha hb labels

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

/-- Pushing the uniform law through a bijection gives the uniform law on the
  target. A bijection preserves cardinality, so the equal-mass uniform law is
  carried to the equal-mass uniform law on the target type. -/
theorem map_bijective_uniformDist {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) :
    (uniformDist X).map e = uniformDist Y := by
  ext y
  change Dist.mass ((uniformDist X).map e) y = Dist.mass (uniformDist Y) y
  -- LHS: the bijection fiber over y is the singleton {e.symm y}
  have hLHS : Dist.mass ((uniformDist X).map e) y = (Fintype.card X : Rat)⁻¹ := by
    have hy : y = e (e.symm y) := (Equiv.apply_symm_apply e y).symm
    rw [hy]
    simp only [Dist.mass, Convexity.StdSimplex.map]
    rw [Finsupp.mapDomain_apply_of_injective e.injective]
    simp only [Dist.mass, uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  -- RHS: uniform
  have hRHS : Dist.mass (uniformDist Y) y = (Fintype.card Y : Rat)⁻¹ := by
    simp only [Dist.mass, uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  -- the two cardinalities agree (e is a bijection)
  have hcard : (Fintype.card X : Rat) = (Fintype.card Y : Rat) := by
    exact_mod_cast Fintype.card_congr e
  rw [hLHS, hRHS]
  simpa [hcard] using rfl

/-- The independent product of two uniform label laws: a uniform law on the
  product of a `Fin a` minor array and a `Fin b` major array. -/
noncomputable def productUniformLabels {n a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    Dist ((Fin n → Fin a) × (Fin n → Fin b)) := by
  letI : Nonempty ((Fin n → Fin a) × (Fin n → Fin b)) :=
    ⟨(fun _ => ⟨0, ha⟩, fun _ => ⟨0, hb⟩)⟩
  exact uniformDist ((Fin n → Fin a) × (Fin n → Fin b))

/-- The per-card `labelReparam` carries the product of two uniform label laws
  (independent uniform `Fin a` and `Fin b` arrays) to the uniform `Fin (a*b)`
  label law: a `(a*b)`-alphabet GSR label has the same law as the independent
  product of a `b`- and an `a`-alphabet label. -/
theorem productLabels_pushforward_uniform {n a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (productUniformLabels ha hb).map (labelReparam ha hb) =
      uniformLabels n (a*b) (mul_pos ha hb) := by
  letI : Nonempty (Fin n → Fin (a*b)) := ⟨fun _ => ⟨0, mul_pos ha hb⟩⟩
  letI : Nonempty ((Fin n → Fin a) × (Fin n → Fin b)) :=
    ⟨(fun _ => ⟨0, ha⟩, fun _ => ⟨0, hb⟩)⟩
  have hRHS : uniformLabels n (a*b) (mul_pos ha hb) =
      uniformDist (Fin n → Fin (a*b)) := by
    simp only [uniformLabels]
  rw [hRHS]
  exact map_bijective_uniformDist (labelReparam ha hb)

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
