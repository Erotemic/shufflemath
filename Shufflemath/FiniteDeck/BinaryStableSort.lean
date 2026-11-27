/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Shufflemath.GSRPermutationLaw
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.FiniteDeck.HistogramKernel
public import Shufflemath.GSRDeckRound
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace Shufflemath
namespace BinaryStableSort

set_option linter.style.haveILetI false

/-!
## Binary stable sorts — the binary-riffle bridge

`a = 2` specialization of the GSR rank law, made into a genuine permutation
action on decks: the `t`-fold iterated binary stable sort is exactly the
single `2^t`-label stable-sort — `compPow (PAK pullLaw_2) t = PAK pullLaw_(2^t)`.

This is the *actual* binary-riffle reading of the 2^23-label laws used by the
99-card certificates — the GSR's alphabet-size-2 law is the repeated binary
rffle, and `2^23` labels = 23 sequential binary stable sorts.
-/

open GSR FiniteDeck

/-! ## The deck-as-list encoding -/

/-- The deck-as-list encoding: `(List.finRange n).map d`, the list of card
identities at positions `0 … n-1` after applying deck `d`. -/
noncomputable def encodeDeck (n : Nat) (d : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map d

theorem encodeDeck_injective (n : Nat) : Function.Injective (encodeDeck n) := by
  classical
  intro d e h
  have h1 : List.ofFn ⇑d = List.ofFn ⇑e := by
    simpa [encodeDeck, List.ofFn_eq_map] using h
  have h2 : ⇑d = ⇑e := List.ofFn_inj.mp h1
  exact Equiv.ext (fun i => congrFun h2 i)

/-! ## The deterministic "filter commutes with map" content -/

theorem map_filter {X Y : Type*} (f : X → Y) (p : Y → Bool) (xs : List X) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons, List.map_cons]
    by_cases hp : p (f x)
    · simp [hp]
      rw [ih]
    · simp [hp]
      exact ih

/-- **Filtering a mapped deck commutes with the map.** The deterministic content
of the encode square: group an `f`-mapped list by labels `ell` and you get the
`f`-map of the filtered list. -/
theorem stableBuckets_map {X Y : Type*} (a : Nat) (f : X → Y) (ell : Y → Fin a)
    (xs : List X) :
    stableBuckets a ell (xs.map f) = (stableBuckets a (ell ∘ f) xs).map f := by
  unfold stableBuckets
  conv_rhs => rw [List.map_flatMap]
  congr 1
  funext i
  conv_lhs => rw [map_filter]
  simp

/-! ## The pullback noise law -/

/-- **The pullback noise law**: the `a`-label stable-sort law with the
permutation orientation flipped — the permutation a stable-sort actually
*applies* to a deck is `(rankEquiv ℓ).symm`, so the deck-action noise is the
inversion of the GSR permutation law. This is the form `Gate6Corrected`'s
`rhoRoundFiniteCorrected`/`rhoRoundIdealCorrected` regularize. -/
noncomputable def pullLaw (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    Dist (Equiv.Perm (Fin n)) :=
  (PermutationLaw.gsrPermutationLaw n a ha hn).map (fun p => p.symm)

/-- Precomposition by a deck `d`, as an `Equiv` on `Fin n → Fin a`. -/
noncomputable def precompEquiv (n a : Nat) (d : Equiv.Perm (Fin n)) :
    (Fin n → Fin a) ≃ (Fin n → Fin a) where
  toFun := fun ℓ i => ℓ (d i)
  invFun := fun ℓ i => ℓ (d.symm i)
  left_inv := fun ℓ => by
    funext i
    simp
  right_inv := fun ℓ => by
    funext i
    simp

/-- Precomposition by a deck is uniform-preserving: uniform labels on card
identities induce uniform labels on positions. -/
theorem precompEquiv_uniformLabels (n a : Nat) (ha : 0 < a) (d : Equiv.Perm (Fin n)) :
    (uniformLabels n a ha).map (precompEquiv n a d) = uniformLabels n a ha := by
  letI : Nonempty (Fin n → Fin a) := ⟨fun _ => ⟨0, ha⟩⟩
  exact map_bijective_uniformDist (precompEquiv n a d)

/-! ## The commuting square at the canonical deck -/

/-- **Canonical-deck square (permutation form).** Pushing the pullback noise
law at the identity deck through `encodeDeck` yields the canonical
`idealShuffle` law. This is the content the binary-riffle bridge stands on. -/
theorem pullLaw_map_encodeDeck_id (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    (pullLaw n a ha hn).map (encodeDeck n) =
      idealShuffle n a ha (List.finRange n) := by
  have hR : idealShuffle n a ha (List.finRange n) =
      (uniformLabels n a ha).map (fun ℓ => (List.finRange n).map (rankEquiv n a hn ℓ).symm) :=
    PermutationLaw.idealShuffle_canonical_eq_permPushforward n a ha hn
  rw [pullLaw, hR]
  unfold PermutationLaw.gsrPermutationLaw
  rw [Convexity.StdSimplex.map_map]
  rw [Convexity.StdSimplex.map_map]
  congr 1

/-! ## The commuting square at an arbitrary deck -/

/-- **The commuting square (arbitrary deck).** Pushing the one-step deck kernel
`PAK pullLaw_a` at a deck `d` through `encodeDeck` yields exactly the list-side
GSR law at `encode d`. This is the key identification of the binary stable-sort
action: `PAK pullLaw_a ; deterministic encode = deterministic encode ; idealShuffle`. -/
theorem permutationActionKernel_pullLaw_map_encode (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (d : Equiv.Perm (Fin n)) :
    ((permutationActionKernel (pullLaw n a ha hn)) d).map (encodeDeck n) =
      idealShuffle n a ha (encodeDeck n d) := by
  letI : Nonempty (Fin n → Fin a) := ⟨fun _ => ⟨0, ha⟩⟩
  -- LHS: ((pullLaw).map (fun p => p.trans d)).map encodeDeck
  have hLHS : ((permutationActionKernel (pullLaw n a ha hn)) d).map (encodeDeck n) =
      (uniformLabels n a ha).map
        (fun ℓ => ((List.finRange n).map (rankEquiv n a hn ℓ).symm).map d) := by
    unfold permutationActionKernel pullLaw PermutationLaw.gsrPermutationLaw
    rw [Convexity.StdSimplex.map_map]
    rw [Convexity.StdSimplex.map_map]
    rw [Convexity.StdSimplex.map_map]
    -- now the LHS is uniformLabels.map (fun ℓ => (finRange n).map ((rankEquiv ℓ).symm.trans d))
    congr 1
    funext ℓ
    simp [encodeDeck, List.map_map]
  -- RHS: idealShuffle law at encode d
  have hRHS : idealShuffle n a ha (encodeDeck n d) =
      (uniformLabels n a ha).map
        (fun ℓ => (stableBuckets a (ℓ ∘ d) (List.finRange n)).map d) := by
    dsimp only [idealShuffle, labelShuffle]
    congr 1
    funext ℓ
    rw [encodeDeck, stableBuckets_map]
  -- Uniform-invariance under the precomposition Equiv
  have hinv : (uniformLabels n a ha).map
      (fun ℓ => (stableBuckets a (ℓ ∘ d) (List.finRange n)).map d) =
      (uniformLabels n a ha).map
        (fun ℓ => (stableBuckets a ℓ (List.finRange n)).map d) := by
    have hcomp : (fun ℓ => (stableBuckets a (ℓ ∘ d) (List.finRange n)).map d) =
        (fun ℓ => (stableBuckets a ℓ (List.finRange n)).map d) ∘ (precompEquiv n a d) := by
      funext ℓ
      rfl
    rw [hcomp, Convexity.StdSimplex.map_comp, precompEquiv_uniformLabels]
  rw [hLHS, hRHS, hinv]
  -- now both sides: (uniformLabels).map (fun ℓ => (stableBuckets a ℓ (finRange n)).map d)
  congr 1
  funext ℓ
  rw [stableBuckets_eq_orderByNewPosition n a ha hn ℓ]

/-! ## The left inverse of the deck encoding -/

/-- **Left inverse of the deck encoding.**  Packs an encoded list back into a
deck, choosing the witness via `Classical.choose` when one exists and falling
back to the identity otherwise.  Left-inverse to `encodeDeck n` on its range
(and by injectivity, exactly at the range); used only to cancel the common
`map encodeDeck` in the kernel composition laws below. -/
noncomputable def encodeInv (n : Nat) (ℓ : List (Fin n)) : Equiv.Perm (Fin n) :=
  if h : ∃ d, encodeDeck n d = ℓ then Classical.choose h else Equiv.refl (Fin n)

theorem encodeInv_leftInverse (n : Nat) :
    Function.LeftInverse (encodeInv n) (encodeDeck n) := by
  classical
  intro d
  have hpos : ∃ d', encodeDeck n d' = encodeDeck n d := ⟨d, rfl⟩
  unfold encodeInv
  rw [dite_eq_left hpos]
  exact encodeDeck_injective n (Classical.choose_spec hpos)

/-! ## The kernel-level commuting square -/

/-- **The kernel-level commuting square.**  Composing the pullback-noise deck
kernel with the deterministic encoding of decks as lists is the same as
composing the deterministic encoding with the list-side `idealShuffle` law:
`PAK pullLaw_a ; det encode = det encode ; idealShuffle`.  The pointwise
content is `permutationActionKernel_pullLaw_map_encode`. -/
theorem kernel_commuting_square (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    FiniteKernel.comp (permutationActionKernel (pullLaw n a ha hn))
                      (FiniteKernel.deterministic (encodeDeck n)) =
      FiniteKernel.comp (FiniteKernel.deterministic (encodeDeck n)) (idealShuffle n a ha) := by
  funext d
  change FiniteKernel.apply ((permutationActionKernel (pullLaw n a ha hn)) d)
        (FiniteKernel.deterministic (encodeDeck n)) =
      FiniteKernel.apply (Dist.pointMass (encodeDeck n d)) (idealShuffle n a ha)
  rw [GSR.apply_deterministic, FiniteKernel.apply_pointMass]
  exact permutationActionKernel_pullLaw_map_encode n a ha hn d

/-! ## The binary-refinement orientation: the `a = 1` degenerate case -/

/-- **The `a = 1` rank is the identity.**  A single-label permutation is the
position identity (`rankVal n 1 ℓ i = i.val`). -/
theorem rankEquiv_a1 (n : Nat) (hn : 0 < n) (ℓ : Fin n → Fin 1) :
    rankEquiv n 1 hn ℓ = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  have hrank : rankEquiv n 1 hn ℓ i = Fin.mk (rankVal n 1 ℓ i) (rankVal_lt_n n 1 hn ℓ i) := by
    dsimp only [rankEquiv, Equiv.ofBijective]
    rfl
  rw [hrank]
  exact Fin.ext (rankVal_a1 n hn ℓ i)

/-- **The `a = 1` GSR permutation law is the point mass at the identity.** -/
theorem gsrPermutationLaw_a1 (n : Nat) (hn : 0 < n) :
    PermutationLaw.gsrPermutationLaw n 1 (by norm_num : 0 < 1) hn =
      Dist.pointMass (Equiv.refl (Fin n)) := by
  have hconst : (fun ℓ => rankEquiv n 1 hn ℓ) = fun _ => Equiv.refl (Fin n) := by
    funext ℓ
    exact rankEquiv_a1 n hn ℓ
  unfold PermutationLaw.gsrPermutationLaw
  conv_lhs => rw [hconst]
  exact Convexity.StdSimplex.map_const _ _

/-- **The `a = 1` pullback law is the point mass at the identity.** -/
theorem pullLaw_a1 (n : Nat) (hn : 0 < n) :
    pullLaw n 1 (by norm_num : 0 < 1) hn = Dist.pointMass (Equiv.refl (Fin n)) := by
  unfold pullLaw
  rw [gsrPermutationLaw_a1]
  show (Convexity.StdSimplex.single (Equiv.refl (Fin n))).map (fun p => p.symm) =
    Convexity.StdSimplex.single (Equiv.refl (Fin n))
  rw [Convexity.StdSimplex.map_single, Equiv.refl_symm]

/-! ## The kernel composition law (the product-alphabet identity) -/

/-- **The kernel composition law (the binary-riffle bridge's step 2).**  The
composition of two pullback-noise deck kernels is the kernel of the
product-alphabet law:
`PAK pullLaw_a ; PAK pullLaw_b = PAK pullLaw_(a*b)`.

Proof: pull both sides through the injective `encodeDeck` and cancel it.
The LHS maps through the `apply_observation` bridge to the list-side
composition `idealShuffle a ; idealShuffle b`, which is the product-label
shuffle by `idealShuffle_comp` and is the `(a*b)`-alphabet ideal shuffle by
`productLabelShuffle_uniform_eq_ideal`; the RHS is the `(a*b)`-alphabet law
at the encoded deck by the commuting square. -/
theorem comp_pullLaw (n a b : Nat) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    FiniteKernel.comp (permutationActionKernel (pullLaw n a ha hn))
                      (permutationActionKernel (pullLaw n b hb hn)) =
      permutationActionKernel (pullLaw n (a * b) (mul_pos ha hb) hn) := by
  classical
  funext deck
  show FiniteKernel.apply ((permutationActionKernel (pullLaw n a ha hn)) deck)
        (permutationActionKernel (pullLaw n b hb hn)) =
      (permutationActionKernel (pullLaw n (a * b) (mul_pos ha hb) hn)) deck
  apply GenericQuotient.cancel_map_leftInverse (encodeDeck n) (encodeInv n)
    (encodeInv_leftInverse n) _ _
  have hSqA : FiniteKernel.comp (permutationActionKernel (pullLaw n a ha hn))
                (FiniteKernel.deterministic (encodeDeck n)) =
            FiniteKernel.comp (FiniteKernel.deterministic (encodeDeck n)) (idealShuffle n a ha) :=
    kernel_commuting_square n a ha hn
  have hSqB : FiniteKernel.comp (permutationActionKernel (pullLaw n b hb hn))
                (FiniteKernel.deterministic (encodeDeck n)) =
            FiniteKernel.comp (FiniteKernel.deterministic (encodeDeck n)) (idealShuffle n b hb) :=
    kernel_commuting_square n b hb hn
  have hLHS : (FiniteKernel.apply ((permutationActionKernel (pullLaw n a ha hn)) deck)
                    (permutationActionKernel (pullLaw n b hb hn))).map (encodeDeck n) =
      FiniteKernel.apply (idealShuffle n a ha (encodeDeck n deck)) (idealShuffle n b hb) := by
    have h := GenericQuotient.apply_observation (encodeDeck n)
      (permutationActionKernel (pullLaw n b hb hn)) (idealShuffle n b hb) hSqB
      ((permutationActionKernel (pullLaw n a ha hn)) deck)
    rw [h]
    congr 1
    exact permutationActionKernel_pullLaw_map_encode n a ha hn deck
  have hRHS : ((permutationActionKernel (pullLaw n (a * b) (mul_pos ha hb) hn)) deck).map (encodeDeck n) =
      idealShuffle n (a * b) (mul_pos ha hb) (encodeDeck n deck) :=
    permutationActionKernel_pullLaw_map_encode n (a * b) (mul_pos ha hb) hn deck
  rw [hLHS, hRHS]
  show FiniteKernel.comp (idealShuffle n a ha) (idealShuffle n b hb) (encodeDeck n deck) =
    idealShuffle n (a * b) (mul_pos ha hb) (encodeDeck n deck)
  rw [idealShuffle_comp, productLabelShuffle_uniform_eq_ideal]

/-! ## The binary-riffle bridge (`2^t` labels) -/

/-- **The `t = 0` base case:** the identity kernel is the `a = 1` pullback kernel. -/
theorem identity_eq_pak_pullLaw_one (n : Nat) (hn : 0 < n) :
    FiniteKernel.identity = permutationActionKernel (pullLaw n 1 (by norm_num : 0 < 1) hn) := by
  funext d
  show Convexity.StdSimplex.single d = (pullLaw n 1 (by norm_num : 0 < 1) hn).map (fun p => p.trans d)
  rw [pullLaw_a1]
  show Convexity.StdSimplex.single d = (Convexity.StdSimplex.single (Equiv.refl (Fin n))).map (fun p => p.trans d)
  rw [Convexity.StdSimplex.map_single, Equiv.refl_trans]

/-- **The binary-riffle bridge.**  The `t`-fold iterated binary stable sort is
the single `2^t`-label stable sort (as a deck action):
`compPow (PAK pullLaw_2) t = PAK pullLaw_(2^t)`.  Proof by induction on `t`:
the base case is `a = 1` (the identity), and the step is the kernel composition
law `comp_pullLaw` at `(a, b) = (2^t, 2)` composed with `2^t * 2 = 2^(t+1)`. -/
theorem compPow_pullLaw (n : Nat) (hn : 0 < n) (t : Nat) :
    FiniteKernel.compPow (permutationActionKernel (pullLaw n 2 (by norm_num) hn)) t =
      permutationActionKernel (pullLaw n (2 ^ t) (by positivity) hn) := by
  induction t with
  | zero =>
    rw [FiniteKernel.compPow_zero]
    show FiniteKernel.identity = permutationActionKernel (pullLaw n 1 (by norm_num : 0 < 1) hn)
    exact identity_eq_pak_pullLaw_one n hn
  | succ t ih =>
    rw [FiniteKernel.compPow_succ, ih]
    rw [comp_pullLaw]
    congr 1


/-! ## The two-pile embedding homomorphism -/

/-- **The two-pile embedding is multiplicative** (componentwise multiplication on
    within-pile permutations becomes deck multiplication; the `*`-flip convention of
    `perm_mul_eq_trans_flip` is honored — left factor applied first).
    Proved pointwise: on a left position `leftPosition i` both sides reduce to
    `leftPosition (pl₂ (pl₁ i))` (and dually on right positions) via
    `embed_m_left`/`embed_m_right`. -/
theorem embed_m_mul (N m : Nat) (hm : m ≤ N)
    (pl₁ pl₂ : Equiv.Perm (Fin m)) (pr₁ pr₂ : Equiv.Perm (Fin (N - m))) :
    embed_m N m hm (pl₁ * pl₂) (pr₁ * pr₂) =
      embed_m N m hm pl₁ pr₁ * embed_m N m hm pl₂ pr₂ := by
  apply Equiv.ext
  intro x
  by_cases hx : x.val < m
  · have key : x = leftPosition N m hm ⟨x.val, hx⟩ := by
      apply Fin.ext
      rw [leftPosition_val]
    rw [key]
    rw [embed_m_left]
    have hmul : (pl₁ * pl₂) ⟨x.val, hx⟩ = pl₁ (pl₂ ⟨x.val, hx⟩) := by
      rw [perm_mul_eq_trans_flip, Equiv.trans_apply]
    rw [hmul]
    rw [perm_mul_eq_trans_flip, Equiv.trans_apply, embed_m_left, embed_m_left]
  · have hx2 : x.val - m < N - m := by omega
    have key : x = rightPosition N m hm ⟨x.val - m, hx2⟩ := by
      apply Fin.ext
      rw [rightPosition_val]
      have hsub : (⟨x.val - m, hx2⟩ : Fin (N - m)).val = x.val - m := rfl
      rw [hsub]
      omega
    rw [key]
    rw [embed_m_right]
    have hmul : (pr₁ * pr₂) ⟨x.val - m, hx2⟩ = pr₁ (pr₂ ⟨x.val - m, hx2⟩) := by
      rw [perm_mul_eq_trans_flip, Equiv.trans_apply]
    rw [hmul]
    rw [perm_mul_eq_trans_flip, Equiv.trans_apply, embed_m_right, embed_m_right]

/-- The map version: `roundEmbedMap` sends componentwise pair-multiplication to
    full-deck multiplication — `roundEmbedMap (p.1 * p'.1, p.2 * p'.2) = roundEmbedMap p * roundEmbedMap p'`.
    The homomorphism every two-pile composition of within-pile laws uses. -/
theorem roundEmbedMap_mul (N m : Nat) (hm : m ≤ N)
    (pl₁ pl₂ : Equiv.Perm (Fin m)) (pr₁ pr₂ : Equiv.Perm (Fin (N - m))) :
    roundEmbedMap N m hm (pl₁ * pl₂, pr₁ * pr₂) =
      roundEmbedMap N m hm (pl₁, pr₁) * roundEmbedMap N m hm (pl₂, pr₂) :=
  embed_m_mul N m hm pl₁ pl₂ pr₁ pr₂

/-- **The two-pile embedding commutes with the `t`-fold power.**  The `t`-fold
    componentwise within-pile power embedded is the `t`-fold full-deck power. -/
theorem embed_m_pow (N m : Nat) (hm : m ≤ N)
    (pl : Equiv.Perm (Fin m)) (pr : Equiv.Perm (Fin (N - m))) (t : Nat) :
    embed_m N m hm (pl ^ t) (pr ^ t) = (embed_m N m hm pl pr) ^ t := by
  induction t with
  | zero =>
    simp only [pow_zero]
    ext x
    by_cases hx : x.val < m
    · have key : x = leftPosition N m hm ⟨x.val, hx⟩ := by
        apply Fin.ext
        rw [leftPosition_val]
      rw [key]
      rw [embed_m_left]
      simp
    · have hm1 : (x.val - m) < N - m := by omega
      have key : x = rightPosition N m hm ⟨x.val - m, hm1⟩ := by
        apply Fin.ext
        rw [rightPosition_val]
        have hsub : (⟨x.val - m, hm1⟩ : Fin (N - m)).val = x.val - m := rfl
        rw [hsub]
        omega
      rw [key]
      rw [embed_m_right]
      simp
  | succ t ih =>
    simp only [pow_succ]
    rw [embed_m_mul, ih]

/-! ## The law-level bridge at a fixed deck -/

/-- **The per-deck binary-riffle bridge.**  Starting from a deterministic deck
    `d`, the `t`-fold binary stable-sort (as a kernel) applied to `d` is exactly
    the `2^t`-label stable-sort kernel applied to `d`.  This is `compPow_pullLaw`
    read as a law at a fixed deck — the content of the binary-riffle bridge once
    the noise-to-law pushforward is unfolded. -/
theorem compPow_pullLaw_apply_pointMass (n : Nat) (hn : 0 < n) (t : Nat)
    (d : Deck n) :
    FiniteKernel.apply (Dist.pointMass d)
        (FiniteKernel.compPow (permutationActionKernel (pullLaw n 2 (by norm_num) hn)) t) =
      FiniteKernel.apply (Dist.pointMass d)
        (permutationActionKernel (pullLaw n (2 ^ t) (by positivity) hn)) := by
  rw [compPow_pullLaw]

/-- **The concrete 23-riffle specialization.**  At `t = 23`, the `2^23`-label pullback
    law on a single pile is exactly the `23`-fold composition of the binary pullback
    kernel — the binary-riffle reading of the `2^23`-label laws used by the 99-card
    certificates (23 binary riffles per pile, one corrected call per pile). -/
theorem binary23_eq_compPow_pullLaw_23 (n : Nat) (hn : 0 < n) :
    permutationActionKernel (pullLaw n (2 ^ 23) (by norm_num) hn) =
      FiniteKernel.compPow (permutationActionKernel (pullLaw n 2 (by norm_num) hn)) 23 :=
  (compPow_pullLaw n hn 23).symm

/-! ## The full-deck two-pile composition law (kernel-level) -/

/-- **The kernel-level composition of two action kernels is the action kernel of
the convolution of the noise laws.**  With `W` the noise of the first round and
`W'` the noise of the second, the composition
`PAK W ; PAK W'` is the single action kernel of the `*`-convolution law
`conv W W'`.  This is the one-step `*`-composition of the action kernels — the
group-level convolution the two-pile rounds compose by. -/
theorem comp_pak_eq_pak_conv {N : Nat} (W W' : Dist (Deck N)) :
    FiniteKernel.comp (permutationActionKernel W) (permutationActionKernel W') =
      permutationActionKernel (FiniteDeck.conv W W') := by
  funext d
  show FiniteKernel.apply ((permutationActionKernel W) d) (permutationActionKernel W') =
        (permutationActionKernel (FiniteDeck.conv W W')) d
  show FiniteKernel.apply (W.map fun p => FiniteDeck.act p d) (permutationActionKernel W') =
        (FiniteDeck.conv W W').map (fun p => FiniteDeck.act p d)
  exact convMapEqApplyMap W W' d

/-- **The `t`-fold composition of an action kernel is the action kernel of the
`t`-fold convolution power.**  Induction on `t`: base `compPow 0 = identity`
(the `a = 1` case is a point mass at the identity, the zero-noise law), step by
the one-step composition law and `powConv`'s recursive definition. -/
theorem compPow_pak_eq_pak_powConv {N : Nat} (W : Dist (Deck N)) (t : Nat) :
    FiniteKernel.compPow (permutationActionKernel W) t =
      permutationActionKernel (FiniteDeck.powConv W t) := by
  induction t with
  | zero =>
      rw [FiniteKernel.compPow_zero]
      funext d
      show Dist.pointMass d = (permutationActionKernel (Dist.pointMass (Equiv.refl (Fin N)))) d
      show Dist.pointMass d = (Convexity.StdSimplex.single (Equiv.refl (Fin N))).map (fun p => p.trans d)
      rw [Convexity.StdSimplex.map_single, Equiv.refl_trans]
      rfl
  | succ t ih =>
      rw [FiniteKernel.compPow_succ, ih, comp_pak_eq_pak_conv]
      rfl

/-- **The two-pile binary-riffle bridge (kernel level).**  The `t`-fold
iterated binary stable sort of the two-pile round law (left/right within-pile
`2`-label stable sorts, `t` binary riffles per pile) is exactly the action
kernel of the `t`-fold convolution power of the two-pile round law — the honest
`t`-fold full-deck two-pile composition.  The concrete specialization
`t = 23`, `2 ^ t = 2 ^ 23` labels, is the A2 follow-up; the kernel-level
identity here is the `2^t`-label content the A2 assembly stands on (the
within-pile-`2^t` ↔ `t`-fold-binary law identification is the remaining step). -/
theorem compPow_rhoRoundFinite (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m) (hRpos : 0 < N - m)
    (t : Nat) :
    FiniteKernel.compPow (permutationActionKernel (rhoRoundFinite N m hm hLpos hRpos 2 (by norm_num))) t =
      permutationActionKernel (FiniteDeck.powConv (rhoRoundFinite N m hm hLpos hRpos 2 (by norm_num)) t) :=
  compPow_pak_eq_pak_powConv _ _

/-- **The two-pile per-deck bridge.**  The `t`-fold two-pile binary-riffle
kernel applied to a deterministic start `d` is the action kernel of the
`t`-fold convolution power of the two-pile round law at `d` — the per-deck
law-level form of the two-pile bridge. -/
theorem compPow_rhoRoundFinite_apply_pointMass (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (t : Nat) (d : Deck N) :
    FiniteKernel.apply (Dist.pointMass d)
        (FiniteKernel.compPow (permutationActionKernel (rhoRoundFinite N m hm hLpos hRpos 2 (by norm_num))) t) =
      FiniteKernel.apply (Dist.pointMass d)
        (permutationActionKernel (FiniteDeck.powConv (rhoRoundFinite N m hm hLpos hRpos 2 (by norm_num)) t)) := by
  rw [compPow_rhoRoundFinite]


/-! ## The law-level composition law -/

/-- **Injectivity of the action kernel** at the identity deck: pushing the
noise law through `p.trans (Equiv.refl (Fin N)) = id` makes the kernel of two
laws distinguishable — `PAK S = PAK T → S = T`.  (Concretely: `S.map id =
T.map id`, so the two source laws coincide.) -/
theorem permutationActionKernel_injective {N : Nat} (S T : Dist (Deck N))
    (h : permutationActionKernel S = permutationActionKernel T) : S = T := by
  have h1 := congrFun h (Equiv.refl (Fin N))
  simp only [permutationActionKernel] at h1
  have heq : (fun p : Equiv.Perm (Fin N) => p.trans (Equiv.refl (Fin N))) = id := by
    funext p
    rw [Equiv.trans_refl]
    rfl
  rw [heq] at h1
  simp only [Convexity.StdSimplex.map_id] at h1
  exact h1

/-- **The law-level composition of the pullback laws is the pullback law of the
product** — the within-pile composition identity the `t`-fold bridge stands on.
Proved via kernel-level `comp_pullLaw` (the `*`-composition kernel) plus the
injectivity of the action kernel. -/
theorem conv_pullLaw (n a b : Nat) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    FiniteDeck.conv (pullLaw n a ha hn) (pullLaw n b hb hn) = pullLaw n (a * b) (mul_pos ha hb) hn := by
  apply permutationActionKernel_injective _ _
  rw [← comp_pak_eq_pak_conv]
  exact comp_pullLaw n a b ha hb hn

/-- **The `t`-fold convolution power of the `2`-label pullback law is the
`2^t`-label pullback law.**  The law-level form of the binary-riffle bridge
(independent of the kernel-level `compPow_pullLaw`, via the law-level
composition `conv_pullLaw`). -/
theorem powConv_pullLaw (n : Nat) (hn : 0 < n) (t : Nat) :
    FiniteDeck.powConv (pullLaw n 2 (by norm_num) hn) t = pullLaw n (2 ^ t) (by positivity) hn := by
  induction t with
  | zero =>
      show FiniteDeck.powConv (pullLaw n 2 (by norm_num) hn) 0 = pullLaw n 1 (by positivity) hn
      rw [pullLaw_a1]
      rfl
  | succ t ih =>
      rw [show FiniteDeck.powConv (pullLaw n 2 (by norm_num) hn) (t + 1) =
            FiniteDeck.conv (FiniteDeck.powConv (pullLaw n 2 (by norm_num) hn) t)
                              (pullLaw n 2 (by norm_num) hn) from rfl,
          ih, conv_pullLaw]
      congr 1


end BinaryStableSort
end Shufflemath
