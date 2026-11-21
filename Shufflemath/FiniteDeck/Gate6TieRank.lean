module

public import Shufflemath.GSR
public import Shufflemath.GSRF42
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm

@[expose]
public section

namespace Shufflemath

/-!
## Gate 6 batch 2 — the tie-broken GSR rank: `tieRank` and its exact uniformity

This module lands batch-2 items **(a)**, **(b)** and **(d)** of the Gate 6 plan
(`docs/agent_handoff.md`, 2026-11-21 note; `docs/planning/proof-strategies/
2026-11-21-gate6-nonobvious-proof-hints.md` §2):

* **(a)** `tieRank` — the tie-broken GSR rank: sort by the lexicographic key
  `(ℓ i, σ i)` via `rankEquiv` on the `σ.symm`-reindexed array, conjugated
  back by `σ`.
* **(b)** `tieRank_precompEquiv` — equivariance under the simultaneous
  precomposition `(ℓ, σ) ↦ (ℓ ∘ θ, θ.trans σ)`.
* **(d)** the generic finite-group fact `uniformDist_of_rightInvariant`
  (a right-translation-invariant law on `Equiv.Perm α` is the uniform one),
  plus `tieRankLaw` (joint-uniform law on
  `(Fin n → Fin a) × Equiv.Perm (Fin n)` pushed through `tieRank`) and
  `tieRankLaw_rightInvariant` (its pushforward invariance via the
  measure-preserving `precompMapEquiv`).

**Key fact A** (Gate 6 §2.2) is the corollary `tieRankLaw_uniform`:
`tieRankLaw n a ha hn = GSR.uniformDist (Equiv.Perm (Fin n))` for every
`a ≥ 1` — the tie-broken rank law is *exactly uniform* on the permutation
group, with no counting of injective arrays and no conditioning.  The next
batch-2 items (Key fact B `tieRank ℓ σ = rankEquiv ℓ` for injective `ℓ`, the
generic same-source coupling inequality, and
`TV(ν_{n,a}, U_{S_n}) ≤ Pr(ℓ ∈ badLabels) ≤ C(n,2)/a`) build on these.

**Fintype note:** `Fintype (ΩTieRank n a)` for
`ΩTieRank n a := (Fin n → Fin a) × Equiv.Perm (Fin n)` is not synthesizable
by plain instance resolution in a proof context (the `Fintype` product
instance does not fire there); it is built explicitly with
`Fintype.mk (Finset.product …)` and a `letI`, which makes it available to
later instance resolution in the same term (see `tieRankLaw`).
-/

/-- The tie-broken GSR rank (Gate 6 §2.1): sort by the lexicographic key
    `(ell i, σ i)` — implemented as `rankEquiv` on the array reindexed by
    `σ.symm`, then conjugated back by `σ`.  The tie key of original card `i`
    is `(ell i, σ i)`, since the reindexed array at position `σ i` carries
    label `ell (σ.symm (σ i)) = ell i` at index `σ i`. -/
noncomputable def tieRank (n a : Nat) (hn : 0 < n)
    (ell : Fin n → Fin a) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  σ.trans (rankEquiv n a hn (fun j => ell (σ.symm j)))

/-!## 2.1 equivariance under simultaneous precomposition -/

theorem tieRank_precompEquiv (n a : Nat) (hn : 0 < n) (ell : Fin n → Fin a)
    (σ θ : Equiv.Perm (Fin n)) :
    tieRank n a hn (fun i => ell (θ i)) (θ.trans σ) =
      θ.trans (σ.trans (rankEquiv n a hn (fun j => ell (σ.symm j)))) := by
  unfold tieRank
  -- The reindexed array for (ℓ∘θ, θ.trans σ) is, pointwise, the same array
  -- ℓ∘σ⁻¹: (ℓ∘θ) ∘ (θ.trans σ)⁻¹ = ℓ ∘ θ ∘ (σ.symm.trans θ.symm) = ℓ ∘ σ⁻¹.
  have hArr : (fun k => (fun i => ell (θ i)) ((θ.trans σ).symm k)) =
      (fun j => ell (σ.symm j)) := by
    funext k
    simp only [Equiv.symm_trans, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [← hArr]
  rw [Equiv.trans_assoc]

/-!## 2.3 rank-compatibility for injective labels -/

/-- For an injective label array the index tie-breaker never fires, so the
    lower-key set is exactly the set of strictly-lower labels. -/
theorem keyBelow_eq_labelBelow (n a : Nat) (ell : Fin n → Fin a)
    (hinj : Function.Injective ell) (i : Fin n) :
    keyBelow n a ell i =
      (Finset.univ : Finset (Fin n)).filter (fun j => ell j < ell i) := by
  rw [keyBelow]
  apply Finset.ext
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [keyNat_lex]
  have hContra : ¬ (((ell k).val = (ell i).val) ∧ k.val < i.val) := by
    rintro ⟨heq, hval⟩
    have hki : k = i := hinj (Fin.ext heq)
    subst hki
    omega
  apply Iff.intro
  · intro h
    exact Or.elim h (fun ha => ha) (fun hc => False.elim (hContra hc))
  · intro h
    exact Or.inl h

/-- For injective labels, the reindexed array has the same lower-set cardinality
    at the reindexed position: the lower set is the image under `σ` of the
    original lower set, and a bijection preserves cardinality. -/
theorem rankVal_tieRank_invariant (n a : Nat) (hn : 0 < n) (ell : Fin n → Fin a)
    (hinj : Function.Injective ell) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    rankVal n a (fun j => ell (σ.symm j)) (σ i) = rankVal n a ell i := by
  rw [rankVal, rankVal]
  have hinj' : Function.Injective (fun j => ell (σ.symm j)) := by
    intro x y h
    have h' : ell (σ.symm x) = ell (σ.symm y) := by simpa using h
    have hmid := hinj h'
    simpa only [Equiv.apply_symm_apply] using congrArg (fun z => σ z) hmid
  have hL : keyBelow n a (fun j => ell (σ.symm j)) (σ i) =
      (Finset.univ : Finset (Fin n)).filter (fun j => ell (σ.symm j) < ell i) := by
    rw [keyBelow_eq_labelBelow n a (fun j => ell (σ.symm j)) hinj' (σ i)]
    apply Finset.ext
    intro j
    simp [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  rw [hL]
  rw [keyBelow_eq_labelBelow n a ell hinj i]
  -- The LHS filter set is the image under σ of the RHS filter set.
  have hImg : (Finset.univ : Finset (Fin n)).filter (fun j => ell (σ.symm j) < ell i) =
      ((Finset.univ : Finset (Fin n)).filter (fun k => ell k < ell i)).image σ := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨σ.symm j, h, Equiv.apply_symm_apply σ j⟩
    · rintro ⟨k, hk, heq⟩
      rw [heq.symm]
      simpa only [Equiv.symm_apply_apply] using hk
  rw [hImg]
  rw [Finset.card_image_of_injective (Finset.univ.filter (fun k => ell k < ell i))
      (fun x y (h : σ x = σ y) => by
        simpa only [Equiv.symm_apply_apply] using congrArg (fun t => σ.symm t) h)]

/-- **Key fact B** (Gate 6 §2.3): for injective labels the tie-breaker is
    irrelevant — `tieRank` equals the plain `rankEquiv`. -/
theorem tieRank_eq_rankEquiv_ofInjective (n a : Nat) (hn : 0 < n)
    (ell : Fin n → Fin a) (hinj : Function.Injective ell)
    (σ : Equiv.Perm (Fin n)) :
    tieRank n a hn ell σ = rankEquiv n a hn ell := by
  unfold tieRank
  apply Equiv.ext
  intro i
  rw [Equiv.trans_apply]
  apply Fin.ext
  have hL : ((rankEquiv n a hn (fun j => ell (σ.symm j))) (σ i)).val =
      rankVal n a (fun j => ell (σ.symm j)) (σ i) := by
    dsimp only [rankEquiv, Equiv.ofBijective]
    exact rfl
  have hR : ((rankEquiv n a hn ell) i).val = rankVal n a ell i := by
    dsimp only [rankEquiv, Equiv.ofBijective]
    exact rfl
  rw [hL, hR]
  exact rankVal_tieRank_invariant n a hn ell hinj σ i

/-!## 2.2 the tie-broken law is uniform (right-translation symmetry) -/

def ΩTieRank (n a : Nat) := (Fin n → Fin a) × Equiv.Perm (Fin n)

noncomputable instance tieRankPermNonempty (n : Nat) : Nonempty (Equiv.Perm (Fin n)) :=
  ⟨Equiv.refl (Fin n)⟩

theorem hNonemptyΩ (n a : Nat) (ha : 0 < a) : Nonempty (ΩTieRank n a) :=
  ⟨⟨fun _ => Fin.mk 0 ha, Equiv.refl (Fin n)⟩⟩

/-- The joint simultaneous-precomposition map `(ℓ, σ) ↦ (ℓ∘θ, θ.trans σ)`.
    Its inverse is the same map with `θ.symm`; together they form a bijection of
    the joint space. -/
noncomputable def precompMap (n a : Nat) (θ : Equiv.Perm (Fin n))
    (p : ΩTieRank n a) : ΩTieRank n a :=
  (fun i => p.1 (θ i), θ.trans p.2)

noncomputable def precompMapEquiv (n a : Nat) (θ : Equiv.Perm (Fin n)) :
    Equiv (ΩTieRank n a) (ΩTieRank n a) := by
  have hInj : Function.Injective (precompMap n a θ) := by
    rintro ⟨ℓ1, σ1⟩ ⟨ℓ2, σ2⟩ h
    have h1 := congrArg (fun p : ΩTieRank n a => p.1) h
    have h2 := congrArg (fun p : ΩTieRank n a => p.2) h
    have hℓ : ℓ1 = ℓ2 := by
      funext i
      have := congrArg (fun p : ΩTieRank n a => p.1 (θ.symm i)) h
      simpa only [precompMap, Equiv.apply_symm_apply] using this
    have hσ : σ1 = σ2 := by
      have h12 := congrArg (fun p : ΩTieRank n a => p.2) h
      have h13 := congrArg (fun e : Equiv.Perm (Fin n) => θ.symm.trans e) h12
      simpa only [precompMap, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans] using h13
    rw [hℓ, hσ]
  have hSurj : Function.Surjective (precompMap n a θ) := by
    intro q
    refine ⟨(fun i => q.1 (θ.symm i), θ.symm.trans q.2), ?_⟩
    dsimp only [precompMap]
    cases q with
    | mk l s =>
      have h1 : (fun i => (fun i => l (θ.symm i)) (θ i)) = l := by
        funext i
        simpa [Equiv.symm_apply_apply]
      have h2 : θ.trans (θ.symm.trans s) = s := by
        simpa [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
      rw [h1, h2]
  apply Equiv.ofBijective (precompMap n a θ)
  exact ⟨hInj, hSurj⟩

/-- **Generic finite-group fact** (Gate 6 §2.2): a `Dist` on a finite permutation
    group that is invariant under every right multiplication is the uniform
    distribution.  Any two elements differ by a right translation, so all point
    masses are equal, and normalization fixes the common value. -/
theorem mass_rightTrans {α : Type*}
    (ν : Dist (Equiv.Perm α))
    (hInvar : ∀ θ : Equiv.Perm α, (ν.map (fun e => θ.trans e)) = ν)
    (a b : Equiv.Perm α) :
    Dist.mass ν (a.trans b) = Dist.mass ν b := by
  have hInj : Function.Injective (fun e : Equiv.Perm α => a.symm.trans e) := by
    rintro x y (h : (fun e : Equiv.Perm α => a.symm.trans e) x = (fun e : Equiv.Perm α => a.symm.trans e) y)
    apply Equiv.ext
    intro z
    have hz := congrArg (fun t : Equiv.Perm α => t (a z)) h
    simpa [Equiv.trans_apply, Equiv.symm_apply_apply] using hz
  have hfb : (fun e : Equiv.Perm α => a.symm.trans e) (a.trans b) = b := by
    apply Equiv.ext
    intro z
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  have hmass : Dist.mass (ν.map (fun e => a.symm.trans e)) b = Dist.mass ν (a.trans b) := by
    dsimp only [Dist.mass]
    rw [Convexity.StdSimplex.weights_map]
    conv =>
      lhs
      rw [← hfb, Finsupp.mapDomain_apply_of_injective hInj ν.weights (a.trans b)]
  have heq : (ν.map (fun e => a.symm.trans e)) = ν := hInvar (a.symm)
  have hm : Dist.mass (ν.map (fun e => a.symm.trans e)) b = Dist.mass ν b := by rw [heq]
  simpa only [hmass] using hm

theorem uniformDist_of_rightInvariant (n : Nat)
    (ν : Dist (Equiv.Perm (Fin n)))
    (hInvar : ∀ θ : Equiv.Perm (Fin n), (ν.map (fun e => θ.trans e)) = ν) :
    ν = GSR.uniformDist (Equiv.Perm (Fin n)) := by
  haveI : Nonempty (Equiv.Perm (Fin n)) := tieRankPermNonempty n
  have hMass (e : Equiv.Perm (Fin n)) : Dist.mass ν e = Dist.mass ν (Equiv.refl (Fin n)) := by
    have hA := mass_rightTrans ν hInvar (e.symm) e
    simp only [Equiv.symm_symm, Equiv.symm_trans_self] at hA
    exact hA.symm
  have hCard : (Fintype.card (Equiv.Perm (Fin n)) : Rat) ≠ 0 := by
    intro h
    norm_cast at h
    have hpos : 0 < Fintype.card (Equiv.Perm (Fin n)) := by
      simp only [Fintype.card_perm]
      exact Nat.factorial_pos _
    omega
  have hConst : (Fintype.card (Equiv.Perm (Fin n)) : Rat) * Dist.mass ν (Equiv.refl (Fin n)) = 1 := by
    have hs : Finset.sum Finset.univ (fun e : Equiv.Perm (Fin n) => Dist.mass ν e) = 1 :=
      Dist.sum_mass ν
    rw [Finset.sum_congr rfl (fun e _ => hMass e)] at hs
    simp [Finset.sum_const, Finset.card_univ] at hs
    exact hs
  have hm : Dist.mass ν (Equiv.refl (Fin n)) = 1 / (Fintype.card (Equiv.Perm (Fin n)) : Rat) := by
    apply mul_left_cancel₀ hCard
    rw [hConst]
    field_simp [hCard]
  ext e
  simpa only [Dist.mass, GSR.uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm, one_div]
      using (hMass e).trans hm

/-- The law on `Equiv.Perm (Fin n)` obtained by pushing the **joint uniform**
    law on `(Fin n → Fin a) × Equiv.Perm (Fin n)` (independent uniform labels and
    tie-breaker) through `tieRank`.  This is exactly the finite-GSR rank law
    perturbed by random tie-breaking. -/
noncomputable def tieRankLaw (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    Dist (Equiv.Perm (Fin n)) :=
  let hFinPi : Fintype (Fin n → Fin a) := (by infer_instance : Fintype (Fin n → Fin a))
  let hFinPerm : Fintype (Equiv.Perm (Fin n)) := (by infer_instance : Fintype (Equiv.Perm (Fin n)))
  letI hΩ : Fintype (ΩTieRank n a) := Fintype.mk (Finset.product hFinPi.elems hFinPerm.elems)
    (fun p => Finset.mem_product.2 ⟨hFinPi.complete p.1, hFinPerm.complete p.2⟩)
  letI hNonempty : Nonempty (ΩTieRank n a) := hNonemptyΩ n a ha
  (GSR.uniformDist (ΩTieRank n a)).map (fun p => tieRank n a hn p.1 p.2)

theorem tieRankLaw_rightInvariant (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (θ : Equiv.Perm (Fin n)) :
    (tieRankLaw n a ha hn).map (fun e => θ.trans e) = tieRankLaw n a ha hn := by
  haveI : Nonempty (ΩTieRank n a) := hNonemptyΩ n a ha
  letI hFinPi : Fintype (Fin n → Fin a) := (by infer_instance : Fintype (Fin n → Fin a))
  letI hFinPerm : Fintype (Equiv.Perm (Fin n)) := (by infer_instance : Fintype (Equiv.Perm (Fin n)))
  letI hΩ : Fintype (ΩTieRank n a) := Fintype.mk (Finset.product hFinPi.elems hFinPerm.elems)
    (fun p => Finset.mem_product.2 ⟨hFinPi.complete p.1, hFinPerm.complete p.2⟩)
  unfold tieRankLaw
  rw [Convexity.StdSimplex.map_map]
  have hH (p : ΩTieRank n a) :
      (fun e => θ.trans e) (tieRank n a hn p.1 p.2) =
        tieRank n a hn (fun i => p.1 (θ i)) (θ.trans p.2) := by
    simpa only [tieRank] using (tieRank_precompEquiv n a hn p.1 p.2 θ).symm
  have hFn : (fun p : ΩTieRank n a => (fun e => θ.trans e) (tieRank n a hn p.1 p.2)) =
      (fun p => tieRank n a hn (fun i => p.1 (θ i)) (θ.trans p.2)) := by
    funext p
    exact hH p
  rw [hFn]
  have hH2 : (fun p : ΩTieRank n a => tieRank n a hn (fun i => p.1 (θ i)) (θ.trans p.2)) =
      (fun p => tieRank n a hn p.1 p.2) ∘ (precompMap n a θ) := by
    funext p
    simp only [Function.comp_apply, precompMap]
  rw [hH2, Convexity.StdSimplex.map_comp]
  have hFun : precompMap n a θ = (precompMapEquiv n a θ) := by
    funext p
    rfl
  have hBij : (GSR.uniformDist (ΩTieRank n a)).map (precompMap n a θ) =
      GSR.uniformDist (ΩTieRank n a) := by
    rw [hFun]
    exact GSR.map_bijective_uniformDist (precompMapEquiv n a θ)
  rw [hBij]

/-- **Key fact A** (Gate 6 §2.2): the tie-broken rank is *exactly uniform* on
    `Equiv.Perm (Fin n)` for every `a ≥ 1` — by right-translation symmetry, with
    no counting of injective arrays and no conditioning. -/
theorem tieRankLaw_uniform (n a : Nat) (ha : 0 < a) (hn : 0 < n) :
    tieRankLaw n a ha hn = GSR.uniformDist (Equiv.Perm (Fin n)) := by
  haveI : Nonempty (Equiv.Perm (Fin n)) := tieRankPermNonempty n
  apply uniformDist_of_rightInvariant n
  exact fun θ => tieRankLaw_rightInvariant n a ha hn θ

end Shufflemath
