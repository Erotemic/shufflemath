module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSR

@[expose]
public section

namespace Shufflemath

/-!
# Gate 6 K1 — combinatorial core: permuting a uniform `k`-subset is uniform.

The K1 gate identity (`_ProbeK1gap`) reduces (at the *membership* level) to a
standard symmetric-group fact: the pushforward of a uniform permutation through
the map `e ↦ (image of a fixed `k`-subset)` is the uniform law on `k`-subsets.

Strategy: let `G = Equiv.Perm (Fin n)` act on `Finset (Fin n)` by
`g • S = S.image g`.  The orbit of a `k`-subset `s` is **all** `k`-subsets
(transitivity: any `k`-subset can be sent to any other).  By the
orbit-stabilizer theorem, `|orbit s| · |stabilizer s| = |G|`; since the orbit
is the whole `k`-subset set, `|stabilizer s| = |G|/|{k-subsets}|`.  And the
fiber of `(e ↦ s.image e)` over any target `k`-subset `t` is in bijection with
the stabilizer (transport by a fixed `e₀` with `s.image e₀ = t`).  Hence every
`k`-subset gets the same pushforward mass `1/|{k-subsets}|` — the uniform law.
-/

/-- The type of `k`-subsets of `Fin n` (a `Fintype`). -/
abbrev SubsetsK (n k : Nat) := {s : Finset (Fin n) // s.card = k}

/-- A `k`-subset of `Fin n` with `0 < n`, `k ≤ n` is inhabited (the first `k`). -/
theorem SubsetsK_nonempty (n k : Nat) (hn : 0 < n) (hk : k ≤ n) : Nonempty (SubsetsK n k) := by
  classical
  let f : Fin k → Fin n := fun i => ⟨i.val, by nlinarith [i.2, hk]⟩
  have hinj : Function.Injective f := fun a b h => Fin.ext (congrArg (fun x => x.val) h)
  have hcard : (Finset.image f (Finset.univ : Finset (Fin k))).card = k := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin k)) hinj,
        Finset.card_univ, Fintype.card_fin]
  exact ⟨⟨Finset.image f (Finset.univ : Finset (Fin k)), hcard⟩⟩

/-- The permutation group of `Fin n` acts on `Finset (Fin n)` by `g • S = S.image g`.
    (A perm is a bijection, so the image is again a Finset and the action laws
    follow from `Finset.image` composing as function composition.) -/
instance permImageAction (n : Nat) : MulAction (Equiv.Perm (Fin n)) (Finset (Fin n)) where
  smul := fun g S => S.image g
  one_smul := fun S => by
    change S.image (1 : Equiv.Perm (Fin n)) = S
    simp
  mul_smul := fun g h S => by
    change S.image (g * h) = (S.image h).image g
    ext x
    simp [Equiv.trans_apply, Finset.mem_image]

/-- The `Fintype` cardinality of the membership subtype `{x // x ∈ s}` is `s.card`.
    (`Fintype.univ` for that subtype is `s.attach`, whose card is `s.card`.) -/
theorem subTypeCard (n : Nat) (s : Finset (Fin n)) : Fintype.card {x : Fin n // x ∈ s} = s.card := by
  show (Finset.univ : Finset {x : Fin n // x ∈ s}).card = s.card
  rw [← Finset.attach_eq_univ, Finset.card_attach]

/-- **Transitivity.** Any two `k`-subsets of `Fin n` lie in the same orbit of the
    permutation-image action: for `s, t` of cardinality `k` there is a permutation
    `g` with `s.image g = t`.  (A bijection `s ≃ t` and one `sᶜ ≃ tᶜ` glue to a
    permutation of `Fin n`; the glued map is injective because the `t`- and
    `tᶜ`-images are disjoint, and a finite-type injection is a permutation.) -/
theorem permImage_transitive (n k : Nat) (s t : Finset (Fin n)) (hs : s.card = k) (ht : t.card = k) :
    ∃ (g : Equiv.Perm (Fin n)), s.image g = t := by
  classical
  -- equal-card subtypes (concrete forms so `Fintype.card` and `⟨…⟩` resolve cleanly)
  have hS : Fintype.card {x : Fin n // x ∈ s} = k := by simp [subTypeCard, hs]
  have hT : Fintype.card {x : Fin n // x ∈ t} = k := by simp [subTypeCard, ht]
  have hSC : Fintype.card {x : Fin n // x ∈ sᶜ} = n - k := by
    simp [subTypeCard, Finset.card_compl, Fintype.card_fin, hs]
  have hTC : Fintype.card {x : Fin n // x ∈ tᶜ} = n - k := by
    simp [subTypeCard, Finset.card_compl, Fintype.card_fin, ht]
  -- bijective maps between the subtypes and between their complements
  have eST : {x : Fin n // x ∈ s} ≃ {x : Fin n // x ∈ t} :=
    Fintype.equivOfCardEq (Eq.trans hS hT.symm)
  have eSC : {x : Fin n // x ∈ sᶜ} ≃ {x : Fin n // x ∈ tᶜ} :=
    Fintype.equivOfCardEq (Eq.trans hSC hTC.symm)
  -- glue to a function on all of Fin n
  let f : Fin n → Fin n := fun x =>
    by
      by_cases hx : x ∈ s
      · exact Subtype.val (eST ⟨x, hx⟩)
      · exact Subtype.val (eSC ⟨x, by simpa using hx⟩)
  -- the `s`- and `sᶜ`-branches land in the disjoint sets `t` and `tᶜ`
  have himg_s : ∀ x ∈ s, f x ∈ t := by
    rintro x hx
    simpa [f, hx] using Subtype.mem_coe (eST ⟨x, hx⟩)
  have himg_sc : ∀ x, x ∉ s → f x ∈ tᶜ := by
    rintro x hx
    simpa [f, hx, Finset.mem_compl] using Subtype.mem_coe (eSC ⟨x, by simpa using hx⟩)
  -- injectivity
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · -- both in s:  via eST
        have hfx : f x = (eST ⟨x, hx⟩).val := by simpa [f, hx]
        have hfy : f y = (eST ⟨y, hy⟩).val := by simpa [f, hy]
        have hev : (eST ⟨x, hx⟩).val = (eST ⟨y, hy⟩).val := by rw [← hfx, ← hfy]; exact hxy
        have hes : eST ⟨x, hx⟩ = eST ⟨y, hy⟩ := by
          apply Subtype.val_injective
          exact hev
        exact congrArg (fun (z : {x : Fin n // x ∈ s}) => (z : Fin n)) (eST.injective hes)
      · -- x ∈ s (f x ∈ t),  y ∉ s (f y ∈ tᶜ):  disjoint
        have hxt : f x ∈ t := himg_s x hx
        have hyt : f y ∈ tᶜ := himg_sc y hy
        have hxtc : f x ∈ tᶜ := by simpa [hxy] using hyt
        have hnot : f x ∉ t := by simpa [Finset.mem_compl] using hxtc
        exact False.elim (hnot hxt)
    · by_cases hy : y ∈ s
      · -- x ∉ s (f x ∈ tᶜ),  y ∈ s (f y ∈ t):  disjoint
        have hxt : f x ∈ tᶜ := himg_sc x hx
        have hyt : f y ∈ t := himg_s y hy
        have hytc : f y ∈ tᶜ := by simpa [hxy] using hxt
        have hnot : f y ∉ t := by simpa [Finset.mem_compl] using hytc
        exact False.elim (hnot hyt)
      · -- both ∉ s:  via eSC
        have hx' : x ∈ sᶜ := by simpa [Finset.mem_compl] using hx
        have hy' : y ∈ sᶜ := by simpa [Finset.mem_compl] using hy
        have hfx : f x = (eSC ⟨x, hx'⟩).val := by simpa [f, hx]
        have hfy : f y = (eSC ⟨y, hy'⟩).val := by simpa [f, hy]
        have hev : (eSC ⟨x, hx'⟩).val = (eSC ⟨y, hy'⟩).val := by rw [← hfx, ← hfy]; exact hxy
        have hes : eSC ⟨x, hx'⟩ = eSC ⟨y, hy'⟩ := by
          apply Subtype.val_injective
          exact hev
        exact congrArg (fun (z : {x : Fin n // x ∈ sᶜ}) => (z : Fin n)) (eSC.injective hes)
  -- surjectivity
  have hf_surj : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ t
    · rcases (Equiv.surjective eST) ⟨y, hy⟩ with ⟨w, hw⟩
      exact ⟨w.1, by simp [f, w.2, hw]⟩
    · have hyt : y ∈ tᶜ := by simpa [Finset.mem_compl] using hy
      rcases (Equiv.surjective eSC) ⟨y, hyt⟩ with ⟨w, hw⟩
      have w1nS : w.1 ∉ s := (Finset.mem_compl : w.1 ∈ sᶜ ↔ w.1 ∉ s).mp w.2
      exact ⟨w.1, by simp [f, w1nS, hw]⟩
  have hf_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  let g : Equiv.Perm (Fin n) := Equiv.ofBijective f hf_bij
  refine ⟨g, ?_⟩
  -- `g.toFun` is definitionally `f`
  have : (g : Fin n → Fin n) = f := by
    change (g.toFun : Fin n → Fin n) = f
    rfl
  rw [this]
  -- s.image f = t
  ext x
  constructor
  · -- x = f x' with x' ∈ s  ⇒  x ∈ t
    intro h
    rcases (Finset.mem_image.1 h) with ⟨x', hx', rfl⟩
    exact himg_s x' hx'
  · -- x ∈ t:  eST is onto T, so some x' ∈ s has f x' = x
    rintro hx
    rcases (Equiv.surjective eST) ⟨x, hx⟩ with ⟨w, hw⟩
    have w1S : w.1 ∈ s := w.2
    have hfw : f w.1 = x := by simp [f, w1S, hw]
    exact Finset.mem_image.mpr ⟨w.1, w1S, hfw⟩

end Shufflemath
