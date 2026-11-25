module

public import Shufflemath.Gate6K1Capstone
public import Shufflemath.Gate6K1BridgeA
public import Shufflemath.FiniteDeck.RelabelInvariance
public import Shufflemath.Gate6K1Direct

@[expose]
public section

namespace Shufflemath

/-!
# Gate 6: generic bridge lemmas for the deterministic-start and GSR-pullback
    headlines

Generic (non-`99!`-enumerating) building blocks for finishing the Gate-6
three-round physical headline beyond the fiber-uniform start.  All the algebra
here is independent of concrete deck sizes; the one 99-card corollary
(`ideal_batch5b`) reuses an already-proved bridge.  These were supplied as the
uncompiled candidate `dev/qwen-hints/2026-11-25/GenericClosure.lean` and are
now integrated here.

* `uniform_same_image` — two injective maps with the same image push the
  uniform law to the same law (applies `GSR.map_injective_uniform_mass` twice).
* `range_iff_mem_of_card_eq` — a same-cardularity finite inclusion is onto
  (enumerates only the abstract choice domain, never the ambient type).
* `reset_absorption` / `equal_after_first_run` — ideal-reset kernel algebra:
  `H ; L = L` when `H = P ; U` and `L = P ; (Q ; U)`, transported past any
  number of runs.
* `action_comp_eq_conv` — a point-mass convolution bridge, lifted to kernels.
* `action_run_tv_noise` — every deterministic start for a state-independent
  noise law has the same TV (relabelling invariance).
* `permInverseEquiv` / `perm_inverse_uniform` / `perm_inverse_tv` — the
  rank-to-pullback inversion is a bijection preserving uniform law and TV.
* `ideal_batch5b` — the batch-5b headline as a corollary of the already-proved
  `paK_rho99Ideal_eq_localLift` (no new support-set equality).
-/

-- Both injective maps have the same image. Domain need not be a permutation type.
theorem uniform_same_image {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Nonempty A] (f g : A → B)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ b : B, (∃ a, f a = b) ↔ (∃ a, g a = b)) :
    (GSR.uniformDist A).map f = (GSR.uniformDist A).map g := by
  classical
  ext b
  change Dist.mass ((GSR.uniformDist A).map f) b =
    Dist.mass ((GSR.uniformDist A).map g) b
  rw [GSR.map_injective_uniform_mass f hf b, GSR.map_injective_uniform_mass g hg b]
  by_cases hb : ∃ a, f a = b
  · rw [if_pos hb, if_pos ((h b).mp hb)]
  · have hb' : ¬ ∃ a, g a = b := fun hgb => hb ((h b).mpr hgb)
    rw [if_neg hb, if_neg hb']

-- A same-cardinality finite inclusion is onto. Only the abstract choice
-- domain is enumerated, not the ambient type B.
theorem range_iff_mem_of_card_eq {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (R : Finset B) (hf : Function.Injective f)
    (hR : ∀ a, f a ∈ R) (hcard : Fintype.card A = R.card) (b : B) :
    (∃ a, f a = b) ↔ b ∈ R := by
  classical
  have hsub : (Finset.univ.image f) ⊆ R := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hR a
  have hc : (Finset.univ.image f).card = R.card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hcard]
  have heq : Finset.univ.image f = R :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hc])
  constructor
  · rintro ⟨a, rfl⟩
    exact hR a
  · intro hb
    rw [← heq] at hb
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb
    exact ⟨a, ha⟩

-- P reads membership; U resets order; Q exchanges memberships.
-- All algebra is independent of finiteness and concrete deck sizes.
theorem reset_absorption {X Y : Type*} (P : FiniteKernel X Y)
    (U : FiniteKernel Y X) (Q : FiniteKernel Y Y)
    (h : FiniteKernel.comp U P = FiniteKernel.identity) :
    FiniteKernel.comp (FiniteKernel.comp P U)
      (FiniteKernel.comp P (FiniteKernel.comp Q U)) =
      FiniteKernel.comp P (FiniteKernel.comp Q U) := by
  calc
    _ = FiniteKernel.comp P (FiniteKernel.comp U
          (FiniteKernel.comp P (FiniteKernel.comp Q U))) :=
      FiniteKernel.comp_assoc P U _
    _ = FiniteKernel.comp P (FiniteKernel.comp
          (FiniteKernel.comp U P) (FiniteKernel.comp Q U)) := by
      rw [FiniteKernel.comp_assoc U P (FiniteKernel.comp Q U)]
    _ = _ := by rw [h, FiniteKernel.comp_id_left]

theorem equal_after_first_run {X : Type*} (K : FiniteKernel X X)
    (μ ν : Dist X) (t : Nat)
    (h : FiniteKernel.apply μ K = FiniteKernel.apply ν K) :
    FiniteKernel.run K (t+1) μ = FiniteKernel.run K (t+1) ν := by
  rw [FiniteKernel.run_rec_eq, FiniteKernel.run_rec_eq, h]

-- The already-proved pointMass convolution bridge implies a kernel bridge.
-- Keep this generic; never expand concrete swapLaw or rho99Finite.
theorem action_comp_eq_conv {N : Nat} (S W : Dist (FiniteDeck.Deck N)) :
    FiniteKernel.comp (FiniteDeck.permutationActionKernel S)
      (FiniteDeck.permutationActionKernel W) =
      FiniteDeck.permutationActionKernel (FiniteDeck.conv S W) := by
  funext d
  have h := convPush_eq_pointMassComp S W d
  rw [FiniteKernel.apply_pointMass] at h
  exact h.symm

-- Every deterministic start for a state-independent noise law has the same TV.
-- If `simp only` does not bridge the coercions, make the function equality
-- explicit by funext; never unfold uniformDist or powConv.
theorem action_run_tv_noise {N : Nat} (W : Dist (FiniteDeck.Deck N))
    (t : Nat) (d : FiniteDeck.Deck N) :
    Dist.tv (FiniteKernel.run (FiniteDeck.permutationActionKernel W) t (Dist.pointMass d))
      (GSR.uniformDist (FiniteDeck.Deck N)) =
    Dist.tv (FiniteDeck.powConv W t) (GSR.uniformDist (FiniteDeck.Deck N)) := by
  classical
  let e := relabel_equiv d
  have hf : e.toFun = (fun p : FiniteDeck.Deck N => FiniteDeck.act p d) := by
    funext p
    rfl
  have hu : (GSR.uniformDist (FiniteDeck.Deck N)).map e.toFun =
      GSR.uniformDist (FiniteDeck.Deck N) := by
    rw [hf]
    exact uniformDeck_relabel_invariant N d
  have h := tv_bijective_invariance e (FiniteDeck.powConv W t)
    (GSR.uniformDist (FiniteDeck.Deck N))
  rw [hu, hf] at h
  rw [FiniteDeck.powConvRunEq]
  exact h

-- Rank-to-pullback conversion preserves distance from uniform. The embedded
-- ideal subgroup needs a separate inverse-invariance lemma (see A3).
def permInverseEquiv (X : Type*) : Equiv.Perm X ≃ Equiv.Perm X where
  toFun p := p.symm
  invFun p := p.symm
  left_inv p := Equiv.symm_symm p
  right_inv p := Equiv.symm_symm p

theorem perm_inverse_uniform {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty (Equiv.Perm X)] :
    (GSR.uniformDist (Equiv.Perm X)).map (fun p => p.symm) =
      GSR.uniformDist (Equiv.Perm X) := by
  exact GSR.map_bijective_uniformDist (permInverseEquiv X)

theorem perm_inverse_tv {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty (Equiv.Perm X)] (v : Dist (Equiv.Perm X)) :
    Dist.tv (v.map (fun p => p.symm)) (GSR.uniformDist (Equiv.Perm X)) =
      Dist.tv v (GSR.uniformDist (Equiv.Perm X)) := by
  classical
  have h := tv_bijective_invariance (permInverseEquiv X) v
    (GSR.uniformDist (Equiv.Perm X))
  change Dist.tv (v.map (fun p => p.symm))
    ((GSR.uniformDist (Equiv.Perm X)).map (fun p => p.symm)) = _ at h
  rw [perm_inverse_uniform] at h
  exact h

-- Batch 5b without a new support equality. Isolate the generic identity-map
-- lemma if `simpa` on this concrete specialization is expensive.
theorem ideal_batch5b :
    Gate6Crux.rho99Ideal = CommanderMembershipKernels.localLift
      (CommanderMembershipKernels.membership (Equiv.refl (Fin 99))) := by
  have h := paK_rho99Ideal_eq_localLift (Equiv.refl (Fin 99))
  rw [FiniteDeck.permutationActionKernel_eq_map] at h
  have hf : (fun p : Equiv.Perm (Fin 99) => p.trans (Equiv.refl (Fin 99))) = id := by
    funext p
    apply Equiv.ext
    intro i
    rfl
  rw [hf, Convexity.StdSimplex.map_id] at h
  exact h

end Shufflemath
