module

public import Shufflemath.Finite
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderFiberWitness
public import Shufflemath.CommanderPermutation
public import Mathlib.Tactic

@[expose] public section

open Shufflemath
open BernoulliLaplace
open CommanderPermutation
open FiniteKernel

/-
## RESUME BLUEPRINT — 50th session: the μ_x invariance assembly

**This file is a plan/blueprint, NOT a buildable module** (it lives in `.pi-glla/`,
out of the Lake module graph, so a `sorry` here can never break a `lake build`).
Integrate the theorems below into `Shufflemath/CommanderPhysicalExchange.lean`,
where `.trans`/`.symm` on `Deck = Equiv.Perm (Fin 99)` resolve — an isolated-probe
build of this blueprint fails only on `Equiv.trans` dot-notation (the probe lacks
the library's full import context); the same code compiles in
`CommanderPhysicalExchange.lean`, as `leftOriginalCount_conjugate` /
`rawExchangeMembership_conjugate` (both using `d.trans g`) demonstrate.

**The target** (the A3 capstone's invariance input, and the 99-card instance of the
generic T4 measure-half):
    μ_x = comp (fiberLaw project project_surjective) rawExchangeMembership x
    μ_x.map (relabelMembership_equiv (g:Fin99→Fin99) g.bijective) = μ_x
  for a deck `g` with `g '' leftOrigSet = leftOrigSet` (a deck map preserving the
  originally-left set).

**Status of the pieces** (as of 50th session):
  - [DONE] `project_conjugate` / `leftOriginalCount_conjugate` — in the library
    (commit d04296e). This is the `hE : ∀ d, project (d.trans g) = project d` that
    step 1 (`fiberLaw_invariant_underFiberEquiv`) needs.
  - [DONE] `rawExchangeMembership_conjugate` — in the library (commit 6a45608).
  - [DONE] `fiberLaw_invariant_underFiberEquiv` — in the library (commit 7cbc3e6).
  - [TODO 1] `apply_deterministic_eq_map`: `apply μ (deterministic f) = μ.map f`,
    a general `Finite.lean` map/join identity. Prove by `ext y` + the Finsupp
    pushforward-sum simp set (`Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index,
    Finsupp.sum_smul_index, Finsupp.smul_sum`). The 47b1 probe reduced the LHS to
    `Σ_{a, f a = y} μ a` cleanly; the one open step is to NOT over-reduce the RHS
    `μ.map f` (drop `Convexity.StdSimplex.map` from the simp set so the RHS stays
    `μ.map f`, then close `Σ_{a, f a = y} μ a = μ.map f` by the `map` pushforward
    definition). Put it in `Finite.lean` next to `map_join_kernels`.
  - [TODO 2] `comp_L_Mk_eq_comp_E_L`: kernel equality
    `comp L (det M) = comp (det (fun d => d.trans g)) L` for L =
    rawExchangeMembership, M = relabelMembership_equiv g g.bijective. Proof:
    `funext d`; LHS = `(rawExchangeMembership d).map M`, RHS =
    `rawExchangeMembership (d.trans g)`; equal by `rawExchangeMembership_conjugate`
    (the Equiv's toFun IS `relabelMembership g g.bijective`).

**The 7-step calc** (below) type-checks modulo the two TODO lemmas. The
`deckTransEquiv` is the `Equiv Deck Deck` form of `fun d => d.trans g` needed by
`fiberLaw_invariant_underFiberEquiv` (which takes an `Equiv`, not a bare function).
-/

-- deck relabeling map and its genuine-Equiv form.
def deckEquiv (g : Deck) : Deck → Deck := fun d => d.trans g

def deckTransEquiv (g : Deck) : Equiv Deck Deck := by
  have hInj : Function.Injective (fun d => d.trans g) := by
    intro d1 d2 h
    simpa [Equiv.trans_assoc, Equiv.trans_self_symm, Equiv.trans_one] using
      (congrArg (fun x : Deck => x.trans g.symm) h)
  have hSurj : Function.Surjective (fun d => d.trans g) := by
    intro d
    exact ⟨d.trans g.symm, by simpa [Equiv.trans_assoc, Equiv.trans_self_symm, Equiv.trans_one]⟩
  exact Equiv.ofBijective (fun d : Deck => d.trans g) ⟨hInj, hSurj⟩

variable (g : Deck) (hfSet : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)

-- [TODO 1] the map/join identity (belongs in Finite.lean).
theorem apply_deterministic_eq_map {α β : Type*} (μ : Dist α) (f : α → β) :
    FiniteKernel.apply μ (FiniteKernel.deterministic f) = μ.map f := by
  sorry

-- [TODO 2] the exchange kernel conjugates at the kernel level.
theorem comp_L_Mk_eq_comp_E_L :
    FiniteKernel.comp rawExchangeMembership
        (FiniteKernel.deterministic (relabelMembership_equiv (g : Fin 99 → Fin 99) g.bijective)) =
      FiniteKernel.comp (FiniteKernel.deterministic (deckEquiv g)) rawExchangeMembership := by
  sorry

-- The full invariance (structure complete; fills in once the two TODO lemmas land).
theorem membershipLaw_invariant_underRelabeling (x : BernoulliLaplace.CommanderState) :
    (FiniteKernel.comp (FiberDisintegration.fiberLaw project project_surjective) rawExchangeMembership x).map
        (relabelMembership_equiv (g : Fin 99 → Fin 99) g.bijective) =
      FiniteKernel.comp (FiberDisintegration.fiberLaw project project_surjective) rawExchangeMembership x := by
  set K := FiberDisintegration.fiberLaw project project_surjective
  set L := rawExchangeMembership
  set M := relabelMembership_equiv (g : Fin 99 → Fin 99) g.bijective
  set E := FiniteKernel.deterministic (deckEquiv g)
  set Mk := FiniteKernel.deterministic M
  set μ := FiniteKernel.comp K L x
  change μ.map M = μ
  have h1 : μ.map M = FiniteKernel.apply μ (Mk) :=
    (apply_deterministic_eq_map μ (fun m : Membership => M m)).symm
  have h2 : FiniteKernel.apply μ (Mk) = FiniteKernel.apply (FiniteKernel.apply (K x) L) (Mk) := by
    have hμ : μ = FiniteKernel.apply (K x) L := by
      unfold FiniteKernel.comp FiniteKernel.apply
      rfl
    rw [hμ]
  have h3 : FiniteKernel.apply (FiniteKernel.apply (K x) L) (Mk) =
      FiniteKernel.apply (K x) (FiniteKernel.comp L (Mk)) :=
    FiniteKernel.apply_comp (K x) L (Mk)
  have h4 : FiniteKernel.apply (K x) (FiniteKernel.comp L (Mk)) =
      FiniteKernel.apply (K x) (FiniteKernel.comp (E) L) := by
    simpa using (comp_L_Mk_eq_comp_E_L).symm
  have h5 : FiniteKernel.apply (K x) (FiniteKernel.comp (E) L) =
      FiniteKernel.apply (FiniteKernel.apply (K x) (E)) (L) :=
    (FiniteKernel.apply_comp (K x) E L).symm
  have h6 : FiniteKernel.apply (K x) (E) = K x := by
    have hmap : FiniteKernel.apply (K x) (E) = (K x).map (deckEquiv g) :=
      (apply_deterministic_eq_map (K x) (deckEquiv g)).symm
    rw [hmap]
    have hinv : (K x).map (deckEquiv g) = K x :=
      CommanderMembershipExchange.fiberLaw_invariant_underFiberEquiv project
        CommanderFiberWitness.project_surjective x (deckTransEquiv g)
        (fun d => by simpa [Equiv.trans_apply] using
            (CommanderPhysicalExchange.project_conjugate d g hfSet))
    simpa [Equiv.coe_fn_mk] using hinv
  have h7 : FiniteKernel.apply (FiniteKernel.apply (K x) (E)) (L) = FiniteKernel.apply (K x) L := by
    rw [h6]
  have h8 : FiniteKernel.apply (K x) L = μ := by
    unfold FiniteKernel.comp FiniteKernel.apply
    rfl
  calc
    μ.map M = FiniteKernel.apply μ (Mk) := h1
    _ = FiniteKernel.apply (FiniteKernel.apply (K x) L) (Mk) := h2
    _ = FiniteKernel.apply (K x) (FiniteKernel.comp L (Mk)) := h3
    _ = FiniteKernel.apply (K x) (FiniteKernel.comp (E) L) := h4
    _ = FiniteKernel.apply (FiniteKernel.apply (K x) (E)) (L) := h5
    _ = FiniteKernel.apply (K x) L := h7
    _ = μ := h8

end
