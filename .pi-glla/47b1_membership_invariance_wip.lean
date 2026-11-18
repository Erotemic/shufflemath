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
  - [DONE — in the library] `apply_deterministic_eq_map` (Fintype version) is now in
    `Shufflemath/Finite.lean` (next to `apply_comp`), proved by `ext y` + `apply_mass`
    for the LHS and `mapDomain`/`Finsupp.sum_fintype` for the RHS (the Fubini side
    conditions close under a bare default `simp` with the imported `SMulWithZero` lemmas).
    ORIGINAL PLAN (now historical): `apply μ (deterministic f) = μ.map f`,
    a general `Finite.lean` map/join identity.
    **50th session — nearly solved.** The practical **Fintype version** is the one the
    μ_x case needs (α = Deck, β = Membership, both Fintype) and it goes:
      ```
      theorem apply_deterministic_eq_map [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
          (μ : Shufflemath.Dist α) (f : α → β) :
          Shufflemath.FiniteKernel.apply μ (Shufflemath.FiniteKernel.deterministic f) = μ.map f := by
        ext y
        rw [← Shufflemath.Dist.mass, Shufflemath.FiniteKernel.apply_mass]   -- LHS → ∑ a, μ a * (det f a).weights y
        simp only [Shufflemath.Dist.mass, Convexity.StdSimplex.map, Finsupp.mapDomain]
        rw [Finsupp.sum_fintype]     -- RHS (μ.weights.mapDomain f) y → Finset.sum
        <;> simp [Finsupp.smul_apply, Finsupp.single_apply, Finsupp.zero_apply, mul_comm]
        apply Finset.sum_congr rfl; intro a _
        simp [Shufflemath.FiniteKernel.deterministic, Shufflemath.Dist.pointMass,
              Convexity.StdSimplex.single, Finsupp.single_apply, eq_comm]
      ```
    **The one residual**: `rw [Finsupp.sum_fintype]` (≡ the Fubini `Finsupp.sum_finsetSum`,
    `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:418` `(∑ i ∈ s, f i).sum g =
    ∑ i ∈ s, (f i).sum g`) emits a bilinearity side condition `∀ i, Finsupp.single (f i) 0 = 0`
    (i.e. `0 • Finsupp.single (f i) = 0`, = `smul_zero`). The side condition + the RHS
    summand normalization (`(Finsupp.single (f a₁) m) y → m * (Finsupp.single (f a₁)) y`) need
    the right `SMul`-linearity simp lemmas. **Next session:** in the FULL library context
    (a probe that imports `Shufflemath.Finite` and the SMulWithZero file `Finite.lean` already
    imports, `Mathlib.Data.Finsupp.SMulWithZero`), close the side condition with
    `Finsupp.smul_zero`/`SMulWithZero`-class lemmas (grep `SMulWithZero` for the exact names —
    `Finsupp.smul_zero`/`smul_add` do NOT exist under those bare names in this Mathlib), or
    avoid it by `rw [Finsupp.sum_finsetSum]` with the two explicit `h₁`/`h₂` goals discharged
    by `ring`. Once it compiles, put it in `Finite.lean` next to `apply_mass`.
    **Once TODO 1 lands, TODO 2 is trivial** (`comp L (det M) = comp (det E) L` reduces to
    `funext; rw [apply_comp, apply_deterministic_eq_map]; exact rawExchangeMembership_conjugate`),
    and the 7-step μ_x calc assembles.
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
