/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.Gate6TieRank
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-!
## Relabeling invariance of the physical-deck TV (batch 1 — the generic core)

The on-mission `TV < 1/1000` headline (`DobrushinDecay99.physicalExchange_decay_41_lt_thousand`)
is stated from a *fiber-uniform* start.  The objective asks for it from **any** starting
deck.  The documented bridge (2026-11-21 proof-hints §5/§7; the G6.6/G6.7 endgame) is the
**right-convolution / colorblind theorem**: because every random choice in the physical
exchange is position-based, the `t`-exchange law from a deck `d'` is the *card-relabeling
pushforward* of the law from `d`, i.e. `K^t(d') = K^t(d).map (·∘g)` for `g` the deck that
sends `d` to `d'`.  Since the uniform full-deck law is fixed by that same relabeling and TV
is invariant under a common bijective pushforward, `TV(K^t(d), U) = TV(K^t(d'), U)`, so the
fiber-uniform bound transports to every deterministic start.

This probe lands the **generic, wall-free core** of that theorem.  The statements are
polymorphic (no concrete 99-card `Equiv.Perm (Fin 99)` term is ever forced into a goal), so
they compile regardless of the N=99 whnf wall that bounds the batch-3/5b end-to-end theorems
(2026-12-09 batch-5b note: the wall is a kernel limitation on 99-card deck *equality* terms,
not a logic gap, and the generic-`n` forms build cleanly):

* `map_bijection_inverse` — pushing a law through a bijection and then its inverse is the
  identity (`map_map` + `symm_comp_self` + `map_id`).
* `tv_bijective_invariance` — TV is invariant under a *common bijective* pushforward
  (`=`, not just the `≤` of `tv_map_contraction`): `map_bijection_inverse` in both directions.
* `relabel_bijective` / `relabel_equiv` / `uniformDeck_relabel_invariant` — the deck-relabeling
  `e ↦ g ∘ e` (i.e. `e.trans g`, since `f.trans g = g ∘ f`) is a bijection of the deck space
  and the uniform full-deck law is fixed by it (`map_bijective_uniformDist`).

Batch 2 lands the *kernel* equivariance (the cross-pile exchange law is equivariant under
card relabeling, via the already-proven membership-level `rawExchangeMembership_conjugate`);
batch 3 composes them into the headline `TV(K^t(d), U) = TV(K^t(d'), U)` /
`TV(K^41(d), U) < 1/1000` for **any** deterministic `d`.
-/

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Pushing a law through a bijection `e` and then through its inverse `e.symm` is the
    identity: `(μ.map e).map e.symm = μ`.  `map_map` collapses the two pushforwards to one
    through the composed function, `Equiv.symm_comp_self` identifies that composition with
    the identity, and `map_id` closes.  This is the reverse-direction ingredient of the
    TV-invariance argument. -/
theorem map_bijection_inverse (e : α ≃ β) (μ : Dist α) :
    (μ.map e.toFun).map e.symm.toFun = μ := by
  have hcomp : (fun x => (e.symm.toFun) ((e.toFun) x)) = (id : α → α) := by
    funext x
    exact e.symm_apply_apply x
  calc
    (μ.map e.toFun).map e.symm.toFun = μ.map (fun x => (e.symm.toFun) ((e.toFun) x)) := by
      simp only [Convexity.StdSimplex.map_map]
    _ = μ.map (id : α → α) := by simp only [hcomp]
    _ = μ := by simp only [Convexity.StdSimplex.map_id]

/-- Total variation is invariant under a *common bijective* pushforward:
    `tv (μ.map ↑e) (ν.map ↑e) = tv μ ν` for a bijection `e : α ≃ β`.  The forward `≤` is
    `tv_map_contraction` (a deterministic map cannot raise TV); the reverse applies the same
    contraction to the inverse `↑e.symm`, and `map_bijection_inverse` rewrites the
    double-pushforward back to the original laws.  No concrete deck term is forced, so this
    is wall-free at any size (it instantiates at the 99-card deck space, whose *deck-equality*
    reductions are wall-bound but whose *pushforward-TV* reduction is not). -/
theorem tv_bijective_invariance [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (μ ν : Dist α) :
    Dist.tv (μ.map e.toFun) (ν.map e.toFun) = Dist.tv μ ν := by
  have hle : Dist.tv (μ.map e.toFun) (ν.map e.toFun) ≤ Dist.tv μ ν :=
    Dist.tv_map_contraction μ ν e.toFun
  have hge : Dist.tv μ ν ≤ Dist.tv (μ.map e.toFun) (ν.map e.toFun) := by
    have hc : Dist.tv ((μ.map e.toFun).map e.symm.toFun)
        ((ν.map e.toFun).map e.symm.toFun) ≤
      Dist.tv (μ.map e.toFun) (ν.map e.toFun) :=
      Dist.tv_map_contraction (μ.map e.toFun) (ν.map e.toFun) e.symm.toFun
    rw [map_bijection_inverse e μ, map_bijection_inverse e ν] at hc
    exact hc
  exact le_antisymm hle hge

variable {n : Nat}

/-- The deck-relabeling action `e ↦ g ∘ e` (pre-compose the deck permutation `e` with the
    card-identity relabeling `g`, i.e. `e.trans g` since `f.trans g = g ∘ f`) is a bijection
    of the deck space `Equiv.Perm (Fin n)`, with inverse `e ↦ g.symm ∘ e`.  This is the right
    action of the permutation group on itself.  Generic `n`; no 99-card term is forced. -/
theorem relabel_bijective (g : Equiv.Perm (Fin n)) :
    Function.Bijective (fun (e : Equiv.Perm (Fin n)) => Equiv.trans e g) := by
  refine ⟨?_, ?_⟩
  · -- injective: g ∘ e₁ = g ∘ e₂ → e₁ = e₂ (unpre-compose with g.symm)
    intro e₁ e₂ h
    apply Equiv.ext
    intro x
    have hp : (e₁.trans g) x = (e₂.trans g) x := Equiv.congr_fun h x
    have h₁ : g (e₁ x) = g (e₂ x) := by simpa [Equiv.trans_apply] using hp
    have h₂ : g.symm (g (e₁ x)) = g.symm (g (e₂ x)) := by simpa using h₁
    simpa [Equiv.symm_apply_apply] using h₂
  · -- surjective: every d = g ∘ (g.symm ∘ d), preimage d.trans g.symm
    intro d
    use Equiv.trans d (g.symm : Equiv.Perm (Fin n))
    apply Equiv.ext
    intro x
    simp [Equiv.trans]

/-- The deck-relabeling as an explicit `Equiv` (built from `relabel_bijective`), used to
    feed `map_bijective_uniformDist`. -/
noncomputable def relabel_equiv (g : Equiv.Perm (Fin n)) :
    Equiv (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) :=
  Equiv.ofBijective (fun (e : Equiv.Perm (Fin n)) => Equiv.trans e g) (relabel_bijective g)

/-- The uniform full-deck law is fixed by the deck-relabeling `e ↦ g ∘ e`: pushing the
    uniform law through the relabeling bijection gives the uniform law on the target.  This
    is the "the uniform full-deck law is invariant under the bijection `e ↦ g ∘ e`" clause
    of the right-convolution theorem.  Generic `n` (no 99-card term forced), so it is
    wall-free even though its 99-card *instantiation* would be. -/
theorem uniformDeck_relabel_invariant (n : Nat) (g : Equiv.Perm (Fin n))
    [Nonempty (Equiv.Perm (Fin n))] :
    (GSR.uniformDist (Equiv.Perm (Fin n))).map (fun (e : Equiv.Perm (Fin n)) => Equiv.trans e g) =
    GSR.uniformDist (Equiv.Perm (Fin n)) := by
  let hFinPerm : Fintype (Equiv.Perm (Fin n)) :=
    (by infer_instance : Fintype (Equiv.Perm (Fin n)))
  simpa only [relabel_equiv, Equiv.coe_ofBijective] using
    GSR.map_bijective_uniformDist (relabel_equiv g)

end Shufflemath
