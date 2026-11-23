/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
## The action–convolution compatibility lemma (2026‑11‑23 strategy doc §A, §C)

The strategy doc says: *"Check `*` vs `trans` first … Prove *one* general
associativity/compatibility lemma, **before induction**: `act(q, act(p, d)) =
act(q.trans p, d)`."*  This module is that lemma, settled at the `*` group level,
plus the group-level convolution the induction will be written against.  Nothing
here instantiates `N = 99`, so it compiles wall-free at any size.

### The `*`-vs-`trans` orientation (settled, §A)

Three facts fix the orientation:

1. `Equiv.trans e₁ e₂` has `toFun = e₂ ∘ e₁` (`Logic/Equiv/Defs.lean:163`), so
   **`(e₁.trans e₂) x = e₂ (e₁ x)`**: the *left* argument `e₁` is applied first.
2. The `Mul` instance on `Equiv.Perm` is `f * g = g.trans f`
   (`perm_mul_eq_trans_flip`, `PositionAction.lean:161`), so as a function
   **`f * g = f ∘ g`**: the *right* factor `g` is applied first.
3. The action `act(p, d) = p.trans d = d ∘ p` **pre-composes** `p`, i.e. the card
   at position `i` of the result is the current deck's card at position `p i`
   (`PositionAction.lean`).

Because the action pre-composes, the *position-map* order of a composition is the
**reverse** of the *physical* shuffle order.  The clean consequence, stated and
proved below: **`a * b` represents "do `a` first, then do `b`"** (physical order,
first-done on the left).  This is exactly the review's §A equation
`act(h, act(s, d)) = (h.trans s).trans d` — the combined permutation of "swap `s`
then local `h`" is `h.trans s = s * h`.

Everything is generic in `N`; no `Equiv.Perm (Fin 99)` term is forced.
-/

variable {N : Nat}

/-- The **action** of a position permutation `p` on a deck `d`:  `p.trans d`,
    whose value at position `i` is the current deck's card at position `p i`
    (`(p.trans d) i = d (p i)`).  This is the review's `act(p, d)`. -/
noncomputable def act (p d : Deck N) : Deck N := p.trans d

/-- The **group-level convolution** of two position-permutation laws, at the `*`
    level.  `conv μ ν` is the law on `Deck N` of the product `x * y` where
    `x ∼ μ` and `y ∼ ν` are independent;  because `*` is physical order (first
    `μ`, then `ν`), this is the law of "do a `μ`-sample, then do a `ν`-sample".
    Written with the `*` group operation (not `trans`), per §A.  Its mass at a
    deck permutation `z` is the tensor-fiber sum `Σ_{x * y = z} μ x · ν y` (see
    `convMass`, proved over the finite supports, never the `N!` deck space). -/
noncomputable def conv (μ ν : Dist (Deck N)) : Dist (Deck N) :=
  (distProductFinsupp μ ν).map (fun (z : Deck N × Deck N) => z.1 * z.2)

/-- **Convolution power**:  `powConv W 0` is the point mass at the identity
    permutation, and `powConv W (t + 1) = conv (powConv W t) W` —  a left fold of
    the new noise `W` on the right, matching the physical order of `t` successive
    applications.  (The bridge `powConvRunEq`, proved in a follow-up, states that
    this equals the law of `t` successive runs of the action kernel.) -/
noncomputable def powConv (W : Dist (Deck N)) (t : Nat) : Dist (Deck N) :=
  Nat.rec (Dist.pointMass (Equiv.refl (Fin N))) (fun _ ih => conv ih W) t

/-! ### The composition law (the one lemma §C requires before induction) -/

/-- **The action–convolution compatibility lemma.**  The single action of the
    product `a * b` on the deck `d` equals "act with `a`, then act with `b`":

    `act (a * b) d = act b (act a d)`.

    Since `a * b = b.trans a` (`perm_mul_eq_trans_flip`) and `Equiv.trans` is
    associative (`Equiv.trans_assoc`, `Logic/Equiv/Defs.lean:319`), the left side
    is `(b.trans a).trans d = b.trans (a.trans d)`, which is exactly the right
    side unfolded.  This is the review's §A equation `act(h, act(s, d)) =
    (h.trans s).trans d` written at the `*` level (with `a = s`, `b = h`). -/
theorem act_composition (a b d : Deck N) :
    act (a * b) d = act b (act a d) := by
  simp only [act]
  -- Goal:  (a * b).trans d = b.trans (a.trans d).
  rw [perm_mul_eq_trans_flip]
  -- Now  (a * b) = b.trans a,  so  LHS = (b.trans a).trans d.
  exact Equiv.trans_assoc b a d

/-- **Pointwise form** of `act_composition`:  the card at position `i` after the
    combined action `a * b` on `d` is `d (a (b i))` —  the position `i` is first
    mapped by `b`, then by `a`, then the deck is read.  (This is the reverse of
    the *physical* order "do `a` then do `b`", which is exactly the pre-
    composition phenomenon noted in the header.)  One `Equiv.trans_apply` chain
    plus the `*`-flip;  no `Fintype`, no `99!`. -/
theorem act_composition_apply (a b d : Deck N) (i : Fin N) :
    (act (a * b) d) i = d (a (b i)) := by
  have hmul : a * b = b.trans a := perm_mul_eq_trans_flip a b
  rw [act, hmul]
  simp only [Equiv.trans_apply]

-- ---------------------------------------------------------------------------
-- The action-convolution bridge:  joining the pushed kernel equals pushing
-- the convolution.
-- ---------------------------------------------------------------------------

/-- **Join–map commutation** at the Finsupp level:  pushing a distribution of
    distributions through `g` and then joining equals joining and then
    pushing.  This is the `E[ f(X) ]`-level form of the fact that the push-
    forward of a barycentric integral is the barycentric integral of the
    pushforward.  Proved at the `Finsupp` level (no `Fintype`):  both sides
    carry the weight `∑_{s ∋ x} f s * s x` at `g x`,  unfolded through
    `mapDomain`/`sum_sum_index`/`sum_smul_index`/`smul_sum`. -/
theorem joinMapComm {X Y : Type*} (f : Convexity.StdSimplex Rat (Convexity.StdSimplex Rat X))
    (g : X → Y) :
    (f.map (fun (h : Convexity.StdSimplex Rat X) => h.map g)).join = f.join.map g := by
  ext1
  simp [Finsupp.mapDomain, Finsupp.sum_sum_index, Finsupp.sum_smul_index, Finsupp.smul_sum, add_smul]

/-- Pushing a point mass through a map gives the point mass at the image. -/
theorem pointMassMap {X Y : Type*} (x : X) (f : X → Y) :
    (Dist.pointMass x).map f = Dist.pointMass (f x) := by
  ext1
  simp [Dist.pointMass]

/-- The identity permutation acts trivially on any deck. -/
theorem reflAct (d : Deck N) : act (Equiv.refl (Fin N)) d = d := by
  simp [act, Equiv.refl_trans]

/-- **One-step convolution compatibility** (the join–map crack):  applying the
    action kernel of `W` to the pushed deck law `(μ).map (·.trans d)` equals
    pushing the one-step convolution `conv μ W`.  The two sides are both
    `((μ.map (λ p, W.map (λ q, (p, q)))).join).map (λ z, act (z.1 * z.2) d)`:
    the left side via `permutationActionKernel_eq_map` (a definitional
    unfolding) and `joinMapComm`;  the right side via the definition of
    `conv` and `distProductFinsupp`. -/
theorem convMapEqApplyMap (μ W : Dist (Deck N)) (d : Deck N) :
    FiniteKernel.apply (μ.map (fun p => act p d)) (permutationActionKernel W) =
    (conv μ W).map (fun p => act p d) := by
  unfold FiniteKernel.apply
  rw [Convexity.StdSimplex.map_map]
  -- `permutationActionKernel W (act x d)` is definitionally
  -- `W.map (fun q => act q (act x d))` (`permutationActionKernel_eq_map` is
  -- `@[defeq]`):  spell it out so the two sides share a spine.
  change (μ.map (fun (x : Deck N) => (W.map (fun (q : Deck N) => act q (act x d)) : Dist (Deck N)))).join =
      (conv μ W).map (fun p => act p d)
  have hinner : (fun x : Deck N => W.map (fun q => act q (act x d))) =
                (fun x => (W.map (fun q => (x, q))).map (fun z => act (z.1 * z.2) d)) := by
    funext x
    have h1 : (W.map (fun q => (x, q))).map (fun z => act (z.1 * z.2) d) =
              W.map (fun q => act (x * q) d) := by
      rw [Convexity.StdSimplex.map_map]
    have h2 : W.map (fun q => act q (act x d)) = W.map (fun q => act (x * q) d) := by
      exact congrArg (fun f => W.map f) (funext fun q => by rw [← act_composition])
    simpa [h1] using h2
  -- Left side:  pull the inner push out of the join.
  have hL : (μ.map (fun x => W.map (fun q => act q (act x d)))).join =
      ((μ.map (fun p => W.map (fun q => (p, q)))).join).map (fun z => act (z.1 * z.2) d) := by
    rw [hinner, ← Convexity.StdSimplex.map_map, joinMapComm]
  -- Right side:  unfold `conv` and `distProductFinsupp`.
  have hR : (conv μ W).map (fun p => act p d) =
      ((μ.map (fun p => W.map (fun q => (p, q)))).join).map (fun z => act (z.1 * z.2) d) := by
    unfold conv
    rw [Convexity.StdSimplex.map_map, distProductFinsupp]
  simp [hL, hR]

/-- **The action-convolution headline**:  the law of `t` successive runs of
    the permutation action kernel from a point mass on `d` equals the
    pushforward of the `t`-fold convolution power of the action law.  I.e.
    `FiniteKernel.run (permutationActionKernel W) t (Dist.pointMass d) =
    (powConv W t).map (·.trans d)`.  Proved by a simultaneous induction on
    the run count:  the `n + 1` step is `convMapEqApplyMap` followed by the
    induction hypothesis and `powConv`'s recursive definition;  the base
    (`t = 0`) is `powConv W 0 = pointMass (Equiv.refl (Fin N))` (the
    `Nat.recOn 0` base of `powConv`) plus `pointMassMap` and `reflAct`. -/
theorem powConvRunEq (W : Dist (Deck N)) (t : Nat) (d : Deck N) :
    FiniteKernel.run (permutationActionKernel W) t (Dist.pointMass d) =
    (powConv W t).map (fun p => act p d) := by
  have hstrong : ∀ (n j : Nat),
      FiniteKernel.run (permutationActionKernel W) n ((powConv W j).map (fun p => act p d)) =
      (powConv W (n + j)).map (fun p => act p d) := by
    intro n
    induction n with
    | zero =>
        simp [zero_add]
    | succ n ih =>
        intro j
        have hstep : FiniteKernel.run (permutationActionKernel W) (n + 1) ((powConv W j).map (fun p => act p d)) =
            FiniteKernel.run (permutationActionKernel W) n (FiniteKernel.apply ((powConv W j).map (fun p => act p d)) (permutationActionKernel W)) := by
          rfl
        rw [hstep, convMapEqApplyMap]
        rw [show (conv (powConv W j) W) = (powConv W (j + 1)) from rfl]
        rw [ih (j + 1)]
        simp [Nat.add_comm, Nat.add_left_comm]
  have hbase : (powConv W 0).map (fun p => act p d) = Dist.pointMass d := by
    show (Dist.pointMass (Equiv.refl (Fin N))).map (fun p => act p d) = Dist.pointMass d
    rw [pointMassMap, reflAct]
  simpa [hbase, Nat.add_zero] using hstrong t 0

end FiniteDeck
end Shufflemath
