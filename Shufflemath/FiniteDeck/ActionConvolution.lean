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

end FiniteDeck
end Shufflemath
