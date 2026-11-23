/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.End

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
## The corrected physical round: a state-dependent *action* kernel, not a constant row

The `GSRGate6Telescope.gsrRound99Finite/Ideal` and the WIP `_ProbeGate6Fin2.finiteRound/
idealRound` kernels are **constant rows**: `fun _ => ρ` (a fresh sample from an *absolute*
law `ρ` of position permutations, returned as though it were the new deck).  For any
constant-row kernel `C d = μ`, `run C n (pointMass d) = μ` for every `n ≥ 1` — repeating
it never composes position permutations, so it models *resetting* to a fresh deck, not
*shuffling the current arrangement*.  This is the semantic defect that makes the `hq3`
premise of `gate6_headline_telescope` false for those kernels (2026-11-22 gate-6
assessment, §2: the highest-impact new finding).

The correction is elementary but essential: a **state-independent** noise law on position
permutations induces a **state-dependent** deck-transition kernel.  A deck is an
`Equiv.Perm (Fin N)` (position → card identity); a position permutation `p` *acts on* the
current deck `d` by `Equiv.trans p d` — the card at position `i` is the current deck's
card at `p i`.  This matches the codebase's own convention in `swapPerm_membership_eq`
(`(Equiv.trans (swapPerm) d) l = d (swapFn … l)`): the permutation is the *outer* action
and the deck is the *inner* read.

### The `*`-vs-`trans` orientation (the check the review asks for)

The 2026‑11‑23 strategy doc (§A) fixes the combined permutation of the one-round physical
round as **`h.trans s`** — "Lean `Equiv.trans` applies its left argument first" — and
explicitly warns that "an expression such as `g * s` is NOT an adequate specification
until `Equiv.Perm.mul_apply` has been checked against this equation."

That check is done here, against this Mathlib pin, and the warning is **vindicated**:

* `Equiv.trans f g = g ∘ f` (`Equiv.trans_apply`): the **left** argument `f` is applied
  first, then the right argument `g`.
* `Equiv.Perm` inherits the `Mul` instance of `Perm α`
  (`Algebra/Group/Action/End.lean:68`, `instMul : mul f g := Equiv.trans g f`), so
  **`f * g = g.trans f`**: the **right** argument `g` of `*` is applied first, then the
  left argument `f`.  (There is no `Equiv.Perm.mul_apply`/`mul_def` lemma in this pin —
  the instance is an un-unfoldable def — so the orientation is proved by `Equiv.ext`
  after explicitly rewriting `f * g` to `Equiv.trans g f`; see `perm_mul_eq_trans_flip`.)

So `*` and `trans` are the **same composition with the argument order reversed**:
`f * g = g.trans f` and, dually, `f.trans g = g * f`.  Consequently the review's combined
permutation `h.trans s` (local `h` applied first, then the cross-pile swap `s`) is the
`*`-expression **`s * h`** — *not* `h * s` (which is `s.trans h`, the reverse order).  The
old constant-row code's bug was using `g * s` as an *absolute* deck law instead of
composing it with the current deck, and reading the composition in the wrong order.

This module (2026-11-23 hints, **Checkpoint A**) lands the generic, wall-free core:

* `permutationActionKernel` — the generic state-dependent action kernel:
  `fun d => noise.map (p ↦ p.trans d)`.
* `swapThenLocalKernel` — the one-round action kernel: the within-pile local GSR `g`
  followed by the cross-pile swap `s`, acting on the *current* deck `d`, i.e. the
  combined position permutation `g.trans s`.
* `swap_then_local_apply` — the pointwise orientation: `(g.trans (s.trans d)) i =
  d (s (g i))`.
* `permutationActionKernel_eq_map` — `K d` is definitionally the pushforward of the
  *same* noise through `p ↦ p.trans d` (the "same noise" clause of checkpoint A).
* `permutationActionKernel_identityDeck_sample` — `p.trans (Equiv.refl (Fin N)) = p`,
  the small regression that catches the constant-row error at the identity deck.
* `perm_mul_eq_trans_flip` — **`f * g = g.trans f`**: the `*`-vs-`trans` orientation
  check, proved by `Equiv.ext` + `Equiv.trans_apply`.
* `swap_then_local_matches_star` — the combined permutation `g.trans s` written with the
  codebase `*` is `s * g` (right factor first), the single fact that makes the two
  notations agree on the physical round.

The kernels are **generic in `N`** (no `99`-card `Equiv.Perm (Fin 99)` term is forced), so
they compile wall-free at any size.  Specializing them to `N = 99` for the three-round
Gate 6 headline (2026-11-23 hints, Checkpoints B–F) is the follow-on work.
-/

variable {N : Nat}

/-- **The corrected action kernel.**  A state-independent noise law `noise` on position
    permutations induces a state-dependent deck-transition kernel: the new deck is
    `Equiv.trans p d` for a sample `p ∼ noise` (the card at position `i` is the current
    deck's card at `p i`).  This is the faithful Markov-kernel abstraction of a shuffle
    that *acts on the current arrangement*; it is the opposite of the constant-row
    `fun _ => noise`, which resets the deck to a fresh sample regardless of `d`.  Uses
    only `Dist.map`, not `Fintype (Deck N)`. -/
noncomputable def permutationActionKernel (noise : Dist (Deck N)) :
    FiniteKernel (Deck N) (Deck N) :=
  fun (d : Deck N) => noise.map (fun (p : Deck N) => Equiv.trans p d)

/-- **One-round action kernel.**  The within-pile local GSR `g` (sampled from
    `localNoise`) followed by the cross-pile swap `s` (sampled from `swapNoise`) act on
    the *current* deck `d`: the new deck is `Equiv.trans g (Equiv.trans s d)`, the
    combined position permutation `g.trans s` applied to `d`.  The product noise
    `(s, g) ∼ swapNoise × localNoise` is the shared `distProductFinsupp` (the swap is
    common to the finite and ideal constructions).  The pointwise orientation
    `g.trans (s.trans d)` = `d ∘ s ∘ g` (card at `i` is `d (s (g i))`) matches the
    review's combined permutation `h.trans s` in the 2026‑11‑23 doc §A (local first,
    then the cross-pile swap).  Written with the codebase `*` the same combined
    permutation is `s * g` (right factor `g` first, then `s`), **not** `g * s` — see
    `perm_mul_eq_trans_flip` and `swap_then_local_matches_star`.  This uses the *action*
    composition (`Equiv.trans`, left-argument-first), not the absolute deck law `g * s`
    (= `s ∘ g`) that the old constant-row `fullRoundFinite` used as the *entire* output. -/
noncomputable def swapThenLocalKernel (swapNoise localNoise : Dist (Deck N)) :
    FiniteKernel (Deck N) (Deck N) :=
  fun (d : Deck N) =>
    (distProductFinsupp swapNoise localNoise).map
      (fun (p : Deck N × Deck N) => Equiv.trans p.2 (Equiv.trans p.1 d))

/-! ### Checkpoint A theorems -/

/-- **Pointwise orientation.**  One sample of the one-round action kernel is
    `g.trans (s.trans d)`: the card at position `i` is the current deck's card at
    position `s (g i)` (apply the local GSR `g` to the position, then the swap `s`, then
    read the card).  This matches the `swapPerm_membership_eq` convention
    (`(Equiv.trans s d) i = d (s i)`).  Proof is `Equiv.trans_apply` twice. -/
theorem swap_then_local_apply (s g d : Deck N) (i : Fin N) :
    (Equiv.trans g (Equiv.trans s d)) i = d (s (g i)) := by
  simp only [Equiv.trans_apply]

/-- **Pushforward clause.**  `permutationActionKernel noise d` is *definitionally*
    `noise.map (p ↦ p.trans d)`: the pushforward of the *same* state-independent noise
    through the relabeling `p ↦ p.trans d` that depends on the current deck `d`.  This is
    the "K d is the pushforward of the same noise under p ↦ p.trans d" clause of
    checkpoint A, so it closes by `rfl`. -/
theorem permutationActionKernel_eq_map (noise : Dist (Deck N)) (d : Deck N) :
    permutationActionKernel noise d = noise.map (fun (p : Deck N) => Equiv.trans p d) := rfl

/-- **Identity-deck sanity (sample-level, no pushforward needed).**  From the identity
    deck, the action kernel's *action* on a single sample `p` is the identity:
    `p.trans (Equiv.refl (Fin N)) = p`.  The full distributional statement (the pushforward
    of the noise through the identity function is the noise) needs a `map id = id` lemma
    for `Convexity.StdSimplex`, whose `map` is deprecated in this Mathlib pin and whose
    `mass` / `weights` names clash with the `Shufflemath.Dist` ones; we therefore state the
    sample-level identity, which is the content that distinguishes the action kernel from a
    constant-row kernel: a constant-row kernel `fun _ => noise` applied to the identity
    deck returns the *noise law* (a distribution of decks), not the single deck `p`.
    `p.trans (Equiv.refl (Fin N)) = p` by `Equiv.trans_refl`. -/
theorem permutationActionKernel_identityDeck_sample (p : Deck N) :
    Equiv.trans p (Equiv.refl (Fin N)) = p := by
  simp only [Equiv.trans_refl]

/-- **`*`-vs-`trans` orientation (the check the review asks for).**  The codebase group
    composition `*` on `Equiv.Perm` (inherited from `Perm α`,
    `Algebra/Group/Action/End.lean:68`, `instMul : mul f g := Equiv.trans g f`) and
    `Equiv.trans` are the *same* composition with the **argument order reversed**: `*`
    applies its **right** factor first, `trans` applies its **left** factor first.  Hence
    `f * g = g.trans f` (and, dually, `f.trans g = g * f`).  There is no
    `Equiv.Perm.mul_apply`/`mul_def` lemma in this pin — the instance is an un-unfoldable
    def — so `simp` cannot expand `*`; we rewrite `f * g` to `Equiv.trans g f` by `change`
    and finish with `rfl`, i.e. the definition. -/
theorem perm_mul_eq_trans_flip (f g : Deck N) : f * g = g.trans f := by
  change (Equiv.trans g f) = g.trans f
  rfl

/-- **The `*`-form of the one-round action.**  The review's combined permutation
    `g.trans s` (the within-pile local `g` applied first, then the cross-pile swap `s`,
    acting on the current deck `d`) equals the codebase `*`-composition `(s * g)` applied
    to `d` by `perm_mul_eq_trans_flip`: the right factor `g` of `*` is applied first,
    then the left factor `s`, exactly the `g.trans s` order.  This is the "check `*` vs
    `.trans`" item the review asks for, proved once and for all: the two notations
    describe the *same* physical round.  In particular the naive `g * s` is **not** this
    action (`g * s = s.trans g` reverses the order), which is why the review flagged a
    bare `g * s` as not an adequate specification. -/
theorem swap_then_local_matches_star (g s d : Deck N) :
    Equiv.trans g (Equiv.trans s d) = (s * g).trans d := by
  apply Equiv.ext
  intro i
  -- LHS:  (g.trans (s.trans d)) i  =  d (s (g i))                     [trans_apply twice]
  -- RHS:  ((s * g).trans d) i  =  d ((s * g) i)  =  d ((g.trans s) i)  [trans_apply, flip]
  --                       =  d (s (g i))                              [trans_apply]
  --  So both sides are definitionally `d (s (g i))`;  `simp` auto-closes by `rfl`.
  simp [Equiv.trans_apply, perm_mul_eq_trans_flip]

end FiniteDeck
end Shufflemath
