# Action–convolution bridge: status and the one remaining lemma

Status: **2026‑11‑23; RESOLVED 2026‑12‑02** — the bridge is complete. `joinMapComm`,
`pointMassMap`, `reflAct`, `convMapEqApplyMap`, and `powConvRunEq` all landed in
`Shufflemath/FiniteDeck/ActionConvolution.lean` (see the addendum at the bottom). The
sections below are the original status note, kept for the reduction record.

## Landed (committed `1867eff`)

`Shufflemath/FiniteDeck/ActionConvolution.lean` (generic in `N`; wall-free; no
`sorry`/`admit`), wired into `dev/verify_next_phase.sh` next to
`Shufflemath.FiniteDeck.PositionAction`:

- `act (p d) := p.trans d` — the action (card at `i` is the current deck's card at
  `p i`).
- `conv μ ν := (distProductFinsupp μ ν).map (fun z => z.1 * z.2)` — the group-level
  convolution at the `*` level.
- `powConv W t := Nat.rec (Dist.pointMass (Equiv.refl (Fin N))) (fun _ ih => conv ih W) t`
  — a **left fold** of the new noise on the right, matching physical order.
- `act_composition : act (a * b) d = act b (act a d)` — **the §C "one lemma before
  induction"**, proved by `perm_mul_eq_trans_flip` + `Equiv.trans_assoc`.
- `act_composition_apply : (act (a * b) d) i = d (a (b i))` — pointwise, one
  `Equiv.trans_apply` chain.

## The `*`-vs-`trans` orientation (settled, §A)

- `Equiv.trans e₁ e₂` has `toFun = e₂ ∘ e₁` (`Logic/Equiv/Defs.lean:163`) →
  `(e₁.trans e₂) x = e₂ (e₁ x)`: **left applied first**.
- `f * g = g.trans f` (`perm_mul_eq_trans_flip`, `PositionAction.lean:161`) → as a
  function `f * g = f ∘ g`: **right factor applied first**.
- `act(p,d) = p.trans d = d ∘ p` **pre-composes** `p`.
- Net: the combined *position-map* order is the **reverse** of the *physical*
  shuffle order, giving the clean rule **`a * b` = "do `a` first, then do `b`"**.
  This matches the review's §A `act(h, act(s,d)) = (h.trans s).trans d`
  (`h.trans s = s * h`).

## The bridge, exactly

Target (headline):

```
powConvRunEq (W : Dist (Deck N)) (t : Nat) (d : Deck N) :
    run (permutationActionKernel W) t (Dist.pointMass d)
        = (powConv W t).map (fun p => act p d)
```

Proof by induction on `t`:

- **Base `t = 0`.** `run K 0 (pointMass d) = pointMass d`; RHS =
  `(Dist.pointMass (Equiv.refl (Fin N))).map (fun p => p.trans d) =
  Dist.pointMass (Equiv.refl (Fin N).trans d) = Dist.pointMass d`. Closes by
  `apply_pointMass`/`map` of a point mass + `Equiv.trans_refl`.

- **Step.** IH gives `run K t (pointMass d) = (powConv W t).map act_d` with
  `act_d p := act p d`. Need:

  ```
  apply ((powConv W t).map act_d) (permutationActionKernel W)
      = (conv (powConv W t) W).map act_d                     (∗)
  ```

  `(∗)` is a **general** statement (any `μ : Dist (Deck N)`, any `d`):
  `apply (μ.map act_d) (permutationActionKernel W) = (conv μ W).map act_d`.

  Chain for the LHS of `(∗)`:

  1. `apply X K = (X.map K).join` (`Finite.lean` `apply`).
  2. `map_map` (`Geometry/Convex/ConvexSpace/Defs.lean:216`,
     `(f.map g₁).map g₂ = f.map (g₂ ∘ g₁)`):
     `((μ.map act_d).map (permutationActionKernel W)) =
       μ.map (permutationActionKernel W ∘ act_d)`.
  3. `permutationActionKernel_eq_map` (rfl, `PositionAction.lean`):
     `permutationActionKernel W (act_d p) = W.map (fun q => q.trans (act_d p))`.
  4. `act_composition` (`ActionConvolution`):
     `q.trans (p.trans d) = (p * q).trans d = act_d (p * q)`.
  5. **Join-map commutation** (the blocker, below):
     `(μ.map (fun p => W.map (fun q => act_d (p * q)))).join
       = ((μ.map (fun p => W.map (fun q => (p, q)))).join).map
             (fun z => act_d (z.1 * z.2))`
     i.e. with `F := μ.map (fun p => W.map (fun q => (p,q)))` and
     `h z := act_d (z.1 * z.2)`:  `(F.map (·.map h)).join = F.join.map h`.

  RHS of `(∗)`: `conv μ W = (distProductFinsupp μ W).map (·*·)` and
  `distProductFinsupp μ W = (μ.map (fun p => W.map (fun q => (p,q)))).join = F.join`,
  so `(conv μ W).map act_d = (F.join.map (·*·)).map act_d = F.join.map h` by
  `map_map`.  So `(∗)` reduces to the join-map commutation.  Then
  `conv (powConv W t) W = powConv W (t+1)` by definition, closing the step.

## The one remaining lemma: **join-map commutation**

```
joinMapComm (f : Convexity.StdSimplex Rat (Convexity.StdSimplex Rat X)) (g : X → Y) :
    (f.map (·.map g)).join = f.join.map g
```

This is the **symmetric** of the **private** `Convexity.StdSimplex.map_join`
(`Geometry/Convex/ConvexSpace/Defs.lean:313`), which is inaccessible. It is pure
Finsupp hygiene (a monad `join`/`map` interchange); the content is trivial but the
closure in this Mathlib pin is fiddly.

**What I got close to** (throws no errors past a final `∑` goal):

```
ext1
simp [Convexity.StdSimplex.map, Convexity.StdSimplex.join,
      Finsupp.mapDomain, Finsupp.sum, add_smul,
      Finsupp.sum_sum_index, Finsupp.sum_smul_index, Finsupp.smul_sum]
```

Both sides reduce to a `Finsupp.sum`-level `∑`; the leftover is a double-index
`∑` that does not close under that simp set. The missing reindex is
`∑ d', (coeff d') • d'.weights  y  =  ∑ d, f.weights d • (d.weights.mapDomain g) y`
(the pushforward of the `.sum` through the `mapDomain`).

**Routes to try (in order):**

1. Add the `mapDomain` **linearity** lemmas to the simp set — they exist but are
   **not** `@[simp]`: `Finsupp.mapDomain_add`, `Finsupp.mapDomain_smul`
   (`LinearAlgebra/Finsupp/Defs.lean:151-152`, used to build `lmapDomain`). Combined
   with `Finsupp.map` being an `AddMonoidHom`, this should push the `.map g` inside
   the `∑` and let `Finsupp.sum`'s LSum associativity finish it.
2. If the raw `∑` still resists, reduce both sides by `Finsupp.ext` to pointwise
   `y : Y` and compute each as `∑ d, f.weights d • (d.weights.mapDomain g) y`
   explicitly, then `rfl`.
3. Nuclear but valid: prove it via `Convexity.StdSimplex.ext` / `weights_inj`
   (`Defs.lean:87`: `f.weights = g.weights ↔ f = g`) with a manual
   `Finsupp.sum`/`mapDomain` expansion (the private `map_join` is
   `ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]`; the
   only reason my copy lags is the `Finsupp.sum` (LSum) `.sum (fun d r => r • d.weights)`
   double-index normalization — the private file has `Mathlib.LinearAlgebra.Finsupp.LSum`
   in scope, so import it).

**Hand-verified math (the target, already checked by hand):** for the step `(∗)` at
a deck `y`, let `y' := y.trans d.symm`. Both sides have mass

```
∑_r  μ r  ·  W (y'.trans r.symm)      (r over all decks;  finite support ⇒ wall-free)
```

because the `·.trans ·` fibers are unique (cancellation): LHS fiber
`{s : (s.trans d).trans ? …}` reindexes to `{(r, y'.trans r.symm)}`. So once
`joinMapComm` lands, `(∗)` and `powConvRunEq` are `map_map`-only.

## Guardrails

- Stay **generic in `N`** — never instantiate `Equiv.Perm (Fin 99)` / `99!`
  (rule 9; `maxHeartbeats 0` forbidden). `Fintype (Equiv.Perm (Fin N))` is available
  (generic) via `Equiv.instFintype`/`fintypePerm` if a Fintype-based mass route is
  preferred, but the structural (`map_map` + `joinMapComm`) route is cleaner.
- Do **not** copy the private `map_join` proof by name; write the public
  `joinMapComm` in `ActionConvolution.lean` (or a small `Convexity.StdSimplex`
  helper module) and `import` `Mathlib.LinearAlgebra.Finsupp.LSum`.
- This is the **probabilistic bridge** the plan asked for; the follow-on after it is
  specializing `W` to the one-round `swapThenLocalKernel` noise and reading the
  Gate 6 headline off `powConvRunEq`.

## Addendum — RESOLVED (2026‑12‑02): the bridge is complete

`Shufflemath/FiniteDeck/ActionConvolution.lean` now carries, all generic in `N`,
wall-free, no `sorry`/`admit`, zero new warnings:

- `joinMapComm {X Y : Type*} (f : Convexity.StdSimplex Rat (Convexity.StdSimplex Rat X))
    (g : X → Y) : (f.map (·.map g)).join = f.join.map g`
  — proved by **route 2/3 hybrid**: `ext1` then **one** controlled
  `simp [Finsupp.mapDomain, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
  Finsupp.smul_sum, add_smul]` (no `Finsupp.sum`/`LSum` names — they re-expand and
  re-swell; both sides normalize to the same double-index `∑` under that set).
- `pointMassMap {X Y : Type*} (x : X) (f : X → Y) : (Dist.pointMass x).map f =
  Dist.pointMass (f x)` — `ext1; simp [Dist.pointMass]`.
- `reflAct (d : Deck N) : act (Equiv.refl (Fin N)) d = d` — `simp [act, Equiv.refl_trans]`.
- `convMapEqApplyMap (μ W : Dist (Deck N)) (d : Deck N) :
  FiniteKernel.apply (μ.map (·.trans d via act)) (permutationActionKernel W) =
  (conv μ W).map (fun p => act p d)` — the one-step crack: `unfold FiniteKernel.apply;
  rw [map_map]`; `change` to the definitional `W.map` form of the kernel (the
  `@[defeq]` `permutationActionKernel_eq_map` — `rw` on it inside a nested lambda is
  unreliable, `change` is not); `hinner` (product-level spelling, `funext` +
  `map_map` + `act_composition`); `hL` via `rw [hinner, ← map_map, joinMapComm]`;
  `hR` via `unfold conv; rw [map_map, distProductFinsupp]`; `simp [hL, hR]`.
- `powConvRunEq (W : Dist (Deck N)) (t : Nat) (d : Deck N) :
  FiniteKernel.run (permutationActionKernel W) t (Dist.pointMass d) =
  (powConv W t).map (fun p => act p d)` — the **headline**: simultaneous induction
  on the run count `n` (the law is the `j`-fold power, so the step needs the IH at
  `j+1`: introduce `n`, induct, *then* `intro j`; the step is `hstep` (`rfl` from the
  `run` definition) + `convMapEqApplyMap` + `conv (powConv W j) W = powConv W (j+1)`
  (definitional) + IH + additive `simp [add_comm, add_left_comm]`); base is
  `powConv W 0 = pointMass (Equiv.refl (Fin N))` (the `Nat.recOn 0` base of
  `powConv`) + `pointMassMap` + `reflAct`.

**Naming pitfalls (cost a full day — read before touching this area again):**

1. `Shufflemath.apply` / `Shufflemath.run` **do not exist** — `apply`, `run`, `comp`,
   `deterministic`, `identity` live in **`Shufflemath.FiniteKernel`** (a namespace
   inside the `noncomputable section` of `Finite.lean`). Unqualified `apply` in a
   module file resolves to a stray *local* declaration (from some exposed variable)
   and fails with `Local variable 'apply' has no definition` / `Function expected` —
   not `Unknown identifier`. Always write `FiniteKernel.apply` / `FiniteKernel.run`
   (unqualified `FiniteKernel.` works from anywhere inside `namespace Shufflemath`).
2. `pointMass`/`mass` live in **`Shufflemath.Dist`** — `Dist.pointMass` works
   unqualified inside the `Shufflemath` namespace.
3. `.map`/`.join` **method** syntax on `Dist`-typed terms only resolves when the
   file **directly imports** `Mathlib.Geometry.Convex.ConvexSpace.Defs` (the
   method lives in `Convexity.StdSimplex` and the `Dist` abbreviation is not
   unfolded for method lookup). `Shufflemath.Finite`'s import of that file is not
   enough for downstream files.
4. **Never put a `join`-expanding `simp` on a law-of-laws term** — the default
   simp set pulls `sConvexComb`-dependent lemmas that spawn uncloseable
   `⊢ Convexity.sConvexComb` side goals (the same swamp that stalled the Nov 24
   batch-5b headline). Keep `join` under **`rw`** (e.g. `rw [joinMapComm]`), or
   keep it out of the simp set entirely; `rw`'s final definitional check happily
   closes `X.map h = ((X).map h)`-style leftovers, so the trailing `rfl`/`simpa`
   are often already redundant (the linter says so — heed it).
5. `permutationActionKernel_eq_map` is `@[defeq]` — usable as a definitional
   `change` (reliable) or a top-level `rw` (works); inside a lambda under another
   `map`, prefer `change` to the whole goal.

Build state at resolution: `lake build` (full project, 3272 jobs) succeeds; the only
warnings in the new code were three linter nits (`Dist.mass` / `Nat.add_assoc`
unused in two simp sets, `simpa`→`simp`), all fixed.
