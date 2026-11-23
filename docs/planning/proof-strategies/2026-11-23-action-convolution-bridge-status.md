# Action–convolution bridge: status and the one remaining lemma

Status: **2026‑11‑23**. Follows `2026-11-23-convolution-orbits-and-first-round-smoothing.md`
(§A "check `*` vs `trans`", §C "one general associativity/compatibility lemma, before
induction"). This note records what landed, the exact reduction of the probabilistic
bridge, and the single lemma that still blocks the headline.

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
