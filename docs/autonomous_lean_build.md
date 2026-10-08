# Autonomous Lean Formalization Build — Handoff & Resume Document

**Status:** ACTIVE. **Owner:** any pi agent pointed at this file.
**Deadline: Mon Oct 12 22:27:06 EDT 2026.**

## 0. Standing rules for the agent reading this document (non-negotiable)

1. **Do not stop, ask, or end the session before Mon Oct 12 22:27:06 EDT 2026.**
   This is a long autonomous build. You **will be compacted multiple times**;
   compaction is normal and is not a stopping signal.
2. **After every compaction, do exactly this, in order:**
   a. Read this document top to bottom.
   b. Run `git log --oneline -10` and `git status --short` in `/home/joncrall/code/shufflemath`.
   c. Run `lake build` to confirm the tree is green (if red, fix before anything else).
   d. Resume work at the last unchecked item in §7 (Progress) / "Next action".
3. **Small batches only.** One batch = 1–3 related lemmas/theorems in one file.
   Each batch must end with: `lake build` green → `git add` + `git commit`.
   Never let the working tree carry more than one batch of uncommitted work.
4. **Commit trailer (exact, from 2026-10-04 onward):**
   `Co-authored-by: Qwen3.8-27B-W4A16-AutoRound <noreply@qwen.ai>` — the model
   is the W4A16-AutoRound quantization of Qwen3.8-27B
   (`hf://dbirks/Qwen3.8-27B-W4A16-AutoRound`) served through a vLLM
   `hyperqwen` deployment (image `ghcr.io/syv-ai/hyperqwen:sha-684e927`, MTP
   spec, long context, prefix caching); the LiteLLM model name is
   `qwen3.8-27b-dbirks-hyperqwen-long`. Older commits in this session's
   history carry the earlier `Qwen3.8:27b <noreply@openai.com>` form —
   **do not rewrite history**; use the new form only for new commits.
   Subject line: short imperative, e.g. `Add kernel composition associativity`.
5. **Every commit must build.** `lake build` (full repo, not just one file) must
   pass before you commit. `./dev/verify.sh` (lake update + build + python tests)
   must pass at the end of each priority (A, B, C, …).
6. **Keep this document updated.** After each commit, tick the item in §7 and
   adjust "Next action". This file is the only thing a compacted/fresh agent
   can trust; the conversation is not.
7. **Do not stop early even if A–G are all done.** Fall through to §4-H
   stretch goals, then to verification pass (re-run `./dev/verify.sh`, audit
   docstrings, re-check §6 regression values), until the deadline.
8. **Stuck protocol.** If a single proof resists ~2 build iterations, write a
   `-- TODO(proof): <sketch>` comment at the exact location, commit what
   builds, move to the next item, and return later. Never leave a broken
   build, never leave a `sorry`.
9. **Taste rules:** see §8. Exact rationals only; no `set_option maxHeartbeats 0`;
   no floating point in proofs; docstring on every nontrivial theorem;
   no sweeping refactors of existing names.

## 1. Background (one minute)

`shufflemath` studies constrained physical card shuffling: which finite
sequences of cuts, mashes, and exchanges drive a deck to uniform fastest.
Three tracks: literature (`docs/`), exact finite computation
(`experiments/bernoulli_laplace.py`), and this Lean library (`Shufflemath/`).

Two models, never conflate them:

- **Bernoulli–Laplace (BL):** macrostate = count of original-left cards in the
  left pile after exchanging `k` cards between two piles. A projection of the
  full process; macrostate mixing is *not* full-deck mixing.
- **GSR (Gilbert–Shannon–Reeds):** riffle shuffle theory (stretch goal §4-H).

Three distances, never conflate them: total variation (the one formalized),
separation distance, and event probability.

**Architecture rules (binding):**

- `Dist α := Convexity.StdSimplex Rat α` — the *only* probability type.
  Nonnegativity and unit mass live in the type; never build a parallel
  probability structure.
- `FiniteKernel α β := α → Dist β` — the semantic kernel.
- Matrices (`Matrix α β Rat`) are a *derived* computational representation;
  the bridges live in `Shufflemath/Matrix.lean`.
- All arithmetic in `Rat` (ℚ). Executable exact certificates use
  materialized `Array` tables + `native_decide` (existing pattern in
  `Shufflemath/BernoulliLaplace.lean`); symbolic theorems must be proved
  symbolically (Vandermonde etc.), not decided.

## 2. Environment

- Repo: `/home/joncrall/code/shufflemath`, branch `main`.
- Toolchain: `leanprover/lean4:v4.34.0` (pinned in `lean-toolchain`);
  mathlib v4.34.0 pinned in `lakefile.lean`. Do not bump either.
- Build: `lake build`. Full verify: `./dev/verify.sh`.
- `.lake` on this VM is a **bind mount** from `/var/cache/lake` (ext4, fast).
  Check with `mount | grep lake` / `df -hT .lake`. If you are on a fresh
  VM where `.lake` is virtiofs: first `sudo cp -a .lake /var/cache/lake/<repo>/.lake`
  (seed, only if a build already exists), then run
  `submodules/aiq-lean-formalization-tools/scripts/setup-lake-cache.sh`
  (`--all` after reboots, `--status` to inspect; bind mount, never a symlink).
- mathlib sources are browsable for exact lemma names:
  `.lake/packages/mathlib/Mathlib/…` — grep before writing proofs.
  Verified hooks you can rely on are listed in §5.
- Lean tooling from the submodule (`aiq-lean`, `leanq`) is available for
  audits; not required for the main build. If you rename or move a tracked
  declaration, update any census ledger in the same commit.

## 3. Current state — exact inventory (as of 2026-10-05, pre-build)

`Shufflemath.lean` imports: `Finite`, `Matrix`, `TotalVariation`,
`Perturbation`, `Dobrushin`, `Cost`, `BernoulliLaplace`,
`BernoulliLaplaceGeneral` (the last added with the GPT-review #8 fix;
new modules are added here when created).

**`Shufflemath/Finite.lean`** — `namespace Shufflemath`, `noncomputable section`:
- `Dist α := Convexity.StdSimplex Rat α` (abbrev).
- `Dist.mass μ x := μ.weights x`; `mass_nonneg`; `sum_mass` (`= 1`, simp).
- `Dist.ofFun f hnonneg htotal : Dist α` (via `Finsupp.equivFunOnFinite.symm`);
  `mass_ofFun` (simp).
- `Dist.pointMass x := Convexity.StdSimplex.single x`; `mass_pointMass` (simp, needs `DecidableEq`).
- `FiniteKernel α β := α → Dist β`; `deterministic f`; `identity`;
  `apply μ K := (μ.map K).join`; `comp K L := fun x => ((K x).map L).join`;
  `run K : Nat → Dist α → Dist α` (recursion on n).
- `apply_pointMass` (simp), `deterministic_apply_pointMass` (simp).
- **Done (Priority A, commit 754dfa9):** `Dist.join_sConvexComb`; private
  weights-level `map_join_kernels` / `join_join_kernels`; `apply_comp` (simp),
  `comp_assoc` (simp), `comp_id_right` (simp), `comp_id_left` (simp),
  `apply_id_left` (simp); `compPow` with `compPow_zero` / `compPow_succ`
  (simp, definitional); `run_succ` / `run_succ_add` / `run_apply_self` (simp)
  via private simultaneous induction (`run_rec_eq` bridges `n + 1` / `Nat.succ`
  forms); `run_compPow` (simp: `run K n mu = apply mu (compPow K n)`).
  (Priority A complete; the matrix bridges live in `Matrix.lean`, see below.)
- **Done (Priority B, commit 90fa10c):** `apply_mass [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] (μ : Dist α) (K : FiniteKernel α β) (x : β) :
  mass (apply μ K) x = ∑_j mass μ j * mass (K j) x` — the mass-level Fubini
  bridge for kernel pushforward (weights_join + weights_map + Finsupp.sum_apply
  + Finsupp.sum_finsetSum + Finsupp.sum_single_index; NOT @[simp] — it
  re-introduces sums). The `FiniteKernel` variable block carries **no**
  instances, so Fintype theorems state them per-theorem (file idiom).

**Lean-mechanics notes learned the hard way (keep these!):**
- The compiler turns tail-recursive `def`s into `Nat.brecOn` with an opaque
  `_f` wrapper that stalls whnf on variable-level successors inside heavy
  `StdSimplex` proof terms. `run` is therefore written with an explicit
  `Nat.recOn`; the kernel then reduces `run K (Nat.succ n) _` by clean
  recursor steps. Non-tail-recursive defs (`compPow`) compile to plain
  matches whose equation lemmas are `rfl`.
- `Nat.recOn` / `Nat.rec` zero/successor reductions fire under **kernel
  defeq** (`rfl`, `exact`) but **not** under `simp`'s normalizer. In zero
  branches use `rw [theorem]` for the non-reducible side, then `rfl`.
- `induction n` hands succ-branch goals over in `n + 1` (add) form, not
  `Nat.succ` form; `rw [Nat.succ_eq_add_one]` / `[← Nat.succ_eq_add_one]`
  switches between the two display forms. `rw` never reduces recursive
  defs; only pure syntactic pattern matching is safe.
- `unfold apply, comp` is a parse bomb (comma after a tactic name); use two
  separate `unfold` lines.
- **`@[defeq]` lemmas are invisible to `rw`.** `Finsupp.smul_apply`
  `((b • v) a = b • v a)` is `@[defeq]`: `rw` reports "Did not find an
  occurrence of the pattern" even when the target visibly contains it. Bridge
  with `change` (kernel defeq includes `@[defeq]` transparency), then continue
  with `rw`/`rfl`.
- **Keep `Matrix`-typed arguments until after the matrix `*`/`vecMul`
  rewrite.** `Matrix` is an opaque `def` at the `implicit` transparency level:
  if you `unfold toMatrix` before `Matrix.mul_apply`, the `HMul`/application
  subterms stop being type-correct and the following `rw`/`simp` fail ("Did
  not find an occurrence" / "made no progress" / "function expected"). Do the
  matrix-shaped rewrites first, then unfold, then finish with `change` + `rfl`.
- **Def equation theorems can refuse to rewrite dot-notation forms**
  ("Failed to rewrite using equation theorems for `toMatrix`" on
  `(K.compPow n).toMatrix`). A `change` to the fully-unfolded target
  (kernel defeq) is the robust escape hatch.
- `rw [h1, h2]` requires **every** listed rule to fire; a rule that matches
  nothing fails the whole `rw`. And `rw` auto-closes a goal that becomes
  syntactically `x = x` after the last rewrite (no trailing `rfl` needed then;
  a trailing `rfl` on an already-closed goal is a "No goals" error).
- **`rw` has a binder-capture restriction (bit us hard in B4).** A rewrite
  pattern's metavariables cannot be instantiated with terms containing
  variables bound *outside* the matched subterm: rewriting the inner sum
  `∑ i ∈ s, b i j` inside a goal `∑ j, a j * (…)` fails ("Did not find an
  occurrence") because `?f` would have to capture the outer `j`. Workaround:
  provide the lambda **explicitly** — `rw [Finset.sum_congr rfl fun j _ =>
  (Finset.sum_insert hc (f := fun i => b i j)).symm]` — and wrap coefficient
  factors in `congrArg (fun u => a j * u)`. `conv` is the alternative but
  multi-line `conv in (…)` lambdas are parse bombs.
- **`set_option` is NOT a tactic.** Inside `by` it's a parse error; at the
  top level of a proof term use `:= set_option maxHeartbeats N in by …`,
  **but the `in` scope does not cover the final kernel check** (it runs at
  declaration end, under the default heartbeat) — raising the heartbeat this
  way did NOT fix whnf timeouts. Command-level `set_option` before the
  declaration works for linter options (e.g.
  `set_option linter.overlappingInstances false`).
- **`end section` must be `end <section-name>`** (`end PositiveSet`).
- **`max` on `Rat` displays as `⊔` (sup) at kernel level**; the unifier does
  not delta-reduce `max` to `⊔`, so `exact maxDiffAbs` with implicit `{a b}`
  fails to unify. Name the implicit args: `maxDiffAbs (a := p x) (b := q x)`.
- **v4.34.0 Finset/order lemma inventory (grep results):** `le_or_lt` /
  `lt_or_lt` do NOT exist — only `le_total : a ≤ b ∨ b ≤ a`; `abs_add` does
  not exist — use `abs_add_le (a b) : |a + b| ≤ |a| + |b|`; `Or.resolveLeft`
  does not exist; `Finset.sum_congr` takes **two** explicit args `(h : s₁ =
  s₂) (h₂ : ∀ x ∈ s₂, f x = g x)`; `Finset.sum_nonneg` (not deprecated
  `sum_nonneg'`) has the membership arg `(i, x ∈ s)`; `Finset.single_le_sum`
  exists, `Finset.le_sum_of_nonneg` does not; `max_nonneg` does not exist —
  use `le_max_left 0 x`; `Finset.abs_sum_le_sum_abs (f) (s) : |∑ i ∈ s, f i|
  ≤ ∑ i ∈ s, |f i|`; `Fintype.sum_mul_sum` (product of two sums = double sum
  of products — only for **separable** factors); `Finset.sum_univ_pi` /
  `prod_univ_sum` (univ.pi ↔ piFinset) exist but there is **no plain
  `∑_i ∑_j f i j = ∑_j ∑_i f i j` swap lemma** — prove it locally (see
  `Dist.double_sum_pullout`).
- **Finsupp sum machinery (verified B4):** `Finsupp.sum` is definitionally
  `∑ a ∈ f.support, g a (f a)`; `Finsupp.sum_apply` pushes an evaluation
  inside `.sum`; `Finsupp.sum_fintype` (needs `g i 0 = 0`) converts to univ
  sums; `Finsupp.sum_finsetSum` (`(∑ i ∈ s, f i).sum g = ∑ i ∈ s, (f i).sum
  g`, needs zero + additive `g`; `rw` generates subgoals for the hypotheses);
  `Finsupp.sum_single_index` (`(single a b).sum h = h a b`, needs `h a 0 = 0`);
  `Finsupp.mapDomain_apply` (fiber-sum form); `Finsupp.smul_apply` is not
  only `@[defeq]` but has an **instance-mismatch problem** (two SMul
  instances for `Rat →₀ Rat`: `smulZeroClass` vs `distribSMul`) — `rw`
  refuses even on visual matches inside nested lambdas; convert smuls to
  muls with `Finsupp.sum_smul_index` instead.
- **`Finset.insert` is not a constant** — Finset insert is the `Insert`
  typeclass (`Insert.insert`); write `insert a s` (unqualified) or `a ∈`
  forms, never `Finset.insert`.
- **`∑ i, f i` (Fintype univ notation) is definitionally `Finset.sum
  Finset.univ f`** (`rfl` bridges them); `Finset.sum` over `univ` and the
  notation are interchangeable in `change`/`exact`.

**`Shufflemath/TotalVariation.lean`** — imports `Shufflemath.Matrix`,
`Mathlib.Data.Finset.Max`, `Mathlib.Algebra.Order.BigOperators.Group.Finset`,
`Mathlib.Algebra.Order.Sub.Basic`:
- `vectorTV p q := (1/2) * ∑_x |p x − q x|` over `Fintype` univ.
- `vectorTV_self` (simp), `vectorTV_comm`, `vectorTV_nonneg`,
  `vectorTV_le_one_of_probability` (four hypotheses: nonneg×2, total×2).
- `Dist.tv p q := vectorTV (mass p) (mass q)`; `tv_self` (simp), `tv_comm`,
  `tv_nonneg`, `tv_le_one`.
- **Done (Priority B, commits B1/B2/B3/B4):**
  - `vectorTV_triangle` / `Dist.tv_triangle` (B1): pointwise
    `|p x − r x| = |(p x − q x) + (q x − r x)|` + `abs_add_le`, then
    `mul_le_mul_of_nonneg_left` + `Finset.sum_le_sum` + `sum_add_distrib`.
  - `vectorTV_eq_zero` / `Dist.tv_eq_zero` (B2): stated **at mass level**
    (`tv p q = 0 ↔ ∀ x, mass p x = mass q x`), not `p = q` (distinct `Dist`
    reps can share a mass function).
  - `section PositiveSet` (B3, commit bb49a50): `positiveSet p q :=
    (Finset.univ : Finset α).filter (fun x => p x > q x)`; `positiveSum p q :=
    ∑_{x ∈ positiveSet} (p x − q x)`; private `maxDiffAbs` / `maxDiffSub`
    (pointwise max identities; call with explicit named args `(a := p x)
    (b := q x)` — see mechanics note on `max`/`⊔`); `sumPosPartEqPositiveSum`
    (no probability hypotheses — the pointwise max identities don't need
    them); `vectorTV_eq_positive_set` (probability vectors: `vectorTV p q =
    positiveSum p q`); `vectorTV_sum_le_positive_set` (for every `S`,
    `∑_S (p − q) ≤ positiveSum p q`; proved by **ite-embedding** —
    `∑_S u = ∑_univ (fun x => if x ∈ S then u x else 0)` by bare `simp`,
    then `Finset.sum_le_sum` — avoids the sdiff/Fintype-fold whnf timeout
    that even `set_option maxHeartbeats 0` couldn't fix).
  - `Dist.kernel_contraction` (B4, commit df58ecd):
    `tv (apply μ K) (apply ν K) ≤ tv μ ν` for any finite kernel `K` —
    classic weighted-triangle + Fubini + row-stochasticity proof; uses
    private `Dist.double_sum_pullout` (`∑_i ∑_j a_j b_{ij} = ∑_j a_j ∑_i
    b_{ij}`, one `Finset.induction`, all rewrites explicit-lambda `sum_congr`
    to dodge `rw`'s binder-capture restriction) and `apply_mass` from
    `Finite.lean`. **Priority B complete**; `verify.sh` green after B4.
  - `double_sum_pullout` is now **public** (`Dist.double_sum_pullout`) —
    used by `Perturbation.lean` and `Dobrushin.lean`.
- `namespace MatrixTV`: `rowTV P i j`; `pairDistances P` (`Finset Rat`, image over
  `univ × univ`); `pairDistances_nonempty`; `dobrushinCoeff P :=
  (pairDistances P).max' …` (**max of TV**, i.e. ≤ 1, convention note in §4-D);
  `rowTV_le_dobrushin`; `dobrushinCoeff_nonneg` (simp); `dobrushinCoeff_le_one`
  (from `Matrix.rowStochastic`).
- **`Shufflemath/Perturbation.lean`** (Priority C, commits 3599326 / 39d89b1;
  **rewritten session 9, GPT review findings #2/#6**; **reshaped session 12,
  finding #4**): imports
  `Shufflemath.Dobrushin` (and `open Dobrushin` — the D decls live in the
  nested `namespace Dobrushin`, so bare `dobrushinCoeff` is NOT in scope
  after the import) and carries a file-local
  `set_option maxHeartbeats 400000` (the protocol calc steps whnf
  `dobrushinCoeff (compList …)`; see the comment at the option).
  `kernelDiscrepancy (K L) : Rat` (max over `x` of `tv (K x) (L x)`, Finset
  image + `max'`; `rowTV_le_kernelDiscrepancy`, `_nonneg` (simp),
  `_le_one`); `apply_discrepancy_bound` (`tv (apply μ K) (apply μ L) ≤
  kernelDiscrepancy K L`, now via the public `Dist.double_sum_pullout`);
  `compList` (noncomputable def, foldr over `comp`; execution order `[K1, K2]`
  = K1 then K2) with `compList_nil` / `compList_cons` (simp) and
  `apply_compList`; `telescopeBound d Δ` (the damped sum `Δ₀·dⁿ⁻¹ + … +
  Δₙ₋₁`, nil/cons simp); **`compList_submult`
  (`δ(compList Ks) ≤ (map δ Ks).prod`** — lives here, not in Dobrushin,
  import direction); **`weightedTelescopeBound (Δ δ : List Rat)`** (recursive
  def, nil/cons simp: the per-step weighted sum `Δ₀·δ₁…δₙ + Δ₁·δ₂…δₙ + …`)
  + private `wtB_le_uniform` (weighted → uniform: each L-tail product ≤
  `d^tail length`, via `list_prod_le_pow_of_le` + `mem_of_mem_drop`);
  **`weightedTelescope` — the flagship** (session 12, finding #4):
  equal-length `Ks Ls` from `μ`, **no contraction hypotheses at all**,
  `tv (μ·compList Ks, μ·compList Ls) ≤
  weightedTelescopeBound (map disc (Ks.zip Ls)) (map δ (Ls.drop 1))` — head
  removal induction: same-input-tail part = IH, same-tail-different-input
  part = `compList_contraction_prod` (the tail's contraction, submult over
  the L-tail) × `apply_discrepancy_bound`, triangle gluing; **
  `hybridTelescope_uniform`** (uniform `d`: `≤ telescopeBound d Δ` under
  `∀ K ∈ Ls, δ K ≤ d`, `0 ≤ d`) and **`crudeTelescope`** (unconditional
  `d := 1`, plain `∑ Δ_i`) are now **corollaries** of the flagship via
  `le_trans` + `wtB_le_uniform`; `hybridTelescope` (symmetric d-form with
  `hdK`/`hdL` contraction hypotheses; `hdK` unused in the proof — the K side
  never enters through contraction) is a one-line corollary of the uniform
  bound; `hybridTelescope_n1` (n = 1 recovers `apply_discrepancy_bound`).
  Private helpers: `mem_of_mem_drop`, `list_prod_le_pow_of_le`,
  `list_prod_nonneg`, `compList_contraction_prod`. (The session-9 private
  `compList_contraction` was deleted when the flagship subsumed it.)
- **`Shufflemath/Dobrushin.lean`** (Priority D, commit afff9d9; **sharpened
  in session 8, GPT review finding #1**):
  `rowTV K i j`; `pairDistances K` / `pairDistances_nonempty` (public);
  `dobrushinCoeff K` (= `(pairDistances K).max' …`, max-TV convention, ≤ 1);
  `dobrushinCoeff_nonneg` (simp); `dobrushinCoeff_le_one`;
  `dobrushinCoeff_zero_iff` / `dobrushinCoeff_zero` (coeff 0 ↔ all rows agree
  as mass functions — stated at mass level, as `Dist.tv_eq_zero` is);
  public workhorses `absSumLeTV` / `rowWeightBound` / `sumOnSEqWeighted`
  (the `∑_S (Kμ − Kν) = ∑_x (μx − νx) · r_x` Fubini with
  `r_x := ∑_{y∈S} K x y`); private `sumUnivIte` (univ-ite-sum = set-sum);
  **`dobrushin_contraction` — SHARP, no factor of 2:**
  `tv (apply μ K) (apply ν K) ≤ dobrushinCoeff K * tv μ ν`. Proof: one-sided
  positive-set argument — output TV = `∑_x (μx − νx) · r_x` with
  `r_x =` mass of the *output* positive set under `K x`; let `m` = min of `r`
  and shift `s x := r x − m` (legal because `∑ (μ − ν) = 0`); then
  `0 ≤ s x ≤ δ(K)` (from `|r x − r x₀| ≤ rowTV ≤ δ`) and only the input side
  where `μx > νx` (mass `tv μ ν`) can contribute, so
  `∑ η·s ≤ ∑_A η·s ≤ δ·∑_A η = δ·tv(μ,ν)`.
  **`dobrushinCoeff_submult`** (`δ (comp K L) ≤ δ K * δ L`, via the sharp
  contraction applied to `L`); **`run_contraction`**
  (`tv (run K n μ) (run K n ν) ≤ dobrushinCoeff K ^ n * tv μ ν`);
  `dobrushinCoeff_matrix_link` (kernel coeff of a row-stochastic matrix-as-
  kernel = `MatrixTV.dobrushinCoeff`; private `matrixKernel` def via
  `mem_rowStochastic_iff_sum` + `max'`/`sup'`/`WithBot.unbot_inj`).
  **`dobrushin2` has been deleted** — the coefficient itself is the
  contraction constant (the old `2·δ` bound is the 2δ version of the same
  argument via `|·| ≤ δ` on both sides of an absolute value).
- **Missing (E–G):** Markov theory, general BL symbolic theory, first
  eigenfunction.

**`Shufflemath/Matrix.lean`** — `namespace FiniteKernel` (imports `Shufflemath.Finite`,
Stochastic, `Data.Matrix.Mul`, `Data.Matrix.Diagonal`, Finsupp basic/big-ops/smul,
`Algebra.Group.Monoid`):
- `toMatrix K := fun x y => Dist.mass (K x) y`.
- `toMatrix_mem_rowStochastic` (`Fintype` + `DecidableEq`).
- `ofRowStochastic P hP : FiniteKernel α α` (noncomputable);
  `toMatrix_ofRowStochastic` (simp).
- **Done (Priority A, commits 40b05a0, a08ae2f):**
  - `toMatrix_comp [Fintype β] : toMatrix (comp K L) = toMatrix K * toMatrix L` (simp).
    Proof: `ext`; `change` the LHS to `Dist` level (`unfold toMatrix` would also hit
    the RHS, whose `HMul` instance needs `Matrix`-typed arguments); `simp` the
    join/map to Finsupp; `Finsupp.sum_mapDomain_index` (with explicit `f, s, h`,
    `h_zero := fun b => zero_smul Rat b.weights`, `h_add := fun _ _ _ => add_smul _ _ _`)
    rearranges the pushforward; `Finsupp.sum_apply` pushes the evaluation in;
    `Matrix.mul_apply` **before** unfolding `toMatrix` on the RHS; final `change`
    (crosses the `@[defeq]` `Finsupp.smul_apply` gap) + `Finsupp.sum_fintype` + `rfl`.
  - `toMatrix_identity [DecidableEq α] : toMatrix (identity : FiniteKernel α α) = 1`
    (simp). NOTE: the statement needs the type ascription — bare `identity`
    (= `deterministic id`) has undetermined domain and the `OfNat (Matrix _ _ _) 1`
    instance search gets stuck.
  - `toMatrix_compPow [Fintype α] [DecidableEq α] : toMatrix (compPow K n) = (toMatrix K) ^ n`
    (simp), by `induction n with | zero | succ n ih` — explicit pattern form (plain
    `induction n` misbehaved here: "Unknown identifier ih"). `compPow`'s execution
    order matches `pow_succ` exactly, so no commutativity is needed.
  - `toMatrix_run : mass (run K n mu) x = Matrix.vecMul (fun y => mass mu y) (toMatrix K ^ n) x`.
    Same weights-level machinery as `toMatrix_comp` with `mu` in place of a point
    mass; RHS goes `Matrix.vecMul_apply_eq_sum` → `← toMatrix_compPow` → one `change`
    (the `toMatrix` equation theorem refuses to rewrite the dot-notation form
    `(K.compPow n).toMatrix`; kernel defeq unfolds it directly).

**`Shufflemath/Cost.lean`**:
- `structure CostedKernel α : step : FiniteKernel α α; cost : Rat; cost_nonneg`.
- `protocolCost ops := (ops.map CostedKernel.cost).sum`; simp lemmas
  `protocolCost_nil/cons/append`. (No pending work; use as needed.)

**`Shufflemath/BernoulliLaplace.lean`** — Commander 99-card, 50/49 split, k=25:
- `transitionNumerator (N m k x y : Nat) : Nat` — **already general in N, m, k**;
  single sum over `a ∈ range (k+1)`, `b := y − (x − a)`, guards `b ≤ k` else 0;
  terms `choose x a * choose (m−x) (k−a) * choose (m−x) b * choose (N−2m+x) (k−b)`
  (out-of-range `choose` = 0 is load-bearing).
- `transitionDenominator (N m k) := choose m k * choose (N−m) k`.
- `transitionWeight := numerator / denominator` (Rat).
- `firstModeFactor (N m k) := 1 − (N·k)/(m·(N−m))`; Commander instances
  `commanderExchangeSize (Fin 49)`, `commanderFirstMode`, `exchange24/25/26`:
  values `37/1225`, `−1/98`, `−62/1225` (`commander_factor_24/25/26`, simp);
  `commander_exchange25_minimizes_first_mode` (native_decide).
- `CommanderState := Fin 50` (actual count `val + 1`); `commanderLeftCount`;
  `commanderExchangeMatrix k`; `commanderExchange25Matrix`;
  private instance `commanderExchange25RowNonnegDecidable` (namespace-scope
  on purpose — see its docstring);
  `commanderExchange25Matrix_rowStochastic` (native_decide);
  `commanderExchange25 : FiniteKernel` via `ofRowStochastic`.
- Stationary: `commanderStationaryVector x :=
  choose 50 (count x) * choose 49 (50 − count x) / choose 99 50` (Rat);
  `…_nonneg`, `…_total` (native_decide); `commanderStationary : Dist`.
- Initial: `commanderSegregatedState = Fin.mk 49`; `commanderInitialVector`.
- Certificate engine (keep exactly as is): `CommanderArray`/`CommanderTable`,
  `commanderExchange25Table`, `commanderInitialArray`, `commanderStationaryArray`,
  `commanderArrayGet`/`commanderTableGet`, `stepCommanderArray`,
  `runCommanderArray`, `commanderRun25`, `commanderArrayAsVector`.
- `commanderStationary_fixed_point` (native_decide);
  **exact 2-step TV** = `12255318415559330995522631403472464258192877 /
  4933350368865509640837610315994582805439728012`;
  **exact 3-step TV** = `172379525755689183991816396516567920780192827919620440221147749 /
  6691837923759692633601708022649918108038775216019298375918637677488`.
- **In progress (F, G):** general symbolic theory in
  `Shufflemath/BernoulliLaplaceGeneral.lean` (F1: state space — now
  `BLState (N m)`, `k`-free — + `blStationary`; symbolic F proofs pending)
  + future `BernoulliLaplaceCommanderBridge.lean` (bridge, §4a). Do NOT
  restructure `BernoulliLaplace.lean` itself; it is a stable certificate
  base (byte-identical; the general theory keeps its own copy of the
  transition formulas and the bridge proves they coincide).

**Docs / other:** `docs/lean_plan.md` (theorem ladder — read it; this document
supersedes and extends it), `docs/formalization_dependency_audit.md`,
`docs/problem.md`, `docs/literature.md`; `experiments/bernoulli_laplace.py`
(`protocol_distance`, `transition_probability`, `stationary_distribution`,
`validate_matrix`, `best_pair_protocol`, `main` CLI) — the Python side is the
numeric oracle; `./dev/verify.sh` runs its unit tests.

## 4. Priority plan (A → H) — what to build, in order

Each item lists: file, names to add, statement sketches, proof strategy,
done-criteria. Work strictly in this order; later items use earlier ones.

### A. Kernel algebra — extend `Shufflemath/Finite.lean`

- `apply_comp (μ : Dist α) (K : FiniteKernel α β) (L : FiniteKernel β γ) :
  apply (apply μ K) L = apply μ (comp K L)` — the main associativity law.
  Strategy: unfold `apply`/`comp`; reduce to associativity of Finsupp
  pushforward (`Finsupp.map`) and `join`. Grep mathlib for `Finsupp.map_map` /
  `Finsupp.join_map` / `Finsupp.map_join`; if not present as needed, prove the
  two small Finsupp associativity lemmas as private lemmas *inside* this file
  (keep them local, docstringed).
- `comp_assoc (K : FiniteKernel α β) (L : FiniteKernel β γ) (M : FiniteKernel γ δ) :
  comp (comp K L) M = comp K (comp L M)` — `funext`, then `apply_comp`-style
  reasoning at a point mass, or direct Finsupp argument.
- `comp_id_right`, `comp_id_left` (`comp K identity = K`, `comp identity K = K`).
- `run_succ (n) : run K (n+1) μ = apply (run K n μ) K` (simp) and
  `run_comp (n) : apply (run K n) μ` vs iterates if useful.
- In `Shufflemath/Matrix.lean`: `toMatrix_comp :
  toMatrix (comp K L) = toMatrix K * toMatrix L` (use `Matrix.mul_apply`,
  located at `Mathlib/Data/Matrix/Mul.lean`); optionally
  `toMatrix_run : toMatrix (run K n) = (toMatrix K) ^ n` (matrix power).

**Done:** all simp-friendly, build green, docstrings, committed.

### B. TV laws — extend `Shufflemath/TotalVariation.lean`

- `vectorTV_triangle p q r : vectorTV p r ≤ vectorTV p q + vectorTV q r`
  (`abs_sub_le`-style: `|p−r| ≤ |p−q| + |q−r|`, then `Finset.sum_le_sum`).
- `vectorTV_eq_zero : vectorTV p q = 0 ↔ p = q` —
  `Finset.sum_eq_zero_iff_of_nonneg` (exists in mathlib; grep to confirm form)
  + `abs_eq_zero` + `funext`.
- **Workhorse — `vectorTV_eq_positive_set`** (max-event characterization):
  for probability vectors `p q`: `vectorTV p q = s` where
  `s := ∑ x ∈ {x // p x > q x}, p x − q x` (use the Finset
  `Finset.filter univ (fun x => p x > q x)`); and for *every* `S : Finset α`,
  `∑ x ∈ S, p x − q x ≤ s`. Proof sketch: let `u x := max 0 (p x − q x)`,
  `v x := max 0 (q x − p x)`; then `|p x − q x| = u x + v x`,
  `∑ (p − q) = 0` (totals), so `∑ u = ∑ v = (1/2) ∑ |p−q| = s`, and
  `∑_S (p−q) = ∑_S u − ∑_S v ≤ ∑_S u ≤ ∑_univ u = s`. No division by `s`.
  Specialize: `Dist.tv_eq_positive_set` (same statement with `Dist`;
  the set `{x // mass p x > mass q x}` is a Finset via `Finset.univ.toFinset`
  filtering — `α` is Fintype so use `Finset.filter (Finset.univ) …`).
- **Workhorse — `kernel_contraction (K : FiniteKernel α β) (μ ν : Dist α) :
  Dist.tv (apply μ K) (apply ν K) ≤ Dist.tv μ ν`.**
  Proof: `|(Kμ) y − (Kν) y| = |∑_x (μ x − ν x) · K x y| ≤
  ∑_x |μ x − ν x| · K x y` (triangle inside, `K x y ≥ 0`);
  sum over `y`; swap the two finite sums (grep `Finset.sum_mul` / `mul_sum` /
  `Finset.bicommutative` for the swap lemma); use row mass 1
  (`Dist.sum_mass (K x)`). All factors in `Rat`, nonnegativity from
  `mass_nonneg`. No `s`-division anywhere.

**Done:** build green; use the new lemmas to *reprove* `tv_le_one` more
briefly if it comes out shorter (optional, only if strictly cleaner).

### C. Perturbation / hybrid protocols — NEW `Shufflemath/Perturbation.lean`

(Superseded by the session-9 rewrite and the session-12 reshaping — the
final design, recorded in §3: `apply_discrepancy_bound`, `compList`,
`telescopeBound`, `compList_submult`, **`weightedTelescopeBound` +
`weightedTelescope` (flagship, no contraction hypotheses)**, with
`hybridTelescope_uniform` / `crudeTelescope` / `hybridTelescope` as
corollaries. The original spec below anticipated the pre-sharpening
`dobrushin2` constants; the delivered form replaces `d2` with `δ` and
drops the uniform-both-sides requirement.)

(Import `Shufflemath.TotalVariation`, `Shufflemath.Dobrushin` once D exists;
add to `Shufflemath.lean` imports after D.)

- `kernelDiscrepancy (K L : FiniteKernel α α) : Rat` — max over `x` of
  `Dist.tv (K x) (L x)`; mirror `MatrixTV.dobrushinCoeff` for kernels:
  `((Finset.univ : Finset α).image (fun x => Dist.tv (K x) (L x))).max' …`
  with `[Fintype α] [DecidableEq α] [Nonempty α]`.
- `apply_discrepancy_bound : Dist.tv (apply μ K) (apply μ L) ≤
  kernelDiscrepancy K L` — same swap argument as B's contraction with the
  same input on both sides.
- `compList (Ks : List (FiniteKernel α α)) : FiniteKernel α α :=
  List.foldr FiniteKernel.comp FiniteKernel.identity Ks` (execution order:
  `compList [K1, K2]` runs K1 then K2 — document the convention and make the
  simp lemma `compList_cons` reflect it).
- **Flagship — `hybridTelescope`**: for protocols `Ks, Ls` of the same length
  `n`, initial `μ`, letting `δ := 2 * Dobrushin.dobrushinCoeff`-style bound
  (use the D contraction constant `d2` defined in D) and
  `Δ_i := kernelDiscrepancy (Ks.get i) (Ls.get i)`:
  `Dist.tv (apply (compList Ks) (pointMass-ish μ)) … ≤
  ∑_{i < n} (d2_prefix) ^ (n − 1 − i) * Δ_i` — the standard telescoping
  bound: difference of two n-step protocols ≤ sum over the step at which they
  are perturbed, damped by subsequent contraction. Proof by induction on the
  list pair (unzip both lists; case `nil`; case `K :: Ks, L :: Ls`:
  split `(K∘K̂)μ − (L∘L̂)μ = K(K̂μ − L̂μ) + (Kμ̂' − Lμ̂')`-style, use
  B-contraction for the first part, C-bound for the second).
  If the dependent indexing gets heavy, state it for `Fin n →` functions or
  equal-length `List`s with `getDef` — pick whichever proofs cleanly, and say
  so in the docstring.

**Done:** build green; the `n=1` instance of the telescope must reduce to
`apply_discrepancy_bound` (add that as a lemma or test).

### D. Dobrushin contraction — NEW `Shufflemath/Dobrushin.lean` — **DONE
(sharpened in session 8, GPT review finding #1)**

- `dobrushinCoeff (K : FiniteKernel α α) : Rat` — max over `i, j` of
  `Dist.tv (K i) (K j)` (mirror of `MatrixTV.dobrushinCoeff`; same
  `pairDistances`-style Finset image + `max'`). `dobrushinCoeff_nonneg` (simp),
  `dobrushinCoeff_le_one` (via `vectorTV_le_one` — rows are distributions).
- **The coefficient itself is the sharp contraction constant.**
  `dobrushin_contraction : tv (apply μ K) (apply ν K) ≤ dobrushinCoeff K * tv μ ν`
  (no factor of 2 — see §3 for the one-sided positive-set proof). The old
  `dobrushin2 := 2·δ` constant and its `2δ` contraction / submult / run
  lemmas were **deleted**; `dobrushinCoeff_submult` (`δ(comp K L) ≤ δ K·δ L`)
  and `run_contraction` (with `δ ^ n`) replace them. `dobrushinCoeff_zero_iff`
  records when the coefficient vanishes (all rows agree as mass functions).
- `dobrushinCoeff_matrix_link` (matrix⇄kernel consistency) preserved verbatim.

**Mechanics notes (session 8):** the sharp proof's `r`/`S₀`/`A`/`m` are local
`let`s — fine because they are only *used* (as arguments to public defs, or in
`change`/`rfl` kernel-defeq steps), never unfolded by `rw`/`simp`; the one
exception is the ite-gated sum, handled by the private `sumUnivIte` helper
(let-bound bodies are invisible to `simp`/`rw` — the F2 lesson). `Finset.mem_univ`
is a bare `@[simp]` proof (not an iff): after
`simp only [positiveSet, Finset.mem_filter] at h`, a plain `simp at h` clears
the `x ∈ univ` conjunct (even under a negation, landing on `nu ≤ mu` / the
`> ` side as needed). `mul_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0)
: a*b ≤ 0` — mind the argument order; `rw [mul_comm]` first if the summand
is written the other way. `Finset.max'_eq_iff (s) (H) (a)` — all three args
explicit. `simp using h` does **not** exist in v4.34.0. `Finset.sum_mul` in
v4.34.0 is the `(∑ f) * a = a * ∑ f` direction; `mul_sum` is
`a * ∑ f = ∑ (a * f)` — use `← mul_sum` to go `∑ (a·f) → a·∑ f`.
`Finset.univ_nonempty {α} [Fintype α] [Nonempty α]` exists (parameter name is
`α`, not `alpha`); `Finset.nonempty_univ` does not.

### E. Stationarity & reversibility — NEW `Shufflemath/Markov.lean`

- `Stationary (μ : Dist α) (K : FiniteKernel α α) : apply μ K = μ` (def/
  abbrev over the equation; pick the direction `apply μ K = μ` to match `apply`).
- `Stationary.run : Stationary μ K → ∀ n, apply (run K n) μ = μ` (induction).
- `DetailedBalance (μ : Dist α) (K : FiniteKernel α α) :
  ∀ x y, mass μ x * Dist.mass (K x) y = mass μ y * Dist.mass (K y) x`.
- `detailedBalance_implies_stationary` — for fixed `y`:
  `∑_x mass μ x · K x y = ∑_x mass μ y · K y x = mass μ y · 1 = mass μ y`
  (no sum-swap needed; use row-total `Dist.sum_mass` on the `K y` row and the DB
  equation inside `Finset.sum_congr`).
- Reversibility / self-adjointness: define
  `weightedInner (μ : Dist α) (f g : α → Rat) := ∑_x mass μ x · f x · g x`.
  `selfAdjoint_of_detailedBalance : DetailedBalance μ K →
  ∀ f g, weightedInner μ f (K.applyFn g…) = weightedInner μ g (…)`. Careful:
  `apply` acts on *distributions*; for functions define the row-action
  `K.applyFn (f : β → Rat) (x : α) := ∑_y Dist.mass (K x) y * f y` (or reuse
  matrix multiplication if cleaner via `toMatrix`). Statement:
  `∑_x μ x f x ∑_y K x y g y = ∑_{x,y} μ x K x y f x g y =
  ∑_{x,y} μ y K y x f x g y` (DB, swap the double sums both ways) `=
  ∑_y μ y g y ∑_x K y x f x`. All `Rat`, all finite — no analysis.
- `stationary_of_detailedBalance` follows; keep the file about the
  abstract theory only (no Commander content here).

**Done:** build green; each theorem docstringed with its downstream use
(eigen-decomposition in G, Commander certificates in F).

### F. General Bernoulli–Laplace — `Shufflemath/BernoulliLaplaceGeneral.lean`

Parameters: `N m k : Nat` with `0 < m < N`, `0 < k`, `k ≤ m`, `k ≤ N − m`
(two piles of sizes `m` and `N − m`, exchanging `k` from each). Macrostate
`x` = original-left cards in the left pile.

**Redesign (GPT review #2/#3; supersedes the pre-redesign spec below in
two points):** the state space depends only on `N m` (`k` is a kernel
parameter, so different `k`-kernels and compositions of them live on one
state type); the upper bound is `m`, **not** `min m (N − m)` (the
pre-redesign bound excluded the segregated state whenever `m > N − m`);
this module does **not** import the Commander file — the
Commander-link theorems move to a new small bridge module
`Shufflemath/BernoulliLaplaceCommanderBridge.lean` importing both (see
§4a for the decision and why).

- `BLState (N m : Nat) := { x : ℕ // max (2*m − N) 0 ≤ x ≤ m }` (lower
  bound = `m − (N − m)` clamped to 0: the right pile must hold the
  `m − x` original-left cards; upper bound = left-pile capacity).
  Fintype via `Fintype.ofFinset`; bounds lemmas simp.
  Commander check: `N=99, m=50` → `1 ≤ x ≤ 50` ✓.
- The general module carries its **own copy** of the exchange-transition
  formulas (`transitionNumerator` / `Denominator` / `Weight` —
  definitionally the frozen `BernoulliLaplace.lean` formulas; the bridge
  module proves they coincide — §4a decision).
- **Row stochasticity (symbolic)**: `blRowStochastic : ∀ x (admissible),
  ∑_y transitionWeight N m k x y = 1` (sum over admissible `y`; out-of-range
  terms are 0 so summing over the admissible Finset suffices — prove the
  support lemma first: `y` contributes nonzero only if in the admissible range).
  Proof: `∑_y num(x,y) = ∑_{a=0..k} choose(x,a)·choose(m−x,k−a) ·
  [∑_{b=0..k} choose(m−x,b)·choose(N−2m+x,k−b)]` =
  `∑_a choose(x,a)·choose(m−x,k−a) · choose(N−m, k)` (Vandermonde,
  `Nat.add_choose_eq`, with `M := m−x`, `L := N−2m+x`, `M+L = N−m`; the `b`
  sum is exactly `∑_{b} choose(M,b)·choose(L,k−b)` — note `choose` is 0 for
  `b > k` and `k−b > L` so the `range (k+1)` sum equals the full Vandermonde
  sum; prove that zero-extension lemma) =
  `choose(m, k)·choose(N−m, k)` (Vandermonde again: `∑_a choose(x,a)
  choose(m−x,k−a) = choose(x + m − x, k)`). Hence row sum = denominator /
  denominator = 1.
  Use `Nat.add_choose_eq (x) (m−x) k` and `Nat.add_choose_eq (m−x) (N−2m+x) k`
  (statement at `Mathlib/Data/Nat/Choose/Vandermonde.lean`:
  `(m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2`;
  `Finset.antidiagonalEquivFin (n)` reindexes to `Fin (n+1)`). Beware
  `Nat`-subtraction in `N − 2m + x` and `m − x`: hypotheses give
  `x ≤ m`, `m − x ≤ N − 2m + x + k` etc. — set up the arithmetic hypotheses
  carefully; a `have`-block translating parameter bounds is worth it.
- **Stationary distribution (hypergeometric)**:
  `blStationary (x : BLState) := choose(m, x)·choose(N−m, m−x) / choose(N, m)`
  (Rat). Nonneg: trivial. **Total = 1** (symbolic):
  `∑_x choose(m,x)·choose(N−m, m−x) = choose(N, m)` — Vandermonde with a
  symmetry step: `choose(N−m, m−x) = choose(N−m, (N−m) − (m−x))` =
  `choose(N−m, N − 2m + x)`, then match indices into
  `Nat.add_choose_eq m (N−m) m` (write the index change explicitly — a
  `Finset.sum_bij` or a `Finset.sum_range_reflect`-style reindex is fine).
- `blStationaryDist : Dist (BLState)` via `Dist.ofFun` (noncomputable def).
- **Detailed balance** (hardest proof in the project). Target:
  `∀ x y, blStationary x · num(x,y) = blStationary y · num(y,x)` as a `Nat`
  identity (denominator is symmetric so it cancels). Candidate strategies,
  try in order:
  1. **Index bijection inside the `a`-sums**: `num(x,y) =
     ∑_a T(x,y,a)` with `T(x,y,a) :=` the 4-choose product with
     `b := y − x + a`. Show the map `a ↦ a'` sending `T(x,y,a)` to
     `T(y,x,a')` is a bijection between the nonzero supports. Candidates to
     check on paper first: `a' := k − a` and `a' := a + (x − y)` — verify
     which one makes all four `choose` factors match (use
     `choose (n) (k) = choose (n) (n−k)` symmetry on the mismatched factors).
  2. **Rat factorial identity**: expand each `choose n r` as
     `(n! : Rat) / (r! · (n−r)!)` under support hypotheses, simplify both
     sides to the same factorial monomial; descend to `Nat` with
     `Nat.cast_injective` on `ℕ → ℚ`.
  Either route: do a **native_decide spot check on the Commander instance
  first** (50×50 termwise equality) as a private certificate to validate the
  formula *before* the symbolic proof — mirroring the existing file's workflow.
- **Matrix-level view**: `blExchangeKernel (N m k) : FiniteKernel (BLState) (BLState)`
  via `ofRowStochastic` (using the symbolic row-stochasticity), and the
  theorem that the Commander instance *is* the existing
  `BernoulliLaplace.commanderExchange25` (state-space equiv `Fin 50 ↔
  {x // 1 ≤ x ≤ 50}`; `toMatrix` equality). This ties the general theory to
  the certificates and to the §6 regression values.

**Done:** build green; `./dev/verify.sh` green; the Commander matrix-link
theorem proved; no changes to `BernoulliLaplace.lean`.

### G. First eigenfunction — extend `Shufflemath/BernoulliLaplaceGeneral.lean`

- Hypergeometric moments (symbolic, `choose` arithmetic):
  `E_π[x] = m·m / N` and the conditional means
  `E[a | x] = k·x / m`, `E[b | x] = k·(m−x)/(N−m)` for the exchange
  (`∑_a a·choose(x,a)·choose(m−x,k−a) = k·x/m·choose(m,k)` — standard
  `a·choose(x,a) = x·choose(x−1,a−1)` shifting trick; same for `b`).
- **First-mode theorem**: with `f(x) := (x : Rat) − m·m/N` and
  `λ := firstModeFactor N m k = 1 − N·k/(m·(N−m))` (existing def, reuse):
  `∀ x, ∑_y W(x,y)·f(y) = λ·f(x)`.
  Proof: `E[y|x] = x − k·x/m + k·(m−x)/(N−m)` from the conditional means;
  then `k·((m−x)/(N−m) − x/m) = k·(m² − N·x)/(m·(N−m)) =
  −(N·k/(m·(N−m)))·(x − m²/N)` (one line of field algebra in `Rat`) `=
  (λ − 1)·f(x)`. So the sum is `f(x) + (λ−1)·f(x) = λ·f(x)`.
- **Commander specialization**: `commanderFirstMode k` (existing def) equals
  the eigenvalue of the existing `commanderExchange25Matrix` on the first
  mode — tie the existing `commander_factor_24/25/26` values
  (`37/1225`, `−1/98`, `−62/1225`) to the theorem as corollaries
  (the numeric simp lemmas already exist; add the semantic statement).

**Done:** build green; eigenfunction statement for general `(N,m,k)` proved
symbolically; Commander corollaries committed.

### H. Stretch (after A–G, in order)

1. GSR (Gilbert–Shannon–Reeds): a-shuffle kernel on `Fin (n+1)` cut counts
   (`P(c = k) = 2^{-k}`-style / Poisson cuts), the a-shuffle transition on
   permutations or on a macrostate, TV after n riffles (the falling-factorial /
   coupon-coefficient formula), and the known 52-card and 99-card numeric
   targets (see §6 / `experiments/`). Keep it exact rational.
2. Higher eigenmodes of the BL chain (2nd mode etc.) if the moment machinery
   from G extends cleanly.
3. Separation distance vs TV: a short section proving the standard
   inequalities for the models already built (do not conflate; §1).
4. Anything else from `docs/lean_plan.md` not covered above (re-read it).

## 4a. GPT review (2026-10-04) — findings and status

Verbatim record: `docs/gpt_review_2026-10-04.md` (recovered from the pi
session transcript `01a104d1-84ab-75e8-9ce6-86eeb46b1e80`). The review
judged the overnight work a net positive ("correct it rather than
replace it") but ordered the fixes below before further BL theory. **This
section is the authoritative per-finding ledger** — update the status line
in the same commit as any fix.

| # | Finding (short) | Severity | Status | Commit |
|---|-----------------|----------|--------|--------|
| 1 | Dobrushin: drop `dobrushin2`, prove sharp `δ(K)` contraction | High | **DONE** | `b69d00a` (session 8) |
| 2 | `BLState` must not depend on `k` (phantom param) | High | **DONE** | this commit |
| 3 | General module must not import the Commander module (bridge module instead) | High-ish | **PARTIAL** (import removed; bridge module lands with the F commit) | this commit |
| 4 | Perturbation API: unconditional crude telescope + sharp per-step weighted bound; uniform-`d` as corollary | Medium | **DONE** (`weightedTelescope` flagship, no contraction hypotheses; uniform/crude/symmetric all corollaries) | this commit |
| 5 | `tv_eq_zero` false comment; add real `tv p q = 0 ↔ p = q` | Medium | **DONE** (`tv_zero_iff_eq`) | `734141f` |
| 6 | LLM duplication: private `double_sum_pullout` (a), Dobrushin nonneg/sum-one reproofs (b), matrix vs kernel row-TV/canon (c) | Medium-low | **DONE** | `b69d00a`, `06c2f4b`, `734141f` |
| 7 | `Markov.lean` self-adjointness docstring overclaims orthogonal eigenbasis | Medium-low | **DONE** | `734141f` |
| 8 | New BL module not imported by `Shufflemath.lean` (not in build graph) | Process | **DONE** | this commit |
| 9 | `Finite.lean` "Krein–von Neumann pushforward" hallucinated term | Minor | **DONE** | `734141f` |
| 10 | Commit trailer not followed (wrong name/email) | Workflow | **DONE** (new trailer `Co-authored-by: Qwen3.8-27B-W4A16-AutoRound <noreply@qwen.ai>` on all new commits; history NOT rewritten, per review's own advice and user instruction) | `a09e2b0` onward |

**Order per the review's recommendation:** #1 ✅ → #4 (perturbation API:
crude + uniform-`d` ✅, sharp weighted form **next**) → #2/#3/#8 ✅ (this
commit) → then continue F (row stochasticity / stationarity / detailed
balance, via the general file's own transition formulas + the bridge
module). #5/#6/#7/#9 done in the quick-win commit `734141f`. **Remaining:
#4 (completion) + #3 (bridge module, lands with F).**

**Decision on #3 vs. the frozen `BernoulliLaplace.lean`:** the §4-F spec
said "reuse `BernoulliLaplace.transitionNumerator` verbatim, do not
redefine" and "no changes to `BernoulliLaplace.lean`"; both cannot hold
simultaneously with #3. Resolution (review-endorsed architecture): the
general file gets its **own** copy of the exchange-transition formulas
(the frozen Commander file keeps its copy for the concrete certificates),
and a new small module `Shufflemath/BernoulliLaplaceCommanderBridge.lean`
imports **both** and proves the definitions/theorems coincide (the bridge
is where `blExchangeKernel N m k` = `commanderExchange25` lives).
`BernoulliLaplace.lean` stays byte-identical.

## 5. Verified mathlib hooks (v4.34.0, checked on this machine)

- `Convexity.StdSimplex` — `Mathlib/Geometry/Convex/ConvexSpace/Defs.lean`:
  fields `weights` (Finsupp), `nonneg`, `total`; lemmas `single`, `map`,
  `join`, `ext` (alias of `weights_inj`), `total_of_fintype`, `weights_nonneg`,
  `weights_apply_le_one`.
- `Matrix.rowStochastic` — `Mathlib/LinearAlgebra/Matrix/Stochastic.lean`:
  `mem_rowStochastic_iff_sum`, `nonneg_of_mem_rowStochastic`,
  `sum_row_of_mem_rowStochastic`.
- `Matrix.mul_apply` — `Mathlib/Data/Matrix/Mul.lean`.
  `Matrix.vecMul` / `Matrix.vecMul_apply_eq_sum` (`(v ᵥ* M) i = ∑ j, v j * M j i`,
  an `rfl` lemma) — same file (line ~717/726). `Matrix.one_apply` —
  `Mathlib/Data/Matrix/Diagonal.lean`.
- Finsupp Fubini/evaluation hooks (all verified this session):
  `Finsupp.sum_mapDomain_index` (additive of `prod_mapDomain_index`;
  explicit args `f, s, h, h_zero, h_add`; `h_zero` needs `zero_smul`,
  `h_add` needs `add_smul` — NOT `smul_add`, which is the other direction);
  `Finsupp.sum_apply` (`(f.sum g) a = f.sum fun a₁ b => g a₁ b a`);
  `Finsupp.sum_fintype` (`f.sum g = ∑ i, g i (f i)`, `h : ∀ i, g i 0 = 0`);
  `Finsupp.smul_apply` is **`@[defeq]`** (usable by `rfl`/`change`, not `rw`);
  `zero_smul` has an explicit type argument: `zero_smul Rat _`.
- `pow_succ : a ^ (n + 1) = a ^ n * a` — `Mathlib/Algebra/Group/Monoid.lean`
  (import `Mathlib.Algebra.Group.Monoid`); `Mathlib.Algebra.GroupPower.Basic`
  does **not** exist in v4.34.0. `pow_zero` / `a ^ 0` are definitional (`rfl`).
- `Finset.powerset_nonempty` — `Mathlib/Data/Finset/Powerset.lean`.
- `Finset.sum_eq_zero_iff_of_nonneg` — exists (grep `Data/Finset` for the
  exact namespace/form before use).
- `Nat.add_choose_eq (m n k)` — `Mathlib/Data/Nat/Choose/Vandermonde.lean`:
  `(m + n).choose k = ∑ ij ∈ Finset.antidiagonal k, m.choose ij.1 * n.choose ij.2`;
  `Finset.antidiagonalEquivFin (n)` reindexes `antidiagonal n ↔ Fin (n+1)`.
- `choose` is 0 out of range (`Nat.choose_eq_zero_of_lt` etc.) — the existing
  `transitionNumerator` already relies on this; keep relying on it.
- Everything else: **grep `.lake/packages/mathlib/Mathlib`** before assuming a
  name; prefer existing mathlib lemmas over local copies.

## 6. Numeric regression targets (must stay reproducible — do not change them)

- GSR TV after n riffles for 52-card and 99-card decks (Python: `experiments/`).
- Commander BL TV after 0–4 exchanges of 25 cards (Python `protocol_distance`;
  Lean 2-step and 3-step exact fractions are pinned in
  `BernoulliLaplace.lean` — values listed in §3; the Lean 0- and 1-step values
  are 1 and `25/49`-family — re-derive, don't trust this note).
- First-mode factors k=24/25/26: `37/1225`, `−1/98`, `−62/1225`.
- When any symbolic theorem touches these numbers, add a small
  `norm_num`/`native_decide` agreement check in the same commit.

## 7. Progress log (update after every commit)

- [x] 2026-10-05 (session 1): repo audit; `lake build` verified green; this
  handoff document written. No formalization code yet.
- [x] 2026-10-05 (session 2): commit 754dfa9 — `Finite.lean` kernel algebra
  complete: `apply_comp`, `comp_assoc`, `comp_id_right`, `comp_id_left`,
  `apply_id_left`, `compPow` (+zero/succ), `run_succ`/`run_succ_add`/
  `run_apply_self`, `run_compPow`, plus the `join`↔`sConvexComb` bridge and
  private Finsupp-level associativity lemmas. Root-caused and worked around
  the `run` big-recursion kernel stall (see §3 mechanics notes).
- [x] 2026-10-05 (session 3): commit 40b05a0 — `Matrix.lean` `toMatrix_comp`,
  `toMatrix_identity`, `toMatrix_compPow`; commit a08ae2f — `toMatrix_run`
  (vector–matrix bridge). **Priority A complete** (see §3 for the new
  mechanics notes: `@[defeq]`/rw gap, Matrix-type opacity, dot-notation
  equation-theorem refusal, rw all-must-fire/auto-close).
- [x] A. Kernel algebra — `Finite.lean` monad laws + `Matrix.lean` bridges
  (`toMatrix_comp`, `toMatrix_identity`, `toMatrix_compPow`, `toMatrix_run`),
  all committed, full build green.
- [x] 2026-10-05 (session 4): **Priority B complete.** Commits: B1
  `vectorTV_triangle`/`tv_triangle`; B2 `4eeddcc` `vectorTV_eq_zero` /
  `tv_eq_zero`; B3 `bb49a50` PositiveSet section (max-event characterization:
  `vectorTV_eq_positive_set`, `vectorTV_sum_le_positive_set`, pointwise max
  workhorses); B4a `90fa10c` `Finite.lean apply_mass` (kernel pushforward
  mass = weighted row sum); B4b `df58ecd` `Dist.kernel_contraction` (+
  private `double_sum_pullout` Fubini). `./dev/verify.sh` green after B4
  (3190 jobs, 7/7 Python tests).
- [x] B. TV laws (triangle, eq_zero, positive-set, kernel contraction) —
  all in `Shufflemath/TotalVariation.lean` + `apply_mass` in `Finite.lean`.
- [x] 2026-10-05 (session 5): **Priority C complete.** C1 commit 3599326 —
  `Perturbation.lean`: `kernelDiscrepancy` (+nonneg/le_one/rowTV bounds),
  `apply_discrepancy_bound`, `compList` (+nil/cons simp, `apply_compList`),
  `telescopeBound`. C2 commit 39d89b1 — `hybridTelescope` flagship
  (uniform contraction constant `d`, list-pair induction) +
  `hybridTelescope_n1` (n=1 reduces to `apply_discrepancy_bound`).
- [x] C. Perturbation (`Perturbation.lean`: discrepancy, compList, hybridTelescope) —
  committed 3599326 / 39d89b1.
- [x] 2026-10-05 (session 6): **Priority D complete.** Commit afff9d9 —
  `Dobrushin.lean`: `dobrushinCoeff` / `dobrushin2` + nonneg/le_one
  bounds, `dobrushin_contraction` (positive-set pivot: `tv(Kμ, Kν) =
  positiveSum = ∑_S signed mass = ∑_x (μx−νx)·r_x ≤ cK·∑|μ−ν| =
  dobrushin2·tv(μ,ν)`, via private `sumOnSEqWeighted` / `rowWeightBound`),
  `dobrushin2_submult`, `run_contraction`, `dobrushinCoeff_matrix_link`
  (matrix⇄kernel consistency). `double_sum_pullout` made public in
  `TotalVariation.lean`; `Shufflemath.lean` now imports Perturbation +
  Dobrushin. `./dev/verify.sh` green after D (3192 jobs, 7/7 Python tests).
- [x] D. Dobrushin (`Dobrushin.lean`: coeff, contraction, submult, run, matrix link) —
  committed afff9d9.
- [x] 2026-10-05 (session 9): **GPT review findings #2/#6 done —
  `Perturbation.lean` rewritten.** Added `compList_submult` (δ(compList) ≤
  ∏ δ — here, not Dobrushin: import direction), `hybridTelescope_uniform`
  (flagship: only `∀ K ∈ Ls, δ K ≤ d` — **no** K-side contraction
  hypothesis; head-removal induction: same-input-tail = IH, same-tail =
  `dobrushin_contraction (compList Ls'')` + `compList_submult` +
  `apply_discrepancy_bound`, triangle gluing), `crudeTelescope` (unconditional
  `d := 1`, via `dobrushinCoeff_le_one`), private
  `list_prod_le_pow_of_le`. Private `double_sum_pullout` deleted (use public
  `Dist.double_sum_pullout`). `hybridTelescope` (symmetric d-form) and
  `hybridTelescope_n1` preserved verbatim. New imports: `Shufflemath.Dobrushin`
  (+ `open Dobrushin` — D's decls are in the nested `namespace Dobrushin`;
  bare `dobrushinCoeff` is not in scope from the import alone) and
  `Mathlib.Algebra.Group.Monoid` (`pow_succ'`). File-local
  `set_option maxHeartbeats 400000`: the main calc whnfs
  `dobrushinCoeff (compList …)` while checking the triangle step — **the
  calc's first step must be preceded by `rw [compList_cons, compList_cons,
  ← apply_comp, ← apply_comp]`** or the compiler stalls in whnf trying to
  unify `apply μ (compList (K0::Ks'))` with `apply (apply μ K0) (compList
  Ks')` (same stall family as the `run` comment in Finite.lean). Also: a
  `calc` whose LAST step is an equality whose two sides only differ by a
  length-map equality can orient the bridge as an unprovable inequality —
  avoid by ending the calc at the heavier term (or using the direct proof
  term). `List.mem_cons_self` takes NO explicit args in v4.34 (implicits
  only); `List.prod_cons` likewise. `mul_le_mul_of_nonneg_left (h : b ≤ c)
  (hc : 0 ≤ a)` / `_right` — inequality first, nonnegativity second. Full
  `lake build` green, zero warnings, zero sorry; `./dev/verify.sh` green
  (7/7). **This commit.** GPT review remaining: #3 (BL redesign, next),
  #4 (import direction), #5 (`tv_eq_zero` comment), #7 (Markov docstring),
  #9 (Finite.lean "Krein–von Neumann" hallucination), #10 (process).
- [x] 2026-10-05 (session 10, quick-win commit `734141f`): **GPT review
  #5/#6c/#7/#9.** `tv_zero_iff_eq` added to TotalVariation.lean
  (`tv p q = 0 ↔ p = q` — StdSimplex ext on the weights Finsupp;
  `tv_eq_zero`'s false comment about distinct reps sharing a mass
  function fixed — mass equality determines the `Dist` since proof
  fields are proof-irrelevant). MatrixTV `rowTV`/`pairDistances`/
  `dobrushinCoeff` docstrings mark the matrix API as the compatibility
  view (canonical: kernel versions in Dobrushin.lean; bridge:
  `dobrushinCoeff_matrix_link`). Markov self-adjointness docstring no
  longer claims an orthogonal eigenbasis (states the Rat/degeneracy
  caveats). Finite.lean `apply_mass` docstring: "Krein–von Neumann
  pushforward" → kernel pushforward / mixture of rows.
- [x] 2026-10-05 (session 11, this commit): **GPT review #2/#3/#8 —
  BL architecture.** `BLState (N m)` — the phantom `k` parameter is gone
  (#2: `k` is a kernel parameter, so different `k`-kernels and
  compositions of them are comparable on one state type); `blStationary
  (N m x)`; `Params` keeps `k` (exchange size, with its fit proofs).
  Removed `import Shufflemath.BernoulliLaplace` from the general file
  (#3 — the dependency arrow was backwards; the 114-line file used
  nothing from it); Commander-link theorems move to a new small bridge
  module `BernoulliLaplaceCommanderBridge` (imports both, proves
  coincidence — lands with the F commit; §4a records the decision and
  why the general file gets its own copy of the transition formulas
  rather than importing the frozen Commander file). `Shufflemath.lean`
  now imports BernoulliLaplaceGeneral (#8 — the module is in the
  library build graph). `BernoulliLaplace.lean` byte-identical. §4a
  ledger updated; §4-F spec rewritten to the post-redesign version.
- [x] 2026-10-06 (session 12, this commit): **GPT review finding #4 —
  sharp weighted telescope.** `Perturbation.lean` reshaped: new recursive
  def `weightedTelescopeBound (Δ δ : List Rat)` (nil/cons simp: the
  per-step weighted sum `Δ₀·δ₁…δₙ + Δ₁·δ₂…δₙ + …` — for protocols of
  length `n`, `Δ` has `n` entries, `δ` the `n−1` L-suffix coefficients)
  and **`weightedTelescope` — the new flagship**: equal-length `Ks Ls`
  from `μ`, **no contraction hypotheses at all** (only the always-true
  `δ ∈ [0,1]`),
  `tv (μ·compList Ks, μ·compList Ls) ≤
  weightedTelescopeBound (map disc (Ks.zip Ls)) (map δ (Ls.drop 1))`.
  Same head-removal induction as the old uniform proof: same-input-tail
  part = IH at `(μ·K₀, same L-tail)`; same-tail-different-input part =
  `compList_contraction_prod` (new private helper: tail contraction ≤
  `(map δ tail).prod × tv`, via `dobrushin_contraction` +
  `compList_submult` + `dobrushinCoeff_le_one`) × `apply_discrepancy_bound`
  (head discrepancy); triangle gluing. The WHNF-stall mitigation (`rw
  [compList_cons ×2, ← apply_comp ×2]` before the main calc, after all
  `have`s) was kept from session 9 and re-verified as load-bearing.
  **`hybridTelescope_uniform`, `crudeTelescope`, `hybridTelescope` are now
  corollaries** (statements unchanged): uniform/crude via `le_trans`
  (weightedTelescope) (new private `wtB_le_uniform`: weighted bound ≤
  uniform-`d` bound — each L-tail product ≤ `d^tail length`, with
  `list_prod_le_pow_of_le` + new private `mem_of_mem_drop` for the IH
  membership bookkeeping; crude = `d := 1` via `dobrushinCoeff_le_one`);
  symmetric `hybridTelescope` = one-line call of the uniform corollary
  (its `hdK` contraction hypothesis is unused in the proof — the K side
  only ever enters through the one-step discrepancy; kept in the
  signature for API stability, `let _ := hdK` silences the warning).
  Session-9 private `compList_contraction` deleted (subsumed by
  `compList_contraction_prod` + `wtB_le_uniform`); the three duplicated
  60-line direct proofs collapsed to 2–20-line corollary proofs.
  Mechanics learned this session: after `cases Ls`, the variable `Ls` is
  GONE (destructive cases on a variable) — write the goal's tail as
  `((L0::Ls'').drop 1)`; `rw`/`simp` do NOT reduce `(L0::Ls'').drop 1`
  (their matchers don't instantiate `i := 0` in `drop_succ_cons`'s
  `i+1` pattern) — `dsimp only [List.drop, List.tail]` does; the δ-list
  re-identification in the final calc step closes with
  `simp only [List.map_drop, ← hδs]` + `ring`. Full `lake build` green,
  zero warnings, zero sorry; `./dev/verify.sh` green (7/7). All 10 GPT
  review findings are now addressed (§4a).
- [x] 2026-10-05 (session 8): **D sharpened (GPT review finding #1).**
  Removed `dobrushin2` (def + `dobrushin2_def`/`_nonneg`/`_submult`)
  and the private `apply_mass_nonneg`/`apply_sum_mass`; `absSumLeTV`,
  `rowWeightBound`, `sumOnSEqWeighted` made public. New sharp
  `dobrushin_contraction : tv (μK, νK) ≤ δ(K) · tv(μ,ν)` (one-sided
  positive-set + min-shift proof, §4-D), new `dobrushinCoeff_submult`,
  `run_contraction` now `δ ^ n`, new `dobrushinCoeff_zero_iff`/`_zero`.
  `dobrushinCoeff_matrix_link` preserved verbatim. Full `lake build` green
  (3193 jobs), zero warnings, zero sorry. **This commit.**
  GPT review triage: #1 done (this commit); #2 (perturbation telescoping)
  + #6 (uniform bound) → next: rewrite `Perturbation.lean`
  (`crudeTelescope`, `weightedTelescope` with the per-step `Δ·∏δ` bound,
  `compList_submult`, `hybridTelescope_uniform` without the extra
  hypothesis); #3 → BL redesign (`BLState (N m)`, `lo := m − (N − m)`,
  `hi := m`, `blStationary (N m x)`; Commander bridge stays in
  `BernoulliLaplaceGeneral`); #4 (import direction generic→Commander),
  #5 (`tv_eq_zero` comment), #7 (Markov docstring overclaim),
  #9 (Finite.lean hallucinated "Krein–von Neumann" doc), #10 (process) —
  remaining after #2/#6 (done in session 9) and #3. The shelved F2 rewrite
  (`/tmp/BLG_F2_attempt_final.lean`) was written against the old `BLState
  (N m k)` design — **obsolete**, re-derive against the §4-F redesign.
- [x] 2026-10-04 (session 7): **Priority E complete.** Commit 50bdde5 —
  `Markov.lean`: `Stationary` / `stationary_run` (iteration preserves a
  one-step certificate), `DetailedBalance`,
  `detailedBalance_implies_stationary` (single-sum argument: sum the
  balance equation over `x` at fixed `y`; only row-mass-1 of `K` needed),
  `applyFn` (row action on functions) / `weightedInner` (mu-weighted
  bilinear form; degenerate at states with mass 0, so not an inner
  product in the strict sense), `selfAdjoint_of_detailedBalance`
  (reversible row operator is
  self-adjoint in the stationary-weighted form: double-sum expansion,
  termwise balance swap, regroup via `Dist.double_sum_pullout`),
  `stationary_of_detailedBalance`. `Shufflemath.lean` now imports Markov.
  `./dev/verify.sh` green after E (3193 jobs, 7/7 Python tests). Mechanics
  notes: `applyFn`/`weightedInner` defs need explicit `[Fintype]` args
  (bodies use `Finset.univ`); `rw` of a def equation theorem fails on the
  eta form `(def K f) x` — use `simp only [def]`; a `calc` whose targets
  are themselves equalities (Props) needs `congrArg` gymnastics — restructure
  as a chain of `have`-proved term equalities instead; `nlinarith` cannot
  multiply a hypothesis by a compound monomial — do the factor swap as a
  3-step `ring`/`rw [hdb]`/`ring` calc.
- [x] E. Markov (`Markov.lean`: stationary, detailed balance, self-adjointness) —
  committed 50bdde5.
- [x] 2026-10-04 (session 13): **F part 1 — general BL states, row
  stochasticity, exchange kernel.** `Shufflemath/BernoulliLaplaceGeneral.lean`
  rewritten to a free `r` parameter: `BLState N m r := {x : Nat // blLo ≤ x ∧
  x ≤ blHi}` with `blLo := max (r - (N - m)) 0`, `blHi := min m r`; parameterless
  `ExchangeAdmissible` structure (N, m, r, k + six admissibility proofs);
  generalized `transitionNumerator`/`transitionDenominator`/`transitionWeight`.
  **`blRowStochastic` (double Vandermonde, row sum = 1)** — the general-`r`
  proof restructures the y-split into three window cases (below lo / in
  `[lo, min m r]` / above hi). Since the window predicates now only give
  `y ≤ r`, the "all three windows hold" branch splits on `y ≤ m`: `y ≤ m`
  forces `y ∈ As`, a contradiction; `y > m` kills the second factor
  `choose (m-x) (k-a)` via the contradiction argument
  `y ≤ (x-a)+k ≤ (x-a)+((m-x)+a) = m`. The inner `a↔b` bijection is
  truncated when `r > m`: the image set splits into `Bs1 := {b ≤ r-x,
  b < m+1-(x-a)}` (where the bijection holds) and `Bs \ Bs1` (terms vanish —
  second factor zero for `a ≤ x`, first factor zero for `a > x`).
  **`blExchangeKernel`** is the `FiniteKernel (BLState N m r) (BLState N m r)`
  via `Dist.ofFun`; its total-mass argument bridges `Finset.univ` (the pmap
  finset of the `Fintype.ofFinset` instance) to `stateFinset` with
  `Finset.sum_bij (fun y _ => y.val)` — the v4.34 signature is the dependent
  5-argument form (image / injective / surjective / term-equality bullets;
  injective bullet needs `Subtype.coe_injective`, surjective bullet closes
  with `Fintype.complete`, not `by simp`). Mechanics learned: `rw [← hk]`
  with `hk : (k-a)+a = k` rewrites the `k` *inside* `(k-a)` — scope it with
  `conv in (x - a + k) => ...`; `rw [def]` of a let/ite body fails at
  subterm positions inside a sum — bridge with `change`; `rw [hlo]` on a
  `have` with a non-rfl body fails — re-derive with `have h' := by simpa
  using h`; `Finset.sum_bij`'s surjectivity bullet desugars to a 3-level
  `∧` chain plus the equality, so simp the goal before the 5-leaf refine;
  `Finset.mem_Icc` / `Fintype.complete` are the v4.34 membership lemmas;
  `Nat.add_sub_cancel_left/right`, `Nat.sub_add_cancel`,
  `Nat.choose_eq_zero_of_lt`, `Nat.choose_symm`, `min_eq_left/right`
  (one-way, no `.mpr`), `Nat.sub_le_iff_le_add`, `Nat.le_max_left` for
  extracting the `blLo` bound; `Nat.cast_sum` before `Finset.sum_nonneg`;
  `div_nonneg_iff` wants `0 ≤ den`, feed `Nat.cast_nonneg`. Full `lake build`
  green, zero warnings; tests 7/7.
- [x] 2026-10-04 (session 13, cont.): **F part 2 — general stationary
  distribution.** `blStationary N m r (x : BLState N m r)` is the
  hypergeometric mass `choose r x.val * choose (N-r) (m-x.val) / choose N m`.
  **`blStationaryTotal`**: the state-space sum equals 1 — three steps:
  (1) extend the window sum to `Finset.range (m+1)` via `Finset.sum_sdiff`
  plus `blStationaryTerm_zero` (off-window terms vanish: `b < blLo` splits
  on `r ≤ N-m` — `blLo = 0`, impossible — vs `r > N-m`, where a pure-`Nat`
  chain `(N-m)+b < r → N+b < m+r → N+b-r < m → N-r+b < m → N-r < m-b`
  kills `choose (N-r) (m-b)`; `b > blHi` kills `choose r b`);
  (2) the range sum is `choose (r + (N-r)) m = choose N m` via
  `vandermondeRange`; (3) division by the positive denominator. The
  off-window lemma is proved *entirely in `Nat`* — the earlier `ℤ`-bridge
  attempts kept failing on cast-repacking (`↑(a-b)` vs `↑a - ↑b` are not
  definitionally equal; `exact_mod_cast` only normalizes in one direction),
  so the chain uses `Nat.sub_lt_sub_iff_right (h : c ≤ a)`,
  `Nat.sub_add_comm {n m k} (h : k ≤ n) : n + m - k = n - k + m`
  (k implicit in v4.34), and `Nat.lt_sub_iff_add_lt` (no side condition).
  **`blStationaryDist : Dist (BLState N m r)`** via `Dist.ofFun` with the
  same `Finset.sum_bij` univ-to-window bridge as `blExchangeKernel`; the
  term-equality bullet needs one extra `rw [Nat.cast_mul]` because the
  summand's `(a * b : Rat)` ascription elaborates to a *product of casts*
  while the `blStationary` definition carries a *cast of the product*
  (the pretty printer shows both the same way — a trap). `rw` does not
  descend into the lambda body of `∑` notation, so packing the summand
  casts uses `simp only [← Nat.cast_mul, ← Nat.cast_sum]` (both reverse —
  `Nat.cast_sum`'s default direction is cast-of-sum → sum-of-casts).
  Full `lake build` green, zero warnings; tests 7/7.
- [x] 2026-10-05 (session 14, commits e91370f / 924e820 / adc4b82 /
  6b807ad): **F part 3 (in progress) — fiber factorization.** The
  detailed-balance proof is done by *counting the exchange fiber directly*
  rather than the §4-F 4-tuple `(S, A, B)` index-bijection sketch: F3a
  (`e91370f`) — `fiberSum` (7-level nested fiber count of the pair `(x, y)`),
  `fiberABcount`/`fiberABchoose` (the `(A, B)` part of a fiber is the product
  of four powerset-cardinalities = the `a`-summand of
  `transitionNumerator`), `fiberSum_eq`
  (`fiberSum (x, y) = C(r, x)·C(N−r, m−x)·num(x, y)`; the plain-card
  saturation identity `N−r−(m−x) = N−m−(r−x)` handled by a two-case split on
  `m+r ≤ N+x`). F3b (3 stages: `924e820`/`adc4b82`/`6b807ad`) — flat
  7-tuple fiber `fiber7Tuple` with projections `tS1…tB2`, ambient universe
  `fiber7Univ` (nested powerset products), `fiber7Pred` (12 conditions),
  `fiber7Set`; 3-tuple/4-tuple repackaging `t3Of`/`t4Of`/`mk7` with
  losslessness `re7`/`re7'`/`re7''`; `fiberFlat`
  (`#fiber7Set (x, y) = fiberSum (x, y)`, 5-step cardinality-computation
  proof avoiding sum-rewrite descension into the nested products).
- [x] F. General BL (`BernoulliLaplaceGeneral.lean`: states, row stochasticity,
  stationary, detailed balance, Commander link) — **complete** (sessions 13–16
  and the 2026-10-07 session): `BLState N m r` / `blLo` / `blHi` /
  `stateFinset` / `ExchangeAdmissible`, generalized
  `transitionNumerator`/`transitionDenominator`/`transitionWeight`,
  `blRowStochastic` (double Vandermonde, general `r`),
  `transitionWeight_nonneg`, `transitionDenominator_pos`, `blExchangeKernel`,
  `blStationary` / `blStationaryTotal` / `blStationaryDist`, fiber machinery
  (`fiberSum`/`fiberSum_eq`/`fiber7*`/`fiberFlat`/`fiber7Inv`/
  `fiberSum_swap`), detailed balance (private `detailedBalance` Nat-level
  identity via `fiberSum_swap` + `fiberSum_eq`; public `blDetailedBalance`),
  `blStationaryDist_is_stationary` (via
  `Markov.detailedBalance_implies_stationary`) and `blStationaryRun`.
  The Commander link lives in the separate bridge module
  `Shufflemath/BernoulliLaplaceCommanderBridge.lean` (imports both,
  GPT review #3): state-space equivalences `commanderToBL` / `blToCommander`
  (+round-trips), `transitionWeight_general_eq_commander`,
  `commanderExchange25_matches_blExchange`,
  `commanderStationary_matches_blStationary`.
- [x] 2026-10-07 (session 15): commit 1a0cb94 — **F part 3 stage 4
  complete.** `fiber7Inv` (the 7-tuple exchange involution),
  `fiber7Inv_mem`, `fiber7Inv_inv`, `fiberSum_swap`. **Math finding:**
  `fiber7Pred`'s 12 conditions do not force the left-pile capacity
  `x ≤ p.m` (they stay consistent with `x > p.m`, where `p.m - x = 0`;
  concrete counterexample N=10, m=6, r=9, k=2, x=7, y=6, a=2), and for
  such tuples the image leaves the `(y,x)` fiber — the `#S2' = p.m - y`
  arithmetic breaks. The theorems therefore carry `x ≤ p.m` (and
  `fiberSum_swap` also `y ≤ p.m`) as physical-admissibility hypotheses;
  the detailed-balance theorem must restrict to such `(x, y)`. Mechanics
  (all in `docs/lessons_learned.md`): `omega` takes no `[h]` list and
  cannot do nested Nat-subtraction algebra (break into small rearrangement
  equalities it can prove, then rw: `Nat.sub_sub`,
  `Nat.le_sub_iff_add_le`, `Nat.sub_add_cancel`, `Nat.add_sub_assoc`);
  Finset membership is not a Prop structure (use `mem_union`/`mem_sdiff`
  `.mp`/`.mpr`, not `constructor`/`rcases`/simp-at); `ext` on nested
  products recurses to the bottom; `refine F (g ?_)` breaks `⟨⟩`
  elaboration (use `apply` chains); `simp` on a `×ˢ` chain stops one level
  short and yields a left-nested `And` (rebuild with explicit
  `Finset.mem_product.mpr` per level).
- [x] 2026-10-07 (session 16, commits f5a4716 / 8d40b9a / b49fcb3): **F
  complete.** (1) Detailed balance: private `detailedBalance` —
  `π(x)·W(x,y) = π(y)·W(y,x)` as a `Rat` identity; both sides reduce to
  `fiberSum / D` with the common denominator
  `D = (C(N,m) : Rat) · (transitionDenominator : Rat)` (`hside` helper:
  `field_simp` + `← Nat.cast_mul` + `← fiberSum_eq` + `dsimp [D]` + one
  more `field_simp [hC]` + `rw [Nat.cast_mul]` to match the two-cast
  denominator shape), then `calc` over `fiberSum_swap` (needs the
  `x.val ≤ p.m` / `y.val ≤ p.m` physical-admissibility hypotheses from the
  session-15 math finding). Public `blDetailedBalance` unpacks it via
  `mass_ofFun`. (2) Reversibility + stationarity: `blStationaryDist_is_
  stationary` via `Markov.detailedBalance_implies_stationary` (the
  `Stationary`-as-`Dist`-equality goal is closed through
  `tv_zero_iff_eq` + `Dist.mass_ofFun`); `blStationaryRun` by
  `Markov.stationary_run`. (3) Bridge module `BernoulliLaplaceCommander
  Bridge.lean` (110 lines): `BLState 99 50 50 ↔ Fin 50` via
  `blLo 99 50 50 = 1`, `blHi 99 50 50 = 50`; `transitionWeight_general_eq
  _commander` (the two copies of the transition formula coincide — the
  general one is `r`-free at `r = 50`); kernel- and stationary-mass
  matching theorems. `Shufflemath.lean` gains the bridge import.
- [x] 2026-10-07 (session 17, commit 184f7b1): **G batch 1 — first-mode
  binomial lemmas** in the new `section firstMode` of
  `BernoulliLaplaceGeneral.lean`: `chooseSucc_weighted`
  (`(x+1)·C(n, x+1) = n·C(n-1, x)`, all `n x` — the `x ≥ n` branch kills
  both binomials, `n = 0` handled by a nested case) and
  `chooseSum_weighted (n x k) (hx : x ≤ n)`:
  `∑_{a<k+1} (a : Rat)·C(x,a)·C(n-x,k-a) = (k·x/n)·C(n,k)` — the 1-D
  hypergeometric mean identity. Proof: case-split on `k = 0` / `x = 0`
  (both sides 0), then reindex `a = i+1, i < k` via `Finset.sum_bij`
  (the `a = 0` summand is 0), per-term `a·C(x,a) = x·C(x-1,a-1)`-style
  shift (Pascal), Vandermonde over the antidiagonal
  (`Nat.add_choose_eq` + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`),
  closed by `chooseSucc_weighted n (k-1)`. Mechanics recorded in
  `docs/lessons_learned.md` (cast-ascription parsing, `rw` rewriting
  inside `k-1`, `simp at` on opaque locals).
- [ ] G. First eigenfunction (general + Commander corollaries) — **in
  progress**: G1 `chooseSucc_weighted` + `chooseSum_weighted` (184f7b1);
  G2 `innerYToB_b` (this session): the weighted version of `innerYToB` —
  for fixed `a ≤ k`, the inner `y`-sum of the `a`-term of `guardedTerm`
  weighted by `y - (x - a)` (the number `b` of special cards returning)
  reindexes, via the same support window / bijection / zero-tail argument
  as `innerYToB`, to the `b`-sum of `exchangeTerm` weighted by `b`
  (needed for `E[b | x]`). Remaining: G3 the conditional-mean theorem
  `E[y | x] = x − (k/m)·x + (k/(N−m))·(r−x)` (see "Next action"), G4 the
  first-mode eigenfunction `∑_y W(x,y)·(y − m·r/N) = λ·(x − m·r/N)` with
  `λ = 1 − N·k/(m·(N−m))` (one line of `Rat` field algebra over G3 —
  verified by hand: the fixed point `μ = m·r/N` satisfies
  `E[y|μ] = μ` for general `r`), G5 Commander corollaries tying
  `commanderFirstMode k` / the k=24/25/26 factor values to the general
  eigenvalue (home: the bridge module, which imports both sides).
- [ ] H. Stretch: GSR, higher modes, separation distance.
- [ ] Final: full `./dev/verify.sh` green, docstrings audited, §6 values
  re-confirmed, this file updated, everything committed.

**Next action:** G3 — conditional mean, in `section firstMode` of
`BernoulliLaplaceGeneral.lean`. Target theorem (Rat, admissible `p`,
state `x`):

```lean
theorem blConditionalMean (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    (∑ y ∈ stateFinset p.N p.m p.r,
      (y : Rat) * (transitionWeight p.N p.m p.r p.k x.val y)) =
      (x.val : Rat) - (p.k : Rat) * (x.val : Rat) / (p.m : Rat) +
      (p.k : Rat) * ((p.r - x.val) : Rat) / ((p.N - p.m) : Rat) := by …
```

Strategy (mirror `blRowStochastic`'s structure; all pieces are already in
the file): the `y`-sum over the window = the `y`-sum over `Finset.range
(m+1)` — off-window terms vanish with their weight (new private support
lemmas: `y-weighted num_zero_below_lo` / `num_zero_above_r`; the weighted
`guardedTerm` is 0 whenever the unweighted one is, since the weight is a
pure `Nat` factor). For each `a`: `y = (x - a) + (y - (x - a))`, so the
weighted inner sum = `(x - a) · (innerYToB) + (innerYToB_b)`. Then:
`∑_b exchangeTerm(x,a,b) = C(x,a)·C(m-x,k-a)·C(N-m,k)`
(`vandermondeRange (r - x) (N - m - (r - x)) k` — note the cast-to-Rat
bookkeeping: do the `Nat` computation first, cast once at the end) and
`∑_b b·exchangeTerm(x,a,b) = C(x,a)·C(m-x,k-a)·(k·(r-x)/(N-m))·C(N-m,k)`
(`chooseSum_weighted (p.N - p.m) (p.r - x.val) p.k` — its `hx : x ≤ n`
hypothesis is `r - x ≤ N - m`, which is exactly `blLo ≤ x` when
`r > N - m` and trivial when `r ≤ N - m`; the existing `num_zero_below_lo`
splits on that same `r ≤ N - m` — reuse the pattern). Outer `a`-sum:
`∑_a C(x,a)·C(m-x,k-a) = C(m,k)` (`vandermondeRange x (m-x) k`),
`∑_a a·… = (k·x/m)·C(m,k)` (`chooseSum_weighted m x k`). All in `Rat`,
`field_simp [hden]` with `hden : (transitionDenominator : Rat) ≠ 0`.
Mechanics: keep `Nat` until the final cast (the `chooseSum_weighted`
statement is Rat; `innerYToB*` / `vandermondeRange` are Nat — bridge
with `Nat.cast_mul`/`Nat.cast_add`/`Nat.cast_sub` where the types meet).
Then G4 (eigenfunction) and G5 (Commander corollaries in the bridge
module).

## 8. Taste & style rules

- Proofs should read like the mathematics: small lemmas, `calc` blocks, named
  intermediate claims (`have` with a name, or a private lemma). Prefer explicit
  `calc` over `aesop` for anything nontrivial; `aesop`/`tauto`/`linarith`/`ring`/`norm_num`/
  `positivity` are fine for the mechanical tail of a proof.
- `native_decide` only for genuinely finite certificates (existing pattern);
  never as a substitute for symbolic structure. Never `set_option maxHeartbeats 0`.
- Docstring on every nontrivial theorem: what it says, why it matters downstream.
- Extend existing files/namespaces; new files only where the plan says so
  (C, D, E, F). Keep `Shufflemath.lean` as the import list of record.
- When stuck on `Nat` arithmetic (subtraction, bounds), convert to `ℤ`/`Rat`
  with a `have` cast lemma rather than fighting `Nat` lemmas; exactness is
  preserved because everything lives in `ℚ` at the end.
- Commit messages: `Add <thing>`, `Prove <theorem>`, `Fix <bug>`; body may
  explain the proof idea in 1–3 lines; always the co-author trailer (§2 rule
  4: `Qwen3.8-27B-W4A16-AutoRound <noreply@qwen.ai>`).
