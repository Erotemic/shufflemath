# Autonomous Lean Formalization Build — Handoff & Resume Document

**Status:** ACTIVE. **Owner:** any pi agent pointed at this file.
**Deadline: Sat Oct 6 22:27:06 EDT 2026.**

## 0. Standing rules for the agent reading this document (non-negotiable)

1. **Do not stop, ask, or end the session before Sat Oct 6 22:27:06 EDT 2026.**
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
4. **Commit trailer (exact):** `Co-authored-by: Qwen3.8:27b <noreply@openai.com>`
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

`Shufflemath.lean` imports: `Finite`, `Matrix`, `TotalVariation`, `Cost`,
`BernoulliLaplace`. Add new modules here when created.

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
- **Missing (Priority A):** associativity/identity laws, `apply_comp`, matrix bridges.

**`Shufflemath/TotalVariation.lean`** — imports `Shufflemath.Matrix`:
- `vectorTV p q := (1/2) * ∑_x |p x − q x|` over `Fintype` univ.
- `vectorTV_self` (simp), `vectorTV_comm`, `vectorTV_nonneg`,
  `vectorTV_le_one_of_probability` (four hypotheses: nonneg×2, total×2).
- `Dist.tv p q := vectorTV (mass p) (mass q)`; `tv_self` (simp), `tv_comm`,
  `tv_nonneg`, `tv_le_one`.
- `namespace MatrixTV`: `rowTV P i j`; `pairDistances P` (`Finset Rat`, image over
  `univ × univ`); `pairDistances_nonempty`; `dobrushinCoeff P :=
  (pairDistances P).max' …` (**max of TV**, i.e. ≤ 1, convention note in §4-D);
  `rowTV_le_dobrushin`; `dobrushinCoeff_nonneg` (simp); `dobrushinCoeff_le_one`
  (from `Matrix.rowStochastic`).
- **Missing (Priority B):** triangle, `eq_zero`, positive-set/max-event
  characterization, kernel contraction. **Missing (C/D):** discrepancy, hybrid
  telescope, kernel Dobrushin + contraction + submultiplicativity.

**`Shufflemath/Matrix.lean`** — `namespace FiniteKernel`:
- `toMatrix K := fun x y => Dist.mass (K x) y`.
- `toMatrix_mem_rowStochastic` (`Fintype` + `DecidableEq`).
- `ofRowStochastic P hP : FiniteKernel α α` (noncomputable);
  `toMatrix_ofRowStochastic` (simp).
- **Missing (A):** `toMatrix_comp`, `toMatrix_run`.

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
- **Missing (F, G):** general symbolic theory in a *new* file
  `Shufflemath/BernoulliLaplaceGeneral.lean` — do not restructure this file;
  it is a stable certificate base.

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

### D. Dobrushin contraction — NEW `Shufflemath/Dobrushin.lean`

- `dobrushinCoeff (K : FiniteKernel α α) : Rat` — max over `i, j` of
  `Dist.tv (K i) (K j)` (mirror of `MatrixTV.dobrushinCoeff`; same
  `pairDistances`-style Finset image + `max'`). `dobrushinCoeff_nonneg` (simp),
  `dobrushinCoeff_le_one` (via `vectorTV_le_one` — rows are distributions).
- `dobrushin2 (K) := 2 * dobrushinCoeff K` — the actual contraction constant
  (document the convention: `MatrixTV.dobrushinCoeff` and this one are max-TV,
  ≤ 1; `dobrushin2 ≤ 2` and is submultiplicative).
- **`dobrushin_contraction : Dist.tv (apply μ K) (apply ν K) ≤
  dobrushin2 K * Dist.tv μ ν`.**
  Proof (all event-level, no division): by B's `tv_eq_positive_set`,
  `tv(Kμ, Kν) = max_S ∑_S (Kμ − Kν)`; for any `S`, writing
  `r x := ∑_{y ∈ S} K x y` (a `[0,1]`-valued weight, nonneg + row-total):
  `∑_S (Kμ − Kν) = ∑_x (μ x − ν x) · r x` (swap sums). Key sub-lemma:
  for any `S` and any `i, j`, `|r i − r j| ≤ Dist.tv (K i) (K j)`:
  because `tv(K i, K j) = max_T ∑_T (K i − K j)`, take `T := S` and
  `T := Sᶜ` (complement Finset). Then with arbitrary base point `x₀`:
  `∑_x (μ x − ν x) r x = ∑_x (μ x − ν x) (r x − r x₀) ≤
  ∑_x |μ x − ν x| · |r x − r x₀| ≤ dobrushinCoeff K · ∑_x |μ x − ν x|
  = 2 · dobrushinCoeff K · tv(μ, ν) = dobrushin2 K · tv(μ,ν)`
  (use `∑ (μ − ν) = 0` to insert the `r x₀` term).
- `dobrushin2_submult : dobrushin2 (comp K L) ≤ dobrushin2 K * dobrushin2 L`:
  `tv((K∘L) i, (K∘L) j) = tv(apply (K i) L, apply (K j) L) ≤
  dobrushin2 L · tv(K i, K j) ≤ dobrushin2 L · dobrushinCoeff K ≤
  (dobrushin2 L · dobrushin2 K) / 2`, i.e. `2·…` works out — verify the
  constants on paper before coding; state whatever the clean true inequality
  is with a docstring spelling the convention.
- `run_contraction (n) : Dist.tv (run K n μ) (run K n ν) ≤
  (dobrushin2 K) ^ n * Dist.tv μ ν` (induction on `n`).

**Done:** build green; cross-check against `MatrixTV.dobrushinCoeff` via
`toMatrix` (add `dobrushinCoeff_matrix_link : dobrushinCoeff (ofRowStochastic
P h) = MatrixTV.dobrushinCoeff P`-style lemma — cheap, proves consistency).

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

### F. General Bernoulli–Laplace — NEW `Shufflemath/BernoulliLaplaceGeneral.lean`

Parameters: `N m k : Nat` with `0 < m < N`, `0 < k`, `k ≤ m`, `k ≤ N − m`
(two piles of sizes `m` and `N − m`, exchanging `k` from each). Macrostate
`x` = original-left cards in the left pile.

- `BLState (N m k) (h…) : Type := { x : ℕ // max (m − (N − m)) 0 ≤ x ≤ min m (N − m) }`
  (Fintype via `Fintype.ofFinset`; keep the bounds lemmas as simp).
  Commander check: `N=99, m=50` → `1 ≤ x ≤ 50` ✓.
- Reuse the existing `BernoulliLaplace.transitionNumerator/Denominator/Weight`
  verbatim (they are already general) — import and use; do **not** redefine.
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

## 5. Verified mathlib hooks (v4.34.0, checked on this machine)

- `Convexity.StdSimplex` — `Mathlib/Geometry/Convex/ConvexSpace/Defs.lean`:
  fields `weights` (Finsupp), `nonneg`, `total`; lemmas `single`, `map`,
  `join`, `ext` (alias of `weights_inj`), `total_of_fintype`, `weights_nonneg`,
  `weights_apply_le_one`.
- `Matrix.rowStochastic` — `Mathlib/LinearAlgebra/Matrix/Stochastic.lean`:
  `mem_rowStochastic_iff_sum`, `nonneg_of_mem_rowStochastic`,
  `sum_row_of_mem_rowStochastic`.
- `Matrix.mul_apply` — `Mathlib/Data/Matrix/Mul.lean`.
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
- [ ] A. Kernel algebra (`Finite.lean`, `Matrix.lean`).
- [ ] B. TV laws (triangle, eq_zero, positive-set, kernel contraction).
- [ ] C. Perturbation (`Perturbation.lean`: discrepancy, compList, hybridTelescope).
- [ ] D. Dobrushin (`Dobrushin.lean`: coeff, contraction, submult, run).
- [ ] E. Markov (`Markov.lean`: stationary, detailed balance, self-adjointness).
- [ ] F. General BL (`BernoulliLaplaceGeneral.lean`: states, row stochasticity,
  stationary, detailed balance, Commander link).
- [ ] G. First eigenfunction (general + Commander corollaries).
- [ ] H. Stretch: GSR, higher modes, separation distance.
- [ ] Final: full `./dev/verify.sh` green, docstrings audited, §6 values
  re-confirmed, this file updated, everything committed.

**Next action:** Priority A — start with `apply_comp` in `Shufflemath/Finite.lean`.

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
  explain the proof idea in 1–3 lines; always the Qwen trailer.
