# Autonomous Lean formalization build — handoff & resume document

**Status:** ACTIVE. **Deadline: Mon Oct 12 22:27:06 EDT 2026.** This file
is the compaction-resume document: after any compaction, read it top to
bottom, then `git log --oneline -10` and `lake build`, then resume at the
"Next action" section at the end of this file. The session-by-session
history and reference material live in `docs/lean_build_history.md`.

## 0. Standing rules for the agent reading this document (non-negotiable)

1. **Do not stop, ask, or end the session before Mon Oct 12 22:27:06 EDT 2026.**
   This is a long autonomous build. You **will be compacted multiple times**;
   compaction is normal and is not a stopping signal.
2. **After every compaction, do exactly this, in order:**
   a. Read this document top to bottom.
   b. Run `git log --oneline -10` and `git status --short` in `/home/joncrall/code/shufflemath`.
   c. Run `lake build` to confirm the tree is green (if red, fix before anything else).
   d. Resume work at the "Next action" section at the end of this file.
      The compact §5 log records what is done; the full session log is
      in `docs/lean_build_history.md`.
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
6. **Keep this document updated.** After each commit, tick the item in §5 and
   adjust "Next action". This file is the only thing a compacted/fresh agent
   can trust; the conversation is not.
7. **Do not stop early even if A–G are all done.** Fall through to §4-H
   stretch goals, then to verification pass (re-run `./dev/verify.sh`, audit
   docstrings, re-check §6 regression values), until the deadline.
8. **Stuck protocol.** If a single proof resists ~2 build iterations, write a
   `-- TODO(proof): <sketch>` comment at the exact location, commit what
   builds, move to the next item, and return later. Never leave a broken
   build, never leave a `sorry`.
9. **Taste rules:** see §7. Exact rationals only; no `set_option maxHeartbeats 0`;
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
  Verified hooks you can rely on are listed in `docs/lean_build_history.md` §3.
- Lean tooling from the submodule (`aiq-lean`, `leanq`) is available for
  audits; not required for the main build. If you rename or move a tracked
  declaration, update any census ledger in the same commit.

## 3. Current state — file map (as of 2026-10-08, after the cleanup batch e19afb5)

The library root `Shufflemath.lean` imports, in this order: `Finite`,
`Matrix`, `TotalVariation`, `Perturbation`, `Dobrushin`, `Markov`, `Cost`,
`BernoulliLaplace`, `BernoulliLaplaceGeneral`, `BernoulliLaplaceFiber`,
`BernoulliLaplaceCommanderBridge`. All eleven modules build; the Python
side of the repo is unchanged by the Lean work.

- **`Finite.lean`** — `Dist`/`Kernel` algebra (identity, `comp`, `run`,
  `compPow`, `run_compPow`, `apply_mass`, `double_sum_pullout`).
- **`Matrix.lean`** — the `toMatrix` bridge (identity/comp/compPow/run
  agree).
- **`TotalVariation.lean`** — `vectorTV`/`Dist.tv` laws, the `PositiveSet`
  section, `kernel_contraction`, `tv_zero_iff_eq`.
- **`Perturbation.lean`** — `kernelDiscrepancy`, `compList`, the
  `weightedTelescope` flagship and its corollaries. File-level
  `maxHeartbeats 400000` (see the file header comment).
- **`Dobrushin.lean`** — the sharp `δ(K)` contraction, `submult`,
  `run_contraction`, `zero_iff`, the matrix link.
- **`Markov.lean`** — `Stationary`, `DetailedBalance`, `applyFn`/
  `weightedInner`, self-adjointness.
- **`Cost.lean`** — `CostedKernel`, `protocolCost`.
- **`BernoulliLaplace.lean`** — the frozen Commander 99-card 50/49 k=25
  certificates (row stochasticity, stationarity, the 1-/2-/3-step fixed
  points, the exact TV values, the first-mode finite theorem).
  **Do not restructure this file**; the general module deliberately keeps
  its own copy of the transition formula and the bridge proves the two
  agree.
- **`BernoulliLaplaceGeneral.lean`** (~1500 lines) — the general N m r
  theory: `BLState`/`blLo`/`blHi`/`stateFinset`, `ExchangeAdmissible`, the
  transition formula, the symbolic `blRowStochastic`,
  `blStationary`/`blTotal`/`blStationaryDist`, `blExchangeKernel`, and
  `section firstMode` (G1 `chooseSucc_weighted`/`chooseSum_weighted`, G2
  `innerYToB_b` — note `innerYToB_b` is a file-level private lemma above
  the section).
- **`BernoulliLaplaceFiber.lean`** — the detailed balance by fiber
  counting (the fiberSum/fiber7* machinery, `fiberFlat`, the involutive
  swap, `fiberSum_swap`, `detailedBalance`, `blDetailedBalance`,
  `blStationaryDist_is_stationary`, `blStationaryRun`). Imports only the
  general file.
- **`BernoulliLaplaceCommanderBridge.lean`** — the `BLState 99 50 50`
  `↔` `Fin 50` identification, the transition-weight / stationary /
  kernel match theorems. In the build graph since the 2026-10-08 cleanup
  (e19afb5), which also repaired it against the redesigned API.

The hard-won Lean-mechanics notes and the verified mathlib hook list
(keep reading these before heavy proof work) live in
`docs/lean_build_history.md` §1 (mechanics) and §3 (hooks).

## 4. Remaining plan (A–F done; G in progress; then H)

**G. First eigenfunction** (in progress) — `BernoulliLaplaceGeneral.lean`,
`section firstMode`, plus the bridge module:

- **G1 (done):** `chooseSucc_weighted` + `chooseSum_weighted` (weighted
  Vandermonde + weighted-sum identities).
- **G2 (done):** `innerYToB_b` (the weighted `y → b` reindexing).
- **G3 (done):** `innerYToB_w` (16b667b), `bSumE`/`bSumE_nat` (64e4024),
  `bSumE_w` (bf86684), `aSumE`, and the `blConditionalMean` theorem
  (00cd98c) — the conditional mean `x - (k/m)·x + (k/(N-m))·(r-x)`.
- **G4:** the first *centered* eigenfunction theorem: the centered
  observable `f(x) = x - m·r/N` (stationary mean `μ = m·r/N`) satisfies
  `applyFn (blExchangeKernel p) f = blFirstModeFactor p.N p.m p.k • f`,
  where the general first-mode factor is
  `blFirstModeFactor (N m k) := 1 - (N : Rat) * k / ((m : Rat) * (N - m))`. This
  is the first centered linear mode; it is **not** a claim about the
  largest nontrivial eigenvalue in absolute value, nor a TV-optimality
  statement.
- **G5:** the Commander corollaries in the bridge module: package the
  conversions as `commanderBLEquiv : Fin 50 ≃ BLState 99 50 50`, prove the
  general factor agrees with the concrete `firstModeFactor`, and derive
  the specializations `λ₁(24) = 37/1225`, `λ₁(25) = -1/98`,
  `λ₁(26) = -62/1225` from the single general formula.
  (The older draft of this plan had `f(x) = 1 - x/m + (x-r)·k/(N-m)` and
  `λ = -25/49` for Commander — both wrong, corrected 2026-10-08.)

**H. Stretch** (after G, in the order of `docs/lean_plan.md` §4): the GSR
theorem, higher modes, the separation distance, the perturbation→TV
chain, the mixing time.

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

## 5. Progress (compact; full session log in `docs/lean_build_history.md`)

- **A** (2026-10-05): kernel algebra — commutative case, compPow/run
  laws, `double_sum_pullout` (`Finite.lean`, `Matrix.lean`).
- **B**: TV laws + contraction + `tv_zero_iff_eq` (`TotalVariation.lean`).
- **C**: `Perturbation.lean` — `weightedTelescope` flagship + corollaries.
- **D**: `Dobrushin.lean` — sharp contraction + run bound.
- **E**: `Markov.lean` — stationarity, reversibility, self-adjointness.
- **F** (2026-10-07): general Bernoulli–Laplace — the frozen
  `BernoulliLaplace.lean` and `BernoulliLaplaceGeneral.lean`
  (`blRowStochastic` symbolic; stationarity; detailed balance; kernel
  agreement).
- **G1/G2** (2026-10-07/08): the first-mode building blocks in
  `section firstMode`.
- **Cleanup** (2026-10-08, e19afb5): the fiber section moved to
  `BernoulliLaplaceFiber.lean`; the bridge module repaired and brought
  into the build graph; this document split into a slim handoff (this
  file) + `docs/lean_build_history.md`.

## 6. Numeric regression targets (must stay reproducible — do not change them)

- GSR TV after n riffles for 52-card and 99-card decks (Python: `experiments/`).
- Commander BL TV after 0–4 exchanges of 25 cards (Python `protocol_distance`;
  Lean 2-step and 3-step exact fractions are pinned in
  `BernoulliLaplace.lean` — values listed in §3; the Lean 0- and 1-step values
  are 1 and `25/49`-family — re-derive, don't trust this note).
- First-mode factors k=24/25/26: `37/1225`, `−1/98`, `−62/1225`.
- When any symbolic theorem touches these numbers, add a small
  `norm_num`/`native_decide` agreement check in the same commit.

## 7. Taste & style rules

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

**Next action:** G4 — the first *centered* eigenfunction theorem, in
`section firstMode` of `BernoulliLaplaceGeneral.lean` (after
`blConditionalMean`). The centered observable
`f(x) = (x : Rat) - (p.m : Rat)·(p.r : Rat)/(p.N : Rat)` (stationary mean
`μ = m·r/N`) satisfies, for the exchange kernel `K = blExchangeKernel p`:

```lean
theorem blFirstModeFunc (p : ExchangeAdmissible) (x : BLState p.N p.m p.r) :
    applyFn (blExchangeKernel p) (fun z => (z : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat)) x =
      blFirstModeFactor p.N p.m p.k • ((x.val : Rat) - (p.m : Rat) * (p.r : Rat) / (p.N : Rat)) := by …
```

Strategy (G3 + `blRowStochastic` + one line of `Rat` field algebra):
1. `applyFn` unfolds to `∑_y W(x,y)·f(y)`; split
   `∑_y W·(y - μ) = ∑_y W·y - μ·∑_y W`.
2. `∑_y W·y` is `blConditionalMean`; `∑_y W` is `1` (`blRowStochastic`;
   the kernel is stochastic, so its `applyFn`-mass is the same
   `stateFinset` sum).
3. Close with `field_simp`/`ring`: both sides are linear in `x` with
   slope `blFirstModeFactor = 1 - N·k/((m)(N-m))` and matching intercept
   (the stationary mean `μ` is a fixed point of the conditional mean,
   which is exactly why the constant terms cancel).

Then G5 (Commander corollaries in the bridge module): `commanderBLEquiv`,
the general-factor agreement, and the specializations `λ₁(25) = -1/98`,
`λ₁(24) = 37/1225`, `λ₁(26) = -62/1225`.
