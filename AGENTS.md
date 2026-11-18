# AGENTS.md

## What this is

`shufflemath` studies constrained physical card shuffling: which finite
sequences of cuts, mashes, and exchanges drive a deck to uniform fastest.
`README.md` has the motivation; `docs/` has the literature, the problem
statement, and the Lean theorem ladder. Three tracks run in parallel:
literature, exact finite computation (`experiments/`), and Lean
formalization (library `Shufflemath`).

## Active roadmap and next task

- **Active status and work queue:** `docs/lean_plan.md`.
- **Current single next action and proof acceptance criteria:**
  `docs/agent_handoff.md` (the active build is the **G1–G4 arbitrary-finite-
  deck generalization**, per the 2026-11-15 pivot; its resume point is
  `card_biUnion_pd`). F1 and F2 are complete.
- **Active do-not-stop rule:** `docs/agent_handoff.md` contains a
  **Standing rules** section (the revived October autonomous-build protocol)
  that is **active until Wed Nov 24 23:59:59 EST 2026** (extended from the
  original Thu Nov 12 22:27:06 EST, then to Wed Nov 18, and now to Wed Nov 24,
  each at the user's request): do not stop, ask,
  or
  end the session before then; compaction is not a stopping signal; its
  compaction-resume protocol, small-batch commit gates, and stuck protocol are
  binding. It has been re-pointed at the current work queue
  (`docs/lean_plan.md`) and the current verification path
  (`./dev/verify_next_phase.sh`).
- `docs/autonomous_lean_build.md` is an **archived October 4-12 session**;
  its expired deadline, old agent instructions, and model-specific commit
  attribution do not apply. `docs/formalization_next_phase.md` and the
  dependency audit are historical design notes, not the next-work queue.
- The user has confirmed the completed October 21 disintegration tranche
  compiles by moving on to the documentation handoff. Do not reopen its
  compilation status without concrete contrary evidence. **F1 is complete;
  resume at the F2c-iv-b capstone.**

## Build and verify

```bash
cd ~/code/shufflemath
lake exe cache get
lake build \
  Shufflemath.CommanderFiberWitness \
  Shufflemath.FiberDisintegration \
  Shufflemath.PhysicalExchangeReduction \
  Shufflemath.CommanderFullDeckDisintegration \
  Shufflemath.CommanderFiberCount \
  Shufflemath.CommanderFiberMembership \
  Shufflemath.CommanderMembershipKernels \
  Shufflemath.CommanderMembershipOrbits \
  Shufflemath.CommanderDeckGSR \
  Shufflemath.CommanderPhysicalExchange \
  Shufflemath.CommanderMarkedRightCount
./dev/verify_next_phase.sh
```

The toolchain and Mathlib versions are pinned (`lean-toolchain`,
`lake-manifest.json`). Prefer `lake exe cache get` before every targeted
`lake build`. `Shufflemath.lean` intentionally omits some optional modules,
so plain `lake build` does not prove the whole new tranche builds.
The legacy `dev/verify.sh` calls `lake update`: do not use that as the
normal incremental verification path. The expensive exhaustive pair
certificate is opt-in: `./dev/verify_next_phase.sh --pair`.

The library uses Lean 4.34's **`module`** system: every `Shufflemath/*.lean`
and the `Shufflemath.lean` aggregator start with a `module` header, use
`public import`, and wrap their body in an `@[expose] public section`. Keep new
or edited Lean files in that shape — the exact recipe (why `@[expose]`, why
`public import`, `native_decide`'s dual `public meta import`, the ban on
`private` inside `@[expose]` sections, and end-of-file scope auto-close) is
documented in `docs/agent_handoff.md`. `lakefile.lean` stays a plain Lake DSL
file (no `module`).

### Lean proof development and diagnostic output

- **Compilation, not an axiom-print inventory, is the routine proof-development
  check.** Keep `lake build <module>` and focused Lean commands quiet on
  success so genuine elaboration/type errors are easy to find. Do not add
  `#print axioms`, bulk `#check`/`#print`, or per-theorem axiom reporting to
  proof modules, default Lake targets, automatic `prove` commands, or CI.
- Do not repeatedly scan for `sorry` or `admit`, or advertise their absence as
  a meaningful result. Handle actual compiler warnings and errors when they
  occur. Do not manufacture a new proof-obligation gate merely to check that
  contributors wrote ordinary Lean proofs.
- Transitive axiom dependency review is a **separate, explicitly requested,
  end-of-formalization audit**. Compare named theorem dependencies against a
  previously reviewed baseline/allowed set, report **differences only**, and
  keep raw `#print axioms` output captured rather than flooding stdout. An
  audit is not a prerequisite for every edit.

### Proof-development discipline

- Work on one clearly named task from `docs/lean_plan.md` per patch, with
  the prerequisites, proposed theorem, and target build command stated.
- Distinguish canonical project/count/resample oracles, physical perfect-
  local shuffles, and finite-GSR shuffles; they are not pointwise equal.
  Preserve named-card pile membership when shuffling *within* a pile.
- Do not replace an explicit theorem hypothesis (especially
  `HasCommanderFiberCounts` or `hMembershipExchange`) by an invented axiom,
  `sorry`, `admit`, or a weakened theorem statement. Avoid enumerating 99!
  permutations with `native_decide`; prefer structural cardinality proofs.
- Routine proof checks are quiet, targeted `lake build` commands. Do not
  add bulk `#check`/`#print`, axiom inventories, or repeated placeholder
  scans to default builds, CI, or normal reports. Only on explicit request
  at the **end of a formalization** should an axiom audit compare against
  a reviewed baseline, report differences, and capture raw output. Keep
  audit modules opt-in. Avoid globally disabling heartbeat limits.
- Do not hold up substantive Lean progress over non-blocking style-only
  linter suggestions. Use independent Python computations only as tests,
  not evidence that an uncompiled Lean theorem was proved.
- Do not use worktrees for this repo. Preserve the user's working tree;
  do not reset uncommitted work without explicit permission. Stage only
  changed files. If committing, include one `Co-authored-by` trailer for
  the current model, not the historical October session's model name.

## Lean tooling (`submodules/aiq-lean-formalization-tools`)

The shared Lean formalization tooling (`leanq`, `aiq-lean`,
`lake-build-report`, and the `scripts/setup-lake-cache.sh` build-cache
helper) all come from the `submodules/aiq-lean-formalization-tools`
submodule, which is **committed in this repo** (a gitlink; see
`.gitmodules`). You do not need to add it or vendor any copy separately.

**Fresh clone / new agent — run once, in this order.** `git clone` does not
check out the submodule, and the console commands are not on `PATH` until the
editable install is run, so a brand-new checkout needs both lines (the
`pip install -e` alone fails on the empty submodule dir):

```bash
git submodule update --init submodules/aiq-lean-formalization-tools
python -m pip install -e submodules/aiq-lean-formalization-tools
```

That provides three console commands:

- `aiq-lean` — source censuses, clause-by-clause semantic reviews, coverage
  inventories, Python-only source audits (`aiq-lean source scan --root .`),
  import/namespace policies, and HTML reports. The Python-only subcommands
  need no Lean toolchain.
- `leanq` — queries the *elaborated* Lean environment: declaration kinds,
  axiom closure, forward/reverse dependencies, and the project semantic
  graph. Requires a built `.lake` (`lake build` first).
- `lake-build-report` — Lake build diagnostics.

Use the evidence layer that matches the question: structural questions
about sources go to `aiq-lean source`; questions that depend on
elaboration go to `leanq` or a compiler probe. When a census or review
ledger tracks a declaration, edit the ledger by hand in the same commit as
any rename or move of that declaration.

To update the tools: `git submodule update --remote
submodules/aiq-lean-formalization-tools`, commit the new pin, and reinstall
with the `pip install -e` line above.

## Build cache on guest VMs (virtiofs)

When this repo is a virtiofs share (AIVM guest VMs), put `.lake` on VM-local
ext4 with `submodules/aiq-lean-formalization-tools/scripts/setup-lake-cache.sh`
(caches under `/var/cache/lake`); the mount does not survive a reboot, so
re-apply with its `--all`.

Use a **bind mount, not a symlink**: a symlink would be a real file in the
shared tree, so the host would see it too and it would dangle there,
breaking host-side `lake build`, editors, and tooling. A bind mount changes
nothing on disk — the host's own `.lake` stays underneath, untouched and
still usable by the host. Only this VM sees the substitution.

Consequence worth knowing: the two caches are then independent. Builds run
in the VM do not warm the host's cache, and vice versa. That is the price
of letting both sides build at once without fighting over the same oleans.

- `setup-lake-cache.sh` (no args) sets up the cache for the repo at `$PWD`;
  `--status` reports without changing anything; `--unmount` restores the
  host's `.lake`; `--all` re-applies every recorded cache after a reboot.
- If `.lake` already holds a build, seed the derived cache directory first
  (`sudo cp -a .lake /var/cache/lake/<repo>/.lake`) so the VM's first build
  is incremental instead of a cold rebuild.
- On a checkout already on local disk (ext4/xfs/btrfs/...), the script
  refuses to mount — a cache there buys nothing.

The script header documents the full rationale, flags, and owner-marker
behavior; read it before improvising around it.

<!-- BEGIN llm_resource_tally v0.3.0 (managed block — regenerated by `install`; edits below will be overwritten) -->
## LLM resource accounting
A git post-commit hook — and Claude Code hooks when wired — records the measured token and model
usage this repository costs. It is automatic bookkeeping and is not part of whatever task you were
given.

- Rows and mutable rollups are written under `.llm_resource_tally/local/`, which is gitignored.
  Recording therefore never modifies a tracked file and never blocks a commit, merge, rebase, or
  stash.
- Never hand-edit, hand-count, revert, or clean up ledger rows, and never let accounting block the
  repository work you were asked to do. Recording is best-effort by design.
- Treat totals as coverage of observed, allocated work rather than proof of complete history.
  Cross-repo/submodule duplicate guards are local to this user and machine, and
  `python3 .llm_resource_tally/tool doctor` can identify common gaps but cannot prove historical
  completeness.
- **Publish before you hand off substantial work.** Run
  `python3 .llm_resource_tally/tool publish`: it snapshots local rows onto the append-only ledger
  at `.llm_resource_tally/ledger/` and refreshes lifetime totals at
  `.llm_resource_tally/lifetime-totals.json`. Stage and commit what it writes in whichever
  repository owns those paths, preferably as its own commit so accounting stays out of unrelated
  diffs. This is routine — nobody should have to remember to ask you for it, and unpublished rows
  exist only on this machine.
- If accounting itself looks unhealthy, run `python3 .llm_resource_tally/tool doctor` — it checks
  hook wiring, backends, transcript retention, and ledger health, and names what to fix. Otherwise
  continue the repository task normally.
- After a fresh clone, run `python3 .llm_resource_tally/tool install` once to arm git-local hooks.
  It is offline and idempotent, and it reads the committed `.llm_resource_tally/settings.json`
  policy.
<!-- END llm_resource_tally -->
