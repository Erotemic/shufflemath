# AGENTS.md

## What this is

`shufflemath` studies constrained physical card shuffling: which finite
sequences of cuts, mashes, and exchanges drive a deck to uniform fastest.
`README.md` has the motivation; `docs/` has the literature, the problem
statement, and the Lean theorem ladder. Three tracks run in parallel:
literature, exact finite computation (`experiments/`), and Lean
formalization (library `Shufflemath`).

## Build and verify

```bash
./dev/verify.sh   # lake update && lake build && python unit tests
```

The toolchain is pinned by `lean-toolchain` (elan); mathlib is pinned in
`lakefile.lean`.

## Lean tooling (`submodules/aiq-lean-formalization-tools`)

The shared Lean formalization tooling lives in the
`submodules/aiq-lean-formalization-tools` submodule. After cloning, install
it once into the active Python environment:

```bash
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
- On a checkout already on local disk (ext4/xfs/btrfs/...), the script
  refuses to mount — a cache there buys nothing.

The script header documents the full rationale, flags, and owner-marker
behavior; read it before improvising around it.
