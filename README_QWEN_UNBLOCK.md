# Qwen unblock overlay — November 12, 2026

This additive overlay was prepared against snapshot `c935088`. It deliberately
does not overwrite Qwen's active `Shufflemath/` sources, `AGENTS.md`, or
handoff/roadmap files.

Read `docs/qwen_unblock_nov12.md` first. The new development modules under
`dev/` are isolated **Lean proof candidates**, not Lean-verified production
code. Build them independently and merge successful results. The new test
under `tests/` uses exact arithmetic and does not enumerate 99! decks.

```bash
python3 -m unittest discover -s tests -v
lake env lean dev/QwenGSRBridge.lean
lake env lean dev/QwenLocalPermutation.lean
```

The existing build graph remains unchanged. See the main guide for the
subsequent production integration and F3 proof route.
