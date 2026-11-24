# Gate 6 physical-certificate goal — 2026-11-23

This is the **replacement goal text** to submit to `pi-goal-list-loop-audit`. It does not automatically edit the active `.pi-glla` run. That run still references the older November 20 hints as of source snapshot `573d097`.

> Prove the end-to-end Lean certificate that **three physical rounds**—each a uniform 25/25 **position swap followed by 23 inverse-GSR riffles in each of the 50/49 piles**—produce TV distance **< 1/1000 from the uniform 99-card deck for every deterministic starting deck**. Work through `docs/planning/proof-strategies/2026-11-23-swap-local-orbits-and-support-first-proofs.md` and its dated review. Correct the swap/local factor order; use the existing arbitrary-`N` within-pile orbit equivalence to finish the ideal physical-kernel identity (K1); prove the correct-order one-round TV bound, a support-based state-dependent telescope, first-round smoothing, and relabeling transfer. Reuse the already-proved collision estimate, convolution machinery, and exact ideal three-round `q3`. If a `Fin 99` proof requires increasing recursion depth, heartbeats, or unbounded memory, **change the representation or prove an abstract helper instead**. The finish line is a compiled, imported, unconditional physical-shuffle theorem—not an arithmetic inequality, a constant-row kernel, or a conditional telescope.

## Success checklist

- [ ] Every round acts on the **current** deck (no constant-output shuffling kernel), and the order is **swap, then local**.
- [ ] K1 identifies the ideal full round with `exchangeThenLocalReset` on every input deck; no placeholder in the production proof.
- [ ] A theorem bounds every finite-vs-ideal row by `δ1`, using a generic support-based argument.
- [ ] A theorem bounds the three-round finite-vs-ideal discrepancy by `3δ1`.
- [ ] The deterministic initial reference deck is bridged to the **fiber-uniform** premise of the existing `q3` theorem.
- [ ] A finished theorem proves TV `< 1/1000` from each deterministic starting deck, with the concrete physical operations in the statement or in unambiguous definitions.
- [ ] The final theorem is imported and compiled by the routine targeted build. Do not mistake a probe with `sorry` or the old constant-row telescope for acceptance.

The mathematical review documents are **hints and background**; the goal above is authoritative about the physical operation and the desired theorem. After closing it, return to arbitrary finite `N`, multi-pile theory, and eventually protocol cost optimization.
