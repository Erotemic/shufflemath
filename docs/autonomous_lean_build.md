# Archived autonomous Lean session (October 4-12, 2026)

**ARCHIVED; not an active handoff or current task list.** The fixed October
12 deadline and autonomous-session instructions in the original version of
this file have expired. In particular, there is no active instruction to
work until that deadline, run `lake update` before every build, use a
historical model-specific commit trailer, or restart from the old GSR
"next action". New agents must use:

1. [AGENTS.md](../AGENTS.md) for repository conventions;
2. [docs/agent_handoff.md](agent_handoff.md) for the exact current first
   action and verification state;
3. [docs/lean_plan.md](lean_plan.md) for the active theorem dependencies.

The historical autonomous work is recorded in
[lean_build_history.md](lean_build_history.md); its general-purpose Lean
mechanics are summarized in [lessons_learned.md](lessons_learned.md).
The older design audit remains available in
[formalization_dependency_audit.md](formalization_dependency_audit.md).

## What that session accomplished

It established the exact finite `StdSimplex Rat` probability model and
kernel/matrix authority; TV contraction, weighted perturbation, Dobrushin
bounds, stationarity and reversibility; general Bernoulli--Laplace row
normalization, hypergeometric stationary law, detailed balance, and the
first centered eigenfunction; a Commander specialization and exact
rational 2-/3-exchange certificates. Subsequent work built the GSR,
permutation, fiber-lifting, and disintegration layers. See the active
roadmap for their current status.

## Stable numerical regression references

- Commander split: 50 left positions, 49 right positions, 50 marked cards.
- Canonical exchange size: 25 cards from each side.
- Exact TV after two ideal exchanges:
  `12255318415559330995522631403472464258192877 / 4933350368865509640837610315994582805439728012`.
- Exact TV after three ideal exchanges:
  `172379525755689183991816396516567920780192827919620440221147749 / 6691837923759692633601708022649918108038775216019298375918637677488`.

Those exact macrostate certificates are already represented in Lean. They
must not be interpreted as unconditional TV guarantees for two human
shuffles of a 99-card deck.
