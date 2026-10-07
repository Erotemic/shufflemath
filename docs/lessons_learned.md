# Lessons learned

Concise, generalizable lessons from the autonomous Lean sessions in this
repo. Only entries that took more than one step to discover belong here.
Lean-mechanics items that are project-local (specific theorems) go in
`docs/autonomous_lean_build.md` §5 instead.

## Workflow

- **Do not deliberate long in one step.** Make the best-guess edit, run
  `lake build`, and let the error messages refine the next move. The
  previous "hyperqwen-huge" session stalled by over-analyzing tactics in
  the abstract; the same file went green in a day-sized session using
  small empirical iterations (one edit → build → read error → repeat).
- **Probe goals by `show 1 = 1`.** When a tactic's error says "expected
  type could not be determined," temporarily replace the tactic with
  `show 1 = 1` (and comment out the following bullets): the resulting
  type-mismatch error prints the actual goal, which usually reveals the
  real structure (And nesting, missing conjuncts, let-expr shapes).

## Lean 4 / mathlib mechanics

- **`omega` (Lean core) takes no `[hypothesis]` list.** Only bare `omega`
  (local context). Passing `[h1, h2]` is a parse error.
- **`omega` cannot do nested Nat-subtraction algebra.** Identities like
  `m - x - (k - a) + (k - (y - (x - a))) = m - y` are not linear in its
  relaxation. Break them into small rearrangement equalities that omega
  *can* prove (`(k-a)+x = k+(x-a)`, `k-(y-(x-a)) = k+(x-a)-y`, the final
  `m-(w+k)+(k+w)-y = m-y`), each under the one inequality it needs, then
  `rw` the chain: `Nat.sub_sub`, `Nat.le_sub_iff_add_le`,
  `Nat.sub_add_cancel`, `Nat.add_sub_assoc`, then one `omega`.
- **Finset membership is not a boolean/Prop structure.** `z ∈ s` reduces
  through the underlying `Multiset`, so `constructor`, `rcases`, `.1`/`.2`
  on membership goals silently do the wrong thing or fail, and
  `simp only [Finset.mem_union, Finset.mem_sdiff] at h` can fail with
  "made no progress" in let-expr tuple contexts even when the same idiom
  works in a plain variable context. Use the explicit iff directions:
  `Finset.mem_union.mp/.mpr`, `Finset.mem_sdiff.mp/.mpr`. They are just
  functions and always work.
- **`ext` on a nested-product equality recurses to the bottom** (through
  every projection, and into `Finset`), so the bullet goals land at the
  deepest level with an unnamed fresh variable — not the per-component
  goals you expected. For tuple/involution equalities, prefer
  per-component `have`s + `change` to the clean form + `Prod.ext`
  assembly, and `ext z` only on bare `Finset` equalities.
- **`rw` is surface-matching.** If the goal has been `dsimp`ed to raw
  projections but your lemma/hypothesis is written with `def` names
  (or vice versa), the rewrite silently does not fire. `change` the goal
  to the same def-level shape on both sides before `rw`ing.
- **Anonymous constructors and holes: `refine F (g ?_)` fails with
  "Invalid ⟨⟩ / expected type could not be determined"** because the
  `⟨...⟩` is elaborated before the hole's type is fixed. Use `apply`
  chains (each `apply` fixes a concrete goal) or a single `exact` whose
  outer type threads through.
- **`simp` on a `Finset.prod` (`×ˢ`) membership chain can stop one level
  short** (observed on let-expr tuples), and the `And` the peel produces
  is *left*-nested while the anonymous `⟨a1, …, an⟩` matches a *right*-
  nested `And` — so "Invalid ⟨⟩" on a 7-conjunct goal. Rebuild the
  membership explicitly: one `Finset.mem_product.mpr ⟨inner, leaf⟩` per
  product level, holes in leaf order.
- **`And`-chain projections mirror the nesting:** a right-nested
  `p1 ∧ p2 ∧ … ∧ p7` splits off the *last* leaf at each level
  (`h.1.1.1.1.1.1`, `h.1.1.1.1.1.2`, …) — the same shape as the tuple
  it came from.
- **`rcases` cannot eliminate `s ∈ u.powerset`** (dependent elimination
  fails inside `Multiset.powersetAux`). First `simp only [Finset.mem_powerset]`
  to get `s ⊆ u`, then project.

## Mathematics

- **An abstract fiber predicate can be looser than the physical model.**
  The 12 conditions of `fiber7Pred` stay consistent with `x > p.m` (the
  left-pile capacity), and there the exchange involution's image leaves
  the `(y, x)` fiber. When a symmetry/bijection theorem fails, look for
  the missing *physical* constraint (here `x ≤ p.m`, i.e. state
  realizability) as an extra hypothesis before suspecting the
  construction. Verify suspected counterexamples with concrete numbers
  against every condition before touching the definitions.
