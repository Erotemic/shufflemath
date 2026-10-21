# October 20 formalization tranche (historical design notes)

**Historical record, not the current next-step list.** The source tranche
started at `55277f4` on October 20, 2026. Its Lean modules have since been
iterated on and the following full-deck tranche introduced additional
modules. For current verification and priorities see
[lean_plan.md](lean_plan.md) and [agent_handoff.md](agent_handoff.md).

## Results carried forward

| Module | Reusable contribution | Not yet supplied by that contribution |
|---|---|---|
| `BernoulliLaplaceSemantic.lean` | Exact array-to-semantic 50-state TV bridge | No full permutation mixing theorem on its own |
| `GSR.lean` | Stable inverse-label buckets; composition by product labels | Numeric `Fin (a*b)` uniform-law identification; physical 49/50-card error bounds |
| `FiberLifting.lean` | TV equality for a recoverable common fiber law | No claim that an arbitrary microstate kernel intertwines |
| `ProtocolCertificate.lean` | Generic terminal TV via reference-plus-weighted-error; costed protocol interface | No 99-card physical kernel or cost optimum by itself |
| `OracleRefinement.lean` | Canonical project/BL-transition/resample oracle and schedule intertwining | Not equal pointwise to a physical exchange |
| `PhysicalRefinement.lean` | Weighted telescope against a physical perfect-local reference | Requires perfect-local macro intertwining and concrete finite-GSR row bound |
| `CommanderPermutation.lean` | `Deck := Equiv.Perm (Fin 99)` and left-pile macro projection | Fiber cardinalities, physical exchange identity |

The October 21 follow-on added `CommanderFiberWitness.lean`,
`FiberDisintegration.lean`, `PhysicalExchangeReduction.lean`, and
`CommanderFullDeckDisintegration.lean`; their mathematics and remaining
premises are in [commander_fiber_disintegration.md](commander_fiber_disintegration.md).

## Two important quantitative results

The original `BernoulliLaplace.lean` gives exact TV after two and three
25-card exchanges. The separate `dev/BernoulliLaplacePairOptimality.lean`
expresses the complete `(k1,k2)` search over 49 squared choices as an
opt-in `native_decide` proof about a single second-step row. The Python
reference independently found the unique macrostate minimizer `(25,25)`.
No successful local `--pair` build was reported in the conversation; do
not silently count that optional Lean theorem as discharged. Its
variable-`k` semantic correspondence is a distinct follow-up.

For `GSR.idealShuffle`, independently chosen label assignments in successive
rounds compose into a lexicographically ordered product alphabet (later
round is the major key). The Lean composition result covers arbitrary
label laws; the desired numeric `Fin (a*b)` uniform-label theorem still
requires a bijection and a proof that the pushed-forward law is uniform.

## Why oracle and physical models must remain separate

The *canonical* full-deck oracle discards named-card membership information
within a given count fiber. A physical shuffle confined to ordering the
left and right piles does **not** change their membership. The correct
physical comparison is finite-GSR versus **physical perfect-local**
shuffling after the same raw exchange, not versus a canonical oracle at
every ordered deck input. Exact small-deck reference calculations exhibit
a five-card pointwise counterexample to that equality.

The generic physical error bound becomes an actual 99-card protocol bound
only after proving the named-membership exchange law and the finite-GSR
row discrepancy; see active tasks F2-F4 in [lean_plan.md](lean_plan.md).

## Verification entry points

```bash
cd ~/code/shufflemath
lake exe cache get
./dev/verify_next_phase.sh
python3 -m unittest discover -s tests -v
```

The regular targeted script checks new Lean modules; the optional exact
pair certificate is checked separately with `--pair`. Previous local
builds verified the earlier tranche. The latest October 21 disintegration
v3 build was not yet confirmed when this note was updated.
