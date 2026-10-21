# Shufflemath: next formalization tranche

Source baseline: `55277f4`, October 20, 2026. This document distinguishes
existing verified Lean results, newly authored source, exact Python
calculations, and still-unproved mathematical hypotheses. New Lean declarations
are not called verified until the pinned `lake build` completes.

## Architecture and deliverables

| File | Purpose | Verification route |
|---|---|---|
| `Shufflemath/BernoulliLaplaceSemantic.lean` | Semantic `Dist`/`FiniteKernel.run` equality for materialized 50-state evolution; transports existing exact 2- and 3-exchange certificates | `lake build Shufflemath.BernoulliLaplaceSemantic` |
| `Shufflemath/GSR.lean` | Actual stable inverse-label shuffle on lists of named cards; uniform label distributions using `StdSimplex`; product-label composition for arbitrary round laws | `lake build Shufflemath.GSR` |
| `Shufflemath/FiberLifting.lean` | TV-isometry for recoverable microstate refinements; full/macro kernel intertwining and its `run` consequence | `lake build Shufflemath.FiberLifting` |
| `Shufflemath/ProtocolCertificate.lean` | Terminal-TV certificate combining ideal TV and weighted telescope; costed schedule kernel semantics | `lake build Shufflemath.ProtocolCertificate` |
| `dev/BernoulliLaplacePairOptimality.lean` | Opt-in 2,401-candidate `native_decide` proof of exact minimum for two-exchange single-row objective | `lake build Shufflemath.BernoulliLaplace && lake env lean dev/BernoulliLaplacePairOptimality.lean` |
| `experiments/commander_pair_search.py` | Independent complete rational enumeration with exported winner JSON | `python3 -m unittest discover -s tests -v` |
| `experiments/gsr_inverse.py` | Exhaustive small-deck stochastic GSR reference | Same Python test run |
| `experiments/oracle_gsr_budget.py` | Conservative candidate 99-card protocol bound and riffle-cost search | Same Python test run |

**Compilation state of this tranche:** New Lean sources need a machine with the
pinned Lean 4.34.0 and Mathlib cache for verification. The packaging environment
has no Lean toolchain and no access to the GitHub release assets. Python's exact
calculations and tests are executable here; they do **not** prove a Lean
statement. The older Lean proofs are not downgraded by this limitation.

## 1. Bernoulli--Laplace exact rational certificates

Existing source `Shufflemath/BernoulliLaplace.lean` contains `native_decide`
certificates for 2 and 3 quarter-deck exchanges. The bridge is intentionally
added in a new file rather than rewriting the frozen numerical development.

- `arrayGet_ofFn` and `tableGet_eq_matrix` connect eager arrays to the
  original mathematical matrix.
- `stepCommanderArray_eq_apply` and `runCommanderArray_eq_run` prove the exact
  same transition/repetition semantics for arrays and `FiniteKernel.run`.
- `commander_run25_tv_semantic` transfers total variation at **any** round
  count, and concrete corollaries use the existing two exact certificates.

An exact Python search independently confirms the unique two-exchange
macrostate-TV minimizer `(25,25)` over all 49² ordered pairs. The key
observation reduces the entire two-step computation to **one** transition
row: from complete segregation, exchanging `k1` cards forces `x = 50-k1`
with probability 1. This reduces the search to 2,401 rows, each of length 50.
`docs/commander_pair_certificate.json` records the winner, unique-tie test,
and closest competitor. The opt-in Lean file (outside the default library source directory) expresses the same finite
row-wise inequality using `native_decide`. It does not yet prove the
semantic *variable-k* kernel correspondence; that is an explicit next target.

## 2. GSR finite-label composition

`GSR.stableBuckets` consumes a list of named cards and an assignment
`Fin n → Fin a` of labels to card identities. It concatenates buckets in
increasing label order, retaining the input order inside each bucket.
`GSR.idealShuffle` pushes uniform `a`-ary label assignments through this
sorting function. Thus it is a distribution-valued kernel, not a random
oracle pseudocode sketch.

The two-round composition theorem has **arbitrary** label-source distributions:

```
labelShuffle a p ; labelShuffle b q
  = productLabelShuffle a b p q
```

where the combined sort key is `(later_major, earlier_minor)`. The combined
alphabet has size `b*a`. On uniform assignments this is the operational
product-alphabet form of inverse-GSR composition. Exact identification with
the numeric `Fin (a*b)` uniform-label kernel, including label-assignment
uniformity under the chosen bijection, is a remaining Lean milestone.

The Python reference independently checks the stable sort and both
composition laws exhaustively for small decks; it also checks the
Bayer--Diaconis formula permutation-by-permutation. The reference works
on the *inverse-shuffle output* convention; counting descents of the
forward permutation is a different operation.

## 3. Fiber lifting: the necessary missing hypothesis

Macrostate mixing is **not** automatically full-deck mixing. If `L` lifts
macrostate `x` to a fixed conditional law on the microscopic fiber and `R`
recovers `x`, then `L ; R = identity` implies

```
TV(p L, q L) = TV(p, q).
```

No equal-fiber-size hypothesis is needed. In particular, this applies to
hypergeometric fibers of *different* cardinalities. The equality holds
for any common conditional fiber law, not just uniform fiber laws.

To turn it into the operational 99-card certificate, two more independent
proof obligations remain:

1. Construct the full 99-card *permutation-valued* oracle local-randomizer
   and its conditional fiber lift `L`, and prove that `L` maps the
   hypergeometric stationary law to the uniform distribution on all 99!
   card permutations. Uniformity **within** fibers must be proved, not
   assumed from projection alone.
2. Prove the kernel intertwining `L ; K_full = K_macro ; L` for the
   specified exchange/local-oracle action. This is the condition needed
   to lift the macro process over **multiple** steps. `run_intertwining`
   and `run_tv_eq_macro` prove the generic consequences once that condition
   is supplied.

It would be incorrect to claim a 99-card full-deck TV bound before those
hypotheses are established. This tranche makes the exact interface clear.

## 4. Protocol certificates and cost

`ProtocolCertificate.terminalTV_le_reference_add_budget` combines the
existing *proved* weighted telescope bound with the triangle inequality to
bound a concrete target error:

```
TV(actual_final, target)
  <= weighted_error(actual_schedule, ideal_schedule)
     + TV(ideal_final, target).
```

No assumption about uniformity is inserted. `kernelOfCosted` uses the
existing `CostedKernel.step` field and `compList`; additive costs continue
to come from `CostedKernel.protocolCost`.

`experiments/oracle_gsr_budget.py` searches three ideal local-riffle phases
surrounding two quarter-deck exchanges, with the conservative candidate
bound

```
TV_macro(25,25) + sum_i [GSR_TV(49,r_i) + GSR_TV(50,r_i)].
```

The Python optimizer is a **planning computation**, not a 99-card full-deck
Lean certificate. The error inequality must still be proved for the actual
finite local kernels and combined with the full-deck oracle theorem.

## Build commands

```bash
cd ~/code/shufflemath
lake exe cache get
lake build \
  Shufflemath.FiberLifting \
  Shufflemath.BernoulliLaplaceSemantic \
  Shufflemath.GSR \
  Shufflemath.ProtocolCertificate
python3 -m unittest discover -s tests -v
```

Or `./dev/verify_next_phase.sh`. For the opt-in 2,401-pair proof use
`./dev/verify_next_phase.sh --pair`; it is isolated from the normal
module imports because compiling a large exact numeric decision procedure
can be more expensive than the ordinary development.

## Most valuable subsequent proof tasks

1. Verify/refine the new Lean code against the pinned Mathlib toolchain.
2. Prove the numeric `(a*b)` uniform-label identification (not just the
   lexicographic product-label result).
3. Lift GSR from list states to valid finite permutations with a proved
   permutation-preservation theorem; expose a finite-permutation kernel.
4. Construct full-deck uniform fiber laws, prove exchange intertwining,
   and connect the uniform 99-card target to macro hypergeometric law.
5. Establish one-step kernel-discrepancy bounds for local GSR versus local
   oracle; discharge the actual schedule costs and output a Lean-checked
   end-to-end 99-card error/cost certificate.
6. Attach a true Lean optimality statement to the two-exchange semantics;
   later optimize under local riffle and physical time costs, not only
   macrostate ideal-exchange TV.

Future exploration: biased/nonexchangeable label sources, robust protocols,
and higher Bernoulli--Laplace spectrum. None blocks the first full-deck
certificate above.

## October 21: full-deck oracle and physical-exchange reference

The subsequent overlay adds `OracleRefinement.lean`,
`PhysicalRefinement.lean`, and `CommanderPermutation.lean`. It is a deliberate decomposition into distinct
mathematical models:

1. **Exact canonical oracle model in Lean.** Project, take a BL macro step,
   and resample a microstate from the resulting conditional fiber. Given a
   recoverable lift, its intertwining identity is now proved *by construction*,
   for individual steps and arbitrarily heterogeneous finite schedules.
   It inherits the original exact two- and three-exchange rational TV values.
2. **Concrete 99-card microstate space in Lean.** `CommanderPermutation.Deck`
   is `Equiv.Perm (Fin 99)`. The first 50 positions form the left pile;
   the macro count tracks cards originally in the left pile. The file proves
   the projection lands in the exact existing `Fin 50` Commander state space:
   one marked card must remain on the left because only 49 unmarked cards
   exist. `Fiber x` consists of full permutations with that count. The
   conditional `uniformFiber` uses the original exact `StdSimplex` authority.
3. **Physical exchange model in exact Python.** Choose `k` positions in each
   pile, swap their paired cards, and then *independently uniformly permute*
   both piles. This is a stronger and more precise model than an unspecified
   physical exchange. Exhaustive full-permutation tests through `N=6` verify
   `lift ; physicalExchangeThenLocalOracle = macroExchange ; lift`. The
   identity is tested at every admissible macrostate, not on one initial
   deck alone.
4. **99-card integer fiber counts.** Without enumerating permutations, exact
   integer arithmetic checks
   `#fiber(x)=C(50,x) C(49,50-x) 50! 49!` and
   `sum_x #fiber(x)=99!`. Hence the macrostate of a uniformly random full
   permutation is the Commander hypergeometric law.
5. **End-to-end error interface.** `PhysicalRefinement.finite_local_uniform_bound`
   attaches the existing *weighted* kernel-telescope error budget to a
   physically implemented perfect-local reference that intertwines with
   the macrostate process. This is the correct comparison for finite GSR:
   an actual exchange-plus-finite-GSR row need not be close to a canonical
   project/macro/resample oracle row. `OracleRefinement` separately supports
   the exact abstract oracle model; neither asserts zero discrepancy.
6. **Exact finite-GSR check.** `experiments/full_deck_oracle.py` now includes
   concrete independent-label GSR laws after exchange, and verifies
   their row-wise TV discrepancy against *physical perfect-pile* shuffles
   obeys the sum of the two local GSR-vs-uniform errors on small decks.
   These are exact rational tests, not the general Lean discrepancy proof.

**Remaining Lean obligations, in order:**

- Prove surjectivity of `CommanderPermutation.project`; each of its 50
  integer-count fibers is inhabited.
- `uniformFiber_recovers` supplies the `lift ; deterministic project =
  identity` proof once fiber-surjectivity is established; verify it in Lean.
- Prove that applying `uniformFiber` to the hypergeometric macro stationary
  law gives `GSR.uniformDist Deck`, via the exact binomial fiber count.
- Define `physicalExchangeThenLocalOracle` as a `FiniteKernel Deck Deck`,
  prove exchange/lift intertwining by counting or symmetry, and compare it
  to the canonical oracle at *all* microstates. The toy exhaustive check
  tests intertwining only after a fiber-uniform start, not equality of
  the two kernels at an arbitrary ordered deck.
- For actual finite GSR operations, prove one-step discrepancies against
  the *physical* perfect-local kernel. `PhysicalRefinement` now provides the
  generic weighted-telescope composition theorem, conditional only on
  physical-perfect/macro intertwining and uniform-stationary identification.
  Combining with finite-GSR local error lemmas gives certified costs.

These are real hypotheses, not implementation details; the new Lean
conditional theorems do **not** yet assert an unconditional 99-card
physical-mixing theorem. Exact Python checks are not a substitute for Lean
proofs. The pinned local Lean build determines acceptance of new sources.
