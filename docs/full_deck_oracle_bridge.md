# From 50 Bernoulli–Laplace states to 99-card permutations

The next formalization step represents the complete deck as a permutation of
99 distinct card identities. The existing 50-state Bernoulli–Laplace chain is
a projection: count how many of the original left-pile 50 cards currently
occupy the first 50 positions. Count 1 is state 0; count 50 is state 49.

## Three different kernels

The choice of kernel matters. They are not interchangeable on an arbitrary
ordered deck.

**Canonical abstract oracle** `OracleRefinement.oracleStep`: project a deck
to its macrostate, sample the next macrostate from the exchange kernel,
then uniformly resample a full deck conditional on that macrostate. It is an
exact stochastic kernel. Once the conditional-law kernel is proved to recover
the projection, the generic `oracle_intertwining`, `schedule_intertwining`,
and `run_tv_eq_macro` theorems are unconditional consequences of the kernel
algebra. These theorems are now authored in Lean.

**Physical exchange followed by perfect local pile shuffles**: choose `k`
positions uniformly without replacement from each pile, swap the selected
positions in sorted-order pairs, then independently uniformly permute all
cards within each pile. The exact rational reference implementation is
`experiments/full_deck_oracle.py`. This kernel is *not* equal pointwise to
the canonical oracle on an arbitrary ordered input: the 5-card example
`(0,1,3,2,4)` has TV **13/36** between the two one-step output laws.
However, after a **uniform distribution over all decks in one macrostate
fiber** the two outputs do agree in exhaustive tests through six cards.
This is an intertwining statement, not pointwise kernel equality.

**Finite-GSR physical pile shuffles**: replace perfect local shuffling with
actual `a`-label inverse GSR shuffles. The Python reference implements that
exact independent-label kernel. Its row-wise discrepancy should be bounded
against **physical perfect-local shuffles**, not against the canonical oracle
on an arbitrary ordered input. The small-deck tests verify

\[
  \Delta(\mathrm{physicalGSR}_a,\mathrm{physicalPerfect})
  \leq \mathrm{TV}(\mathrm{GSR}_a^m,U_m)
       +\mathrm{TV}(\mathrm{GSR}_a^{N-m},U_{N-m}).
\]

The new `PhysicalRefinement.finite_local_uniform_bound` formalizes the
correct next-level composition: physical-perfect/macro intertwining plus the
weighted telescope comparing physical-GSR to physical-perfect. The general
Lean one-step discrepancy bound is still outstanding.

## The permutation fiber count

For `N` labelled cards, `m` left positions, and `r` marked cards, the
macrostate fiber containing `x` marked cards on the left has size

\[
|F_x| = {r\choose x}{N-r\choose m-x}\,m!\,(N-m)!.
\]

The two binomial factors choose *which* marked/unmarked cards are in the
left pile; the two factorial factors order the resulting left and right piles.
Consequently

\[
\frac{|F_x|}{N!}=
  \frac{{r\choose x}{N-r\choose m-x}}{{N\choose m}}.
\]

For Commander, `N=99`, `m=r=50`, and `x=1,...,50`.
`experiments/full_deck_oracle.py` verifies the 99-card exact integer
identity `sum_x |F_x|=99!` and every fiber/marginal rational equality.
The required Lean cardinality/disintegration proof is not supplied by a
Python integer check.

## Why the original exact rational certificates still matter

The new Lean source proves `lift ; project = identity` from the explicit
surjectivity of `project`, using `StdSimplex.map_const`. Once the two
remaining obligations

1. every Commander macrostate has a concrete 99-card permutation fiber
   (`Function.Surjective project`), and
2. `commanderStationary ; lift = uniform(Equiv.Perm (Fin 99))`,

have Lean proofs, the `CommanderPermutation.two_oracle_exchanges_uniform`
theorem specializes the old *exact* 50-state two-step distance to TV against
uniform on **all 99! deck permutations**. The exact three-step theorem is
similarly available in `OracleRefinement`.

The original exact rational values, independently reproduced by the new
full-deck Python specification, are:

- Two ideal quarter-deck exchanges:
  `12255318415559330995522631403472464258192877 /`
  `4933350368865509640837610315994582805439728012`.
- Three such exchanges:
  `172379525755689183991816396516567920780192827919620440221147749 /`
  `6691837923759692633601708022649918108038775216019298375918637677488`.

These results are **ideal oracle** statements. They are not a claim that two
actual imperfect physical shuffles mix the deck to those TV distances.

## Verification

After applying the overlay:

```bash
cd ~/code/shufflemath
lake exe cache get
lake build Shufflemath.OracleRefinement Shufflemath.PhysicalRefinement Shufflemath.CommanderPermutation
python3 -m unittest tests.test_full_deck_oracle -v
```

The pinned Lean toolchain is v4.34.0. The `CommanderPermutation` target is
kept out of the default root `Shufflemath.lean` imports because its finite
type of 99! permutations can make elaboration and evaluation expensive. It
is nevertheless compiled by the targeted verification script. Local
compilation is the validation criterion for the new Lean sources. Do not infer failure of older modules
from inability to execute Lean in the packaging environment.

## The next mathematically hard part

A full physical-error certificate needs all of the following independently:

1. Prove fiber-surjectivity (all 50 Commander counts are realized by 99-card
   permutations).
2. The recovery proof is included, conditional on surjectivity. Prove the
   hypergeometric mixture is uniform on full permutations.
3. Prove that the position-exchange plus *perfect local pile shuffles*
   intertwines with the macro kernel for fiber-uniform input laws. A
   bijection of exchange configurations, or the independent action of the
   marked/unmarked relabelling groups, is a promising non-enumerative proof.
4. Prove a finite-GSR local-shuffle discrepancy against the
   physical-perfect kernel, and use the new
   `PhysicalRefinement.finite_local_uniform_bound` with the existing
   weighted telescope. This supports quantitative 99-card TV/cost
   tradeoffs without pretending the physical and canonical oracle kernels
   coincide pointwise.

The executable 4–6-card check is a regression test for item (3), not its
proof for arbitrary decks.
