module

public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# F5 within-pile orbit — progress and next step

**Landed in `Shufflemath/FiniteDeck/WithinPileOrbit.lean` this session:**
- `sumCongr_pairInjective` — `Equiv.sumCongr` determines both within-pile
  permutations (read off on `inl` / `inr`).
- `embed_m_pairInjective` — `embed_m` is injective in the within-pile pair: the
  arbitrary-`(N, m)` generalization of the 99-card `pileRelabelEquiv_pairInjective`
  (cancel the fixed `finSplit` / `finSplit.symm` sandwich around `Equiv.sumCongr`).
- `memLeftPositions_iff` — `x ∈ leftPositions ↔ ∃ i, x = leftPosition i`.
- `embed_m_imageLeft` — `embed_m` maps the left-pile positions onto themselves.

**NEXT (this file is the forward WIP, a build-gate placeholder):**
1. `embed_m_imageRight` — the right-pile mirror. `rightPositions` is
   `univ \ leftPositions`, so use the **bijection-complement** argument: a
   bijection maps a set's complement onto the complement, i.e.
   `(univ \ leftPositions).image (embed_m) = univ \ (leftPositions.image (embed_m))
   = univ \ leftPositions = rightPositions`. (Use the injective
   image-over-set-difference fact, or a direct `Finset.ext` with `Equiv`
   injectivity/surjectivity + `embed_m_imageLeft`.)
2. **The fiber orbit theorem** (the §2 goal of
   `docs/planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md`):
   `H_m ≃ {e : Deck N // membership N m hm e = membership N m hm d}` where
   `H_m = (Fin m ≃ Fin (N - m)) × (Fin m ≃ Fin (N - m))` and the orbit map is
   `act_d (pl, pr) = (embed_m N m hm pl pr).trans d`.
   - Membership-preservation of `act_d`: `embed_m_imageLeft` (+ `imageRight`)
     show `leftCards (act_d ·) = leftCards d`.
   - Injectivity: `embed_m_pairInjective` + cancel the trailing `.trans d`.
   - Surjectivity onto the fiber: for `e` with `membership e = membership d`,
     set `h := e.trans d.symm` (preserves the piles), then reconstruct
     `(pl, pr)` from `h` (it is `embed_m (pl, pr)` for unique `(pl, pr)`);
     finally `e = (embed_m (pl, pr)).trans d = act_d (pl, pr)`.
-/

-- Build-gate placeholder for the next increment; the landed lemmas live in
-- `WithinPileOrbit.lean`.
example : True := by trivial
