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
- `bijection_imageCompl` — a bijection preserving a set preserves its complement.
- `embed_m_imageRight` — `embed_m` maps the right-pile positions onto themselves
  (one-line application of `bijection_imageCompl` + `embed_m_imageLeft`).
- `act_d` — the within-pile orbit action on decks: `(embed_m (pl,pr)).trans d`.
- `act_d_preservesMembership` — the orbit action preserves membership
  (image of the left positions is unchanged).
- `act_d_injective` — the orbit action is injective in the within-pile pair
  (cancel `d` from the right of `.trans d`; reduces to `embed_m_pairInjective`).

**NEXT (this file is the forward WIP, a build-gate placeholder):**
- **The fiber orbit theorem** (the §2 goal of
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
