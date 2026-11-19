module

public import Shufflemath.FinsetCombinatorics
public import Shufflemath.BernoulliLaplace
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderA3Kernel
public import Shufflemath.CommanderA3ExchangePushforward
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFiberCount
public import Shufflemath._Probe47v
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation

-- NOTE: only `BernoulliLaplace` is opened (its 5-arg `transitionNumerator` matches
-- `_Probe47v`); opening `BernoulliLaplaceGeneral` too makes `transitionNumerator`
-- ambiguous and elaborating its 6-arg form recurses.
open CommanderMembershipKernels
open CommanderMembershipExchange
open CommanderPhysicalExchange
open Finset

/-!
## A3-capstone count-bridge **f4** — WIP / recursion-wall characterization (71st session)

This is a **probe**, not part of the library (not in `Shufflemath.lean` nor
`dev/verify_next_phase.sh`).  It documents where the A3 part-(i) count bridge stands.

**State of the A3 part-(i) count bridge** (`rawExchangeMembership_count` → the
fiber-average post-exchange count distribution = the Bernoulli-Laplace transition law):

- f1 `Fintype.card {j // P j} = Finset.card (univ | P)` — **PROVEN** (`_ProbeA3Cap.probe_f1`,
  via `Fintype.card_of_subtype`).
- f2 `= Finset.card (univ | Q)` — **PROVEN** (`_ProbeA3Cap.probe_f2`, predicate congruence).
- f3 `= Finset.card ((univ | Q).image projLR)` — **PROVEN** (`_ProbeA3Cap.probe_f3`,
  `Finset.card_image_of_injOn`).
- f4 `= transitionNumerator 99 50 25 (leftOriginalCount d) c` — **WALLED** (this file).

**The wall (confirmed by direct builds this session, from BOTH candidate targets):**

Both candidate final targets recurse when their membership is decomposed for a
pointwise `Finset.ext`:
  1. `(leftChoices ×ˢ rightChoices).filter (newLeftCards-count = c)` — the `×ˢ`-membership
     `x.1 ∈ leftChoices ∧ x.2 ∈ rightChoices` forces the 2⁵⁰ `powersetCard`-subtype compute.
  2. `(_Probe47v.s50 ×ˢ _Probe47v.t49).filter (markedCount = c)` — the 47v fiber product, whose
     membership *is* the clean `Finset.mem_powersetCard` (`L ⊆ Fin 50 ∧ L.card = 25`).  This side
     is clean on its own, **but** the *image side* of the equality is
     `∃ j : exchangeChoice, j ∈ Fintype.univ.exchangeChoice ∧ …`; the `exchangeChoice` Fintype
     instance is the `×ˢ` of the two `leftChoices`/`rightChoices` **subtypes**, so
     `j ∈ Fintype.univ` has **no simp lemma** and computes the 2⁵⁰ sublists.  (Same wall the
     70th session hit; `_ProbeA3Univ` characterizes it: raw `×ˢ` clean, `Fintype.univ` recurses.)

**Why every bridge recurses:** the count-mass source `exchangeChoice`
(`{L // L ∈ leftChoices} × {R // R ∈ rightChoices}`) is a Fintype **subtype** whose membership
computes the powerset; the clean representation (`s50 = (Finset.univ).powersetCard 25`) is
a *Finset*.  Any `Equiv`/card-bridge between them either (a) recomputes a membership (recurses)
or (b) uses `Fintype.card_equiv` on a subtype `Equiv` whose injectivity/surjectivity subgoal
`a ∈ ↑(…).2` (a Membership-internal / subtype membership) recurses.  The 68th-session
`fintypeCard_subtypeCongr` sidesteps (b) *within a fixed base type* (its `Subtype.ext; rfl`
closes because `P a ↔ Q a` is the *same* base), but here the two sides have **different base
types** (`exchangeChoice` vs `s50 ×ˢ t49`), so it does not apply directly.

**Routes to try next (ranked):**
  1. **Rebase the count-mass source on the powersetCard.**  Define the count predicate over
     `s50 ×ˢ t49` *directly* (never over `exchangeChoice`): `Fintype.card
     (↑(_Probe47v.s50 ×ˢ _Probe47v.t49).filter Q')` = `transitionNumerator` is exactly
     `_Probe47v.transitionNumerator_eq_fiberProduct` (already clean).  Then bridge the
     *Fintype-card over `exchangeChoice`* to the *Fintype-card over `s50 ×ˢ t49`* by a
     **product** `fintypeCard_subtypeCongr`: prove `{j : exchangeChoice // Q j} ≃
     {p : s50 ×ˢ t49 // Q' p}` as subtypes of a **common ambient** `Finset (Fin 50) × Finset (Fin 49)`,
     so the bridge is `∀ a, P a ↔ Q a` on one ambient (clean), reusing `exchangeChoice_equiv_lr`
     + `leftChoices = s50` *at the Finset level only* (never the membership).
  2. **Skip f4 via the generic G4 route:** `docs/planning/proof-strategies/
     2026-11-18-g4-macro-intertwining-plan.md` — `uniformCount_intertwines_subsetExchange`
     (arbitrary N,m,r,k) reduces to `reachSetFiberCard_eq_yMoves` (one self-contained Finset
     bijection, no `native_decide`, no 2⁵⁰ univ) + `detailedBalance`; then specialize to
     (99,50,50,25).  This is the "honest discharger" and does **not** need the concrete f4.
-/

/-- The marked-count-filtered choice space (f1/f3 left-hand Finset). Compiles. -/
def a3UnivFilter (d : Deck) (c : Nat) : Finset exchangeChoice :=
    (Finset.univ : Finset exchangeChoice).filter
      (fun j => (leftOriginalCount d - markedInLeft d j.1.1) + markedInRight d j.2.1 = c)

/-- Its image in the flat `(L, R)` product under the projection. Compiles. -/
def a3Image (d : Deck) (c : Nat) : Finset (Finset (Fin 50) × Finset (Fin 49)) :=
    (a3UnivFilter d c).image (fun j : exchangeChoice => (j.1.1, j.2.1))

/-- The 47v fiber: the `s50 ×ˢ t49` product filtered on the post-exchange left count.
    Clean `powersetCard` membership. Compiles. -/
def a3Fiber (d : Deck) (c : Nat) : Finset (Finset (Fin 50) × Finset (Fin 49)) :=
    (_Probe47v.s50 ×ˢ _Probe47v.t49).filter
      (fun p : Finset (Fin 50) × Finset (Fin 49) =>
        (leftOriginalCount d - markedInLeft d p.1) + markedInRight d p.2 = c)

/-! f4 (WALL).  The image's card equals the 47v fiber's card.  The fiber card is already
    `transitionNumerator` by `_Probe47v.transitionNumerator_eq_fiberProduct` (clean —
    `powersetCard` membership, combinatorial).  The walled step is the image-vs-fiber
    equality `(a3Image d c).card = (a3Fiber d c).card`: a pointwise `Finset.ext` recurses
    (see banner).  `sorry` marks the wall. -/
theorem a3Image_card_eq_fiberCard (d : Deck) (c : Nat) :
    (a3Image d c).card = (a3Fiber d c).card := by
  sorry

end Shufflemath
end
