module

/-
Four-bin overlap count for the membership-exchange fiber (F3 item 3).

For a target membership `T` of size `m` containing `y` of the `r` marked
identities, the number of starting memberships `S` of size `m` with `x`
marked cards and `|S ∩ T| = m - k` is a sum over how many `t` marked cards
of `T` land in `S`; the four marked/unmarked × in/outside-T bins are then
independent `choose` factors. This count equals the *reversed* Bernoulli--
Laplace transition numerator (the content of F3 item 3):

    overlap_count (n m r k) x y  =  transitionNumerator (n m r k) y x

`tests/test_exchange_overlap_identity.py` verifies the identity by exact
integer arithmetic on three small decks and all 2,500 Commander `(x, y)`
pairs.

**Signed `choose`.** The reference `choose(n, k)` returns `0` unless
`0 <= k <= n`.  A naive `Nat.choose (r - y) (x - t)` with `Nat`-saturated
subtraction is wrong when `x - t` is negative: the saturation turns it into
`Nat.choose _ 0 = 1`, inserting spurious terms (e.g. `(n,m,r,k,x,y) =
(99,50,50,25,10,40)`).  We therefore compute the bin sizes in `Int` and use
`chooseSigned`, which reproduces the reference exactly for every `(x, y)`.
-/
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceFiber
public meta import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.BernoulliLaplaceFiber
public meta import Shufflemath.BernoulliLaplaceFiber
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplaceGeneral

/-- Reference binomial coefficient: `0` unless `0 <= k <= n` (mirrors the
Python `choose` in `tests/test_exchange_overlap_identity.py`). -/
def chooseSigned (n k : Int) : Nat :=
  if 0 <= k ∧ k <= n then Nat.choose n.toNat k.toNat else 0

/-- The four-bin overlap count: the number of `m`-subsets `S` of an `n`-set,
with `x` marked cards and `|S ∩ T| = m - k`, where `T` is a fixed `m`-subset
holding `y` of the `r` marked identities.  The sum runs over `t`, the number
of marked cards of `T` that land in `S`; the four bins are
(marked/unmarked) × (inside/outside `T`), giving the four `choose` factors.
Bin sizes are computed in `Int` so that impossible (negative) sizes vanish
exactly as in the reference. -/
def overlap_count (n m r k x y : Nat) : Nat :=
  let nI := (n : Int)
  let mI := (m : Int)
  let rI := (r : Int)
  let kI := (k : Int)
  let xI := (x : Int)
  let yI := (y : Int)
  let plain_outside_target := nI - rI - (mI - yI)
  (Finset.range (m - k + 1)).sum fun (t : Nat) =>
    let tI := (t : Int)
    let plain_overlap := (mI - kI) - tI
    chooseSigned yI tI *
      chooseSigned (rI - yI) (xI - tI) *
      chooseSigned (mI - yI) plain_overlap *
      chooseSigned plain_outside_target ((mI - xI) - plain_overlap)

/-!
## The overlap = reversed-transition-numerator identity

Sub-lemma 3 of the F3 item 3 route (`docs/qwen_unblock_nov12.md` §3): the
four-bin overlap count for a fixed target `T` with macro count `y` equals the
*reversed* Bernoulli--Laplace transition numerator.  Proved here by exact
kernel computation (`native_decide`) on the three small decks from
`tests/test_exchange_overlap_identity.py`; each side is a computable
`Finset.sum` of (signed) `Nat.choose` products, so the equality reduces to a
closed `Bool` the kernel decides.  (The general structural form is the open
part of F3 item 3.)
-/

/- The identity for **every** `(x, y)` in the *valid* macro-state space of the
three small decks.  The valid marked-count range for a deck `(N m r)` is
`Icc (max (r - (N - m)) 0) (min m r)` (the codebase's `stateFinset`); Lean's
`transitionNumerator` uses `Nat`-saturated subtraction and matches the
reference numerator only on valid states, so we quantify exactly over that
finite range using an explicit `Fin` (with an offset where the range does not
start at `0`).  Each side is a computable sum, so the whole finite statement
is decided by the kernel.  These are genuine theorems (quantified over the
valid state space), not spot checks. -/

/-- `(6,3,2,1)`: valid marked counts `x, y ∈ {0,1,2}`. -/
theorem overlap_eq_revTransitionNumerator_valid_6321 :
    ∀ (x y : Fin 3),
      overlap_count 6 3 2 1 x.val y.val = transitionNumerator 6 3 2 1 y.val x.val := by
  native_decide

/-- `(7,4,4,2)`: valid marked counts `x, y ∈ {1,2,3,4}` (offset by `1`). -/
theorem overlap_eq_revTransitionNumerator_valid_7442 :
    ∀ (x y : Fin 4),
      overlap_count 7 4 4 2 (1 + x.val) (1 + y.val) =
        transitionNumerator 7 4 4 2 (1 + y.val) (1 + x.val) := by
  native_decide

/-- `(8,4,3,1)`: valid marked counts `x, y ∈ {0,1,2,3}`. -/
theorem overlap_eq_revTransitionNumerator_valid_8431 :
    ∀ (x y : Fin 4),
      overlap_count 8 4 3 1 x.val y.val = transitionNumerator 8 4 3 1 y.val x.val := by
  native_decide

/-- Commander instance `(99,50,50,25)`, `x=25, y=25` (the symmetric center). -/
theorem overlap_eq_revTransitionNumerator_cmdr_2525 :
    overlap_count 99 50 50 25 25 25 = transitionNumerator 99 50 50 25 25 25 := by
  native_decide

/-- Commander instance `(99,50,50,25)`, `x=25, y=1` (asymmetric, marked-heavy
target). -/
theorem overlap_eq_revTransitionNumerator_cmdr_251 :
    overlap_count 99 50 50 25 25 1 = transitionNumerator 99 50 50 25 1 25 := by
  native_decide

/-- Commander instance `(99,50,50,25)`, `x=10, y=40`: the case where the
`Nat`-saturated version inserts spurious `t > x` terms.  The signed version
matches the reference. -/
theorem overlap_eq_revTransitionNumerator_cmdr_1040 :
    overlap_count 99 50 50 25 10 40 = transitionNumerator 99 50 50 25 40 10 := by
  native_decide

/-!
## The fiber-counting lemma (F3 item 3, 4th-session reduction)

The general identity
`overlap_count (n m r k) x y = transitionNumerator (n m r k) y x`
reduces to a single new counting lemma plus two already-proved facts:

- **(CL) the fiber-counting lemma:**
  `fiberSum p x y = choose(r, y) * choose(N - r, m - y) *
     overlap_count (N m r k) x y`,
  where `choose(r, y) * choose(N - r, m - y)` is the number of `m`-subsets
  carrying `y` marked cards (the stationary-weight numerator).  Combinatorially,
  `fiberSum p x y` counts the triples `(S, A, B)` with `|S| = m`, `x` marked in
  `S`, `|A| = k ⊆ S`, `|B| = k ⊆ Sᶜ`, and `(S\A) ∪ B` carrying `y` marked; the
  target `T = (S\A) ∪ B` satisfies `|S ∩ T| = m - k` and is recovered uniquely
  from `(S, A, B)`, so this is the double count of `(S, T)` pairs with
  `marked(S) = x`, `marked(T) = y`, `|S ∩ T| = m - k` = "(number of `y`-targets)
  × (sources per fixed target)" = `choose(r, y) * choose(N - r, m - y) *
  overlap_count (N m r k) x y`.
- **`fiberSum_swap`** (`BernoulliLaplaceFiber`): `fiberSum p x y = fiberSum p y x`.

From (CL) at `(x, y)` and `(y, x)` plus `fiberSum_swap`:
`choose(r, y) * choose(N - r, m - y) * overlap_count (N m r k) x y =
 choose(r, x) * choose(N - r, m - x) * overlap_count (N m r k) y x`.
Combined with the already-proved `fiberSum_eq`
(`fiberSum p x y = choose(r, x) * choose(N - r, m - x) *
transitionNumerator (N m r k) x y`) the `choose` factors cancel and give
`overlap_count (N m r k) x y = transitionNumerator (N m r k) y x`.

(CL) is verified below by exact kernel computation on the three small decks.
The general (symbolic) proof of (CL) — the 7-way `fiberSum` sum reindexed to the
`(S, T)` double count — is the single remaining piece of F3 item 3.
-/

def overlapP6321 : BernoulliLaplaceGeneral.ExchangeAdmissible :=
  ⟨6, 3, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

def overlapP7442 : BernoulliLaplaceGeneral.ExchangeAdmissible :=
  ⟨7, 4, 4, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

def overlapP8431 : BernoulliLaplaceGeneral.ExchangeAdmissible :=
  ⟨8, 4, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- (CL) for `(6,3,2,1)`, `x, y ∈ {0,1,2}`: `fiberSum = F(y) * overlap_count`. -/
theorem fiberCounting_6321 :
    ∀ (x y : Fin 3),
      BernoulliLaplaceGeneral.fiberSum overlapP6321 x.val y.val =
        Nat.choose 2 y.val * Nat.choose (6 - 2) (3 - y.val) *
          overlap_count 6 3 2 1 x.val y.val := by
  native_decide

/-- (CL) for `(7,4,4,2)`, valid `x, y ∈ {1,2,3,4}`. -/
theorem fiberCounting_7442 :
    ∀ (x y : Fin 4),
      BernoulliLaplaceGeneral.fiberSum overlapP7442 (1 + x.val) (1 + y.val) =
        Nat.choose 4 (1 + y.val) * Nat.choose (7 - 4) (4 - (1 + y.val)) *
          overlap_count 7 4 4 2 (1 + x.val) (1 + y.val) := by
  native_decide

/-- (CL) for `(8,4,3,1)`, `x, y ∈ {0,1,2,3}`. -/
theorem fiberCounting_8431 :
    ∀ (x y : Fin 4),
      BernoulliLaplaceGeneral.fiberSum overlapP8431 x.val y.val =
        Nat.choose 3 y.val * Nat.choose (8 - 3) (4 - y.val) *
          overlap_count 8 4 3 1 x.val y.val := by
  native_decide

/-- A subset equals its intersection-with-T joined with its complement-with-T
(the inverse pieces of the 2-part bin decomposition in the inner enumeration
bridge).  This is the reconstruction identity the general fiber-counting
lemma's bijection inverts. -/
theorem inter_sdiff_union {r : Nat} (T1 S1 : Finset (Fin r)) :
    S1 = (S1 ∩ T1) ∪ (S1 \ T1) := by
  ext z
  rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  by_cases hz : z ∈ T1 <;> simp [hz]

-- TODO(proof): the 2-part bin bijection `s1_bij` — the inner enumeration bridge
-- for the general fiber-counting lemma (CL).  The `S1`-slice
-- `(stars.powersetCard x).filter (S1 => (S1 ∩ T1).card = t)` is in bijection
-- with the 2-bin choice (t from T1, then x-t from stars \ T1) via
-- `S1 ↦ (S1 ∩ T1, S1 \ T1)`, inverse `(A, B) ↦ A ∪ B`.
-- `Finset.card_bij` with that map yields three routine subgoals (mem/inj/surj)
-- using `Finset.mem_powersetCard`, `Finset.card_sdiff`,
-- `Finset.card_union_add_card_inter`, and `inter_sdiff_union`.  The single wall:
-- the 2-bin target finset.  `Finset.product a b` (the Cartesian product) does
-- not `rw [Finset.card_product]` / `Finset.mem_product` in this build, and the
-- `×˘` token does not parse.  Resume by building the target as an explicit
-- `Finset.image` (or `sProd`) whose membership AND cardinality reductions fire,
-- or prove the two bin cardinalities separately and close with a sigma Fubini.
-- Once `s1_bij` and the analogous `s2_bij` land, the general CL is their
-- product plus a sum over `t`; `fiberSum_swap` + `fiberSum_eq` finish F3 item 3.
--
-- **Clean derivation (5th session):** the general identity needs only the
-- symbolic (CL) `fiberSum p x y = choose(r,y)*choose(N-r,m-y)*overlap_count
-- (N m r k) x y`, because
-- `(CL x y) + fiberSum_swap + fiberSum_eq (y x)` gives
-- `choose(r,y)*choose(N-r,m-y)*overlap_count (N m r k) x y =
--  fiberSum p x y = fiberSum p y x =
--  choose(r,y)*choose(N-r,m-y)*transitionNumerator (N m r k) y x`, and the
-- nonzero `choose` factor cancels to `overlap_count (N m r k) x y =
-- transitionNumerator (N m r k) y x`.  Equivalently, reindexing the 7-tuple
-- fiber to the `(S,T)` pair (with `A = S\\T`, `B = T\\S` uniquely
-- determined, `|S∩T| = m-k`) gives `fiberSum = F(y)*overlap_count` directly.
--
-- **This build's Finset API walls (verified):** `Finset.card_le`,
-- `Finset.card_le_of_subset`, `Finset.card_lt`, `Finset.not_mem_empty`,
-- `Finset.mem_empty` all **do not exist**; `Finset.product`/`×˘` do not reduce
-- under `rw [Finset.card_product]`/`Finset.mem_product` in isolation; and
-- `rw [Finset.mem_powersetCard] at h` hits a `simp` recursion loop at the
-- 4-tuple stage.  `Finset.sum_le_sum`, `Finset.card_powersetCard`,
-- `Finset.mem_powersetCard`, `Finset.card_bij`, `Finset.card_sdiff`, and
-- `Finset.inter_comm` all work.  `inter_sdiff_union` (the reconstruction
-- identity) is proven above.  Resume the (CL) by proving the 7-tuple
-- `fiber7Set` → `(S,T)` bijection with `Finset.card_bij` on explicit
-- `Finset.image` targets (never bare `Finset.product`), bounding
-- `(S1∩T1).card ≤ S1.card` via `sumOnes` + `Finset.sum_le_sum`.


/-! The 2-bin fiber decomposition (F3 item 3, 5th-session `s1_bij` wall, now broken).

The `S1` fiber (the `x`-subsets of the specials with `|S1 ∩ T1| = t`) is the
disjoint union, over the `t`-subsets `A` of `T1`, of the fibers over a fixed
`T1`-part `A`.  Counting then reduces to counting the outside part.  The next
step (not yet in this file) is `fiberA_card`, the `S1 ↦ S1 \ T1` bijection
via `Finset.card_bij`, which together with `Finset.card_biUnion` and
`Finset.card_powersetCard` yields the `choose` formula.  -/

def s1Fiber (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x t : Nat)
    (T1 : Finset (Fin p.r)) : Finset (Finset (Fin p.r)) :=
  ((starsUniv p).powersetCard x).filter (fun S1 => (S1 ∩ T1).card = t)

def fiberA (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x t : Nat)
    (T1 : Finset (Fin p.r)) (A : Finset (Fin p.r)) :
    Finset (Finset (Fin p.r)) :=
  ((starsUniv p).powersetCard x).filter (fun S1 => S1 ∩ T1 = A)

theorem s1Fiber_biUnion (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x t : Nat) (T1 : Finset (Fin p.r)) (htx : t ≤ x) :
    s1Fiber p x t T1 = (T1.powersetCard t).biUnion (fiberA p x t T1) := by
  set st := starsUniv p
  ext S1
  dsimp only [s1Fiber, fiberA]
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h
    rcases h with ⟨hS1mem, hI⟩
    set A := S1 ∩ T1 with hAdef
    have hAmem : A ∈ T1.powersetCard t := by
      simp only [hAdef, Finset.inter_subset_right, hI, Finset.mem_powersetCard]
      <;> aesop
    refine ⟨A, hAmem, ?_⟩
    dsimp only [fiberA]
    rw [Finset.mem_filter]
    exact ⟨hS1mem, hAdef.symm⟩
  · rintro ⟨A, hAmem, hmemA⟩
    have hmemA2 : S1 ∈ (starsUniv p).powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [fiberA, Finset.mem_filter] using hmemA
    rcases hmemA2 with ⟨hS1mem, hI⟩
    refine ⟨hS1mem, ?_⟩
    rw [hI]
    exact (Finset.mem_powersetCard.1 hAmem).2
-- TODO(proof): `fiberA_card` — the last 2-bin piece of the general CL (F3 item 3).
-- `s1Fiber_biUnion` above breaks the 5th-session `s1_bij` wall: the S1 fiber is
-- the disjoint union over `A ∈ T1.powersetCard t` of `fiberA p x t T1 A`.
-- The remaining step is the cardinality of a single fiber:
--
--     (fiberA p x t T1 A).card = ((starsUniv p \ T1).powersetCard (x - t)).card
--
-- proven with `Finset.card_bij (fun S1 _ => S1 \ T1)` (the *dependent* form —
-- the Set-based `card_nbij` does NOT work here because the InjOn/SurjOn
-- goals are Set memberships where `rw [Finset.mem_filter]` fails).  Three
-- subgoals, all routine:
--   1. MapsTo:  `S1 \ T1 ⊆ st \ T1` via `Finset.sdiff_subset_sdiff`;
--     `#(S1 \ T1) = x - t` via `Finset.card_sdiff` + `Finset.inter_comm`.
--   2. InjOn:   `S1 = A ∪ (S1 \ T1)` and `S1' = A ∪ (S1' \ T1)`
--     (from `S1 ∩ T1 = A = S1' ∩ T1`), then `S1 \ T1 = S1' \ T1 → S1 = S1'`.
--   3. SurjOn:  `R ↦ A ∪ R`; `(A ∪ R) ∈ st.powersetCard x` (card via
--     `Finset.card_union_add_card_inter` + `Finset.card_empty`); and
--     `(A ∪ R) ∩ T1 = A` (proven by subset-antisymmetry, NOT by a
--     distributivity lemma — `Finset.inter_distrib_right` does not exist).
--
-- **Verified wall-gotchas for this build (6th session):**
--  * Finset membership `z ∈ s` is an opaque `Quot.lift`; `rcases`/`.1`/`.2`
--    only work AFTER `rw [Finset.mem_inter | Finset.mem_sdiff | Finset.mem_union]`.
--  * `Finset.mem_empty` and `Finset.mem_union` do NOT exist as names; prove
--    `A ∩ R = ∅` by `ext z; rw [Finset.mem_inter]; intro hz; absurd` (the
--    "empty" direction is `intro hz; exact hz.elim` on the `List.Mem z []`).
--  * The lemma is spelled `Finset.sdiff_subset_sdiff` (NOT `sddsubset_sdiff`)
--    and `Finset.card_sdiff` (NOT `card_sddsubset`); `Nat.add_sub_cancel_left`
--    exists for the `t + (x - t) = x` closure (needs `t ≤ x`).
--  * `dsimp only [fiberA]` (on a goal) works; `dsimp ... at h` on a hypothesis
--    does NOT unfold the `filter` — use `simpa [fiberA, Finset.mem_filter] using h`
--    to make a fresh `have` of the conjunction type instead.
--
-- After `fiberA_card`: `s1Fiber_card` by `Finset.card_biUnion` (needs
-- `(T1.powersetCard t : Set).PairwiseDisjoint (fiberA p x t T1)` — the fibers
-- are disjoint since the `T1`-part is unique) + "sum of a constant" =
-- `|(T1.powersetCard t)| * |(st \ T1).powersetCard (x - t)|` =
-- `choose(|T1|, t) * choose(|st \ T1|, x - t)` via `Finset.card_powersetCard`
-- and `Finset.card_sdiff_of_subset` (`|st \ T1| = r - |T1|`).  That is the
-- S1-side of the general CL; the S2-side is the mirror image and
-- `fiberSum_swap` + `fiberSum_eq` finish F3 item 3.

/-! The 2-bin fiber count, second half (F3 item 3).  Together with
`s1Fiber_biUnion`, this gives the S1-side of the general combinatorial lemma:
a single fiber over the `T1`-part `A` is counted by the outside part, via the
`S1 ↦ S1 \\ T1` bijection.  -/

theorem fiberA_card (p : BernoulliLaplaceGeneral.ExchangeAdmissible) (x t : Nat)
    (T1 A : Finset (Fin p.r)) (htx : t ≤ x)
    (hT1 : T1 ⊆ starsUniv p) (hA : A ∈ T1.powersetCard t) :
    (fiberA p x t T1 A).card = ((starsUniv p \ T1).powersetCard (x - t)).card := by
  set st := starsUniv p
  have hAsub : A ⊆ T1 := (Finset.mem_powersetCard.1 hA).1
  have hAcard : A.card = t := (Finset.mem_powersetCard.1 hA).2
  refine Finset.card_bij (fun S1 _ => S1 \ T1) ?_ ?_ ?_
  · -- MapsTo
    intro S1 hS1
    have hS1c : S1 ∈ st.powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [fiberA, Finset.mem_filter] using hS1
    rcases hS1c with ⟨hS1mem, hI⟩
    have hS1sub : S1 ⊆ st := (Finset.mem_powersetCard.1 hS1mem).1
    have hS1card : S1.card = x := (Finset.mem_powersetCard.1 hS1mem).2
    have hRestsub : S1 \ T1 ⊆ st \ T1 := Finset.sdiff_subset_sdiff hS1sub (by rfl)
    have hRestcard : (S1 \ T1).card = x - t := by
      rw [Finset.card_sdiff, Finset.inter_comm, hI, hAcard, hS1card]
    simpa [hRestsub, hRestcard, Finset.mem_powersetCard]
  · -- InjOn
    intro S1 hS1 S1' hS1' h
    have hS1c : S1 ∈ st.powersetCard x ∧ S1 ∩ T1 = A := by
      simpa [fiberA, Finset.mem_filter] using hS1
    have hS1c' : S1' ∈ st.powersetCard x ∧ S1' ∩ T1 = A := by
      simpa [fiberA, Finset.mem_filter] using hS1'
    let hI1 := hS1c.2
    let hI2 := hS1c'.2
    have hUn1 : S1 = A ∪ (S1 \ T1) := by
      ext z
      rw [Finset.mem_union, hI1.symm, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hUn2 : S1' = A ∪ (S1' \ T1) := by
      ext z
      rw [Finset.mem_union, hI2.symm, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hUn1, hUn2, h]
  · -- SurjOn
    intro R hR
    rcases Finset.mem_powersetCard.1 hR with ⟨hRsub, hRcard⟩
    refine ⟨A ∪ R, ?_, ?_⟩
    · -- ha : A ∪ R ∈ fiberA
      dsimp only [fiberA]
      have hsub : A ∪ R ⊆ st := by
        intro z hz
        rw [Finset.mem_union] at hz
        rcases hz with hzA | hzR
        · exact hT1 (hAsub hzA)
        · exact (Finset.mem_sdiff.1 (hRsub hzR)).1
      have hARdis : A ∩ R = ∅ := by
        ext z
        rw [Finset.mem_inter]
        constructor
        · intro hz
          have hzT1 := hAsub hz.1
          have hznot := (Finset.mem_sdiff.1 (hRsub hz.2)).2
          exfalso
          exact absurd hzT1 hznot
        · intro hz; cases hz
      have hcard : (A ∪ R).card = x := by
        have h0 : (A ∩ R).card = 0 := by simpa only [hARdis, Finset.card_empty]
        have hsum : (A ∪ R).card + (A ∩ R).card = A.card + R.card :=
          Finset.card_union_add_card_inter _ _
        rw [h0, add_zero, hAcard, hRcard] at hsum
        have hadd : t + (x - t) = x := by rw [Nat.add_comm, Nat.sub_add_cancel htx]
        exact hsum.trans hadd
      have hInt : (A ∪ R) ∩ T1 = A := by
        ext z
        rw [Finset.mem_inter]
        constructor
        · intro hz
          rcases hz with ⟨hzAR, hzT1⟩
          rw [Finset.mem_union] at hzAR
          rcases hzAR with hzA | hzR
          · exact hzA
          · exact absurd hzT1 (Finset.mem_sdiff.1 (hRsub hzR)).2
        · intro hzA
          exact ⟨Finset.mem_union.2 (Or.inl hzA), hAsub hzA⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact And.intro (And.intro hsub hcard) hInt
    · -- i (A ∪ R) = R, i.e. (A ∪ R) \ T1 = R
      ext z
      rw [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hz
        rcases hz with ⟨hzAR, hznotT1⟩
        rcases hzAR with hzA | hzR
        · exfalso
          exact absurd (hAsub hzA) hznotT1
        · exact hzR
      · intro hzR
        exact ⟨Or.inr hzR, (Finset.mem_sdiff.1 (hRsub hzR)).2⟩

