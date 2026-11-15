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
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic
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


/-!
## The general combinatorial lemma reduces to one pure-bijection identity

With `fiberSum_eq` (the `fiberSum = choose r x * choose (N-r) (m-x) *
transitionNumerator x y` closed form) and `fiberSum_swap` (`fiberSum p x y =
fiberSum p y x`) both proven, the general CL

    fiberSum p x y = choose (p.r) y * choose (p.N - p.r) (p.m - y) *
                     overlap_count (p.N p.m p.r p.k) x y

reduces, for a valid macro state, to the **single** pure-bijection identity
(below): `transitionNumerator (N m r k) y x = overlap_count (N m r k) x y`.
The only existing versions are the three small-deck `native_decide` checks
(`overlap_eq_revTransitionNumerator_valid_*`) and the Commander center
(`..._cmdr_2525`).

**Why they are equal (combinatorial interpretation).**  Both count the same
set of ordered pairs `(S_y, S_x)` of `m`-subsets with `y` / `x` marked cards
and `|S_y ∩ S_x| = m - k`, decomposed into the same four bins
(marked/plain × in/out):

* `transitionNumerator (N m r k) y x` (summed over `a`, the number of marked
  cards moved *out* of the `y`-marked source) has the four factors
  `choose y a`, `choose (m-y) (k-a)`, `choose (r-y) b`,
  `choose ((N-m)-(r-y)) (k-b)` with `b = x - (y - a)`.

* `overlap_count (N m r k) x y` (summed over `t`, the marked overlap
  `|S_x ∩ T|`, for a fixed `y`-marked target `T`) has the four factors
  `choose y t`, `choose (r-y) (x-t)`, `choose (m-y) ((m-k)-t)`,
  `choose (N-r-(m-y)) ((m-x)-((m-k)-t))` (via `chooseSigned`).

A transition from `S_y` to `S_x` (move `k` out, `k` in) exists iff
`|S_y ∩ S_x| = m - k`; the number of such transitions for a fixed pair is
exactly the four-bin overlap count, so the two sums agree.  The symbolic proof
is a reindex of the `t`-sum to the `a`-sum: both are `∑` of a product of four
`Nat.choose` factors with `if`-guards, so no `Finset` API is involved — only
the `choose n k = 0` convention (for `k > n`) replaces the guards, and the two
sum ranges can be unified.

**The reindexing (5th-session advance).**  Set `t := y - a` (the marked overlap
equals the source's `y` marked minus the `a` marked moved out).  Under this
substitution the four transition factors match the four overlap factors:
* `choose y a = choose y (y - t) = choose y t`            (`Nat.choose_sub`/symmetry)
* `choose (r - y) b = choose (r - y) (x - (y - t)) = choose (r - y) (x - t)`
* `choose (m - y) (k - a) = choose (m - y) (m - k - t)`   (symmetry: `(m-y)-(k-a) = m-k-t`)
* `choose (N - m - (r - y)) (k - b) = choose (N - r - (m - y)) (k - x + t)`
  (the base `N - m - (r - y) = N - r - (m - y)`).
The one remaining difficulty is the **boundary**: the transition sum runs over
`a ∈ range (k + 1)` with `if`-guards (and `Nat`-saturated `y - a`), whereas the
overlap sum runs over `t ∈ range ((m - k) + 1)` with `chooseSigned` returning `0`
out of range.  A unified proof rewrites both as `∑` over a common `t`-range with
out-of-range terms `0`, using the guards' failure to force the relevant factor to
`0`.  This is a pure `Nat`/`choose` reindexing (no `Finset` API).

**Complete proof plan (7th session).**  Write the transition summand as `g(a)`
over `a ∈ range (k+1)` and the overlap summand as `h(t)` over
`t ∈ range ((m-k)+1)`, each a product of four `Nat.choose`/`chooseSigned`
factors.  Four facts close
`transitionNumerator (N m r k) y x = overlap_count (N m r k) x y`:

1. **Pointwise match.**  With `t := y - a`, `g(a) = h(t)`: `choose y a =
   choose y (y-t) = choose y t` (`Nat.choose_sub`/symmetry); `choose (r-y)
   (x-t)` (direct, since `b = x - (y-a) = x - t`); `choose (m-y) (k-a) =
   choose (m-y) (m-k-t)` (symmetry: `(k-a) + ((m-k)-t) = m-y`); and
   `choose (N-m-(r-y)) (k-x+t) = choose (N-r-(m-y)) (k-x+t)` (base
   `N-m-(r-y) = N-r-(m-y)`).  The two `if`-guards in `g(a)` are exactly the
   non-negativity conditions the overlap's `chooseSigned` factors enforce
   (`t ≤ x` ⟺ `x-t ≥ 0`; `x-t ≤ k` ⟺ `k-x+t ≥ 0`), so `g(a) = 0` exactly when
   `h(y-a) = 0` (the `Nat`-saturated `y-a` is harmless: the outer guard fails
   first).

2. **Support of `h`.**  `h(t) = 0` for `t > y` (factor `S1 = chooseSigned y t`)
   and for `t < y - k` (factor `S3 = chooseSigned (m-y) ((m-k)-t)`, whose
   argument `(m-k)-t > m-y` exactly when `t < y-k`).  So the overlap sum is
   supported exactly on `[y-k, y]` (clipped to its `range`).

3. **Support alignment.**  Substituting `u := y - a` into the transition sum
   gives `∑_{u = y-k}^{y} h(u)` — the same support as (2).

4. **Sum-reindex (NOT pointwise).**  The *pointwise* identity `g(a) = h(y-a)`
   is **false** for `a > y`: `Nat`-saturating `t := y - a` to `0` makes
   `h(0)` potentially nonzero while `g(a) = 0` (factor `choose y a`).  The
   correct statement is the **sum** equality
   `∑_{a ∈ range (k+1)} g(a) = ∑_{t ∈ range ((m-k)+1)} h(t)`, proved by the
   affine reindex `t := y - a` as a `Finset.sum_bij` between the two
   *supports*.

5. **Supports align exactly.**  `g(a) = 0` outside
   `[max (0, k-m+y), min y (k)]` and `h(t) = 0` outside
   `[max (0, y-k), min y (m-k)]` (factors `S1 = chooseSigned y t` and
   `S3 = chooseSigned (m-y) ((m-k)-t)`); under `t := y - a` these two
   intervals coincide (`[max (0, y-k), min y (m-k)]`).  On that common support
   all four factors are in range, so step 1's factor-match (choose symmetry)
   gives `g(a) = h(y-a)`, and off the support both sides are `0`.  The affine
   reindex (a `Finset.sum_bij` / `Finset.sum_image` on `Finset.range`) then
   identifies the two sums.

Only steps 4–5 touch `Finset` (via `Finset.sum_bij`/`sum_image`); steps 1–3 are
pure `Nat`/`choose` (`Nat.choose_sub`, `Nat.choose_symm`) plus the guard
case-analysis.  This is the single remaining step of F3 item 3 core and it
directly unblocks item 4 (2-exchange TV) and F4.5.
-/
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

-- RESOLVED (6th session): the `s1_bij` wall is broken by `s1Fiber_biUnion`
-- below (the S1 fiber is the pairwise-disjoint biUnion of the per-`A` fibers
-- `fiberA`), `fiberA_card` (each fiber's cardinality = the outside part),
-- `s1Fiber_card` (the biUnion count), and `s1Fiber_choose` (the closed
-- binomial form `choose |T1| t * choose (|stars|-|T1|) (x - t)`).  The
-- general CL follows by applying the same construction on the T-side and
-- combining with `fiberSum_swap` / `fiberSum_eq` (see F3 item 4).  The
-- 5th-session wall (`Finset.product`/`×˘` not reducing under
-- `rw [card_product]`/`mem_product`) is bypassed entirely: we never build a
-- 2-bin product finset — we decompose by the intermediate `A = S1 ∩ T1` and
-- use `Finset.card_bij` + `Finset.card_biUnion` instead.

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
-- RESOLVED (6th session): `fiberA_card` (below), `s1Fiber_card`, and
-- `s1Fiber_choose` break this — see their doc comments for the exact
-- `Finset.card_bij` / `card_biUnion` / `card_powersetCard` recipe and the
-- build-specific gotchas (opaque `Quot.lift` membership, the `∃ a ha, …`
-- form needing `refine ⟨…, ?_, ?_⟩`, nested `(P ∧ Q) ∧ R` conjunctions,
-- and the empty-set direction closing by `cases` on `List.Mem z []`).

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

/-! The S1-side of the general combinatorial lemma (F3 item 3, third piece).
The S1 fiber is a pairwise-disjoint union of the per-`A` fibers (s1Fiber_biUnion),
each counted by the outside part (fiberA_card); the sum of the constant collapses
to a product of two powerset-card counts.  -/

theorem s1Fiber_card (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x t : Nat) (T1 : Finset (Fin p.r)) (htx : t ≤ x) (hT1 : T1 ⊆ starsUniv p) :
    (s1Fiber p x t T1).card =
      (T1.powersetCard t).card * ((starsUniv p \ T1).powersetCard (x - t)).card := by
  rw [s1Fiber_biUnion p x t T1 htx]
  have hdis : (T1.powersetCard t : Set (Finset (Fin p.r))).PairwiseDisjoint
      (fun A => fiberA p x t T1 A) := by
    intro A hA B hB hne
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    ext S1
    dsimp only [fiberA]
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro hz
      rcases hz with ⟨hleft, hright⟩
      rcases hleft with ⟨hS1in, hAeq1⟩
      rcases hright with ⟨hS2in, hAeq2⟩
      have hAeq : A = B := hAeq1.symm.trans hAeq2
      exact False.elim (hne hAeq)
    · intro hz
      cases hz
  rw [Finset.card_biUnion hdis]
  have hc : ∀ A ∈ T1.powersetCard t,
      (fiberA p x t T1 A).card = ((starsUniv p \ T1).powersetCard (x - t)).card := by
    intro A hA
    exact fiberA_card p x t T1 A htx hT1 hA
  rw [Finset.sum_congr rfl (fun A hA => hc A hA)]
  simp [Finset.sum_const]

/-! The general combinatorial lemma, S1-side, in binomial-coefficient form
(F3 item 3).  The S1 fiber over `T1` with `t` marked cards is counted by
`choose |T1| t` (pick the `T1`-part) times `choose (|stars| - |T1|) (x - t)`
(pick the outside part).  This is the symbolic form of the small-deck
`overlap_count` identity; it holds for any `ExchangeAdmissible` parameter.  -/
theorem s1Fiber_choose (p : BernoulliLaplaceGeneral.ExchangeAdmissible)
    (x t : ℕ) (T1 : Finset (Fin p.r)) (htx : t ≤ x) (hT1 : T1 ⊆ starsUniv p) :
    (s1Fiber p x t T1).card =
      Nat.choose T1.card t * Nat.choose ((starsUniv p).card - T1.card) (x - t) := by
  set st := starsUniv p
  rw [s1Fiber_card p x t T1 htx hT1]
  rw [Finset.card_powersetCard t T1]
  rw [Finset.card_powersetCard (x - t) (st \ T1)]
  rw [Finset.card_sdiff_of_subset hT1]

/-! `oterm`: the `t`-th summand of `overlap_count`, the `chooseSigned` to
`Nat.choose` bridges, and the `overlap_count` = sum-of-`oterm` decomposition.
These reduce the general combinatorial lemma (F3 item 3) to a per-term
identity under the reindexing `t = y - a` (9th session). -/

def oterm (N m r k x y t : Nat) : Nat :=
  let nI := (N : Int); let mI := (m : Int); let rI := (r : Int)
  let kI := (k : Int); let xI := (x : Int); let yI := (y : Int)
  let tI := t
  let plain_outside_target := nI - rI - (mI - yI)
  let plain_overlap := (mI - kI) - tI
  chooseSigned yI tI *
    chooseSigned (rI - yI) (xI - tI) *
    chooseSigned (mI - yI) plain_overlap *
    chooseSigned plain_outside_target ((mI - xI) - plain_overlap)

/-- `overlap_count` is the sum of its `oterm` summands (definitional). -/
-- The transition-side summand: the product of the four `choose` factors of
-- `transitionNumerator`'s 4-bin expansion, at a starting overlap `a`.
def tterm (N m r k x y a : Nat) : Nat :=
  let remaining := y - a
  if remaining ≤ x then
    let b := x - remaining
    if b ≤ k then
      Nat.choose y a * Nat.choose (m - y) (k - a) *
        Nat.choose (r - y) b * Nat.choose ((N - m) - (r - y)) (k - b)
    else 0
  else 0

theorem overlap_eq_sum_oterm (N m r k x y : Nat) :
    overlap_count N m r k x y = (Finset.range (m - k + 1)).sum (fun t => oterm N m r k x y t) := by
  rfl

/-- `chooseSigned (n : Int) e = Nat.choose n (e.toNat)` for a nonnegative
    argument `e`: the in-range binomial coefficient, or `0` when `e > n`. -/
theorem cs_eq_chooseNat {n : Nat} (e : Int) (he : 0 ≤ e) :
    chooseSigned (n : Int) e = Nat.choose n e.toNat := by
  dsimp only [chooseSigned]
  by_cases hen : e ≤ (n : Int)
  · split_ifs <;> simp_all [he, hen]
  · have heI : (e.toNat : Int) = e := Int.toNat_of_nonneg he
    have henI : (n : Int) < (e.toNat : Int) := by rw [← heI]; omega
    have hgt : e.toNat > n := Nat.cast_lt.mp henI
    split_ifs
    · exfalso; omega
    · have h0 : n.choose e.toNat = 0 := by rw [Nat.choose_eq_zero_iff]; exact hgt
      simpa using h0.symm

/-- `chooseSigned base e = Nat.choose (base.toNat) (e.toNat)` for a
    nonnegative Int base and argument. -/
theorem cs_eq_chooseNatI (base e : Int) (hbase : 0 ≤ base) (he : 0 ≤ e) :
    chooseSigned base e = Nat.choose base.toNat e.toNat := by
  have hbI : (base.toNat : Int) = base := Int.toNat_of_nonneg hbase
  rw [← hbI]
  exact cs_eq_chooseNat (n := base.toNat) (e := e) he

/-- For `b ≤ a`, `((a : Int) - (b : Int)).toNat = a - b`. -/
theorem intSub_toNat {a b : Nat} (h : b ≤ a) : ((a : Int) - (b : Int)).toNat = a - b := by
  have hz : (a : Int) - (b : Int) = (a - b : Int) := by simp [Int.cast_sub, h]
  rw [hz]; simp

/-- The `.toNat` of a difference of two (nonnegative) Int differences, when it is
    itself nonnegative, is the corresponding nested `Nat` difference.  Used to
    convert the `chooseSigned` arguments in the general-CL summand match
    (`F3`, `F4`) into `Nat.choose` arguments. -/
theorem intDiffDiff_toNat {a b c d : Nat} (hb : b ≤ a) (hd : d ≤ c) (hle : c - d ≤ a - b) :
    (((a : Int) - (b : Int)) - ((c : Int) - (d : Int))).toNat = (a - b) - (c - d) := by
  rw [← Nat.cast_sub hb, ← Nat.cast_sub hd]
  rw [← Nat.cast_sub hle]
  simp

/-- The `.toNat` of `(a-b)` (a difference of casts) minus a single cast `c`,
    when nonnegative, is the nested `Nat` difference.  This matches the `oterm`
    factor whose argument is built as `(mI - kI) - tI` with `tI` a single `Nat`. -/
theorem intDiffSingleCast_toNat {a b c : Nat} (hb : b ≤ a) (hc : c ≤ a - b) :
    (((a : Int) - (b : Int)) - (c : Int)).toNat = (a - b) - c := by
  rw [← Nat.cast_sub hb]
  rw [← Nat.cast_sub hc]
  simp

/-! The `chooseSigned` to `Nat.choose` bridge for single `Nat`-cast arguments, and
the first two summand matches of the general CL (F3 item 3, 9th session). -/

/-- When both arguments are single `Nat`-casts, `chooseSigned` is exactly
    `Nat.choose`.  This is the cleanest form of the bridge, used once the
    `oterm` arguments are put into single-cast shape in the admissible regime. -/
theorem cs_eq_chooseNatNat (n k : Nat) : chooseSigned (n : Int) (k : Int) = Nat.choose n k := by
  dsimp only [chooseSigned]
  split_ifs
  · simp
  · by_cases hk : k ≤ n
    · exfalso
      simp only [Int.natCast_nonneg, Nat.cast_le, true_and, hk] at *
      tauto
    · have h0 : Nat.choose n k = 0 := by simpa [Nat.choose_eq_zero_iff] using hk
      simpa using h0.symm

/-- `chooseSigned n k = 0` when the signed index `k < 0` (the in-range
    binomial guard `0 ≤ k ∧ k ≤ n` fails). -/
theorem chooseSigned_zero_neg (n k : Int) (hk : k < 0) : chooseSigned n k = 0 := by
  dsimp only [chooseSigned]
  by_cases h : 0 ≤ k ∧ k ≤ n
  · exfalso; exact lt_irrefl 0 (lt_of_le_of_lt h.1 hk)
  · rw [if_neg h]

/-- `chooseSigned n k = 0` when the signed index `k > n` (the in-range
    binomial guard `0 ≤ k ∧ k ≤ n` fails). -/
theorem chooseSigned_zero_toobig (n k : Int) (hk : n < k) : chooseSigned n k = 0 := by
  dsimp only [chooseSigned]
  by_cases h : 0 ≤ k ∧ k ≤ n
  · exfalso; exact lt_irrefl k (lt_of_le_of_lt h.2 hk)
  · rw [if_neg h]

/-- First factor of the general CL: the marked-in-S part `choose y a`
    (`chooseSigned (y) (y-a)` via complementary symmetry). -/
theorem F1match (y a : Nat) (ha : a ≤ y) :
    chooseSigned (y : Int) (Nat.cast (y - a)) = Nat.choose y a := by
  rw [cs_eq_chooseNatNat y (y - a)]
  rw [Nat.choose_symm ha]

/-- Second factor of the general CL: the marked-outside part `choose (r-y) (x-t)`.
    In the admissible regime (`y ≤ r`, `t ≤ x`) the difference-of-casts arguments
    are single casts, so the bridge applies directly. -/
theorem F2match (r y x t : Nat) (hy : y ≤ r) (ht : t ≤ x) :
    chooseSigned ((r : Int) - (y : Int)) ((x : Int) - (t : Int)) =
      Nat.choose (r - y) (x - t) := by
  have h1 : (r : Int) - (y : Int) = Nat.cast (r - y) := by rw [← Nat.cast_sub hy]
  have h2 : (x : Int) - (t : Int) = Nat.cast (x - t) := by rw [← Nat.cast_sub ht]
  rw [h1, h2]
  rw [cs_eq_chooseNatNat (r - y) (x - t)]

theorem F3match (m k y a : Nat) (ha : a ≤ y) (hak : a ≤ k) (hky : k ≤ y) (hmy : y ≤ m) :
    chooseSigned ((m : Int) - (y : Int)) (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)) =
      Nat.choose (m - y) (k - a) := by
  have He : ((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int) = (m - y : Int) - (k - a : Int) := by
    have hya : (Nat.cast (y - a) : Int) = (y : Int) - (a : Int) := by rw [Nat.cast_sub ha]
    rw [hya]
    have hmy' : (m - y : Int) = (m : Int) - (y : Int) := by rfl
    have hka : (k - a : Int) = (k : Int) - (a : Int) := by rfl
    rw [← hmy', ← hka]
    ring_nf
  by_cases hk : k - a ≤ m - y
  · -- e ≥ 0
    have he0 : 0 ≤ ((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int) := by
      rw [He]
      have hka : (k - a : Int) = (Nat.cast (k - a) : Int) := by rw [Nat.cast_sub hak]
      have hmy' : (m - y : Int) = (Nat.cast (m - y) : Int) := by rw [Nat.cast_sub hmy]
      rw [hmy', hka]
      simp only [Int.sub_nonneg, Nat.cast_le]
      exact hk
    have hbase0 : 0 ≤ (m : Int) - (y : Int) := by simp only [Int.sub_nonneg, Nat.cast_le]; exact hmy
    rw [cs_eq_chooseNatI ((m : Int) - (y : Int)) (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)) hbase0 he0]
    have hbase_toNat : ((m : Int) - (y : Int)).toNat = (m - y) := by exact intSub_toNat hmy
    have he_toNat : (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)).toNat = (m - y) - (k - a) := by
      rw [He]
      have hka : (k - a : Int) = (Nat.cast (k - a) : Int) := by rw [Nat.cast_sub hak]
      have hmy' : (m - y : Int) = (Nat.cast (m - y) : Int) := by rw [Nat.cast_sub hmy]
      rw [hmy', hka]
      rw [intSub_toNat hk]
    rw [hbase_toNat, he_toNat]
    rw [Nat.choose_symm hk]
  · -- e < 0  ⟺  k - a > m - y
    have hnot : ¬(0 ≤ ((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)) := by
      rw [He]
      have hka : (k - a : Int) = (Nat.cast (k - a) : Int) := by rw [Nat.cast_sub hak]
      have hmy' : (m - y : Int) = (Nat.cast (m - y) : Int) := by rw [Nat.cast_sub hmy]
      rw [hmy', hka]
      simp only [Int.sub_nonneg, Nat.cast_le]
      exact hk
    unfold chooseSigned
    by_cases hge : 0 ≤ ((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)
    · exfalso; exact hnot hge
    · simp only [hge]
      have h0 : Nat.choose (m - y) (k - a) = 0 := by simpa [Nat.choose_eq_zero_iff] using (Nat.not_le.mp hk)
      simpa using h0.symm


/-- For `b ≤ a`, `(a:ℤ)-(b:ℤ)` (difference of `Nat` casts) equals the single
    `Nat`-cast `↑(a-b)`: both denote the exact nonnegative value.  Proven via
    the `.toNat` bridge (`intSub_toNat`). -/
theorem intSub_eqCast (a b : Nat) (h : b ≤ a) : (a : Int) - (b : Int) = (Nat.cast (a - b) : Int) := by
  have h0 : 0 ≤ (a : Int) - (b : Int) := by simp only [Int.sub_nonneg]; omega
  have ht : ((a : Int) - (b : Int)).toNat = a - b := intSub_toNat h
  rw [← Int.toNat_of_nonneg h0]
  rw [ht]

/-- Under `m + r ≤ N`, the target-`Int` form of `N-m-r+y` equals its single
    `Nat`-cast, so the `.toNat` recovers the exact `Nat`. -/
theorem intSubSubAdd_eqCast (N m r y : Nat) (hN : m + r ≤ N) :
    (N - m - r + y : Int) = (Nat.cast (N - m - r + y) : Int) := by
  have hN2 : m + r ≤ N + y := by omega
  have h1 : (N - m - r + y) = (N + y) - (m + r) := by omega
  rw [h1, Nat.cast_sub hN2, Nat.cast_add, Nat.cast_add]
  ring_nf

/-- F3 item 3, **4th summand factor (F4) — RESOLVED.**
    The 4th `chooseSigned` factor (difference-form base `N-r-(m-y)` and
    difference-of-differences argument) equals the 4th transition `Nat.choose`
    factor `choose (N-m-r+y) (k-(x-(y-a)))`, in the admissible regime
    (`t = y-a`; 1st guard `y-a ≤ x`, 2nd guard `x-(y-a) ≤ k`, plus the fiber
    regime `y ≤ m`, `m+r ≤ N`).  Both the base and argument reduce to exact
    `Int` equal to the single `Nat`-casts via `intSub_eqCast` /
    `intSubSubAdd_eqCast`, so `cs_eq_chooseNatI` + `Int.toNat_natCast` finish. -/
theorem F4match (N m r k x y a : Nat)
    (h1g : y - a ≤ x) (h2g : x - (y - a) ≤ k)
    (ha : a ≤ y) (hmy : y ≤ m) (hN : m + r ≤ N) :
    chooseSigned ((N : Int) - (r : Int) - ((m : Int) - (y : Int)))
        (((m : Int) - (x : Int)) - (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int))) =
      Nat.choose (N - m - r + y) (k - (x - (y - a))) := by
  have hR : (Nat.cast (k - (x - (y - a))) : Int) = (Nat.cast k - Nat.cast x + Nat.cast (y - a) : Int) := by
    rw [← intSub_eqCast k (x - (y - a)) h2g]
    rw [← intSub_eqCast x (y - a) h1g]
    ring_nf
  have he : ((m : Int) - (x : Int)) - (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)) =
            (Nat.cast (k - (x - (y - a))) : Int) := by
    rw [hR]
    ring_nf
  have he0 : 0 ≤ ((m : Int) - (x : Int)) - (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)) := by
    rw [he]
    simp only [Nat.cast_nonneg]
  have hbase : (N : Int) - (r : Int) - ((m : Int) - (y : Int)) = (Nat.cast (N - m - r + y) : Int) := by
    have hL : (N : Int) - (r : Int) - ((m : Int) - (y : Int)) = (N - m - r + y : Int) := by ring_nf
    rw [hL, intSubSubAdd_eqCast N m r y hN]
  have hbase0 : 0 ≤ (N : Int) - (r : Int) - ((m : Int) - (y : Int)) := by
    rw [hbase]
    simp only [Nat.cast_nonneg]
  rw [cs_eq_chooseNatI
        ((N : Int) - (r : Int) - ((m : Int) - (y : Int)))
        (((m : Int) - (x : Int)) - (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int)))
        hbase0 he0]
  have hbt : ((N : Int) - (r : Int) - ((m : Int) - (y : Int))).toNat = N - m - r + y := by
    rw [hbase, Int.toNat_natCast]
  have het : (((m : Int) - (x : Int)) - (((m : Int) - (k : Int)) - (Nat.cast (y - a) : Int))).toNat =
             k - (x - (y - a)) := by
    rw [he, Int.toNat_natCast]
  rw [hbt, het]



/-- F3 item 3 — **summand match `tterm_eq_oterm` — RESOLVED.**
    In the admissible regime, the transition summand `tterm` at overlap `a`
    equals the overlap summand `oterm` at `t = y - a`.  The four `Nat.choose`
    factors of `tterm` (with the two guard-ites collapsed) match the four
    `chooseSigned` factors of `oterm` via `F1match`/`F2match`/`F3match`/
    `F4match`; the two are the same 4-factor product up to the order of the
    middle (m/r) factors (`ring`) and the 4th-factor base
    `(N-m)-(r-y) = N-m-r+y` (`omega` under the regime). -/
theorem tterm_eq_oterm (N m r k x y a : Nat)
    (h1g : y - a ≤ x) (h2g : x - (y - a) ≤ k)
    (ha : a ≤ y) (hak : a ≤ k) (hky : k ≤ y) (hmy : y ≤ m) (hry : y ≤ r)
    (hN : m + r ≤ N) (h4g : r - y ≤ N - m) :
    tterm N m r k x y a = oterm N m r k x y (y - a) := by
  dsimp only [tterm, oterm]
  rw [if_pos h1g, if_pos h2g]
  rw [F1match y a ha,
      F2match r y x (y - a) hry h1g,
      F3match m k y a ha hak hky hmy,
      F4match N m r k x y a h1g h2g ha hmy hN]
  have hb : (N - m) - (r - y) = N - m - r + y := by omega
  rw [hb]
  ring_nf

/-- The `a`-summand of `transitionNumerator (N m r k) y x` (with the 4th/5th
    arguments swapped, so the transition's source is `y` and target is `x`) is
    definitionally the `tterm` at `(N m r k) x y a`; hence the transition is
    the sum of the `tterm` summands over `a` in `[0, k]`. -/
theorem transitionNumerator_eq_sum_tterm (N m r k x y : Nat) :
    transitionNumerator N m r k y x =
        (Finset.range (k + 1)).sum (fun a => tterm N m r k x y a) := by
  rfl


/-! F3 item 3 — **general CL: sum reindexing — the single remaining step (STUCK on a Lean term-matching wall).**
    All of the following are PROVEN (above):
    - all four factor matches:  `F1match`, `F2match`, `F3match`, `F4match`;
    - the summand assembly:  `tterm_eq_oterm`  (guard-hold regime:  `tterm a = oterm (y-a)`);
    - the decomposition:  `transitionNumerator_eq_sum_tterm`;
    - `chooseSigned_zero_neg` / `chooseSigned_zero_toobig`;
    - in the guard-FAIL cases the oterm's vanishing factor is provably 0  in ISOLATION:
      * F4 (h1g holds, h2g fails):  index  `(m-x)-(m-k-(y-a))  (Int)`  is  `< 0`  from  `k < x-(y-a)`;
        proven  by  `ring_nf`  +  `nlinarith [ (k:Int)+(y-a:Int) < (x:Int) ]`  (the  Int  inequality  is
        itself  by  `omega`  from  `k < x-(y-a)`  and  `y-a ≤ x`).
      * F2 (h1g fails):  index  `(x:Int)-(y-a:Int)  <  0`  from  `x < y-a`;  `rw [sub_neg]`  +  `omega`.
    **The wall:**  to close  `oterm N m r k x y (y-a) = 0`  I must fold the 4th factor  (=  0)  into the
    4-way product  `F1*F2*F3*F4`.  After  `dsimp only [oterm]`,  `rw`/`simp`/`conv`/`change` all FAIL to
    locate the 4th factor as a subterm of the product (the let-inlined AST does not match fresh
    `chooseSigned (↑N-↑r-(↑m-↑y)) (↑m-↑x-(↑m-↑k-↑(y-a)))`  notation,  though the 4th factor  MATCHES  that
    notation  when  stated  STANDALONE  —  caseB6  succeeds,  caseB5/B7/B8  fail  only  in  the  product
    context).  This is a  Lean  term-representation  issue,  not  a  math  one  (the  math  is  complete).
    **Next angle:**  prove  `oterm ... (y-a) = 0`  WITHOUT  dsimp-ing  into  the  product  —  e.g.  keep  the
    oterm let-binders  (`plain_outside_target`,  `plain_overlap`)  and  show  the  let-based  product  =  0  by
    `rw [chooseSigned_zero_neg _ _ hF4neg]`  on  the  4th  let-applied  factor  directly,  or  build  the
    equality  by  `refine`/`calc`  through  `mul_zero`.  Then  the  reindexing  `∑ tterm = ∑ oterm`  is
    `Finset.sum_bij`/`sum_image`  on  `a ↦ y-a`  over  the  common  support  `[max (0, y-k), min y (m-k)]`
    (outside  it  both  sums  are  0).  Then  F3  item  4  (2-exchange  TV)  follows  from  the  CL  +
    `fiberSum_eq`.  Do  NOT  use  bare  `simp`/`field_simp`  (this  module  is  adjacent  to  `Equiv.Perm (Fin 99)`
    consumers).  Working  scratch:  see  the  11th-session  handoff  note  (docs/agent_handoff.md). -/
