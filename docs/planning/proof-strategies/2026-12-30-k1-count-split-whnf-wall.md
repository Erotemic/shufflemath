# K1b `k1b_count_split`: exponential-whnf wall + decomposition plan (2026-12-30)

Companion to `docs/planning/proof-strategies/2026-12-25-k1-core-and-remaining-assembly.md`.
This corrects that handoff's assumption that the already-written `k1b_count_split`
"elaborates with a few fixes." It does not — the real blocker is a **deep
elaboration-depth / exponential-whnf blowup** plus an **incomplete 2b branch**,
not the (already-fixed) trap list.

## 2026-12-31 session (76th) — precise diagnosis of the 2b elaboration wall

The wall was reproduced across **four structurally different 2b routes** and is now
characterized precisely:

1. **It is an elaboration-budget wall, not a proof error.** The 0-branch
   (`k1b_count_non25`) must derive `(M.1 ∩ leftCards).card = 25` from a hit
   `newMembership Y c = M`, then contradict the `≠ 25` hypothesis. Every route
   whnf's the per-`c` `newMembership Y c` / `swapLeftPart Y c.1.1` / `newLeftCards
   Y c.1.1 c.2.1` term, and that whnf overflows.
2. **Two limits are tripped, and they interact.** With default options the error is
   `maximum recursion depth has been reached` (at the `swapLeftPart_card25 Y c.1.1`
   step). Raising `maxRecDepth` to 1000000 changes it to a **deterministic `whnf`
   heartbeat timeout at the default 200000 heartbeats**; raising `maxHeartbeats` to
   2000000 brings the recursion error back; `maxRecDepth` at 400 / 10000 / 50000 all
   give the same recursion error at the same single step.
3. **The blowup is pathological (likely exponential).** A *single* whnf step
   (`swapLeftPart_card25 Y c.1.1`) needs >50000 recursion depth. Raising the limits
   only makes the build slower before it fails or OOMs — it does not converge.
4. **It is context-dependent, not term-dependent.** The *identical* `swapLeftPart Y
   c.1.1` / `newMembership_set_eq` terms elaborate fine inside `k1b_count_25` (2a,
   committed) with a *bigger* local context, but overflow in the 0-branch's smaller
   context. The goal/context shape (not the term) decides whether the whnf stays
   under the limits.
5. **The membership-based `⊇` (non-circular) proof is sound.** It mirrors 2a's
   `hUnique` in shape but proves `swapLeftPart Y c.1.1 = M.1 ∩ leftCards Y` by
   membership + `leftCards_rightCards_disjoint`, avoiding the circular card argument
   2a needed `hO25` for. It fails only at the elaboration budget, not the math
   (WIP: `Shufflemath/_ProbeK1s.lean`).

**Consequence:** 2b (`k1b_count_non25`) is not crackable by any in-session
restructuring or limit-tuning of the per-c proof. The remaining routes are
structural: (a) prove the per-c fact as a *separate* lemma whose conclusion names
`newMembership Y c` directly (so the in-context whnf never fires) and instantiate it
in the 0-branch, (b) raise the whole-project heartbeat budget (disallowed globally by
AGENTS.md), or (c) a Lean toolchain change to bound the Finset-image/sdiff whnf. None
are appropriate to force in-session. **2a (`k1b_count_25`) is the proven, committed
half of the headline** (commit `e5932d4`); the full `k1b_count_split` assembly (2a +
2b + `countFiber 25 = 0`) is blocked on 2b.

## State (verified on disk)

- **Committed & green:** `_ProbeK1k.lean` (8967 jobs) holds the K1b
  **combinatorial core** `k1b_beta` (the `2^45` `leftChoices × rightChoices`
  count) and all the pile lemmas (`k1b_witnessLeft/Right`, `k1b_witnessLeft_removed`,
  `removedLeft_injective`, `swapRightPart_injective`, `k1b_union_decomp`,
  `newMembership_set_eq`, `swapLeft/RightPart_card25/subset`,
  `swapLeftPart_eq_complement`, `leftCards_card`, `leftWitness`, `rightWitness`,
  `removedLeft`, `swapLeftPart`, `swapRightPart`).
- **Untracked WIP (the wall):** `_ProbeK1m.lean` — a **278-line** `k1b_count_split`
  (the K1b headline: `#(choices (L,R) with newMembership = M) = 1 iff M splits
  25/25, else 0`, unique choice = the witness pair). **No `sorry`** — the proof is
  logically written. Full monolith preserved at
  `.pi-glla/k1b_count_split_v6_monolith.lean`. Sibling WIP probes
  `_ProbeK1n/_ProbeK1o/_ProbeK1p` import it; **none** are in `Shufflemath.lean`
  or `dev/verify_next_phase.sh`, so this cluster is isolated from production.

## The wall (measured)

`k1b_count_split` is a **single 2-branch `by_cases` term**. Building it:

1. **Default limits** → `maximum recursion depth` at the `by_contra`
   (line ~275, inside the 2b branch).
2. **`set_option maxRecDepth 1000000`** → the recursion-depth limit is cleared,
   but it then hits a **whnf / heartbeat timeout** (200 000 heartbeats) at the
   2a branch (`hFilter` region, line ~229) and again at the 2b end (lines
   ~279–280). The file exits "clean" only because the error is at the tail of the
   big term, past the last real `have`.

**Diagnosis:** this is an **exponential whnf blowup** (~10^7 elaborated term
nodes at 200k heartbeats), *not* a deep-but-bounded term. No `maxRecDepth` or
`maxHeartbeats` bump fixes it (raising one limit just moves the error to the
next limit). The deepest unfolds are the two sub-proofs
- `hUnique` (2a, "any choice hitting `M` equals the witness pair") — reduces
  `newMembership Y c.1.1 …` → `newLeftCards Y …` for the bound `c`, plus a
  `Finset.sdiff_sdiff_eq_self` + `Finset.card_sdiff_of_subset` cascade, and
- `hEmpty` (2b, "no choice hits `M` when the split is not 25/25") — the same
  `newMembership`-per-`c` unfold.

Both live in the one big term, so the elaborated term is huge and the kernel
times out on it.

**Also — the 2b branch looks logically incomplete.** Its final step derives
`50 ≤ leftCard.card + rightCard.card` from `25 ≤ leftCard.card` and
`25 ≤ rightCard.card`, then `by_contra; omega`. But to contradict
`leftCard.card ≠ 25` it actually needs `leftCard.card + rightCard.card = 50`
(from `k1b_union_decomp Y M`'s disjointness + `M.2 : M.1.card = 50`), which the
2b branch never establishes. So even past the recursion issue, **2b will not
close until that equality is added and `omega` is fed it.** (This is likely why
the 10-trap list's expected `omega` closure silently failed.)

## The fix (next session) — decompose, then fix 2b

Split the monolith into **two theorems** (each elaborated independently, fresh
budget), and **fix 2b**:

1. `theorem k1b_count_25 (Y) (M) (hO25 : (M.1 ∩ leftCards Y).card = 25) :
   (Finset.filter (fun c => newMembership Y c.1.1 (leftCard25 c.1.2) c.2.1
   (rightCard25 c.2.2) = M) (univ : Finset exchangeChoice)).card = 1 := by …`
   — the **entire 2a branch** verbatim (preamble `Lstar/Rstar/hOsub'/hSsub'/hArith/
   hDbl` + `hS25` + `hLstar25` + `hRstar25` + `hHit` + `hUnique` + `cstar` +
   `hFilter` + `rw [hFilter, Finset.card_singleton]`), goal directly `= 1`
   (drop the `rw [ite_eq_left hO25]`).

2. `theorem k1b_count_non25 (Y) (M) (hnot : (M.1 ∩ leftCards Y).card ≠ 25) :
   (Finset.filter …).card = 0 := by …` — the 2b branch, **fixed**: after
   `hOge : 25 ≤ leftCard.card` and `hSge : 25 ≤ rightCard.card`, add
   `have hSum : leftCard.card + rightCard.card = 50 := by
     have hD0 := Finset.disjoint_iff_inter_eq_empty.2 (k1b_union_decomp Y M).2
     have hU := by rw [(k1b_union_decomp Y M).1];  -- union = M.1
     calc leftCard.card + rightCard.card
       _ = ((swapLeftPart Y leftCard) ∪ (swapRightPart Y rightCard)).card :=
         by rw [← Finset.card_union_of_disjoint hD0]
       _ = M.1.card := by rw [hU]
       _ = 50 := by rw [M.2]`
   and close with `by_contra hNot; omega` from `25 ≤ a`, `25 ≤ b`, `a + b = 50`,
   `a ≠ 25` (so `a ≥ 25` and `a ≠ 25` → contradiction once `a + b = 50` and
   `b ≥ 25`). Then `rw [hEmpty, Finset.card_empty]; norm_num`.

3. `theorem k1b_count_split (Y) (M) : … = if (M.1 ∩ leftCards Y).card = 25
   then 1 else 0 := by classical
   by_cases hO25 : (M.1 ∩ leftCards Y).card = 25
   · rw [ite_eq_left hO25];  exact k1b_count_25 Y M hO25
   · rw [ite_eq_right hO25];  exact k1b_count_non25 Y M hO25`

If a single branch *still* times out (the `hUnique`/`hEmpty` `newMembership`-per-`c`
unfold is intrinsic), decompose **one level deeper**: extract `hUnique` into its own
theorem `k1b_count_unique (Y M) (hO25) (hS25) (Lstar Rstar : Finset …) :
∀ c, newMembership Y c… = M → c.1.1 = Lstar ∧ c.2.1 = Rstar` (pass the sets as
arguments) so `hFilter` elaborates in a much smaller context; do the same for the
2b emptiness lemma. Do **not** just raise `maxRecDepth` in the production file —
decompose.

**Exact identifiers** (verify against `_ProbeK1k`): the set-difference identity is
`Finset.sdiff_sdiff_eq_self`; `rightPosition` is a `Shufflemath`-level def
(`CommanderFiberCount.lean:58`, `Fin 49 → Fin 99`) and `leftPosition` is
`CommanderPermutation.leftPosition` (`Fin 50 → Fin 99`). Both are already
resolvable in `_ProbeK1m`'s import context (import `Mathlib` + `Shufflemath._ProbeK1k`),
so reuse that header when rewriting.

## After `k1b_count_split` builds → assemble `k1b_swap_half`

`_ProbeK1k.k1b_swap_half` (the K1b headline, `sorry` at 230–233) =
**mixture-linearity** (`run_tv_eq_macro` with the `BernoulliLaplaceFiber`
`TV`/`uniform` instances + `Finsupp.map_comp`) **× counting-symmetry**
(`k1b_count_split`) **× rawExchangeMembership mass** (`rawExchangeMembership_pointMass`
/ `uniformPushforward_pointMass`). Assembly details in the 2026-12-25 doc
(git `7d02441`): the exchange kernel's point mass is 0 unless `M` is the
`25/25` split (where it is `1/2^45 = 1 / (Finset.univ : Finset leftChoices).card`),
so `#choices / 2^45` = `1` in the 25/25 case and `0` otherwise = exactly
`k1b_count_split`'s RHS. Then `k1a_swap_half`, then the `k1_swap_half`
2-pile→3-way lift.

## Don'ts

- Do not keep `set_option maxRecDepth 1000000` in a committed file (I added it
  to the WIP `_ProbeK1m` for diagnosis and it did **not** fix the whnf timeout —
  it only moved the error). The fix is decomposition.
- Do not claim the K1 capstone is done from `k1b_beta` alone — `k1b_swap_half`
  (TV headline) still needs `k1b_count_split`.
- Do not let this WIP cluster leak into `Shufflemath.lean` / `dev/verify_next_phase.sh`
  until every theorem in it builds green.
- 2b is the fragile one — add the `leftCard.card + rightCard.card = 50` fact and
  make `omega` actually use `hnot : leftCard.card ≠ 25`; a bare `50 ≤ sum` +
  `25 ≤ a` / `25 ≤ b` does **not** contradict `a ≠ 25`.
