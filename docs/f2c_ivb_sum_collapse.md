# F2c-iv-b capstone: the two-level sum collapse (difficulty note)

**Date:** 2026-10-21. **Author:** autonomous Lean build session.
**Audience:** GPT / any reviewer with Mathlib context. This note records exactly
where the F2c-iv-b capstone is blocked and what is already known, so the next
attempt does not re-derive it.

## 1. The goal

The F2c-iv-b capstone is the **two-layer membership fiber law**: the two-stage
commander resampling

```
membershipLift.comp localLift
```

(pick a `Membership` uniformly among those carrying the macrostate's marked
count `k = commanderLeftCount x`, then resample a `Deck` uniformly inside that
membership's `50! · 49!` fiber) is exactly the direct `project`-fiber uniform
resampling

```
FiberDisintegration.fiberLaw project project_surjective .
```

Both are `FiniteKernel CommanderState Deck`. The mathematical claim: resampling
in two stages (membership, then local) is the same law as resampling directly
uniformly on the `project` fiber, because that fiber is the disjoint union of the
membership fibers and every membership fiber has the same cardinality.

## 2. Status: the statement elaborates; the proof is down to ONE mechanical step

**The capstone statement elaborates without issue.** Verified:

- `#check (FiberDisintegration.fiberLaw project project_surjective)` →
  `FiniteKernel CommanderState Deck`.
- `theorem t : comp membershipLift localLift = fiberLaw project project_surjective := by sorry`
  compiles (only the `sorry` warning).

So this is **not** a statement-level problem. The `Fintype (Equiv.Perm (Fin 99))`,
`DecidableEq`, and `Nonempty` instances for `Deck` all synthesize.

I have a **compiling proof skeleton** for the *point-mass* form of the law that
reduces the goal to a single remaining gap. The skeleton (all steps below compile):

1. **LHS → two-level sum.** `comp K L x = apply (K x) L` by `rfl` (one beta step),
   then the compiled `apply_mass_eq_sum` (Finsupp-Fubini, proved at *generic* `β`)
   gives
   ```
   mass (comp membershipLift localLift x) d
     = ∑ m : Membership, mass (membershipLift x) m * mass (localLift m) d .
   ```
   This step **does not recurse** (it instantiates a compiled theorem; no
   `Equiv.Perm` reduction).

2. **RHS → `fiberLaw_mass`.** `rw [FiberDisintegration.fiberLaw_mass]` (a compiled
   `@[simp]`-style lemma) gives
   ```
   mass (fiberLaw project project_surjective x) d
     = if project d = x then ((fiberSet project x).card : Rat)⁻¹ else 0 .
   ```
   This `rw` **does not recurse** (targeted rewrite of a compiled lemma).

The **only** remaining step is collapsing the two-level sum in (1):

```
∑ m : Membership, mass (membershipLift x) m * mass (localLift m) d
  = mass (membershipLift x) (membership d) * mass (localLift (membership d)) d .
```

The reason this is the whole game: the `localLift` row at `d` is a **selector** —
`mass (localLift m) d = 0` unless `m = membership d`, and
`1/(50!·49!)` (a *constant*, since every membership fiber has the same
cardinality, `fiberSet_membership_card`) when `m = membership d`. So the sum is
supported on the single membership `membership d`.

Once that collapse is in hand, the rest is light `Nat`/`Rat` work:

- `membershipFiber_iff`: `project d = x  ↔  membershipCount (membership d) = k`
  (both sides light — `Fin 50` and `Nat` equalities).
- `fiberSet_card`: `(fiberSet project x).card = membershipFiberCount k · 50! · 49!`.
- `1/a · 1/b = 1/(a·b)` by `field_simp`/`ring` over `Rat`.

## 3. What recurses and what does not (measured by isolated probes)

**Recurses** (200 000-heartbeat `whnf` / max-recursion timeouts):

- The `funext` / `ext` / `apply funext` / `refine funext` **tactics** applied to a
  `Dist Deck` (`StdSimplex Rat Deck`) or `FiniteKernel … Deck` **equality**. The
  `ext`/`funext` lemma-search normalizes the `StdSimplex`/`Finsupp` type, which
  pulls in the `Fintype (Equiv.Perm (Fin 99))` / `DecidableEq` instances — huge
  terms. Even a *self*-equality `fiberLaw project … = fiberLaw project …` recurses
  under `ext`.
- Consequently the *kernel-equality* form of the capstone cannot be finished with
  the usual `funext; ext` — the final `Dist Deck` extensionality step recurses.

**Does NOT recurse** (safe to use):

- `by_cases h : membership d = m` under `classical` (a `Membership` =
  `Finset (Fin 99)`-subtype equality). Tested in isolation; compiles.
- `by_cases` on `Nat` equalities (`membershipCount m = k`).
- `rw` of the **compiled** lemmas `localLift_mass`, `membershipLift_mass`,
  `fiberLaw_mass`, `apply_mass_eq_sum` — these are pre-reduced; applying them does
  not re-normalize the heavy terms.
- The **filter cardinality** over a membership equality:
  ```
  (Finset.univ.filter (fun m : Membership => m = membership d)).card = 1
  ```
  proved by `Finset.ext` + `Finset.card_singleton`; compiles, no recursion.
- The `rfl` bridge `comp K L x = apply (K x) L`.

**Net:** the mathematical content is provable entirely at the `mass`/`Rat` level,
avoiding the recursing `Dist Deck` extensionality. The only obstacle is the
mechanical two-level sum collapse in §2.

## 4. The exact remaining gap

The collapse is the `Fintype`-sum point-mass fact. The cleanest reduction I have
landed on is:

```
(∑ m : Membership, (if m = membership d then (1 : Rat) else 0)) = 1        (* P *)
```

because then, writing `A(m) = mass (membershipLift x) m` and `C = 1/(50!·49!)`,

```
∑ m, A(m) * (if m = membership d then C else 0)
  = C * (∑ m, (if m = membership d then A(m) else 0))        -- ite distributes
  = C * (∑ m, (if m = membership d then A(membership d) else 0))  -- A(m)=A(·) on support
  = C * A(membership d) * (∑ m, (if m = membership d then 1 else 0))
  = C * A(membership d)                                        -- by (P)
  = mass (membershipLift x) (membership d) * mass (localLift (membership d)) d .
```

`(* P *)` reduces, via `FiberDisintegration.sum_if_constant`, to exactly the
non-recursing filter-cardinality fact in §3:

```
(∑ m, (if m = a then 1 else 0))
  = ((Finset.univ.filter (fun m => m = a)).card : Rat) * 1
  = 1 * 1 = 1 .
```

The **only** thing not yet clicking is the definitional plumbing: the `Fintype`
sum notation `∑ m : Membership, …` versus `Finset.sum (Finset.univ : Finset
Membership) …`, and getting `sum_if_constant`'s `p`-argument to unify with the
inline `if m = membership d` (a lambda-matching hiccup in `rw`). I have written
candidate proofs that fail only on this plumbing (a `show`-pattern mismatch /
"Invalid rewrite argument: metavariable"), **not** on recursion.

## 5. Concrete questions for GPT

1. **The exact lemma sequence.** What is the minimal `rw`/`simp`/`ring` sequence,
   with correct Mathlib lemma names, to turn
   ```
   (∑ m : Membership, A m * (if m = membership d then C else 0))
   ```
   into `A (membership d) * C`, using only non-recursing operations
   (`Finset.sum_congr`, `Finset.sum_filter`, `FiberDisintegration.sum_if_constant`,
   `Finset.sum_singleton`, `Finset.card_singleton`, `ring`)? In particular, what is
   the canonical way to bridge the `Fintype` sum `∑ m : Membership, …` to
   `Finset.sum (Finset.univ …)` and to make `sum_if_constant`'s `p` unify with the
   inline membership-equality `ite`?

2. **A one-shot lemma.** Is there a single Mathlib lemma — a `Fintype`-level
   "sum of a point mass is 1", or a `sum_ite` over a `Fintype` — that does this in
   one step, avoiding the definitional bridge? (I have searched for
   `Finset.sum_ite` / `sum_ite_self_eq` and found only the `Finsupp` versions.)

3. **Which form is the deliverable.** Is it acceptable to state the F2c-iv-b
   capstone as the **point-mass** equality
   ```
   mass (comp membershipLift localLift x) d
     = mass (fiberLaw project project_surjective x) d
   ```
   (which I believe is fully provable once §4 is in), rather than the **kernel**
   equality `comp membershipLift localLift = fiberLaw project project_surjective`
   (whose proof needs a final `funext` + `ext` over `Dist Deck` — the recursing
   operation, §3)? If the point-mass form is the acceptable statement, that
   unblocks the mathematical content; the kernel-equality form can be recorded as
   blocked on the `Dist Deck` extensionality wall, with a note that the two are
   equivalent by function+`StdSimplex` extensionality (a step the current
   Mathlib build times out on).

## 6. Files involved

- `Shufflemath/CommanderMembershipKernels.lean` — `Membership`, `membership`,
  `membershipLift`, `localLift`, `apply_mass_eq_sum`, the `*_mass` lemmas,
  `fiberSet_membership_card`, `membershipFiberCount`.
- `Shufflemath/FiberDisintegration.lean` — `fiberSet`, `fiberLaw`,
  `fiberLaw_mass`, `sum_if_constant`.
- `Shufflemath/CommanderFiberWitness.lean` — `project_surjective`.
- `Shufflemath/CommanderPermutation.lean` — `project`, `leftCards`,
  `leftOriginalCount`.
- `Shufflemath/BernoulliLaplace.lean` — `CommanderState = Fin 50`,
  `commanderLeftCount x = x.val + 1`.
