module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.Finite
public import Shufflemath.FinsetCombinatorics
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open CommanderPhysicalExchange
open FiberDisintegration
open CommanderMembershipExchange
open Finset
open Fintype

/-!
## A3 capstone assembly (71st session) — the concrete `hMembershipExchange`

The final A3 discharge is the kernel equality

```
comp (fiberLaw project project_surjective) rawExchangeMembership = comp commanderExchange25 membershipLift
```

(i.e. the `hMembershipExchange` premise of `PhysicalExchangeReduction.intertwining_of_membership_exchange`).
It is a **clean, non-walled assembly** of already-proven lemmas — the f4 count-bridge wall does not
apply here (part (i) already bypassed it via `fintypeCard_subtypeCongr` + `Fintype.card_of_subtype`):

  LHS mass at `m` (count `c`) = (constant on the `c`-fiber, `mu_x_constant_on_countFiber`)
                                = (fiber total, `mu_x_fiberSum` + part (i) `rawExchange_membershipCount_mass`
                                   + `newLeftCount_deckIndependent`) / `membershipFiberCount c`
                              = `transitionWeight 99 50 25 (commanderLeftCount x) c / membershipFiberCount c`
                              = RHS mass (`hMembershipExchange_rhs_mass`).

This probe develops the pieces incrementally (safe: a new file, not in the aggregator, so the
tree stays green).  `mu_x_fiberSum` is the first, self-contained piece.
-/

/-- The post-exchange membership law `mu_x`: push the fiber-uniform law of the source macro
    state `x` forward through the physical (raw) membership-exchange kernel.  This is the
    left-hand side of the A3 `hMembershipExchange` equality. -/
noncomputable def mu_x (x : CommanderState) : Dist Membership :=
    (FiniteKernel.comp (fiberLaw project project_surjective) rawExchangeMembership) x

/-- The `c`-fiber of the marked left-card count. -/
noncomputable def cFiber (c : Nat) : Finset Membership :=
    (Finset.univ : Finset Membership).filter (fun m => membershipCount m = c)

/-- **Fiber-sum lemma.**  Because `mu_x` is constant on each count fiber
    (`mu_x_constant_on_countFiber`), the total mass it puts on the `c`-fiber of a membership
    `m` (count `c = membershipCount m`) is the fiber size `membershipFiberCount c` times the
    point mass at `m`.  Combined with part (i) this recovers the fiber *average* = the BL
    transition weight, the distributional core of the `hMembershipExchange` discharge. -/
theorem mu_x_fiberSum (x : CommanderState) (m : Membership) :
    (∑ m' ∈ cFiber (membershipCount m), Dist.mass (mu_x x) m') =
      (membershipFiberCount (membershipCount m) : Rat) * Dist.mass (mu_x x) m := by
  set c := membershipCount m
  -- every element of the `c`-fiber has mass `mu_x m` (same count => equal mass)
  have hConst (m' : Membership) (hm' : m' ∈ cFiber c) : Dist.mass (mu_x x) m' = Dist.mass (mu_x x) m := by
    simp only [cFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hm'
    exact mu_x_constant_on_countFiber x m' m hm'
  rw [Finset.sum_congr rfl fun m' hm' => hConst m' hm']
  -- the sum of a constant over the fiber is the fiber card times that constant
  simp only [cFiber]
  rw [Finset.sum_const]
  -- nsmul of a Rat by a Nat is the Nat-cast times the value
  rw [nsmul_eq_mul]
  -- the fiber card is `membershipFiberCount c`
  rw [membershipFiber_card c]

/-- A `Finset` × `Fintype` double-sum swap: reordering two iterated sums (a `Finset` on the
    outside, a `Fintype` on the inside) does not change the sum.  Proved by induction on the
    `Finset`, so it never computes `Finset.univ` of the (possibly huge) `Fintype` — this unblocks
    the A3 `h2` Fubini, whose product-set/bijection form recursed on `Finset.univ : Finset Deck`.
    (The `Fintype.sum_mul_sum` / `Finset.sum_mul_sum` factored forms do not fit a 2-D integrand.) -/
theorem finset_fintype_sum_swap (s : Finset Membership) (f : Membership → Deck → Rat) :
    (∑ m' ∈ s, ∑ d : Deck, f m' d) = ∑ d : Deck, ∑ m' ∈ s, f m' d := by
  classical
  induction s using Finset.induction with
  | empty =>
      -- LHS = ∑ m' ∈ ∅, … = 0;  RHS = ∑ d, ∑ m' ∈ ∅, f m' d = ∑ d, 0 = 0
      simp
  | insert m s' hm ih =>
      -- Walk LHS → RHS in four single-step rewrites (all pure / structural — no `Finset.univ`
      -- computation, so no recursion on the 99^13 `Deck` Fintype):
      calc
        -- (a) expand `m` out of the LHS outer sum
        (∑ m' ∈ insert m s', ∑ d : Deck, f m' d) =
            (∑ d : Deck, f m d) + ∑ m' ∈ s', ∑ d : Deck, f m' d := by
          rw [Finset.sum_insert hm]
        -- (b) IH: swap the two sums on the second summand (both now over `s'`)
        _ = (∑ d : Deck, f m d) + ∑ d : Deck, ∑ m' ∈ s', f m' d := by
          rw [ih]
        -- (c) distribute the `+` back under the outer `∑ d`
        _ = ∑ d : Deck, (f m d + ∑ m' ∈ s', f m' d) := by
          rw [← Finset.sum_add_distrib]
        -- (d) re-collapse the inner `insert m s'` (pointwise under the outer `∑ d`)
        _ = ∑ d : Deck, ∑ m' ∈ insert m s', f m' d := by
          congr
          funext d
          -- forward `sum_insert` rewrites the RHS `∑ m' ∈ insert m s', f m' d` to the LHS form
          rw [Finset.sum_insert hm]

/-- **Deck-averaging lemma (crux of the A3 `hMembershipExchange` discharge).**  The total
    mass `mu_x` puts on the `c`-fiber equals the Bernoulli–Laplace transition weight from the
    source count `commanderLeftCount x` to `c`.  Reason: `mu_x x` is the uniform fiberLaw over
    the project-fiber of decks `d` (all with `leftOriginalCount d = commanderLeftCount x`) pushed
    through the raw membership exchange; each such deck's c-fiber mass is the deck-independent
    count law `(1 / #exchangeChoice) · #{j // count (newMembership d j) = c}` =
    `transitionWeight (leftOriginalCount d) c` (part (i) + `newLeftCount_eq_transitionNumerator`
    + `exchangeChoice_card_eq_transitionDenominator`), constant on the fiber, so the fiberLaw
    (a probability) average leaves it unchanged. -/
theorem mu_x_countFiberTotal (x : CommanderState) (c : Nat) :
    (∑ m' ∈ cFiber c, Dist.mass (mu_x x) m') =
      transitionWeight 99 50 25 (commanderLeftCount x) c := by
  -- (1) expand the `comp` mass: `mu_x x` = fiberLaw pushed through the raw exchange (apply_mass)
  have h1 : (∑ m' ∈ cFiber c, Dist.mass (mu_x x) m') =
      ∑ m' ∈ cFiber c, ∑ d : Deck,
        Dist.mass (fiberLaw project project_surjective x) d * Dist.mass (rawExchangeMembership d) m' := by
    -- (h1) unfold `comp`/`apply` (definitionally equal: comp K L x = ((K x).map L).join = apply (K x) L)
    --   and apply `apply_mass` to write (mu_x x).mass m' = ∑ d, (fiberLaw x).mass d · (rawExchange d).mass m'.
    apply Finset.sum_congr rfl
    intro m' _
    rw [mu_x, FiniteKernel.comp, ← FiniteKernel.apply]
    rw [FiniteKernel.apply_mass]
  -- (2) Fubini: pull the fiberLaw weight out of the c-fiber sum.
  --     ∑ m' ∈ S, ∑ d, (w d · f m' d)  =  ∑ d, w d · ∑ m' ∈ S, f m' d.
  --     The 71st-session product-set/bijection form recursed on `Finset.univ : Finset Deck`;
  --     instead use the induction-based `finset_fintype_sum_swap` (no univ computation) on the integrand
  --     g m' d := w d · f m' d, then pull the (d-dependent, m'-independent) weight out via
  --     `Finset.mul_sum` pointwise under the outer `∑ d`.
  have h2 : (∑ m' ∈ cFiber c, ∑ d : Deck,
          Dist.mass (fiberLaw project project_surjective x) d * Dist.mass (rawExchangeMembership d) m') =
      ∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d *
        (∑ m' ∈ cFiber c, Dist.mass (rawExchangeMembership d) m') := by
    -- (i) Fubini swap:  ∑ m' ∈ S, ∑ d, (w d · f m' d)  =  ∑ d, ∑ m' ∈ S, (w d · f m' d)
    rw [finset_fintype_sum_swap]
    -- (ii) pull the fiberLaw weight  w d  out of the inner `∑ m' ∈ S`  (pointwise under `∑ d`)
    congr
    funext d
    rw [← Finset.mul_sum]
  -- (3) the inner c-fiber total of the raw exchange at deck d is the deck-independent count law
  --     = transitionWeight (leftOriginalCount d) c.
  --     WIP wall #2: the count-fiber equinumerosity
  --       #{j : exchangeChoice // count (newMembership d j) = c} = transitionNumerator (leftOriginalCount d) c,
  --     i.e. the exchangeChoice-indexed fiber ↔ the (leftChoices ×ˢ rightChoices)-indexed fiber (via
  --     `exchangeChoice_equiv_lr` + `count_exchangeChoice_eq_markedCount` + `newLeftOriginalCount_eq`),
  --     then `newLeftCount_eq_transitionNumerator`.  Part (i) already gives the (1/#EC)·#{j} form.
  have h3 (d : Deck) :
      (∑ m' ∈ cFiber c, Dist.mass (rawExchangeMembership d) m') =
        transitionWeight 99 50 25 (leftOriginalCount d) c := by
    -- WIP wall #2: part (i) gives (1/#EC)·#{j : exchangeChoice // count(newMembership d j) = c};
    --   the count-fiber equinumerosity #{j // ...} = transitionNumerator (leftOriginalCount d) c
    --   (exchangeChoice_equiv_lr + count_exchangeChoice_eq_markedCount + newLeftOriginalCount_eq
    --   + newLeftCount_eq_transitionNumerator) and #EC = transitionDenominator give the transitionWeight.
    sorry
  -- (4) on the project fiber, leftOriginalCount d = commanderLeftCount x, so the weighted summand
  --     equals the constant (fiberLaw mass 0 off the fiber, and equal transitionWeight on it)
  have h4 : (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d *
          transitionWeight 99 50 25 (leftOriginalCount d) c) =
      transitionWeight 99 50 25 (commanderLeftCount x) c *
        (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d) := by
    -- WIP wall #3: term-wise, (fiberLaw x).mass d · TN (leftOriginalCount d) c =
    --   (fiberLaw x).mass d · TN (commanderLeftCount x) c  (on the fiber leftOriginalCount d =
    --   commanderLeftCount x; off it the mass is 0), then the constant pulls out of the sum.
    sorry
  -- (5) the fiberLaw is a probability (sums to 1) — mirror the `fiberLaw` `ofFun` normalization
  have h5 : (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d) = 1 := by
    calc
      _ = ∑ d : Deck, if project d = x then ((fiberSet project x).card : Rat)⁻¹ else 0 :=
          Finset.sum_congr rfl fun d _ => fiberLaw_mass project project_surjective x d
      _ = ((fiberSet project x).card : Rat) * ((fiberSet project x).card : Rat)⁻¹ := by
          simpa only [fiberSet] using
            sum_if_constant (Finset.univ : Finset Deck) (fun d => project d = x) (((fiberSet project x).card : Rat)⁻¹)
      _ = 1 := by
          have hnz : ((fiberSet project x).card : Rat) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (fiber_card_pos project project_surjective x)
          exact mul_inv_cancel₀ hnz
  -- assemble
  calc
    (∑ m' ∈ cFiber c, Dist.mass (mu_x x) m') =
        ∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d *
          (∑ m' ∈ cFiber c, Dist.mass (rawExchangeMembership d) m') := by rw [h1, h2]
    _ = ∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d *
          transitionWeight 99 50 25 (leftOriginalCount d) c := by
      apply Finset.sum_congr rfl
      intro d _
      exact congrArg (fun (t : Rat) => Dist.mass (fiberLaw project project_surjective x) d * t) (h3 d)
    _ = transitionWeight 99 50 25 (commanderLeftCount x) c * (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d) :=
        h4
    _ = transitionWeight 99 50 25 (commanderLeftCount x) c * 1 := by rw [h5]
    _ = transitionWeight 99 50 25 (commanderLeftCount x) c := by simp

end Shufflemath
end
