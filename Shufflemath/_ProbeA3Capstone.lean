module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderFiberMembership
public import Shufflemath.Finite
public import Shufflemath.FinsetCombinatorics
public import Shufflemath._ProbeA3Cap4
public import Shufflemath._ProbeA3Cap4b
public import Shufflemath.CommanderA3Mass
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

-- (73rd-session note) Next clean micro-step for h3: a helper `cFiberMass_eq_iteMass`  (cFiber mass
--  =  ite-0-guarded mass, so `CommanderA3Mass.rawExchange_membershipCount_mass` applies to a
--  `∑ m' ∈ cFiber c, …` LHS) needs the right Finset filter/ite identity (NOT the looping `sum_ite`
--  simp lemma).  Then h3 = `rw [cFiberMass_eq_iteMass, rawExchange_membershipCount_mass]` + the f4
--  equinumerosity below.

--  NOTE: the `if`-guarded c-fiber mass identity needs a filter/`ite` sum lemma that the current
--  Mathlib does not expose as a matching `rw` pattern (`Finset.sum_ite` does not fire on
--  `∑ x ∈ s, (if P x then g x else 0)`); settle it next session via a short `Finset.induction`
--  (base `∅`, step on `insert`, one `by_cases P a`) or a `Finset.sum_bij` between `s.filter P` and
--  `{x ∈ s // P x}`.  Then h3 = `rw [cFiberMass_eq_iteMass, rawExchange_membershipCount_mass]` + the
--  f4 count-bridge equinumerosity below (the one remaining deep A3 wall).


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
    classical
    set P := fun (m : Membership) => membershipCount m = c
    set f := fun (m : Membership) => Dist.mass (rawExchangeMembership d) m
    --  (a)  the  cFiber  Finset  sum  =  the  ite  -0  -guarded  sum  over  univ  (  `sum  _filter  _eq  _sum  _ite`  ,
    --       76th  -session  crack  ,  `Shufflemath  /  _ProbeA3Cap4b  .lean`  )
    rw [cFiber, sum_filter_eq_sum_ite P (Finset.univ : Finset Membership) f]
    --  (b)  the  univ  -Finset  sum  and  the  Fintype  sum  are  definitionally  the  same  (  `Fintype  .sum  =  Finset  .sum  univ`  )  ,
    --       so  `rawExchange  _membershipCount  _mass`  (  part  (i)  )  applies  :  =  (1  /  #EC)  ·  #  {j  //  Pmem  d  c  j  }
    rw [rawExchange_membershipCount_mass d c]
    --  (c)  #  {j  //  Pmem  d  c  j  }  =  #  (pfiber  d  c)  =  transitionNumerator  (leftOriginalCount  d)  c
    --       (  `a3  _countBridge`  ,  75th  )  ,  and  #EC  =  transitionDenominator  (  `exchangeChoice  _card  _eq  _transitionDenominator`  )  ,
    --       and  `transitionWeight  =  transitionNumerator  /  transitionDenominator`
    have hEC : (Fintype.card exchangeChoice : Rat) = (transitionDenominator 99 50 25 : Rat) :=
      exchangeChoice_card_eq_transitionDenominator
    have hNum : (Fintype.card (pfiber d c) : Rat) = (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat) := by
      exact_mod_cast a3_countBridge d c
    rw [hEC]
    --  the  rawExchange  count  -fiber  set  `{j  :  exchangeChoice  //  count  (...)  =  c}`  is  definitionally
    --  `pfiber  d  c`  (  `Pmem  d  c  j`  is  an  `abbrev`  of  that  exact  condition  ,  so  the  two  subtypes
    --  are  `rfl`  -equal  and  their  cards  are  `rfl`  -equal  ;  no  simp  on  `Pmem`  needed  ,  which  recurses  )
    have hCard : (Fintype.card {j : exchangeChoice // membershipCount (newMembership d j.1.1 (leftCard25 j.1.2) j.2.1 (rightCard25 j.2.2)) = c} : Rat) =
        (Fintype.card (pfiber d c) : Rat) := by rfl
    rw [hCard, hNum]
    --  goal  :  `B⁻¹  *  A  =  transitionWeight`  where  `A  =  transitionNumerator`  and  `B  =  transitionDenominator`  ;
    --  `transitionWeight  :=  A  /  B  =  A  *  B⁻¹  =  B⁻¹  *  A`  (  `Rat  .div  _def`  +  `mul  _comm`  )  ,  in  the  goal  's  order
    have hw : transitionWeight 99 50 25 (leftOriginalCount d) c =
        (transitionDenominator 99 50 25 : Rat)⁻¹ * (transitionNumerator 99 50 25 (leftOriginalCount d) c : Rat) := by
      unfold transitionWeight
      rw [Rat.div_def]
      rw [mul_comm]
    exact hw.symm
  -- (4) on the project fiber, leftOriginalCount d = commanderLeftCount x, so the weighted summand
  --     equals the constant (fiberLaw mass 0 off the fiber, and equal transitionWeight on it)
  have h4 : (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d *
          transitionWeight 99 50 25 (leftOriginalCount d) c) =
      transitionWeight 99 50 25 (commanderLeftCount x) c *
        (∑ d : Deck, Dist.mass (fiberLaw project project_surjective x) d) := by
    --  term  -wise  :  on  the  fiber  (  `project  d  =  x`  )  ,  `leftOriginalCount  d  =  commanderLeftCount  x`
    --  point  -wise  point  -mass  identity  as  a  separate  `have`  (  so  the  `by  _cases`  elaborates  in  isolation
    --  ,  avoiding  the  recursion  of  `apply  Finset  .sum  _congr`  on  a  product  -RHS  goal  )  .  On  the  fiber
    --  (  `project  d  =  x`  )  ,  `leftOriginalCount  d  =  commanderLeftCount  x`  (  `project  _eq  _iff  _leftOriginalCount`
    --  )  so  the  transitionWeight  is  the  fiber  -independent  constant  and  only  the  mass  position  differs
    --  (  `mul  _comm`  )  ;  off  the  fiber  the  fiberLaw  mass  is  0  (  `fiberLaw  _mass`  )  so  both  sides  vanish  .
    have hPoint (d : Deck) :
        Dist.mass (fiberLaw project project_surjective x) d * transitionWeight 99 50 25 (leftOriginalCount d) c =
          transitionWeight 99 50 25 (commanderLeftCount x) c * Dist.mass (fiberLaw project project_surjective x) d := by
      by_cases hf : project d = x
      · have hLO : leftOriginalCount d = commanderLeftCount x :=
          (project_eq_iff_leftOriginalCount d x).mp hf
        rw [hLO]
        apply mul_comm
      · have h0 : Dist.mass (fiberLaw project project_surjective x) d = 0 := by
          simp [fiberLaw_mass, hf]
        simp [h0]
    --  (1)  pointwise  transform  the  LHS  sum  (  `Finset  .sum  _congr`  )  ;  (2)  pull  the  d  -independent  constant
    --  out  of  the  sum  (  `Finset  .mul  _sum`  )  .
    rw [Finset.sum_congr rfl fun d _ => hPoint d, Finset.mul_sum]
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
