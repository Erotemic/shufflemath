module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderMembershipExchange
public import Shufflemath.CommanderMarkedRightCount
public import Shufflemath.BernoulliLaplace
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open BernoulliLaplace
open CommanderPermutation
open CommanderMembershipKernels
open CommanderMembershipExchange
open CommanderMarkedRightCount
open Finset

/-  Sum  over  the  P-filter  =  ite-0-guarded  sum  over  the  same  base  Finset:
    `∑  x  ∈  s  .filter  P,  f  x  =  ∑  x  ∈  s,  (if  P  x  then  f  x  else  0)`.

    This  is  the  A3  capstone  h3  bridge  (  `cFiberMass_eq_iteMass`  ):  it  connects  the
    c-fiber  Finset  sum  `∑  m'  ∈  cFiber  c,  Dist.mass  (rawExchangeMembership  d)  m'`
    to  the  ite-0-guarded  form  that  `CommanderA3Mass.rawExchange_membershipCount_mass`
    (part  (i)  )  states.  Together  with  the  (  committed  ,  75th  session  )  f4  crack
    `a3_countBridge`  and  `exchangeChoice_card_eq_transitionDenominator`  ,  this  discharges
    h3  of  `mu_x_countFiberTotal`  .

    PROOF  (  76th  session  ,  cracked  this  session  )  :  `Finset  .induction`  on  the  base
    Finset  `s`  .  The  naive  disjoint  -union  decomposition  (  `s  =  filter  P  ⊔  filter
    (¬P)`  )  hits  the  `∑  zeros  =  0`  nsmul  -normalization  wall  (  the  sum  of  a  constant
    0  over  an  arbitrary  Finset  does  not  reduce  under  `simp`  /  `ring  _norm`  /
    `nsmul  _zero`  ,  for  a  general  `[AddCommMonoid  β]`  )  .  The  induction  sidesteps  it:
      -  base  (  `s  =  ∅`  )  :  both  sides  are  the  empty  sum  =  0  (  `simp`  )  ;
      -  insert  (  `s  =  insert  a  u`  ,  `a  ∉  u`  )  :  `by  _cases  P  a`  .
          `P  a`  :  `a`  enters  the  filter  and  the  ite  contributes  `f  a`  to  both  sides
            (  `Finset  .filter  _insert  P  a  u`  +  `Finset  .sum  _insert`  +  `if  _pos  hp`  )  ;
          `¬P  a`  :  `a`  drops  out  of  the  filter  and  the  ite  contributes  0  to  the  sum
            (  `Finset  .filter  _insert  P  a  u`  +  `Finset  .sum  _insert`  +  `if  _neg  hp`  +
            `zero  _add`  )  .
          In  both  sub  -cases  the  remaining  difference  is  exactly  the  induction
          hypothesis  (  on  `u`  )  .  `a  ∉  u  .filter  P`  follows  from  `a  ∉  u`  (  the
          filter  is  a  subset  of  its  base  )  .  -/
theorem sum_filter_eq_sum_ite (P : α → Prop) (s : Finset α) (f : α → β) [DecidableEq α]
    [DecidablePred P] [AddCommMonoid β] :
    ∑ x ∈ s.filter P, f x = ∑ x ∈ s, (if P x then f x else 0) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert a u ha ih =>
      by_cases hp : P a
      · --  `P  a`  :  `a`  enters  the  filter  and  the  ite  contributes  `f  a`  to  both  sides
        have hf : (insert a u).filter P = insert a (u.filter P) := by
          simpa [hp] using Finset.filter_insert P a u
        have notin : a ∉ u.filter P := fun h => ha (Finset.mem_filter.mp h |>.1)
        rw [hf, Finset.sum_insert notin, Finset.sum_insert ha]
        simp [hp, ih]
      · --  `¬P  a`  :  `a`  drops  out  of  the  filter  and  the  ite  contributes  0  to  the  sum
        have hf : (insert a u).filter P = u.filter P := by
          simpa [hp] using Finset.filter_insert P a u
        rw [hf, Finset.sum_insert ha]
        simp [hp, ih]

end Shufflemath
end
