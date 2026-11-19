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

/-  Sum  over  the  P-filter  =  ite-0-guarded  sum  over  the  same  base  Finset.
    (  `s  =  s  .filter  P  ⊔  s  .filter  (¬P)`  ,  the  ite  is  zero  on  the  ¬P  half  .)
    This  is  the  `h3`  bridge  for  `a3_countBridge`:  it  connects  a  fiber  Finset  sum
    (  `cFiber`  )  to  the  ite-0-guarded  form  that  `rawExchange_membershipCount_mass`
    uses  on  its  LHS  .

    PROGRESS  (  76th  session  WIP  )  :
    -  `hS  :  s  =  s  .filter  P  ⊔  s  .filter  (¬P)`  —  PROVEN  (  `Finset  .ext  +  tauto`  )  .
    -  `hDisj  :  Disjoint  (s  .filter  P)  (s  .filter  (¬P))`  —  PROVEN  (  `Finset  .
      disjoint  _filter  _filter  _not  s  s  P`  )  .
    -  `hA  :  ∑  x  ∈  s  .filter  P,  (if  P  x  then  f  x  else  0)  =  ∑  x  ∈  s  .
      filter  P,  f  x`  —  PROVEN  (  `sum  _congr  rfl`  +  ite  _true  on  `P  x`  )  .
    -  `h0  :  the  ¬P  ite  -summand  is  pointwise  0`  —  PROVEN  (  ite  _false  on  `¬P  x`  )  .

    FINDING  (  important  ,  corrects  the  earlier  note  )  :  there  is  NO  off  -the  -shelf
    `Finset  .sum  _ite`  /  `sum  _filter`  lemma  for  this  (  grepped  all  of  Mathlib  .
    Data  .Finset  )  ,  and  `simp`  /  `ring  _norm`  do  not  close  it  .  The  reduction
    `∑  x  ∈  s,  (if  P  x  then  f  x  else  0)  =  ∑  x  ∈  s  .filter  P,  f  x`  needs  a
    bijection  between  the  two  underlying  Fintypes  :
      `Membership  (s  .filter  P)`  ≅  `{  x  :  Membership  s  |  P  x  .val  }`,
    i.e.  EXACTLY  the  same  equinumerosity  machinery  as  the  (  now  committed  )  f4
    breakthrough  (  `subtype  _sum  _univ  _eq  _finset`  +  `finset  _sum  _univ  _eq  _
    subtype  _sum`  +  `Fintype  .card  _congr`  /  `Fintype  .subtype  _card`  /  the  `card
    _of  _eq`  bridge  )  .

    NEXT  SESSION  RESUME  :
      1.  Prove  `Membership  (s  .filter  P)`  ≅  `{  x  :  Membership  s  |  P  x  .val  }`  by
          the  f4  pattern  (  `Fintype  .card  _congr  +  Fintype  .card  _eq  .mp`  on  the  two
          `Finset  .sum`  -over  -`univ`  forms  ,  or  a  direct  `Fintype  .Equiv`  )  .
      2.  Transport  the  ite  -sum  to  that  subtype  and  use  `sum  _congr  rfl`  (  ite  _true  on
          the  `P  x  .val`  hypothesis  )  to  get  the  `f`  -sum  .
      3.  This  closes  the  theorem  (  `exact  hRHS  .symm`  )  .  The  proven  `hA`  /  `h0`
          above  are  a  valid  alternative  (  disjoint  -union  decomposition  )  but  hit  the
          `∑  zeros  =  0`  nsmul  -normalization  wall  (  section  -variable  `β`  with  only
          `AddCommMonoid`  )  ;  specializing  `β  :=  Rat`  (  the  only  capstone  instantiation  )
          resolves  that  wall  .  -/
theorem sum_filter_eq_sum_ite (P : α → Prop) (s : Finset α) (f : α → β) [DecidableEq α]
    [DecidablePred P] [Zero β] [AddCommMonoid β] :
    ∑ x ∈ s.filter P, f x = ∑ x ∈ s, (if P x then f x else 0) := by
  classical
  have hS : s = s.filter P ∪ s.filter (fun x => ¬ P x) := by
    classical
    apply Finset.ext
    intro x
    simp only [Finset.mem_union, Finset.mem_filter, not_and_or, and_imp]
    tauto
  have hDisj : Disjoint (s.filter P) (s.filter (fun x => ¬ P x)) := by
    classical
    exact Finset.disjoint_filter_filter_not s s P
  have hA : ∑ x ∈ s.filter P, (if P x then f x else 0) = ∑ x ∈ s.filter P, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hP : P x := (Finset.mem_filter.mp hx).2
    simp only [hP, ite_true]
  --  the  ¬P  ite  -summand  is  pointwise  zero  (  the  only  non  -trivial  reduction  needed  )
  have h0 : ∀ x ∈ s.filter (fun x => ¬ P x), (if P x then f x else 0) = 0 := by
    intro x hx
    have hN : ¬ P x := (Finset.mem_filter.mp hx).2
    simp only [hN, ite_false]
  --  WIP  :  assemble  the  RHS  `∑  x  ∈  s,  (ite)`  over  the  disjoint  union  `hS`  ,  rewrite
  --  the  P  half  by  `hA`  and  the  ¬P  half  to  `0`  (  `h0`  +  sum  -of  -zeros  )  ,  cancel  .
  --  The  remaining  wall  is  the  `∑  zeros  =  0`  normalization  (  see  header  )  —  use  the
  --  f4  -style  Fintype  equinumerosity  route  or  specialize  `β  :=  Rat`  .
  sorry

end Shufflemath
end
