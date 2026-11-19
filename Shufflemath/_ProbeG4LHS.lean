module
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.BernoulliLaplaceGeneral
public import Shufflemath.Finite
@[expose] public section

namespace Shufflemath
namespace FiniteDeck
open BernoulliLaplaceGeneral

/-- Mass body of the fiber-uniform membership lift (base form, `rfl` unfold). -/
theorem uniformCountFiberMembership_mass (p : ExchangeAdmissible)
    (x : BLState p.N p.m p.r) (j : Membership p.N p.m) :
    (uniformCountFiberMembership p x).mass j =
      (if (countInPile p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j).val = x.val
        then (1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card else 0) := by
  dsimp only [uniformCountFiberMembership, Dist.ofFun, Dist.mass]
  rfl

/-- Mass body of the fiber-uniform membership lift, in `ite` form over the marked-count fiber. -/
theorem uniformCountFiberMembership_mass_ite (p : ExchangeAdmissible)
    (x : BLState p.N p.m p.r) (j : Membership p.N p.m) :
    (uniformCountFiberMembership p x).mass j =
      (if (countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN j) = x.val
        then (1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card else 0) := by
  dsimp only [uniformCountFiberMembership, Dist.ofFun, Dist.mass, countInPile]
  rfl

/-- Mass body of the subset-exchange kernel (base form, `rfl` unfold). -/
theorem subsetExchangeMembershipKernel_mass (p : ExchangeAdmissible)
    (j : Membership p.N p.m) (S : Membership p.N p.m) :
    (subsetExchangeMembershipKernel p j).mass S =
      subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm j.1 S.1 := by
  dsimp only [subsetExchangeMembershipKernel, Dist.ofFun, Dist.mass]
  rfl

/-- Mass body of the subset-exchange kernel, in `ite` form over the `ReachSet` of S. -/
theorem subsetExchangeMembershipKernel_mass_ite (p : ExchangeAdmissible)
    (j : Membership p.N p.m) (S : Membership p.N p.m) :
    (subsetExchangeMembershipKernel p j).mass S =
      (if j ∈ ReachSet p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm S
        then (transitionDenominator p.N p.m p.k : Rat)⁻¹ else 0) := by
  have hK (j : Membership p.N p.m) (S : Membership p.N p.m) :
      (subsetExchangeMembershipKernel p j).mass S =
        subsetExchangeKernel p.N p.m p.k (Nat.le_of_lt p.hmn) p.hkm p.hknm j.1 S.1 := by
    dsimp only [subsetExchangeMembershipKernel, Dist.ofFun, Dist.mass]
    rfl
  rw [hK, subsetExchangeKernel, transitionDenominator]
  dsimp only [ReachSet]
  simp only [Finset.mem_filter, Finset.mem_univ, j.2, S.2, and_true, true_and]
  by_cases h : (j.1 \ S.1).card = p.k ∧ (S.1 \ j.1).card = p.k
  <;> simp [h, and_comm]

/-- Mass body of the Bernoulli-Laplace exchange kernel (transition weight, `rfl` unfold). -/
theorem blExchangeKernel_mass (p : ExchangeAdmissible)
    (x : BLState p.N p.m p.r) (j : BLState p.N p.m p.r) :
    (blExchangeKernel p x).mass j =
      transitionWeight p.N p.m p.r p.k x.val j.val := by
  dsimp only [blExchangeKernel, Dist.ofFun, Dist.mass]
  rfl

end FiniteDeck
end Shufflemath
