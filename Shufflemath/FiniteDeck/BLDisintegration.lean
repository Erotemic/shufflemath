module

public import Shufflemath.FiniteDeck.A3KernelLaw
public import Shufflemath.FiniteDeck.TwoPileFiber
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.GSR
public import Shufflemath.FiberDisintegration

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

variable {N m r : Nat} (p : BernoulliLaplaceGeneral.ExchangeAdmissible)

/-- The `FiberDisintegration` fiber of the `membership` observation at `A` is exactly the
    `Fiber` fiber `fiberSet N m hm A` (a deck has left pile `A.1` iff its membership is `A`). -/
theorem fiberSet_membership_eq (hm : p.m ≤ p.N) (A : Membership p.N p.m) :
    FiberDisintegration.fiberSet (membership p.N p.m hm) A =
      fiberSet p.N p.m hm A := by
  apply Finset.ext
  intro d
  simp only [FiberDisintegration.fiberSet, fiberSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [membership, Subtype.ext_iff]
  dsimp only [leftCards]
  exact Iff.rfl

/-- The UCFM pushforward of the BL stationary law is the marginal of the membership
    observation: `apply (blStationaryDist p) (UCFM p) = marginalLaw (membership N m hm)`.
    Both sides carry mass `1 / #Membership` on every membership `A`. -/
theorem blStationary_ucfm_eq_marginalMembership :
    FiniteKernel.apply (BernoulliLaplaceGeneral.blStationaryDist p)
      (uniformCountFiberMembership p) =
      FiberDisintegration.marginalLaw (membership p.N p.m (Nat.le_of_lt p.hmn)) := by
  let hm := Nat.le_of_lt p.hmn
  let hr := p.hrN
  ext A
  have hMemCard : (Fintype.card (Membership p.N p.m) : Rat) = (Nat.choose p.N p.m : Rat) := by
    rw [membershipCount p.N p.m hm]
  have hOneOverMem : 1 / (Fintype.card (Membership p.N p.m) : Rat) =
      1 / (Nat.choose p.N p.m : Rat) := by rw [hMemCard]
  -- ---------------- LHS ----------------
  have hLHS : Dist.mass (FiniteKernel.apply (BernoulliLaplaceGeneral.blStationaryDist p)
      (uniformCountFiberMembership p)) A = 1 / (Fintype.card (Membership p.N p.m) : Rat) := by
    let c (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) :=
      countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN A = x.val
    let g (x : BernoulliLaplaceGeneral.BLState p.N p.m p.r) : Rat :=
      BernoulliLaplaceGeneral.blStationary p.N p.m p.r x *
        ((1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card)
    rw [FiniteKernel.apply_mass_dom (BernoulliLaplaceGeneral.blStationaryDist p)
        (uniformCountFiberMembership p) A]
    -- ∑ j, blStationary j * (if c j then 1/#cfMemb j else 0); move the ite to the top
    simp only [BernoulliLaplaceGeneral.mass_blStationaryDist,
      uniformCountFiberMembership_mass_ite]
    have hTop : (∑ x : BernoulliLaplaceGeneral.BLState p.N p.m p.r,
        BernoulliLaplaceGeneral.blStationary p.N p.m p.r x *
          (if countInPileVal p.N p.m p.r (Nat.le_of_lt p.hmn) p.hrN A = x.val
            then (1 : Rat) / ↑(countFiberMemb p.N p.m p.r p.hrN x).card else 0)) =
        (∑ x : BernoulliLaplaceGeneral.BLState p.N p.m p.r, (if c x then g x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    rw [hTop, Finset.sum_ite]
    -- (∑ x ∈ univ.filter c, g x) + (∑ x ∈ univ.filter (¬c), 0); the (¬c) part is 0
    simp only [Finset.sum_const_zero]
    -- the support of c is exactly {countInPile A}
    have hSing : (Finset.univ : Finset (BernoulliLaplaceGeneral.BLState p.N p.m p.r)).filter c =
        {countInPile p.N p.m p.r hm hr A} := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
      refine Iff.intro ?_ ?_
      · intro h
        apply Subtype.ext
        exact h.symm
      · intro h
        rw [h]
        rfl
    -- ∑ x ∈ {countInPile A}, g x = g (countInPile A) = blStationary (countInPile A) * (1/#cfMemb (countInPile A))
    rw [hSing, Finset.sum_singleton]
    -- g (countInPile A) = blStationary (countInPile A) * (1/#cfMemb (countInPile A))
    -- = (#countFiber (countInPile A).val / #Membership) * (1/#cfMemb (countInPile A))
    dsimp only [g]
    rw [countFiber_blStationary hm hr (countInPile p.N p.m p.r hm hr A)]
    have hEq : (↑(Finset.card (countFiber p.N p.m p.r hm hr
        (countInPile p.N p.m p.r hm hr A).val)) : Rat) =
        (↑(Finset.card (countFiberMemb p.N p.m p.r hr (countInPile p.N p.m p.r hm hr A))) : Rat) := by
      simp [countFiber_eq_countFiberMemb p hm hr (countInPile p.N p.m p.r hm hr A)]
    rw [hEq]
    -- normalize both #Membership (target) and #pileSet (LHS) to #choose N m
    simp [membershipCount p.N p.m hm, pileSet, Finset.card_powersetCard, Nat.cast_mul, Nat.cast_one]
    -- #countFiberMemb (countInPile A) = choose r c * choose (N-r) (m-c) where c = (countInPile A).val;
    -- the admissibility bounds c ≤ min m r and c ≥ max (r-(N-m)) 0 make both binomials positive,
    -- so #cfMemb > 0, which is the nonzero fact field_simp needs.
    have hCFPos : 0 < (countFiberMemb p.N p.m p.r hr (countInPile p.N p.m p.r hm hr A)).card := by
      let c := (countInPile p.N p.m p.r hm hr A).val
      have hAdm := countInPile_admissible p.N p.m p.r hm hr A
      have hCard : (countFiberMemb p.N p.m p.r hr (countInPile p.N p.m p.r hm hr A)).card =
          p.r.choose c * (p.N - p.r).choose (p.m - c) := by
        rw [countFiberMemb_card p.N p.m p.r hm hr (countInPile p.N p.m p.r hm hr A)]
      rw [hCard]
      refine Nat.mul_pos ?_ ?_
      -- 0 < choose r c  (c ≤ min m r ≤ r)
      · dsimp only [BernoulliLaplaceGeneral.blHi] at hAdm
        have hcR : c ≤ p.r := Nat.le_trans hAdm.2 (Nat.min_le_right p.m p.r)
        exact Nat.choose_pos hcR
      -- 0 < choose (N-r) (m-c)  (c ≥ r-(N-m) implies m-c ≤ N-r)
      · dsimp only [BernoulliLaplaceGeneral.blLo] at hAdm
        have hcLo : p.r - (p.N - p.m) ≤ c := (Nat.max_le.mp hAdm.1).1
        have hmc : p.m - c ≤ p.N - p.r := by omega
        exact Nat.choose_pos hmc
    have hCFnz : (↑(countFiberMemb p.N p.m p.r hr (countInPile p.N p.m p.r hm hr A)).card : Rat) ≠ 0 :=
      (Nat.cast_pos.mpr hCFPos).ne'
    field_simp [hCFnz]
  -- ---------------- RHS ----------------
  have hRHS : Dist.mass (FiberDisintegration.marginalLaw (membership p.N p.m hm)) A =
      1 / (Fintype.card (Membership p.N p.m) : Rat) := by
    rw [FiberDisintegration.marginalLaw_mass, fiberSet_membership_eq p hm A, fiberSet_card p.N p.m hm A]
    -- goal: ↑(Fintype.card (FibType N m hm A)) / ↑(Fintype.card (Deck N)) = 1 / ↑(Fintype.card (Membership N m))
    have hDeck : (Fintype.card (Deck p.N) : Rat) =
        (Fintype.card (Membership p.N p.m) : Rat) * (Fintype.card (FibType p.N p.m hm A) : Rat) := by
      rw [deckCard_eq_membershipFiber p hm A]
      norm_cast
    have hNZdeck : 0 < (Fintype.card (Deck p.N) : Rat) := by
      rw [Nat.cast_pos, Fintype.card_pos_iff]
      exact ⟨Equiv.refl (Fin p.N)⟩
    have hNZmem : 0 < (Fintype.card (Membership p.N p.m) : Rat) := by
      rw [Nat.cast_pos, Fintype.card_pos_iff]
      exact ⟨⟨leftPositions p.N p.m hm, leftPositions_card p.N p.m hm⟩⟩
    field_simp [hDeck, hNZdeck, hNZmem]
    rw [hDeck]
    ring
  -- both sides = 1 / #Membership
  simp only [Shufflemath.Dist.mass] at hLHS hRHS
  rw [hLHS, hRHS]

/-- **G2.9 / G2.13 bridge.**  The BL stationary law lifted to the deck level by the
    macro lift (`uniformCountFiberMembership`) followed by the perfect-local resample
    (`localLift`) is exactly the uniform distribution on the full deck:
    `apply (blStationaryDist p) (comp (UCFM p) localLift) = GSR.uniformDist (Deck p.N)`.
    This is the *deck-uniform-target* mass formula the 99-card G2.9 / G2.13 headlines
    need.  It composes three already-proved facts — `apply_comp` (associativity of
    `apply` over `comp`), `blStationary_ucfm_eq_marginalMembership` (the macro lift of
    the BL stationary is the marginal of the *membership* observation), and
    `marginal_comp_fiber_eq_uniform` (the disintegration recovery: mixing the fiber laws
    by their relative sizes is uniform on the deck).  Because it uses the *membership*
    observation (which is surjective), it avoids the `project_surjective` wall that
    blocks the `project : Deck → BLState` route. -/
theorem apply_blStationary_ucfm_locallift_eq_uniformDeck :
    FiniteKernel.apply (BernoulliLaplaceGeneral.blStationaryDist p)
      (FiniteKernel.comp (uniformCountFiberMembership p)
        (localLift p.N p.m (Nat.le_of_lt p.hmn))) =
      GSR.uniformDist (Deck p.N) := by
  let hm := Nat.le_of_lt p.hmn
  rw [← FiniteKernel.apply_comp (BernoulliLaplaceGeneral.blStationaryDist p)
      (uniformCountFiberMembership p) (localLift p.N p.m hm)]
  rw [blStationary_ucfm_eq_marginalMembership p]
  dsimp only [localLift]
  exact FiberDisintegration.marginal_comp_fiber_eq_uniform (membership p.N p.m hm)
    (membership_surjective p.N p.m hm)

end FiniteDeck
end Shufflemath
