module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.Gate6Crux
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath._ProbeK1b

@[expose]
public section

namespace Shufflemath

/-
  Batch-5b K1-arc, K1b — the swap half of the generalized
  exchange-then-local-reset headline `K1_oneRoundLaw_eq_exchangeThenLocalReset`
  (see `Shufflemath/_ProbeGate6K1.lean`, whose remaining `sorry` is exactly
  this composition).

  After `k1a_riffle_half` the LHS of the headline is
      apply (apply (pointMass (membership d)) localLift) (PAK swapLaw)
  and after `k1_rhs_bookkeeping` the RHS is
      apply (rawExchangeMembership d) localLift.
  K1b is the equality of those two (the "swap half").

  COMBINATORIAL HEART (checked on a 4-card model before proving): for every
  deck X and 25/25 choice c,
      X is in the image of the fiber transport  q ↦ (s_c).trans q  (q ∈ fiber d)
      ↔  newMembership d L R = membership X,
  which is what makes the c-mixture on the LHS reduce to
  `rawExchangeMembership d` on the RHS.  Proof facts:
    * `swapFn_involution` → `(swapPerm …).symm` is the same swap;
    * `membership ((s_c).symm.trans X) = newMembership X c`  (k1b_inv_swap_membership);
    * a 25/25 pile-split set computation for the final equivalence (k1b_beta).

  The 99!/25! normalisation wall does not appear in K1b: the only
  fiber-count arithmetic is the already-proved `fiberSet_membership_card`
  and `localLift_mass` (no `Fintype.card` over the 99! deck type).
-/

/- **K1b statement** (the swap half; assembly of the K1 headline pending). -/
theorem k1b_swap_half (d : CommanderPermutation.Deck) :
    FiniteKernel.apply
      (FiniteKernel.apply (Dist.pointMass (CommanderMembershipKernels.membership d))
        CommanderMembershipKernels.localLift)
      (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw) =
      FiniteKernel.apply
        (CommanderPhysicalExchange.rawExchangeMembership d)
        CommanderMembershipKernels.localLift := by
  -- mass at deck X:
  --   LHS = (1/|C|) · Σ_c (1/|F|) · [X ∈ image_c]
  --       = (1/|F|) · (1/|C|) · #{c : newMembership d c = membership X}
  --       = (1/|F|) · mass (rawExchangeMembership d) (membership X)
  --   RHS = (1/|F|) · mass (rawExchangeMembership d) (membership X)
  --        (linearity of `apply` through `localLift` + `localLift_mass`).
  -- Remaining sub-lemmas: the image-membership indicator (k1b_beta, below),
  -- mixture linearity of `apply` (small, from `Dist.map` Finsupp linearity).
  sorry

/- The inverse of a literal-swap permutation is the same permutation,
  pointwise (`swapFn` is an involution, hence a right-inverse of itself,
  and `Equiv.symm` is the unique right-inverse). -/
theorem k1b_symm_pointwise (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) (i : Fin 99) :
    (FiniteDeck.swapPerm 99 50 h50le99 L R b).symm i =
      (FiniteDeck.swapPerm 99 50 h50le99 L R b) i := by
  set s := FiniteDeck.swapPerm 99 50 h50le99 L R b
  -- any right-inverse of s is s.symm (s is injective)
  have huniq : ∀ t : Fin 99 → Fin 99, (∀ x, s (t x) = x) → t = fun x => (s).symm x := by
    intro t ht
    funext x
    exact (s.injective) (by rw [ht x, Equiv.apply_symm_apply (e := s)])
  -- s is a right-inverse of itself (the involution, function-level)
  have hrinv : ∀ x, s (s x) = x := by
    intro x
    change FiniteDeck.swapFn 99 50 h50le99 L R b (FiniteDeck.swapFn 99 50 h50le99 L R b x) = x
    exact FiniteDeck.swapFn_involution 99 50 h50le99 L R b x
  -- so (fun x => s x) = (fun x => s.symm x); apply i and symmetrise.
  have hfun : (fun x => (s).symm x) = (fun x => s x) := (huniq (fun x => s x) hrinv).symm
  simpa using congrArg (fun f => f i) hfun

/- **k1b_inv_swap_membership**: the membership of the inverse-swap deck is the
  `newMembership` of the original deck (K1a transported through the
  involution). -/
theorem k1b_inv_swap_membership (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25) (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    CommanderMembershipKernels.membership
      ((FiniteDeck.swapPerm 99 50 h50le99 L R b).symm.trans d) =
      CommanderPhysicalExchange.newMembership d L hL R hR := by
  -- (s).symm.trans d = s.trans d  pointwise, by the involution
  have heq : (FiniteDeck.swapPerm 99 50 h50le99 L R b).symm.trans d =
      (FiniteDeck.swapPerm 99 50 h50le99 L R b).trans d := by
    ext1 i
    rw [Equiv.trans_apply, Equiv.trans_apply]
    rw [k1b_symm_pointwise L hL R hR b i]
  rw [heq]
  exact K1a_stmt_only d L hL R hR b

/- **k1b_beta** (the combinatorial heart; proof pending the 25/25
  set computation, next session): for every deck `X` and 25/25 choice, `X`
  lies in the image of the fiber transport `q ↦ (s_c).trans q` over the fiber
  of `d` iff `newMembership d L R = membership X`. -/
theorem k1b_beta (d X : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25) (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    (∃ q : CommanderPermutation.Deck,
       CommanderMembershipKernels.membership q = CommanderMembershipKernels.membership d ∧
       (FiniteDeck.swapPerm 99 50 h50le99 L R b).trans q = X) ↔
      CommanderPhysicalExchange.newMembership d L hL R hR =
        CommanderMembershipKernels.membership X := by
  -- (←): q := (s_c).symm.trans X;  membership q = newMembership X c
  --      (k1b_inv_swap_membership);  then the 25/25 split computation.
  -- (→):  membership ((s_c).symm.trans X) = membership d  —  same computation.
  sorry

end Shufflemath
