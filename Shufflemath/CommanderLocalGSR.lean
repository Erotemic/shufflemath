module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.GSR
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderLocalGSR

/-!
# Local (within-pile) shuffling and membership preservation (F4.2)

A *local* shuffle acts only *within* the two fixed working piles: it permutes
the 50 cards among the left-pile positions and the 49 cards among the right-pile
positions, and never moves a card between the piles. This file defines that
within-pile relabeling of deck positions and proves the central F4.2 fact:
**a local shuffle cannot change the membership state** (the set of named cards
in the left pile). The local-GSR *kernel* is the product of a GSR shuffle on
each pile applied through this mechanism; the deterministic pile-permutation
and its membership-preservation are established here.
-/

open CommanderPermutation Finsupp

/-- A function on the 99 deck positions that permutes the *left* pile by `pl`
  and the *right* pile by `pr`, and never moves a card between the piles. A
  left position `leftPosition i` goes to `leftPosition (pl i)`; a right position
  `rightPosition j` goes to `rightPosition (pr j)`. -/
def pileRelabelFn (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (p : Fin 99) : Fin 99 :=
  if h : p.val < 50 then
    leftPosition (pl ⟨p.val, h⟩)
  else
    rightPosition (pr ⟨p.val - 50, by omega⟩)

/-- A left position stays a left position, permuted by `pl`. -/
theorem pileRelabelFn_left (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (i : Fin 50) :
    pileRelabelFn pl pr (leftPosition i) = leftPosition (pl i) := by
  simp [pileRelabelFn, leftPosition]
  <;> omega

/-- A right position stays a right position, permuted by `pr`. -/
theorem pileRelabelFn_right (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) (j : Fin 49) :
    pileRelabelFn pl pr (rightPosition j) = rightPosition (pr j) := by
  simp [pileRelabelFn, rightPosition]
  <;> omega

/-- The 50 cards occupying the left pile of the deck `d` after the within-pile
  relabeling `pileRelabelFn pl pr`. -/
def permutedLeftCards (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image
    (fun i => d (pileRelabelFn pl pr (leftPosition i)))

-- A bijection on `Fin 50` leaves the image of `univ` under any `f` unchanged
-- (reindexing): `univ.image (f ∘ pl) = univ.image f`.
theorem univImage_reindex (f : Fin 50 → Fin 99) (pl : Equiv.Perm (Fin 50)) :
    (Finset.univ : Finset (Fin 50)).image (f ∘ pl) =
      (Finset.univ : Finset (Fin 50)).image f := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply]
  constructor
  · intro hX
    rcases hX with ⟨i, _, hfi⟩
    exact ⟨pl i, by simp, hfi⟩
  · intro hY
    rcases hY with ⟨i, _, hfi⟩
    have h : pl (pl.symm i) = i := pl.apply_symm_apply i
    exact ⟨pl.symm i, by simp, by simpa [h, hfi]⟩

/-- **F4.2 core.** A within-pile relabeling leaves the left-card set unchanged:
  it permutes the 50 left positions by a bijection, so the set of named cards in
  the left pile is the same. Hence the membership state is preserved. -/
theorem permutedLeftCards_eq (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) :
    permutedLeftCards d pl pr = leftCards d := by
  unfold permutedLeftCards leftCards
  -- the permuted image equals the pl-reindexed image (pointwise the maps agree)
  have hg : (fun i : Fin 50 => d (pileRelabelFn pl pr (leftPosition i))) =
      (fun i : Fin 50 => d (leftPosition (pl i))) := by
    funext i
    simpa [pileRelabelFn_left]
  have hL : (Finset.univ : Finset (Fin 50)).image
        (fun i => d (pileRelabelFn pl pr (leftPosition i))) =
      (Finset.univ : Finset (Fin 50)).image
        (fun i => d (leftPosition (pl i))) := by
    simpa [hg]
  -- then reindex by the bijection pl
  exact hL.trans (univImage_reindex (fun i => d (leftPosition i)) pl)

-- Building blocks for the bijection proof: a left position maps to a left
-- position, and a right position maps to a right position. The `if` in
-- `pileRelabelFn` has a fresh binder, so the reduction is driven by `by_cases`
-- on the same condition (which `simp` then uses to close the `if`), not by the
-- hypothesis directly.

-- A left position (`p.val < 50`) maps to a left position.
theorem pileRelabelFn_leftVal (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))
    (p : Fin 99) (h : p.val < 50) : (pileRelabelFn pl pr p).val < 50 := by
  by_cases hlt : p.val < 50
  · dsimp only [pileRelabelFn]
    simp [hlt, leftPosition]
  · exfalso
    omega

-- A right position (`50 ≤ p.val`) maps to a right position.
theorem pileRelabelFn_rightVal (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49))
    (p : Fin 99) (h : 50 ≤ p.val) : 50 ≤ (pileRelabelFn pl pr p).val := by
  by_cases hlt : p.val < 50
  · exfalso
    omega
  · dsimp only [pileRelabelFn]
    simp [hlt, rightPosition]


/-! ## The `Equiv`-based pile relabeling (F4.2, GPT-6 construction)

The within-pile relabeling as a full `Deck = Equiv.Perm (Fin 99)` *by
construction*: transport a left permutation and a right permutation through the
canonical `Fin 50 ⊕ Fin 49 ≃ Fin 99` equivalence. Bijectivity is inherited from
`Equiv` composition — no four-case injectivity/surjectivity proof. This is the
clean version of `pileRelabelFn` above (which keeps the explicit `if` for
compatibility).
-/

/-- The within-pile pile-relabeling as a `Deck` permutation by `Equiv`
  composition: `Fin 99 → (Fin 50 ⊕ Fin 49)`, apply `pl`/`pr` by
  `Equiv.sumCongr`, then back. -/
def pileRelabelEquiv (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) : Deck :=
  ((finSumFinEquiv (m := 50) (n := 49)).symm).trans
    ((Equiv.sumCongr pl pr).trans (finSumFinEquiv (m := 50) (n := 49)))

/-- A left position maps to the `pl`-image left position. -/
theorem pileRelabelEquiv_left (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (i : Fin 50) :
    pileRelabelEquiv pl pr (leftPosition i) = leftPosition (pl i) := by
  dsimp only [leftPosition]
  change (finSumFinEquiv (m := 50) (n := 49)
    (Sum.map (⇑pl) (⇑pr) (finSumFinEquiv (m := 50) (n := 49).symm (Fin.castAdd 49 i)))) =
    Fin.castAdd 49 (pl i)
  rw [finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, finSumFinEquiv_apply_left]

/-- A right position maps to the `pr`-image right position. -/
theorem pileRelabelEquiv_right (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) (j : Fin 49) :
    pileRelabelEquiv pl pr (rightPosition j) = rightPosition (pr j) := by
  dsimp only [rightPosition]
  change (finSumFinEquiv (m := 50) (n := 49)
    (Sum.map (⇑pl) (⇑pr) (finSumFinEquiv (m := 50) (n := 49).symm (Fin.natAdd 50 j)))) =
    Fin.natAdd 50 (pr j)
  rw [finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, finSumFinEquiv_apply_right]

/-- Reindex the deck positions by the pile-preserving permutation before
  reading cards. -/
def reorderedDeck (d : Deck) (pl : Equiv.Perm (Fin 50)) (pr : Equiv.Perm (Fin 49)) : Deck :=
  (pileRelabelEquiv pl pr).trans d

/-- The reordered deck has exactly the original left-card set: a local (within-
  pile) permutation cannot change which named cards sit in the left pile. -/
theorem reorderedDeck_leftCards (d : Deck) (pl : Equiv.Perm (Fin 50))
    (pr : Equiv.Perm (Fin 49)) :
    leftCards (reorderedDeck d pl pr) = leftCards d := by
  change (Finset.univ : Finset (Fin 50)).image
      (fun i => (reorderedDeck d pl pr) (leftPosition i)) =
    (Finset.univ : Finset (Fin 50)).image (fun i => d (leftPosition i))
  have hfun :
      (fun i : Fin 50 => (reorderedDeck d pl pr) (leftPosition i)) =
        (fun i : Fin 50 => d (leftPosition (pl i))) := by
    funext i
    simp only [reorderedDeck, Equiv.trans_apply, pileRelabelEquiv_left]
  rw [hfun]
  exact univImage_reindex (fun i => d (leftPosition i)) pl

/-!
## The within-pile GSR product (F4.2)

The deterministic `pileRelabelEquiv` above reorders each pile by a *fixed*
permutation.  The genuine finite local-GSR step randomizes that relabel: each
pile is shuffled by an independent GSR riffle (the F4.1 `GSR.idealShuffle`),
whose support is the whole within-pile permutation group.  Because a GSR only
reorders within a pile, the membership state is preserved.
-/

noncomputable def gsrProductKernel (nL nR a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    FiniteKernel (List (Fin nL) × List (Fin nR)) (List (Fin nL) × List (Fin nR)) :=
  fun pr => ((GSR.idealShuffle nL a ha pr.1).map (fun L' =>
      (GSR.idealShuffle nR b hb pr.2).map (fun R' => (L', R')))).join

/-- The *delta* that the first-coordinate map applies: mapping the right-pile
    distribution `muR` to pairs `(a, r)` and reading the mass at `(L', R')`
    contributes `muR`'s mass at `R'` exactly when the fixed first coordinate
    `a` equals the queried one `L'`; otherwise the image misses the query point
    entirely and the mass is `0`. Building block of the two-pile point-mass
    formula below. -/
lemma gsrMapDelta_mass (nL nR : Nat) (L' : List (Fin nL)) (R' : List (Fin nR))
    (a : List (Fin nL)) (muR : Convexity.StdSimplex Rat (List (Fin nR))) :
    (muR.map (fun (r : List (Fin nR)) => (a, r))).weights (L', R') =
      if a = L' then muR.weights R' else 0 := by
  simp only [Convexity.StdSimplex.map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  have hrew : (fun (a₁ : List (Fin nR)) (b : Rat) => if (a, a₁) = (L', R') then b else 0) =
      (fun a₁ b => if a = L' then (if a₁ = R' then b else 0) else 0) := by
    ext a₁ b
    by_cases ha : a = L' <;> by_cases hr : a₁ = R' <;> simp [ha, hr]
  rw [hrew]
  by_cases ha : a = L'
  · have hfun : (fun (a₁ : List (Fin nR)) (b : Rat) => if a = L' then (if a₁ = R' then b else 0) else 0) =
        (fun a₁ b => if a₁ = R' then b else 0) := by
      funext a₁ b; exact ite_eq_left ha
    rw [hfun, Finsupp.sum_ite_self_eq', ite_eq_left ha]
  · have hzero : (fun (a₁ : List (Fin nR)) (b : Rat) => if a = L' then (if a₁ = R' then b else 0) else 0) =
        fun _ _ => 0 := by
      funext a₁ b; exact ite_eq_right ha
    rw [hzero, Finsupp.sum, Finset.sum_const_zero, ite_eq_right ha]

/-- F4.3 core (Fintype-free): the point-mass of the two-pile GSR *product*
    kernel, read at `(L', R')`, is the product of the two pile-masses.  The
    kernel is a `map`/`join` of `StdSimplex` values over the Finsupp supports
    (no `Fintype` on the deck-lists is required, unlike `Finite.distProduct`).
    This is the lemma that lets `distProduct_tv_subadditive`-style TV
    subadditivity be applied to the two-pile GSR kernel for the F4.3 bound. -/
theorem gsrProductKernel_mass (nL nR : Nat) (L' : List (Fin nL)) (R' : List (Fin nR))
    (muL : Convexity.StdSimplex Rat (List (Fin nL)))
    (muR : Convexity.StdSimplex Rat (List (Fin nR))) :
    ((muL.map (fun (x : List (Fin nL)) =>
        muR.map (fun (r : List (Fin nR)) => (x, r)))).join).weights (L', R') =
      muL.weights L' * muR.weights R' := by
  let g (x : List (Fin nL)) : Convexity.StdSimplex Rat (List (Fin nL) × List (Fin nR)) :=
    muR.map (fun (r : List (Fin nR)) => (x, r))
  have hmg : muL.map (fun (x : List (Fin nL)) => muR.map (fun (r : List (Fin nR)) => (x, r))) =
      muL.map g := rfl
  rw [hmg]
  simp only [Convexity.StdSimplex.map, Convexity.StdSimplex.join, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  let h (a₁ : Convexity.StdSimplex Rat (List (Fin nL) × List (Fin nR))) : Rat →+ Rat :=
    AddMonoidHom.mk (ZeroHom.mk (fun (b : Rat) => b * a₁.weights (L', R')) (by ring))
      (by intro x y; ring)
  have hsum : (fun (a₁ : Convexity.StdSimplex Rat (List (Fin nL) × List (Fin nR))) (b : Rat) =>
      b * a₁.weights (L', R')) = fun a₁ b => (h a₁) b := by
    ext a₁ b
    dsimp only [h]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.mk, ZeroHom.mk]
  rw [← Finsupp.mapDomain, hsum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  simp only [Finsupp.sum]
  have hsum_eq : ∑ a ∈ muL.weights.support, (h (g a)) (muL.weights a) =
      ∑ a ∈ muL.weights.support, (muL.weights a * (g a).weights (L', R')) := by
    apply Finset.sum_congr rfl
    intro a _
    change (fun (c : Rat) => c * (g a).weights (L', R')) (muL.weights a) =
      muL.weights a * (g a).weights (L', R')
    ring
  rw [hsum_eq]
  dsimp only [g]
  simp only [gsrMapDelta_mass, mul_zero, mul_comm]
  rw [show ∑ a ∈ muL.weights.support, muL.weights a * (if a = L' then muR.weights R' else 0) =
        ∑ a ∈ muL.weights.support, (if a = L' then muL.weights a else 0) * muR.weights R' from by
    apply Finset.sum_congr rfl
    intro a _; by_cases ha : a = L' <;> simp [ha, mul_zero, mul_comm]]
  have hfactor : ∑ a ∈ muL.weights.support, (if a = L' then muL.weights a else 0) * muR.weights R' =
      (∑ a ∈ muL.weights.support, (if a = L' then muL.weights a else 0)) * muR.weights R' := by
    rw [show ∑ a ∈ muL.weights.support, (if a = L' then muL.weights a else 0) * muR.weights R' =
          ∑ a ∈ muL.weights.support, muR.weights R' * (if a = L' then muL.weights a else 0) from by
      apply Finset.sum_congr rfl; intro a _; ring]
    rw [← Finset.mul_sum, mul_comm]
  rw [hfactor]
  have hsumL : ∑ a ∈ muL.weights.support, (if a = L' then muL.weights a else 0) = muL.weights L' := by
    change muL.weights.sum (fun (a : List (Fin nL)) (v : Rat) => (if a = L' then v else 0)) =
      muL.weights L'
    exact Finsupp.sum_ite_self_eq' _ L'
  rw [hsumL]

/-- F4.3: the point-mass of the actual two-pile GSR product kernel at
    `(L', R')` is the product of the two piles' ideal-GSR masses.  This is
    `gsrProductKernel_mass` instantiated at the GSR kernels; the kernel is
    definitionally the `map`/`join` construction the core lemma handles. -/
theorem gsrProductKernel_pointMass (nL nR a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (pr : List (Fin nL) × List (Fin nR))
    (L' : List (Fin nL)) (R' : List (Fin nR)) :
    (gsrProductKernel nL nR a b ha hb pr).weights (L', R') =
      (GSR.idealShuffle nL a ha pr.1).weights L' * (GSR.idealShuffle nR b hb pr.2).weights R' := by
  dsimp only [gsrProductKernel]
  exact gsrProductKernel_mass nL nR L' R' _ _

/-- The two-pile GSR product kernel is, pointwise, exactly the Fintype-free
independent product of the two per-pile F4.1 `idealShuffle` kernels.  Both
sides unfold to the same nested `StdSimplex.map`/`join` construction, so the
identity is definitional.  This is the bridge that lets the F4.3 Fintype-free
total-variation subadditivity (`TotalVariation.distProductFinsupp_tv_subadditive`)
be applied to the concrete `gsrProductKernel`. -/
theorem gsrProductKernel_eq_distProductFinsupp (nL nR a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (pr : List (Fin nL) × List (Fin nR)) :
    gsrProductKernel nL nR a b ha hb pr =
      distProductFinsupp (GSR.idealShuffle nL a ha pr.1) (GSR.idealShuffle nR b hb pr.2) := by
  dsimp only [gsrProductKernel, distProductFinsupp]

/-- A within-pile GSR can never move a card out of its pile: the output
arrangement holds exactly the pile's original cards.  The deterministic
`reorderedDeck_leftCards` is the fixed-relabel instance of this. -/
theorem gsrLocal_preserves_pile (n a : Nat)
    (deck : List (Fin n)) (labels : Fin n → Fin a) (x : Fin n) :
    x ∈ GSR.stableBuckets a labels deck ↔ x ∈ deck := by
  exact GSR.stableBuckets_set a labels deck x

/-- F4.3 row-wise bound: the two-pile GSR product kernel, against *any*
two-pile product reference, has total variation at most the sum of the two
per-pile GSR-versus-reference errors.  This is the Fintype-free GSR two-pile
contraction — the `List (Fin n)` state space is not a `Fintype`, so the bound
is stated with `tvFinsupp` and the Finsupp product, not the `Finset.univ`-based
`Dist.tv`.  Taking the two references to be the per-pile perfect (uniform)
local shuffles gives exactly the "GSR discrepancy is at most the sum of the
two local GSR-versus-uniform errors" statement of the plan.  The proof is the
definitional bridge `gsrProductKernel_eq_distProductFinsupp` plus the general
F4.3 subadditivity. -/
theorem gsrProductKernel_rowTV_bound (nL nR a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (pr : List (Fin nL) × List (Fin nR))
    (perfectL : Dist (List (Fin nL))) (perfectR : Dist (List (Fin nR))) :
    tvFinsupp (gsrProductKernel nL nR a b ha hb pr) (distProductFinsupp perfectL perfectR) ≤
      tvFinsupp (GSR.idealShuffle nL a ha pr.1) perfectL +
      tvFinsupp (GSR.idealShuffle nR b hb pr.2) perfectR := by
  rw [gsrProductKernel_eq_distProductFinsupp]
  exact distProductFinsupp_tv_subadditive _ _ _ _

/-- F4.5 one-step two-pile riffle terminal bound: pushing any starting
distribution through one GSR two-pile shuffle, its TV distance from the two-pile
product reference is at most the starting-distribution-weighted average of the
per-pile GSR-versus-reference errors.  Composes the F4.3 row bound with the
Fintype-free mixture contraction.  The state space `List (Fin n) × List (Fin n)`
is not a `Fintype`, so the bound is `tvFinsupp`-based. -/
theorem gsrOneStep_terminalTV_bound (nL nR a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (mu0 : Dist (List (Fin nL) × List (Fin nR)))
    (perfectL : Dist (List (Fin nL))) (perfectR : Dist (List (Fin nR))) :
    tvFinsupp (FiniteKernel.apply mu0 (gsrProductKernel nL nR a b ha hb))
        (distProductFinsupp perfectL perfectR) ≤
      (mu0.weights.support).sum (fun pr => Dist.mass mu0 pr *
        (tvFinsupp (GSR.idealShuffle nL a ha pr.1) perfectL +
         tvFinsupp (GSR.idealShuffle nR b hb pr.2) perfectR)) := by
  let K := gsrProductKernel nL nR a b ha hb
  have hmix : tvFinsupp (FiniteKernel.apply mu0 K) (distProductFinsupp perfectL perfectR) ≤
      (mu0.weights.support).sum (fun pr => Dist.mass mu0 pr *
        tvFinsupp (K pr) (distProductFinsupp perfectL perfectR)) :=
    mixtureTV_le mu0 K (distProductFinsupp perfectL perfectR) (mu0.weights.support)
      (by simp)
  have hrow (pr : List (Fin nL) × List (Fin nR)) :
      tvFinsupp (K pr) (distProductFinsupp perfectL perfectR) ≤
        tvFinsupp (GSR.idealShuffle nL a ha pr.1) perfectL +
        tvFinsupp (GSR.idealShuffle nR b hb pr.2) perfectR :=
    gsrProductKernel_rowTV_bound nL nR a b ha hb pr perfectL perfectR
  calc
    _ ≤ (mu0.weights.support).sum (fun pr => Dist.mass mu0 pr *
        tvFinsupp (K pr) (distProductFinsupp perfectL perfectR)) := hmix
    _ ≤ (mu0.weights.support).sum (fun pr => Dist.mass mu0 pr *
        (tvFinsupp (GSR.idealShuffle nL a ha pr.1) perfectL +
         tvFinsupp (GSR.idealShuffle nR b hb pr.2) perfectR)) := by
      apply Finset.sum_le_sum
      intro pr _
      apply mul_le_mul_of_nonneg_left
      · exact hrow pr
      · exact Dist.mass_nonneg mu0 pr

  /-- The two-pile GSR shuffle, iterated any number of times, never increases the
      total variation between two starting laws.  Every Giry kernel is 1-Lipschitz
      on TV in one step (`kernel_apply_lipschitz`), and `run_nonexpansive`
      composes that contraction along the `run` iteration; the two-pile GSR
      kernel is just such a kernel on the pile-list state space.  Fintype-free.
      (This is the non-expansive, no-contraction form; a full decay to the
      uniform target would additionally require the Fintype Dobrushin
      coefficient on a finite deck state space.) -/
  theorem gsrRunNonexpansive (nL nR a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℕ)
      (mu nu : Dist (List (Fin nL) × List (Fin nR))) :
      tvFinsupp (FiniteKernel.run (gsrProductKernel nL nR a b ha hb) k mu)
                (FiniteKernel.run (gsrProductKernel nL nR a b ha hb) k nu) ≤
        tvFinsupp mu nu :=
    run_nonexpansive (gsrProductKernel nL nR a b ha hb) k mu nu

end CommanderLocalGSR
end Shufflemath
end
