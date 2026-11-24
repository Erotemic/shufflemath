/-
Copyright (c) 2026 Jon Crall.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSRDeckRound
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.FiniteDeck.RelabelInvariance
public import Shufflemath.Gate6Crux

@[expose] public section

namespace Shufflemath.ConvContractionLeft

variable {N : Nat}

/-- The right-translation map `q ↦ q.trans p` (right action of a fixed
    permutation `p` on the deck space) is a bijection, with inverse
    `q ↦ q.trans p.symm`.  `relabel_bijective` already proves
    `Function.Bijective (fun q => q.trans p)`; wrap it in an `Equiv` so
    `tv_bijective_invariance` applies. -/
noncomputable def rightTransEquiv (p : Equiv.Perm (Fin N)) :
    (Equiv.Perm (Fin N)) ≃ (Equiv.Perm (Fin N)) :=
  Equiv.ofBijective (fun q => q.trans p) (relabel_bijective p)

/-- **Convolution with a fixed law `S` on the *left* is a total-variation
    non-expansion:**  `TV(conv S F, conv S I) ≤ TV(F, I)`.  The mirror of
    `convContraction` (which fixes `S` on the *right*).  The physical 99-card
    round is `conv swapLaw rho99·` (swap first, then the riffle — the
    `k1_capstone_correct` order), so this is the contraction the
    correct-order finite headline needs: both rounds share the fixed swap law
    `S` on the left; only the finite-vs-ideal riffle `F`/`I` varies on the
    right.  Fintype-free (all sums over finite `Finsupp` supports; the inner
    step uses `tv_bijective_invariance`, a pushforward-TV equality that never
    forces a `99!` reduction); no `maxHeartbeats 0`. -/
theorem convContractionLeft (S F I : Dist (Equiv.Perm (Fin N))) :
    tvFinsupp (FiniteDeck.conv S F) (FiniteDeck.conv S I) ≤ tvFinsupp F I := by
  rw [Gate6Crux.convAsApply S F, Gate6Crux.convAsApply S I]
  set P := FiniteKernel.apply S (FiniteDeck.permutationActionKernel F) with hP
  set Q := FiniteKernel.apply S (FiniteDeck.permutationActionKernel I) with hQ
  set KF := FiniteDeck.permutationActionKernel F with hKF
  set KI := FiniteDeck.permutationActionKernel I with hKI
  let SS := S.weights.support
  -- Mass expansion over the support of S (apply_mass_finsupp; SS = S.support).
  have hPmass (y : Equiv.Perm (Fin N)) :
      Dist.mass P y = SS.sum (fun q => Dist.mass S q * Dist.mass (KF q) y) := by
    rw [FiniteKernel.apply_mass_finsupp]
  have hQmass (y : Equiv.Perm (Fin N)) :
      Dist.mass Q y = SS.sum (fun q => Dist.mass S q * Dist.mass (KI q) y) := by
    rw [FiniteKernel.apply_mass_finsupp]
  -- Pointwise bound: |P y - Q y| ≤ Σ_p mass S p · |mass (KF p) y - mass (KI p) y|.
  have hPsub (y : Equiv.Perm (Fin N)) :
      Dist.mass P y - Dist.mass Q y =
        SS.sum (fun p => Dist.mass S p * (Dist.mass (KF p) y - Dist.mass (KI p) y)) := by
    rw [hPmass, hQmass]
    rw [← Finset.sum_sub_distrib
          (fun p => Dist.mass S p * Dist.mass (KF p) y)
          (fun p => Dist.mass S p * Dist.mass (KI p) y)]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hpoint (y : Equiv.Perm (Fin N)) :
      |Dist.mass P y - Dist.mass Q y| ≤
        SS.sum (fun p => Dist.mass S p *
          |Dist.mass (KF p) y - Dist.mass (KI p) y|) := by
    rw [hPsub]
    have h1 := Finset.abs_sum_le_sum_abs
      (fun p => Dist.mass S p * (Dist.mass (KF p) y - Dist.mass (KI p) y)) SS
    have h2 :
        SS.sum (fun p => |Dist.mass S p * (Dist.mass (KF p) y - Dist.mass (KI p) y)|) =
          SS.sum (fun p => Dist.mass S p * |Dist.mass (KF p) y - Dist.mass (KI p) y|) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [abs_mul, abs_of_nonneg (Dist.mass_nonneg S p)]
    exact le_trans h1 (le_of_eq h2)
  let T := P.weights.support ∪ Q.weights.support
  have hA : (2 : Rat) * tvFinsupp P Q = T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) := by
    dsimp only [T]
    unfold Dist.mass
    rw [twoTv_eq_unionSum]
  have hB : T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) ≤
      T.sum (fun y => SS.sum (fun p => Dist.mass S p *
        |Dist.mass (KF p) y - Dist.mass (KI p) y|)) := by
    apply Finset.sum_le_sum
    intro y _
    exact hpoint y
  have hC : T.sum (fun y => SS.sum (fun p => Dist.mass S p *
        |Dist.mass (KF p) y - Dist.mass (KI p) y|)) =
      SS.sum (fun p => Dist.mass S p *
        T.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.mul_sum]
  -- Inner row, for p in the support of S: the row-difference of the two action
  -- kernel rows, summed over T, is at most 2·TV(F, I).  Enlarge T by the two
  -- rows' supports (a trivial containment); the enlarged sum equals
  -- 2·TV(KF p, KI p) (`l1OverEnlarged_eq_twoTv`), and both rows are the
  -- pushforward of F / I through the same bijection (·.trans p), which
  -- preserves TV (`tv_bijective_invariance`).
  have hRow (p : Equiv.Perm (Fin N)) (hp : p ∈ SS) :
      T.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|) ≤
        (2 : Rat) * tvFinsupp F I := by
    let T' := T ∪ ((KF p).weights.support ∪ (KI p).weights.support)
    have hTsub : T ⊆ T' := by
      intro x hx
      exact Finset.mem_union.mpr (Or.inl hx)
    have hle : T.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|) ≤
        T'.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|) := by
      let f := fun (y : FiniteDeck.Deck N) => |Dist.mass (KF p) y - Dist.mass (KI p) y|
      have h1 : T'.sum (fun y => if y ∈ T then f y else 0) = T.sum f := by
        have hI : T' ∩ T = T := Finset.inter_eq_right.mpr hTsub
        simp [hI]
      have h2 : T'.sum (fun y => if y ∈ T then f y else 0) ≤ T'.sum f := by
        apply Finset.sum_le_sum
        intro y _
        split_ifs with hy
        · exact le_rfl
        · exact abs_nonneg _
      calc
        _ = T'.sum (fun y => if y ∈ T then f y else 0) := h1.symm
        _ ≤ T'.sum f := h2
    have hsub : (KF p).weights.support ∪ (KI p).weights.support ⊆ T' := by
      intro x hx
      exact Finset.mem_union.mpr (Or.inr hx)
    have hT2 : T'.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|) =
        (2 : Rat) * tvFinsupp (KF p) (KI p) := by
      simpa [Dist.mass] using (l1OverEnlarged_eq_twoTv (KF p) (KI p) T' hsub)
    have hKFmap : (KF p) = F.map (fun q : Equiv.Perm (Fin N) => Equiv.trans q p) :=
      FiniteDeck.permutationActionKernel_eq_map F p
    have hKImap : (KI p) = I.map (fun q : Equiv.Perm (Fin N) => Equiv.trans q p) :=
      FiniteDeck.permutationActionKernel_eq_map I p
    have hφ : (fun q : Equiv.Perm (Fin N) => Equiv.trans q p) = (rightTransEquiv p).toFun := by
      funext q
      rfl
    have hKFequiv : KF p = F.map (rightTransEquiv p).toFun := by
      rw [hKFmap]
      simp [Convexity.StdSimplex.map, hφ]
    have hKIequiv : KI p = I.map (rightTransEquiv p).toFun := by
      rw [hKImap]
      simp [Convexity.StdSimplex.map, hφ]
    have hTVeq : tvFinsupp (KF p) (KI p) = tvFinsupp F I := by
      rw [hKFequiv, hKIequiv]
      simpa [Convexity.StdSimplex.map, tv_eq_tvFinsupp] using
        tv_bijective_invariance (rightTransEquiv p) F I
    calc
      _ ≤ T'.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|) := hle
      _ = (2 : Rat) * tvFinsupp (KF p) (KI p) := hT2
      _ = (2 : Rat) * tvFinsupp F I := by rw [hTVeq]
  -- Swap the sum and bound the inner row by 2·TV(F, I); factor the mass out.
  have hD : SS.sum (fun p => Dist.mass S p *
        T.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|)) ≤
      (2 : Rat) * tvFinsupp F I * SS.sum (fun p => Dist.mass S p) := by
    calc
      _ ≤ SS.sum (fun p => Dist.mass S p * ((2 : Rat) * tvFinsupp F I)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left (hRow p hp) (Dist.mass_nonneg S p)
      _ = (2 : Rat) * tvFinsupp F I * SS.sum (fun p => Dist.mass S p) := by
        rw [← Finset.sum_mul, mul_comm]
  have hF : SS.sum (fun p => Dist.mass S p) = 1 := by
    dsimp only [SS]
    simpa [Dist.mass] using sumOverEnlarged_eq_one S S.weights.support (fun _ h => h)
  -- The halved-TV identities relate 2·TV to the L1 sums, so run the chain on
  -- 2·TV and divide the 2 out at the end (2·a ≤ 2·b ↔ a ≤ b, 2 > 0, TV ≥ 0).
  have hgoal : 2 * tvFinsupp P Q ≤ 2 * tvFinsupp F I := by
    calc
      _ = T.sum (fun y => |Dist.mass P y - Dist.mass Q y|) := by rw [hA]
      _ ≤ T.sum (fun y => SS.sum (fun p => Dist.mass S p *
            |Dist.mass (KF p) y - Dist.mass (KI p) y|)) := hB
      _ = SS.sum (fun p => Dist.mass S p *
            T.sum (fun y => |Dist.mass (KF p) y - Dist.mass (KI p) y|)) := hC
      _ ≤ (2 : Rat) * tvFinsupp F I * SS.sum (fun p => Dist.mass S p) := hD
      _ = (2 : Rat) * tvFinsupp F I * 1 := by rw [hF]
      _ = (2 : Rat) * tvFinsupp F I := by ring
  -- Divide both sides by 2 (positive) to recover TV(P,Q) ≤ TV(F,I).
  exact by
    calc
      tvFinsupp P Q = (1 / 2 : Rat) * (2 * tvFinsupp P Q) := by ring
      _ ≤ (1 / 2 : Rat) * (2 * tvFinsupp F I) :=
        mul_le_mul_of_nonneg_left hgoal (by norm_num)
      _ = tvFinsupp F I := by ring

end Shufflemath.ConvContractionLeft
