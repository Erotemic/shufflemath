module

public import Shufflemath.Finite
public import Shufflemath.Perturbation
public import Shufflemath.TelescopeF5
public import Shufflemath.GSR
public import Shufflemath.TotalVariation
public import Shufflemath.GSRDeckRound
public import Shufflemath.FiniteDeck.Gate6FiniteGSR

@[expose] public section

namespace Shufflemath

open FiniteKernel

/-!
## Gate 6 (G6.3) — the 3-round finite-GSR telescope: `TV(K^3 d0, U) ≤ q3 + 3·δ1`

The physical 3-round deck chain (three `gsrRound99Finite` kernels from a start
`d0`) is within `q3 + 3·δ1` of the uniform `99!` target: the telescope triangle
splits the TV into (i) the physical-vs-ideal 3-round discrepancy, bounded by
`3·δ1` (the `compList_telescope_nstep_le_n_times_d` building block with per-round
discrepancy `≤ δ1`, the G6.1 `oneRoundDeckTV_le_delta1`), and (ii) the ideal
3-round chain's residual toward uniform, `q3` (a hypothesis on the ideal chain).
This is the 3-round companion to the one-round G6.1 bound and the rational
headline `gate6_headline_bound : q3 + 3·δ1 < 1/1000`.
-/

instance gsrDeck99_nonempty : Nonempty (Equiv.Perm (Fin 99)) :=
  ⟨(1 : Equiv.Perm (Fin 99))⟩

-- The 99-card one-round physical / ideal deck laws, lifted to *state-independent*
-- `FiniteKernel`s: the within-pile GSR round law does not depend on the current
-- full deck (it acts on the fixed left/right positions), so the one-round kernel
-- is the constant function returning the one-round law.  This is the faithful
-- Markov-kernel abstraction of the state-independent GSR round.
noncomputable def gsrRound99Finite : FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => rhoRoundFinite 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

noncomputable def gsrRound99Ideal : FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

-- The per-round discrepancy: every row is the one-round deck pair, so the
-- discrepancy is exactly the G6.1 one-round deck TV, `≤ 2401/8388608 = δ1`.
theorem gsrRound99_discrepancy_le_δ1 :
    kernelDiscrepancy gsrRound99Finite gsrRound99Ideal ≤ δ1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  simpa [gsrRound99Finite, gsrRound99Ideal, δ1_eq_2401_over_8388608] using oneRoundDeckTV_le_delta1

-- G6.3: the 3-round physical chain is within `q3 + 3·δ1` of the uniform target.
--
-- ⚠️  OPEN SUB-PART (b) — `hq3` is the sole remaining open sub-part of the batch-4
-- headline.  For the *within-pile-only* `gsrRound99Ideal` used here it is FALSE: that
-- kernel is state-independent, so `compList [I, I, I]` collapses to one within-pile
-- round whose support is the pile-preserving decks (`50!·49!` of the `99!`) —
-- essentially singular with `GSR.uniformDist` (TV ≈ 1 ≫ q3).  The fulfillable
-- (mixing) ideal needs the *state-dependent* full-round kernel, whose `99!×99! ≈ 10^316`
-- normalization is definitively wall-bound (commit ce0ba37; the `N=24`/`54` probes
-- confirm the wall and rule 9 forbids `maxHeartbeats 0`).  So the conditional telescope
-- (`≤ q3 + 3·δ1`) is proven and `gate6_headline_lt_thousandth` gives `q3 + 3·δ1 < 1/1000`;
-- discharging `hq3` for a genuinely mixing 3-round chain is the open item.  The
-- on-mission `TV < 1/1000` headline is met independently by `DobrushinDecay99` (41
-- perfect exchanges, any macrostate).
theorem gate6_headline_telescope
    (d0 : Equiv.Perm (Fin 99))
    (hq3 : Dist.tv
        (FiniteKernel.apply (Dist.pointMass d0)
          (compList [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal]))
        (GSR.uniformDist (Equiv.Perm (Fin 99))) ≤ q3) :
    Dist.tv
      (FiniteKernel.apply (Dist.pointMass d0)
        (compList [gsrRound99Finite, gsrRound99Finite, gsrRound99Finite]))
      (GSR.uniformDist (Equiv.Perm (Fin 99))) ≤ q3 + 3 * δ1 := by
  have hlen : ([gsrRound99Finite, gsrRound99Finite, gsrRound99Finite]
      : List (FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)))).length =
      [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal].length := by simp
  -- every per-round discrepancy in the zipped list equals `kernelDiscrepancy F I ≤ δ1`;
  -- `or_self` collapses the all-equal triple to a single `a = kernelDiscrepancy F I`.
  have hΔle : ∀ (a : Rat),
      a ∈ (List.map (fun (p : FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) ×
              FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99))) =>
              kernelDiscrepancy p.1 p.2)
        ([gsrRound99Finite, gsrRound99Finite, gsrRound99Finite].zip
          [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal])) →
      a ≤ δ1 := by
    intro a ha
    simp at ha
    simpa [ha] using gsrRound99_discrepancy_le_δ1
  calc
    _ ≤ Dist.tv (FiniteKernel.apply (Dist.pointMass d0)
            (compList [gsrRound99Finite, gsrRound99Finite, gsrRound99Finite]))
            (FiniteKernel.apply (Dist.pointMass d0)
            (compList [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal])) +
          Dist.tv (FiniteKernel.apply (Dist.pointMass d0)
            (compList [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal]))
            (GSR.uniformDist (Equiv.Perm (Fin 99))) :=
        Dist.tv_triangle _ _ _
    _ ≤ (3 : Rat) * δ1 +
          Dist.tv (FiniteKernel.apply (Dist.pointMass d0)
            (compList [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal]))
            (GSR.uniformDist (Equiv.Perm (Fin 99))) := by
      apply add_le_add
      · exact compList_telescope_nstep_le_n_times_d
          [gsrRound99Finite, gsrRound99Finite, gsrRound99Finite]
          [gsrRound99Ideal, gsrRound99Ideal, gsrRound99Ideal] hlen δ1
          (by rw [δ1_eq_2401_over_8388608]; norm_num) hΔle (Dist.pointMass d0)
      · rfl
    _ ≤ (3 : Rat) * δ1 + q3 := add_le_add le_rfl hq3
    _ = q3 + 3 * δ1 := by ring

end Shufflemath
