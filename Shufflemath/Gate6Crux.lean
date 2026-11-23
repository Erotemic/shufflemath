module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSRDeckRound
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.ActionConvolution

@[expose]
public section

namespace Shufflemath.Gate6Crux

/-
Gate 6 batch-3 step-4 CRUX, **generic-kernel version** (2026-12-18 architecture
rework; replaces the Finsupp-univ-fiber version whose 99-specialization blew
the kernel: a 23+ minute / 11 GB check that the user rejected as
"not an acceptable proof architecture").

The full Gate-6 round = one *common* literal-swap law `swapLaw` composed with
the within-pile GSR round, expressed as the group-level convolution
`FiniteDeck.conv` (physical order `*`, first factor on the left):

  `conv A B = (distProductFinsupp A B).map (fun z => z.1 * z.2)`

The crux: both round laws share the *same* swap factor `S`, and convolution
with fixed `S` is the application of the *same* action kernel
`permutationActionKernel S` to the two riffle laws (`convAsApply` below).  A
kernel application is a TV non-expansion (`kernel_apply_lipschitz`,
`TotalVariation` — Fintype-free, proved over supports), so

  `TV(conv F S, conv I S) ≤ TV(F, I) ≤ δ1`

with **no new collision counting**: the residual `TV(F, I) = TV(rho99Finite,
rho99Ideal)` is exactly the already-committed G6.1 bound
`oneRoundDeckTV_le_delta1` (`GSRDeckRound`).  Every lemma except the final
specialization is generic in `N`; no `Finset.univ` sum ever runs over a
99! (or 99!² / 99!³) type, and no `maxHeartbeats 0` is used.  The repeated
physical rounds (the 3-round headline, next unit) use
`FiniteKernel.run (permutationActionKernel W) t` =
`(powConv W t).map (·.trans d)` (`FiniteDeck.powConvRunEq`), never a
constant-output kernel.
-/

-- Building blocks (from the green `_ProbeGate6Fin3`).
theorem exchangeLCard (c : CommanderPhysicalExchange.exchangeChoice) :
    (c.1.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.1.2).2
theorem exchangeRCard (c : CommanderPhysicalExchange.exchangeChoice) :
    (c.2.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.2.2).2

noncomputable def canonicalPairing (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25) :
    {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R} :=
  Finset.equivOfCardEq (by rw [hL, hR])

noncomputable def swapLaw : Dist (Equiv.Perm (Fin 99)) :=
  (GSR.uniformDist (CommanderPhysicalExchange.exchangeChoice)).map
    (fun c : CommanderPhysicalExchange.exchangeChoice =>
      FiniteDeck.swapPerm 99 50 (by norm_num) (c.1.1) (c.2.1)
        (canonicalPairing (c.1.1) (exchangeLCard c) (c.2.1) (exchangeRCard c)))

noncomputable abbrev rho99Finite : Dist (Equiv.Perm (Fin 99)) :=
  rhoRoundFinite 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)
noncomputable abbrev rho99Ideal : Dist (Equiv.Perm (Fin 99)) :=
  rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

-- The full-round permutation laws, physical order `g * s` (swap first, then
-- within-pile riffle): `conv A B` pushes the joint by `z.1 * z.2`.
noncomputable def fullRoundFinite : Dist (Equiv.Perm (Fin 99)) :=
  FiniteDeck.conv rho99Finite swapLaw
noncomputable def fullRoundIdeal : Dist (Equiv.Perm (Fin 99)) :=
  FiniteDeck.conv rho99Ideal swapLaw

/- ------------------------------------------------------------------
   Convolution as a kernel application (the one identity the crux needs)
------------------------------------------------------------------ -/

variable {N : Nat}

/-- **Convolution-as-kernel identity.**  One-step convolution with a noise law
    `W` is the application of the *same* permutation-action kernel to the
    first law:  `conv μ W = apply μ (permutationActionKernel W)`.

    From `convMapEqApplyMap` (`ActionConvolution`) at the identity deck:
    there both sides push by `p ↦ act p (refl) = p.trans refl = p`
    (`Equiv.trans_refl`), and pushing a law through the identity map is the
    identity (`StdSimplex.map_id_apply`);  what remains is exactly the
    definition of `permutationActionKernel` (`permutationActionKernel_eq_map`). -/
theorem convAsApply (μ W : Dist (FiniteDeck.Deck N)) :
    FiniteDeck.conv μ W =
      FiniteKernel.apply μ (FiniteDeck.permutationActionKernel W) := by
  have h := FiniteDeck.convMapEqApplyMap μ W (Equiv.refl (Fin N))
  have hact : (fun (p : FiniteDeck.Deck N) => FiniteDeck.act p (Equiv.refl (Fin N))) =
                (fun p => p) := by
    funext p
    simp [FiniteDeck.act, Equiv.trans_refl]
  rw [hact] at h
  -- h : apply (μ.map id) K = (conv μ W).map id
  have hmapId (ν : Dist (FiniteDeck.Deck N)) : (ν.map (fun p : FiniteDeck.Deck N => p)) = ν := by
    ext1
    simp
  rw [hmapId, hmapId] at h
  exact h.symm

/- ------------------------------------------------------------------
   The generic convolution contraction (the reusable core)
------------------------------------------------------------------ -/

/-- **Convolution with a fixed law `S` is a total-variation non-expansion.**
    Convexing both laws on the *right* with the same `S` (physical order:
    first the `F`/`I` law, then `S`) cannot increase their TV.  Generic in
    `N`; the proof is one application of `kernel_apply_lipschitz` after
    `convAsApply` — no sums over the deck space at all. -/
theorem convContraction (F I S : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv F S) (FiniteDeck.conv I S) ≤ tvFinsupp F I := by
  rw [convAsApply F S, convAsApply I S]
  exact kernel_apply_lipschitz F I (FiniteDeck.permutationActionKernel S)

/- ------------------------------------------------------------------
   The 99-card specialization (the Gate-6 batch-3 step-4 headline)
------------------------------------------------------------------ -/

/-- **Gate-6 one-round crux.**  The physical and perfect full-round
    permutation laws — each the within-pile GSR round `rho99·` convolved with
    the *common* literal-swap law `swapLaw` — are within the per-round
    collision budget:  `TV ≤ 2401/8388608 = δ1`.  Assembled from
    `tv_eq_tvFinsupp`, `convContraction` (generic), and the committed G6.1
    `oneRoundDeckTV_le_delta1` — a three-step calc, no collision counting. -/
theorem gate6_crux :
    Dist.tv fullRoundFinite fullRoundIdeal ≤ (2401 : Rat) / 8388608 := by
  calc
    _ = tvFinsupp fullRoundFinite fullRoundIdeal :=
        tv_eq_tvFinsupp fullRoundFinite fullRoundIdeal
    _ = tvFinsupp (FiniteDeck.conv rho99Finite swapLaw)
                  (FiniteDeck.conv rho99Ideal swapLaw) := by
        simp only [fullRoundFinite, fullRoundIdeal]
    _ ≤ tvFinsupp rho99Finite rho99Ideal :=
        convContraction rho99Finite rho99Ideal swapLaw
    _ = Dist.tv rho99Finite rho99Ideal := by
        rw [← tv_eq_tvFinsupp]
    _ ≤ (2401 : Rat) / 8388608 := by
        simpa [rho99Finite, rho99Ideal] using oneRoundDeckTV_le_delta1

end Gate6Crux
