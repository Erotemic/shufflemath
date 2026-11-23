module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSRDeckRound
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.ActionConvolution

@[expose]
public section

/-
Decisive architecture probe (post ActionConvolution-bridge): the Gate-6
full-round kernel as an ABSTRACT Finsupp-carrier composition (`.map`/`.join`
via `FiniteDeck.conv` = `distProductFinsupp · .map (·*·)`) instead of the
Fintype-carrier `distProduct` (whose 99!×99! ≈ 10^316 joint killed the
November sessions at `isDefEq`/WHNF). If these defs elaborate, the crux
`TV(finiteRound d, idealRound d) ≤ δ1` is attackable at the Finsupp level.
-/

theorem exchangeLCard (c : Shufflemath.CommanderPhysicalExchange.exchangeChoice) :
    (c.1.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.1.2).2
theorem exchangeRCard (c : Shufflemath.CommanderPhysicalExchange.exchangeChoice) :
    (c.2.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.2.2).2

noncomputable def canonicalPairing (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25) :
    {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R} :=
  Finset.equivOfCardEq (by rw [hL, hR])

noncomputable def swapLaw : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  (Shufflemath.GSR.uniformDist (Shufflemath.CommanderPhysicalExchange.exchangeChoice)).map
    (fun c : Shufflemath.CommanderPhysicalExchange.exchangeChoice =>
      Shufflemath.FiniteDeck.swapPerm 99 50 (by norm_num) (c.1.1) (c.2.1)
        (canonicalPairing (c.1.1) (exchangeLCard c) (c.2.1) (exchangeRCard c)))

noncomputable abbrev rho99Finite : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.rhoRoundFinite 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)
noncomputable abbrev rho99Ideal : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

-- The Finsupp-carrier full-round permutation laws (NO 99!² `ofFun` joint).
noncomputable def fullRoundFinite : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.FiniteDeck.conv swapLaw rho99Finite
noncomputable def fullRoundIdeal : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.FiniteDeck.conv swapLaw rho99Ideal

-- Sanity: the kernels elaborate and are constant in the state.
noncomputable def finiteRound : Shufflemath.FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => fullRoundFinite
noncomputable def idealRound : Shufflemath.FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => fullRoundIdeal

example : True := by trivial
