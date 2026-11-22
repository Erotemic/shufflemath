module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.GSRDeckRound
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.GSR

@[expose]
public section

/-
Batch-3, steps 1-2 of the Gate 6 (K-J TV<1/1000) certificate.

`canonicalPairing` is the doc's "fixed pairing swap" `b` that `swapPerm`
requires: a *canonical* bijection between the two 25-element selected-position
subtypes, built from the equal-card finset equivalence (`Finset.equivOfCardEq`
through `Fin 25`). `swapLaw` pushes the uniform `(L,R)` 25-choice law through
the literal-swap permutation, giving the state-independent cross-pile deck law
that step 3 will compose with the within-pile GSR round.
-/

-- Extract the `card = 25` fact from a membership in `leftChoices`/`rightChoices`
-- (both are `powersetCard 25 (univ ...)`, so `mem_powersetCard` gives exactly
-- the card condition, the `⊆ univ` half being trivial).
theorem exchangeLCard (c : Shufflemath.CommanderPhysicalExchange.exchangeChoice) :
    (c.1.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.1.2).2
theorem exchangeRCard (c : Shufflemath.CommanderPhysicalExchange.exchangeChoice) :
    (c.2.1).card = 25 :=
  (Finset.mem_powersetCard.mp c.2.2).2

-- The fixed pairing bijection between the two selected-position subtypes:
-- both have 25 elements, so `Finset.equivOfCardEq` gives the canonical equiv.
noncomputable def canonicalPairing (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25) :
    {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R} :=
  Finset.equivOfCardEq (by rw [hL, hR])

-- The state-independent literal-swap deck law (uniform over the (L,R) choice,
-- mapped to the literal-swap permutation with the fixed canonical pairing).
noncomputable def swapLaw : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  (Shufflemath.GSR.uniformDist (Shufflemath.CommanderPhysicalExchange.exchangeChoice)).map
    (fun c : Shufflemath.CommanderPhysicalExchange.exchangeChoice =>
      Shufflemath.FiniteDeck.swapPerm 99 50 (by norm_num) (c.1.1) (c.2.1)
        (canonicalPairing (c.1.1) (exchangeLCard c) (c.2.1) (exchangeRCard c)))

/-
Batch-3 step 3: the full Gate-6 round kernels. A round = one common literal-swap
`swapLaw` (cross-pile) composed with the within-pile 2^23-riffle law
(`rhoRoundFinite`/`rhoRoundIdeal`, already within `delta1` of each other by
`oneRoundDeckTV_le_delta1`). The full-round permutation is `g * s` (riffle after
swap). Because `s` is the *same common* law in both kernels, the crux
one-round TV bound (step 4) reduces to `oneRoundDeckTV_le_delta1` by cancellation.
-/

-- The within-pile 2^23-riffle deck laws at the concrete 99-card protocol.
noncomputable abbrev rho99Finite : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.rhoRoundFinite 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)
noncomputable abbrev rho99Ideal : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  Shufflemath.rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

-- The full-round permutation laws: compose the common literal-swap with the
-- within-pile riffle (finite resp. ideal).
noncomputable def fullRoundFinite : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  (Shufflemath.distProduct swapLaw rho99Finite).map (fun (s, g) => g * s)
noncomputable def fullRoundIdeal : Shufflemath.Dist (Equiv.Perm (Fin 99)) :=
  (Shufflemath.distProduct swapLaw rho99Ideal).map (fun (s, g) => g * s)

-- The state-independent full-round kernels (the `K` and `J` of the certificate).
noncomputable def finiteRound : Shufflemath.FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => fullRoundFinite
noncomputable def idealRound : Shufflemath.FiniteKernel (Equiv.Perm (Fin 99)) (Equiv.Perm (Fin 99)) :=
  fun _ => fullRoundIdeal

end
