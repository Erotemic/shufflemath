module
public import Mathlib
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

end
