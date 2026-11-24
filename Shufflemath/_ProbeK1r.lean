module
public import Mathlib
public import Shufflemath._ProbeK1k

@[expose]
public section

set_option linter.constructorNameAsVariable false

namespace Shufflemath

/- K1b count formula — the 25/25 branch (2026-12-30 elaboration-wall cracked for this
    branch).  `k1b_hitCount Y M` is `#(exchange choices (L,R) with newMembership = M)`.
    `k1b_count_25`: when `M`'s 50 cards split `25/25` across the two piles, there is
    EXACTLY ONE such choice (the witness pair `Lstar`, `Rstar` hits `M` and is the unique
    hit).  The non-25/25 branch (`= 0`) is still blocked by the elaboration budget and
    lives in `_ProbeK1q` (WIP).  The big per-`c` `newMembership` term is spelled out once,
    in `k1b_hitCount`, and every goal refers to that abbrev.  The `constructorNameAsVariable`
    linter is disabled here: the proof term is deep enough to overflow the linter's stack. -/

abbrev k1b_hitCount (Y : CommanderPermutation.Deck)
    (M : CommanderMembershipKernels.Membership) : Nat :=
    (Finset.filter (fun c => CommanderPhysicalExchange.newMembership Y c.1.1
        (CommanderPhysicalExchange.leftCard25 c.1.2) c.2.1
        (CommanderPhysicalExchange.rightCard25 c.2.2) = M)
      (Finset.univ : Finset CommanderPhysicalExchange.exchangeChoice)).card

/- The two intersection cards of `M.1` sum to `50` (`M.1.card = 50`); both
    branches need this. -/
theorem k1b_arith (Y : CommanderPermutation.Deck)
    (M : CommanderMembershipKernels.Membership) :
    (M.1 ∩ CommanderPermutation.leftCards Y).card + (M.1 ∩ rightCards Y).card = 50 := by
  have hD0 : Disjoint (M.1 ∩ CommanderPermutation.leftCards Y)
      (M.1 ∩ rightCards Y) :=
    Finset.disjoint_iff_inter_eq_empty.2 (k1b_union_decomp Y M).2
  have hSum : (M.1 ∩ CommanderPermutation.leftCards Y).card +
      (M.1 ∩ rightCards Y).card =
      ((M.1 ∩ CommanderPermutation.leftCards Y) ∪ (M.1 ∩ rightCards Y)).card := by
    rw [← (Finset.card_union_of_disjoint hD0)]
  have hUc : ((M.1 ∩ CommanderPermutation.leftCards Y) ∪
      (M.1 ∩ rightCards Y)).card = M.1.card := by
    rw [(k1b_union_decomp Y M).1]
  rw [hSum, hUc, M.2]

/- (2a) the 25/25 split: the witness pair hits `M` and is the unique hit, so the
    filtered choice set has cardinality `1`. -/
theorem k1b_count_25 (Y : CommanderPermutation.Deck)
    (M : CommanderMembershipKernels.Membership)
    (hO25 : (M.1 ∩ CommanderPermutation.leftCards Y).card = 25) :
    k1b_hitCount Y M = 1 := by
  classical
  unfold k1b_hitCount
  set Lstar : Finset (Fin 50) :=
    leftWitness Y (CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y))
  set Rstar : Finset (Fin 49) := rightWitness Y (M.1 ∩ rightCards Y)
  have hOsub' : (M.1 ∩ CommanderPermutation.leftCards Y) ⊆ CommanderPermutation.leftCards Y :=
    Finset.inter_subset_right
  have hSsub' : (M.1 ∩ rightCards Y) ⊆ rightCards Y := Finset.inter_subset_right
  have hArith := k1b_arith Y M
  have hDbl : (CommanderPermutation.leftCards Y \ (CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y))) = (M.1 ∩ CommanderPermutation.leftCards Y) := by
    ext x
    apply Iff.intro
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hlc, hnotD⟩
      by_contra hnot
      have hmemD : x ∈ CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y) :=
        Finset.mem_sdiff.mpr ⟨hlc, hnot⟩
      exact hnotD hmemD
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hM, hlc⟩
      have hnot : x ∉ CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y) := by
        intro hmemD
        rcases Finset.mem_sdiff.mp hmemD with ⟨_, hnotX⟩
        have hInt : x ∈ M.1 ∩ CommanderPermutation.leftCards Y :=
          Finset.mem_inter.mpr ⟨hM, hlc⟩
        exact hnotX hInt
      exact Finset.mem_sdiff.mpr ⟨hlc, hnot⟩
  have hS25 : (M.1 ∩ rightCards Y).card = 25 := by
    have hAr' := hArith
    rw [hO25] at hAr'
    omega
  have hLstar25 : Lstar.card = 25 := by
    show (leftWitness Y (CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y))).card = 25
    have hLsubT : (CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y)) ⊆
        CommanderPermutation.leftCards Y := by
      intro x hx
      exact (Finset.mem_sdiff.mp hx).1
    have hinj : Function.Injective (fun l : Fin 50 => Y (CommanderPermutation.leftPosition l)) := by
      intro l1 l2 h
      have hpos : CommanderPermutation.leftPosition l1 = CommanderPermutation.leftPosition l2 :=
        Y.injective h
      apply Fin.ext
      simp [CommanderPermutation.leftPosition] at hpos ⊢
      exact hpos
    have hCardRev : Lstar.card =
        (Finset.image (fun l : Fin 50 => Y (CommanderPermutation.leftPosition l)) Lstar).card :=
      (Finset.card_image_of_injective _ hinj).symm
    rw [hCardRev, k1b_witnessLeft_image Y
        (CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y)) hLsubT,
      Finset.card_sdiff_of_subset hOsub', leftCards_card Y, hO25]
  have hRstar25 : Rstar.card = 25 := by
    show (rightWitness Y (M.1 ∩ rightCards Y)).card = 25
    have hinj : Function.Injective (fun r : Fin 49 => Y (rightPosition r)) := by
      intro r1 r2 h
      apply Fin.ext
      simpa [rightPosition] using (congrArg Fin.val (Y.injective h))
    have hCardRev : (rightWitness Y (M.1 ∩ rightCards Y)).card =
        (swapRightPart Y (rightWitness Y (M.1 ∩ rightCards Y))).card := by
      simpa [swapRightPart] using (Finset.card_image_of_injective _ hinj).symm
    rw [hCardRev, k1b_witnessRight Y (M.1 ∩ rightCards Y) hSsub', hS25]
  have hHit : CommanderPhysicalExchange.newMembership Y Lstar hLstar25 Rstar hRstar25 = M := by
    refine (newMembership_set_eq Y Lstar ?_ Rstar ?_ M).2 ?_
    · simpa [CommanderPhysicalExchange.leftChoices, Finset.mem_powersetCard] using hLstar25
    · simpa [CommanderPhysicalExchange.rightChoices, Finset.mem_powersetCard] using hRstar25
    · rw [swapLeftPart_eq_complement Y Lstar,
        k1b_witnessLeft_removed Y (M.1 ∩ CommanderPermutation.leftCards Y) hOsub', hDbl,
        k1b_witnessRight Y (M.1 ∩ rightCards Y) hSsub', (k1b_union_decomp Y M).1]
  have hUnique : ∀ c : CommanderPhysicalExchange.exchangeChoice,
      CommanderPhysicalExchange.newMembership Y c.1.1
        (CommanderPhysicalExchange.leftCard25 c.1.2) c.2.1
        (CommanderPhysicalExchange.rightCard25 c.2.2) = M →
        c.1.1 = Lstar ∧ c.2.1 = Rstar := by
    intro c hHit'
    have hSet : (swapLeftPart Y c.1.1) ∪ (swapRightPart Y c.2.1) = M.1 :=
      (newMembership_set_eq Y c.1.1 c.1.2 c.2.1 c.2.2 M).1 hHit'
    have hLpCard : (swapLeftPart Y c.1.1).card = 25 :=
      swapLeftPart_card25 Y c.1.1 (CommanderPhysicalExchange.leftCard25 c.1.2)
    have hLpSubM : swapLeftPart Y c.1.1 ⊆ M.1 := by
      intro x hx
      have hunion : x ∈ (swapLeftPart Y c.1.1) ∪ (swapRightPart Y c.2.1) :=
        Finset.mem_union.mpr (Or.inl hx)
      rw [hSet] at hunion
      exact hunion
    have hLpSubLeft : swapLeftPart Y c.1.1 ⊆ CommanderPermutation.leftCards Y :=
      swapLeftPart_subset Y c.1.1
    have hLpSubT : swapLeftPart Y c.1.1 ⊆ (M.1 ∩ CommanderPermutation.leftCards Y) := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_of_subset hLpSubM hx,
        Finset.mem_of_subset hLpSubLeft hx⟩
    have hLpT : swapLeftPart Y c.1.1 = (M.1 ∩ CommanderPermutation.leftCards Y) := by
      apply Finset.Subset.antisymm hLpSubT
      intro x hx
      by_contra hnot
      have hmemD : x ∈ ((M.1 ∩ CommanderPermutation.leftCards Y) \ (swapLeftPart Y c.1.1)) :=
        Finset.mem_sdiff.mpr ⟨hx, hnot⟩
      have hzero : ((M.1 ∩ CommanderPermutation.leftCards Y) \ (swapLeftPart Y c.1.1)).card = 0 := by
        rw [Finset.card_sdiff_of_subset hLpSubT, hO25, hLpCard]
      have hEmpty : (M.1 ∩ CommanderPermutation.leftCards Y) \ (swapLeftPart Y c.1.1) =
          (∅ : Finset (Fin 99)) := Finset.card_eq_zero.mp hzero
      rw [hEmpty] at hmemD
      simpa using hmemD
    have hRCard : (swapRightPart Y c.2.1).card = 25 :=
      swapRightPart_card25 Y c.2.1 (CommanderPhysicalExchange.rightCard25 c.2.2)
    have hRSubM : swapRightPart Y c.2.1 ⊆ M.1 := by
      intro x hx
      have hunion : x ∈ (swapLeftPart Y c.1.1) ∪ (swapRightPart Y c.2.1) :=
        Finset.mem_union.mpr (Or.inr hx)
      rw [hSet] at hunion
      exact hunion
    have hRSubRight : swapRightPart Y c.2.1 ⊆ rightCards Y :=
      swapRightPart_subset Y c.2.1
    have hRSubS : swapRightPart Y c.2.1 ⊆ (M.1 ∩ rightCards Y) := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_of_subset hRSubM hx,
        Finset.mem_of_subset hRSubRight hx⟩
    have hRS : swapRightPart Y c.2.1 = (M.1 ∩ rightCards Y) := by
      apply Finset.Subset.antisymm hRSubS
      intro x hx
      by_contra hnot
      have hmemD : x ∈ ((M.1 ∩ rightCards Y) \ (swapRightPart Y c.2.1)) :=
        Finset.mem_sdiff.mpr ⟨hx, hnot⟩
      have hzero : ((M.1 ∩ rightCards Y) \ (swapRightPart Y c.2.1)).card = 0 := by
        rw [Finset.card_sdiff_of_subset hRSubS, hS25, hRCard]
      have hEmpty : (M.1 ∩ rightCards Y) \ (swapRightPart Y c.2.1) =
          (∅ : Finset (Fin 99)) := Finset.card_eq_zero.mp hzero
      rw [hEmpty] at hmemD
      simpa using hmemD
    have hLsub_c : removedLeft Y c.1.1 ⊆ CommanderPermutation.leftCards Y := by
      unfold removedLeft
      exact Finset.image_mono (fun l => Y (CommanderPermutation.leftPosition l))
        (Finset.subset_univ c.1.1)
    have hCompl : swapLeftPart Y c.1.1 =
        CommanderPermutation.leftCards Y \ removedLeft Y c.1.1 :=
      swapLeftPart_eq_complement Y c.1.1
    have hComplEta : swapLeftPart Y ↑c.1 =
        CommanderPermutation.leftCards Y \ removedLeft Y ↑c.1 := by
      simpa using hCompl
    have hLpTEta : swapLeftPart Y ↑c.1 = M.1 ∩ CommanderPermutation.leftCards Y := by
      simpa using hLpT
    have hLpSubLEta : swapLeftPart Y ↑c.1 ⊆ CommanderPermutation.leftCards Y := by
      simpa using hLpSubLeft
    have hLrem_c : removedLeft Y c.1.1 =
        CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y) := by
      calc removedLeft Y ↑c.1
        _ = CommanderPermutation.leftCards Y \ swapLeftPart Y ↑c.1 := by
          rw [(Finset.sdiff_sdiff_eq_self hLsub_c).symm, ← hComplEta]
        _ = CommanderPermutation.leftCards Y \
              (M.1 ∩ CommanderPermutation.leftCards Y) := by
          rw [hLpTEta]
    have hLrem_c2 : removedLeft Y Lstar =
        CommanderPermutation.leftCards Y \ (M.1 ∩ CommanderPermutation.leftCards Y) :=
      k1b_witnessLeft_removed Y (M.1 ∩ CommanderPermutation.leftCards Y) hOsub'
    have hC : (CommanderPermutation.leftCards Y \ (removedLeft Y c.1.1)) =
        (CommanderPermutation.leftCards Y \ (removedLeft Y Lstar)) := by
      rw [hLrem_c, hLrem_c2]
    have hLRemoved : removedLeft Y c.1.1 = removedLeft Y Lstar := by
      rw [hLrem_c, hLrem_c2]
    have hc1 : c.1.1 = Lstar := (removedLeft_injective Y) hLRemoved
    have hc2 : c.2.1 = Rstar := by
      apply swapRightPart_injective Y
      change (swapRightPart Y c.2.1) = (swapRightPart Y Rstar)
      rw [hRS, k1b_witnessRight Y (M.1 ∩ rightCards Y) hSsub']
    exact ⟨hc1, hc2⟩
  set cstar : CommanderPhysicalExchange.exchangeChoice :=
    ⟨⟨Lstar, by simpa [CommanderPhysicalExchange.leftChoices, Finset.mem_powersetCard] using hLstar25⟩,
     ⟨Rstar, by simpa [CommanderPhysicalExchange.rightChoices, Finset.mem_powersetCard] using hRstar25⟩⟩
  have hFilter : (Finset.filter (fun c => CommanderPhysicalExchange.newMembership Y c.1.1
      (CommanderPhysicalExchange.leftCard25 c.1.2) c.2.1
      (CommanderPhysicalExchange.rightCard25 c.2.2) = M)
    (Finset.univ : Finset CommanderPhysicalExchange.exchangeChoice)) = {cstar} := by
    ext c
    apply Iff.intro
    · intro hx
      simp at hx
      rcases hUnique c hx with ⟨hc1, hc2⟩
      have hmem1 : c.1 = cstar.1 := by
        apply Subtype.ext
        exact hc1
      have hmem2 : c.2 = cstar.2 := by
        apply Subtype.ext
        exact hc2
      have heq : c = cstar := Prod.ext hmem1 hmem2
      simpa [heq]
    · intro hx
      have hc : c = cstar := Finset.mem_singleton.mp hx
      simpa [hc] using hHit
  rw [hFilter, Finset.card_singleton]

end Shufflemath
