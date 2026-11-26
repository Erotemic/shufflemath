module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderFiberCount
public import Shufflemath.FiberDisintegration
public import Shufflemath.FiniteDeck.Gate6ThreeRound
public import Shufflemath.FiniteDeck.RelabelInvariance
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-!
## Gate 6 — the deterministic-start certificate and its relabeling extension

The headline `g6_threeRound_headline` proves `TV < 1/1000` for three rounds of
the **correct-order** physical round
`comp (PAK swapLaw) (PAK rho99Finite)` from the *fiber-uniform* 49-segregated
start.  The objective asks for the same bound from an **arbitrary
deterministic deck**.  The documented bridge works in four steps:

1. every deck whose left pile is exactly `leftOrigSet` (the 49-segregated
   fiber, `project = commanderSegregatedState`) has the same post-exchange
   membership law — the uniform law on the `x = 25` membership fiber
   `{M // membershipCount M = 25}`;
2. the fiber-uniform start is a *mixture* of exactly those decks with equal
   weight, hence derives the same post-exchange membership law as the
   deterministic reference deck (the identity permutation);
3. one-step bridge (`apply (pointMass segDeck) idealKernel =
   apply g6ThreeRoundStart idealKernel`) + the same three-round telescope give
   `TV < 1/1000` from the reference deck;
4. the deck-relabeling `e ↦ e.trans g` fixes the uniform full-deck law and is
   an equivariance of the physical round, so the bound transports to every
   deterministic start.
-/

open CommanderPermutation
open CommanderMembershipKernels
open CommanderPhysicalExchange
open BernoulliLaplace
open FiberDisintegration

/-! ## 1. The deterministic reference deck -/

/-- The reference segregated deck: the identity permutation — exactly the 50
    initially-left cards in the left pile. -/
noncomputable def segDeck : Deck := Equiv.refl (Fin 99)

/-- The right positions are injective (mirror of `leftPosition_injective`). -/
theorem rightPosition_injective : Function.Injective rightPosition := by
  intro a b hab
  apply Fin.ext
  simpa [rightPosition] using congrArg Fin.val hab

theorem leftCards_segDeck : leftCards segDeck = leftOrigSet := by
  rw [leftOrigSet]
  ext c
  unfold leftCards
  simp only [segDeck, Equiv.refl_apply, leftPosition, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hc
    exact ⟨⟨c.val, hc⟩, rfl⟩

/-- Every deck whose project-class is the 49-segregated commander state has
    exactly the initially-left cards in the left pile. -/
theorem leftCards_eq_leftOrigSet_of_project (d : Deck)
    (h : project d = commanderSegregatedState) : leftCards d = leftOrigSet := by
  have hval : (project d).val = 49 := by
    have hv := congrArg Fin.val h
    have hcmd : commanderSegregatedState.val = 49 := rfl
    rw [hcmd] at hv
    exact hv
  have h50 : leftOriginalCount d = 50 := by
    have hval' := project_count d
    rw [hval] at hval'
    omega
  have hcard : ((Finset.univ : Finset (Fin 50)).filter
      (fun j => (d (leftPosition j)).val < 50)).card = 50 := h50
  have hfilt : ((Finset.univ : Finset (Fin 50)).filter
      (fun j => (d (leftPosition j)).val < 50)) = Finset.univ := by
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard]; exact le_refl 50)
  have hsub : leftCards d ⊆ leftOrigSet := by
    intro c hc
    unfold leftCards at hc
    rcases Finset.mem_image.mp hc with ⟨i, -, rfl⟩
    have hi : (d (leftPosition i)).val < 50 := by
      have hmem : i ∈ ((Finset.univ : Finset (Fin 50)).filter
          (fun j => (d (leftPosition j)).val < 50)) := by
        rw [hfilt]
        exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hmem).2
    unfold leftOrigSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [leftCards_card, leftOrigSet_card])

/-! ## 2. The target subtype and the choice-space card -/

/-- The `x = 25` membership fiber: memberships whose left pile carries exactly
    25 initially-left cards.  (Definitionally `MembershipFiber 25`.) -/
abbrev SegMembership : Type := {M : Membership // membershipCount M = 25}

theorem card_segMembership :
    Fintype.card SegMembership = Nat.choose 50 25 * Nat.choose 49 25 := by
  show Fintype.card (MembershipFiber 25) = _
  rw [MembershipFiber_card, fiberMembershipSets_card]

theorem card_exchangeChoice :
    Fintype.card exchangeChoice = Nat.choose 50 25 * Nat.choose 49 25 := by
  classical
  have hProd : Fintype.card exchangeChoice =
      Fintype.card {L : Finset (Fin 50) // L ∈ leftChoices} *
        Fintype.card {R : Finset (Fin 49) // R ∈ rightChoices} := by
    unfold exchangeChoice
    simp only [Fintype.card_prod]
  have hSubL : Fintype.card {L : Finset (Fin 50) // L ∈ leftChoices} =
      (leftChoices).card := by
    simp [Fintype.card_subtype, leftChoices, Finset.mem_powersetCard]
  have hSubR : Fintype.card {R : Finset (Fin 49) // R ∈ rightChoices} =
      (rightChoices).card := by
    simp [Fintype.card_subtype, rightChoices, Finset.mem_powersetCard]
  have hLc : (leftChoices).card = Nat.choose 50 25 := by
    unfold leftChoices
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hRc : (rightChoices).card = Nat.choose 49 25 := by
    unfold rightChoices
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hProd, hSubL, hSubR, hLc, hRc]

/-! ## 3. The per-deck exchange bijection -/

/-- The cards at the right positions never fall in `leftOrigSet` for a deck
    whose left pile is exactly `leftOrigSet`. -/
theorem rightCards_not_leftOrigSet (d : Deck) (hd : leftCards d = leftOrigSet) :
    Disjoint ((Finset.univ : Finset (Fin 49)).image (fun r => d (rightPosition r)))
      leftOrigSet := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.eq_empty_of_forall_notMem
  intro c hc
  rcases Finset.mem_inter.mp hc with ⟨hcR, hcL⟩
  rcases Finset.mem_image.mp hcR with ⟨r, _, hr⟩
  have hcLsub : c ∈ leftCards d := hd ▸ hcL
  rcases Finset.mem_image.mp hcLsub with ⟨l, _, hl⟩
  have heq : d (leftPosition l) = d (rightPosition r) := by rw [hr]; exact hl
  have heq' : leftPosition l = rightPosition r := d.injective heq
  have hval : (leftPosition l).val = (rightPosition r).val := congrArg Fin.val heq'
  have hlt : (leftPosition l).val < 50 := by simp [leftPosition]
  have hge : 50 ≤ (rightPosition r).val := by simp [rightPosition]
  omega

/-- The left part of a post-exchange membership for a segregated deck is exactly
    the image of the unselected left positions. -/
theorem leftPart_of_newLeftCards (d : Deck) (hd : leftCards d = leftOrigSet)
    (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    newLeftCards d L R ∩ leftOrigSet =
      ((Finset.univ : Finset (Fin 50)) \ L).image (fun (l : Fin 50) => d (leftPosition l)) := by
  classical
  apply Finset.ext
  intro c
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨hUnion, hcL⟩
    rcases Finset.mem_union.mp hUnion with hLeft | hRight
    · rcases Finset.mem_image.mp hLeft with ⟨l, hl, rfl⟩
      exact Finset.mem_image.mpr ⟨l, by simpa using hl, rfl⟩
    · rcases Finset.mem_image.mp hRight with ⟨r, _, hcard⟩
      exfalso
      have hmem : c ∈ ((Finset.univ : Finset (Fin 49)).image
          (fun r => d (rightPosition r))) :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hcard⟩
      have hd_mem := (Finset.disjoint_left.mp (rightCards_not_leftOrigSet d hd)) hmem
      exact hd_mem hcL
  · intro h
    rcases Finset.mem_image.mp h with ⟨l, hl, rfl⟩
    have hcard_left : d (leftPosition l) ∈ leftCards d := by
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨l, by simpa using hl, rfl⟩)),
        hd ▸ hcard_left⟩

/-- The right part of a post-exchange membership for a segregated deck is exactly
    the image of the selected right positions. -/
theorem rightPart_of_newLeftCards (d : Deck) (hd : leftCards d = leftOrigSet)
    (L : Finset (Fin 50)) (R : Finset (Fin 49)) :
    newLeftCards d L R \ leftOrigSet = R.image (fun (r : Fin 49) => d (rightPosition r)) := by
  classical
  apply Finset.ext
  intro c
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨hUnion, hcL⟩
    rcases Finset.mem_union.mp hUnion with hLeft | hRight
    · rcases Finset.mem_image.mp hLeft with ⟨l, _, hcard⟩
      exfalso
      have hcard_left : d (leftPosition l) ∈ leftCards d := by
        exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
      have hcLpos : d (leftPosition l) ∈ leftOrigSet := hd ▸ hcard_left
      rw [hcard] at hcLpos
      exact hcL hcLpos
    · rcases Finset.mem_image.mp hRight with ⟨r, hr, hcard⟩
      exact Finset.mem_image.mpr ⟨r, hr, hcard⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, rfl⟩
    have hnew : d (rightPosition r) ∈ newLeftCards d L R := by
      unfold newLeftCards
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
    have hcL : d (rightPosition r) ∉ leftOrigSet := by
      have hmem : d (rightPosition r) ∈ ((Finset.univ : Finset (Fin 49)).image
          (fun r => d (rightPosition r))) :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
      exact (Finset.disjoint_left.mp (rightCards_not_leftOrigSet d hd)) hmem
    exact Finset.mem_sdiff.mpr ⟨hnew, hcL⟩

/-- The membership count of a post-exchange membership from a segregated deck
    is 25 — exactly the 25 unselected left positions, all of which carry
    initially-left cards. -/
theorem membershipCount_newMembership (d : Deck) (hd : leftCards d = leftOrigSet)
    (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25) :
    membershipCount (newMembership d L hL R hR) = 25 := by
  classical
  have h : membershipCount (newMembership d L hL R hR) =
      ((newLeftCards d L R) ∩ leftOrigSet).card := rfl
  rw [h, leftPart_of_newLeftCards d hd L R]
  have hinj : Function.Injective (fun (l : Fin 50) => d (leftPosition l)) :=
    d.injective.comp leftPosition_injective
  rw [Finset.card_image_of_injective _ hinj]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ L)]
  rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- The exchange choices of a segregated deck map injectively into the `x = 25`
    membership fiber. -/
theorem segChoiceMembership_injective (d : Deck) (hd : leftCards d = leftOrigSet)
    (c₁ c₂ : exchangeChoice)
    (h : newMembership d c₁.1.1 (leftCard25 c₁.1.2) c₁.2.1 (rightCard25 c₁.2.2) =
         newMembership d c₂.1.1 (leftCard25 c₂.1.2) c₂.2.1 (rightCard25 c₂.2.2)) :
    c₁ = c₂ := by
  have hsets : newLeftCards d c₁.1.1 c₁.2.1 = newLeftCards d c₂.1.1 c₂.2.1 :=
    congrArg Subtype.val h
  have hL : (Finset.univ : Finset (Fin 50)) \ c₁.1.1 =
      (Finset.univ : Finset (Fin 50)) \ c₂.1.1 := by
    have hsets' : (newLeftCards d c₁.1.1 c₁.2.1) ∩ leftOrigSet =
        (newLeftCards d c₂.1.1 c₂.2.1) ∩ leftOrigSet := by
      rw [hsets]
    rw [leftPart_of_newLeftCards d hd c₁.1.1 c₁.2.1,
        leftPart_of_newLeftCards d hd c₂.1.1 c₂.2.1] at hsets'
    have hinj : Function.Injective (fun (l : Fin 50) => d (leftPosition l)) :=
      d.injective.comp leftPosition_injective
    exact (Finset.image_inj hinj).mp hsets'
  have hLset : c₁.1.1 = c₂.1.1 := by
    have h1 := (Finset.sdiff_eq_sdiff_iff_inter_eq_inter).mp hL
    simp only [Finset.univ_inter] at h1
    exact h1
  have hRset : c₁.2.1 = c₂.2.1 := by
    have hsets'' : (newLeftCards d c₁.1.1 c₁.2.1) \ leftOrigSet =
        (newLeftCards d c₂.1.1 c₂.2.1) \ leftOrigSet := by
      rw [hsets]
    rw [rightPart_of_newLeftCards d hd c₁.1.1 c₁.2.1,
        rightPart_of_newLeftCards d hd c₂.1.1 c₂.2.1] at hsets''
    have hinj : Function.Injective (fun (r : Fin 49) => d (rightPosition r)) :=
      d.injective.comp rightPosition_injective
    exact (Finset.image_inj hinj).mp hsets''
  have hcc : c₁.1 = c₂.1 := Subtype.ext hLset
  have hcr : c₁.2 = c₂.2 := Subtype.ext hRset
  exact Prod.ext hcc hcr

/-- The exchange choice space is in bijection with the `x = 25` membership fiber
    (any deck whose left pile is exactly `leftOrigSet`).  Injectivity above plus
    equal cardinality (`card_exchangeChoice`, `card_segMembership`). -/
noncomputable def segChoiceMembership_equiv (d : Deck) (hd : leftCards d = leftOrigSet) :
    exchangeChoice ≃ SegMembership := by
  classical
  exact Equiv.ofBijective
    (fun c : exchangeChoice =>
      (⟨newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2),
        membershipCount_newMembership d hd c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)⟩ : SegMembership))
    ((Fintype.bijective_iff_injective_and_card
      (fun c : exchangeChoice =>
        (⟨newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2),
          membershipCount_newMembership d hd c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)⟩ : SegMembership))).2
      ⟨fun c₁ c₂ h => segChoiceMembership_injective d hd c₁ c₂ (congrArg Subtype.val h),
       by rw [card_exchangeChoice, card_segMembership]⟩)

instance : Nonempty SegMembership := by
  exact ⟨⟨newMembership segDeck left25 left25_card right25 right25_card,
    membershipCount_newMembership segDeck leftCards_segDeck left25 left25_card right25 right25_card⟩⟩

/-- The post-exchange membership law of a segregated deck is the uniform `x = 25`
    subtype law, pushed through `Subtype.val`. -/
theorem rawExchangeMembership_eq_fiberUniform (d : Deck) (hd : leftCards d = leftOrigSet) :
    rawExchangeMembership d =
      (GSR.uniformDist SegMembership).map (fun M => M.1) := by
  classical
  unfold rawExchangeMembership
  have hmap : (GSR.uniformDist exchangeChoice).map
      (fun c : exchangeChoice =>
        newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)) =
    (GSR.uniformDist SegMembership).map (fun M => M.1) := by
    have hseq : (fun c : exchangeChoice =>
        newMembership d c.1.1 (leftCard25 c.1.2) c.2.1 (rightCard25 c.2.2)) =
      (fun c : exchangeChoice => ((segChoiceMembership_equiv d hd c).1)) := by
      funext c
      simp only [segChoiceMembership_equiv, Equiv.coe_ofBijective, Subtype.coe_mk]
    rw [hseq]
    rw [← Convexity.StdSimplex.map_map,
      GSR.map_bijective_uniformDist (segChoiceMembership_equiv d hd)]
  exact hmap

/-- Corollary: the reference deck's exchange law. -/
theorem rawExchangeMembership_segDeck_eq :
    rawExchangeMembership segDeck =
      (GSR.uniformDist SegMembership).map (fun M => M.1) :=
  rawExchangeMembership_eq_fiberUniform segDeck leftCards_segDeck

/-! ## 4. The one-step bridge -/

/-- The mass of the fiber-uniform start: a single fiberLaw mass (the point mass
    selects the segregated source state). -/
theorem mass_fiberUniformStart (j : Deck) :
    Dist.mass g6ThreeRoundStart j =
      if project j = commanderSegregatedState then
        ((fiberSet project commanderSegregatedState).card : Rat)⁻¹ else 0 := by
  unfold g6ThreeRoundStart
  rw [FiniteKernel.apply_mass]
  simp only [Dist.mass_pointMass, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ commanderSegregatedState
      (fun i => Dist.mass (fiberLaw project project_surjective i) j)]
  rw [fiberLaw_mass, if_pos (Finset.mem_univ commanderSegregatedState)]

/-- The one-step mixture: the fiber-uniform start derives the same
    post-exchange membership law as any segregated deck — each fiber deck's
    law equals the uniform `x = 25` law, so the mixture does too. -/
theorem apply_fiberUniformStart_rawExchangeMembership :
    FiniteKernel.apply g6ThreeRoundStart rawExchangeMembership = rawExchangeMembership segDeck := by
  classical
  ext M
  rw [← Dist.mass, FiniteKernel.apply_mass]
  have hcard : 0 < (fiberSet project commanderSegregatedState).card :=
    fiber_card_pos project project_surjective commanderSegregatedState
  have hcont : ∀ j : Deck, g6ThreeRoundStart.mass j * Dist.mass (rawExchangeMembership j) M =
      if project j = commanderSegregatedState then
        ((fiberSet project commanderSegregatedState).card : Rat)⁻¹ *
          Dist.mass ((GSR.uniformDist SegMembership).map (fun x => x.1)) M
      else 0 := by
    intro j
    rw [mass_fiberUniformStart]
    by_cases hj : project j = commanderSegregatedState
    · rw [if_pos hj, if_pos hj]
      have hij := leftCards_eq_leftOrigSet_of_project j hj
      rw [rawExchangeMembership_eq_fiberUniform j hij]
    · rw [if_neg hj, if_neg hj, zero_mul]
  have hsum : (Finset.univ.sum fun j => g6ThreeRoundStart.mass j * Dist.mass (rawExchangeMembership j) M) =
      Finset.univ.sum fun j => if project j = commanderSegregatedState then
        ((fiberSet project commanderSegregatedState).card : Rat)⁻¹ *
          Dist.mass ((GSR.uniformDist SegMembership).map (fun x => x.1)) M
      else 0 :=
    Finset.sum_congr rfl (fun j _ => hcont j)
  rw [hsum]
  rw [sum_if_constant Finset.univ (fun j => project j = commanderSegregatedState)]
  -- fiberSet = univ.filter (project = x0)
  show ((fiberSet project commanderSegregatedState).card : Rat) *
    (((fiberSet project commanderSegregatedState).card : Rat)⁻¹ *
      Dist.mass ((GSR.uniformDist SegMembership).map (fun x => x.1)) M) =
    Dist.mass (rawExchangeMembership segDeck) M
  rw [rawExchangeMembership_segDeck_eq]
  have hNe : ((fiberSet project commanderSegregatedState).card : Rat) ≠ 0 := by
    exact_mod_cast hcard.ne'
  field_simp

/-- The ideal `q3` kernel factored through the membership law. -/
theorem idealKernel_eq_comp_rawExchangeMembership_localLift :
    g6ThreeRoundFiniteKernel =
      FiniteKernel.comp CommanderPhysicalExchange.rawExchangeMembership
        CommanderMembershipKernels.localLift := by
  unfold g6ThreeRoundFiniteKernel
  unfold PhysicalExchangeReduction.exchangeThenLocalReset
  unfold PhysicalExchangeReduction.localReset
  rw [← FiniteKernel.comp_assoc, CommanderPhysicalExchange.rawExchange_membership_pushforward]

/-- The one-step bridge: the ideal 3-round round kernel applied to the
    deterministic reference deck equals the same kernel applied to the
    fiber-uniform start. -/
theorem apply_segDeck_idealKernel_eq :
    FiniteKernel.apply (Dist.pointMass segDeck) g6ThreeRoundFiniteKernel =
      FiniteKernel.apply g6ThreeRoundStart g6ThreeRoundFiniteKernel := by
  rw [idealKernel_eq_comp_rawExchangeMembership_localLift,
    ← FiniteKernel.apply_comp, ← FiniteKernel.apply_comp]
  rw [apply_fiberUniformStart_rawExchangeMembership]
  rw [FiniteKernel.apply_pointMass]

/-! ## 5. The deterministic headline -/

/-- **Deterministic Gate 6 headline.** Three rounds of the correct-order physical
    round from the deterministic reference segregated deck land within total
    variation `< 1/1000` of the uniform `99!` deck. -/
theorem g6Deterministic_headline :
    Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
        (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound]))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  have hL : g6ThreeRoundFiniteKernel =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
    dsimp only [g6ThreeRoundFiniteKernel]
    exact g6_3round_idealKernel_eq_fullRound
  -- the ideal-kernel 3-round run from the reference deck equals that from
  -- the fiber-uniform start (the one-step bridge, iterated)
  have hbridge :
      FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]) =
        FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]) := by
    rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel) (μ := Dist.pointMass segDeck),
        g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel) (μ := g6ThreeRoundStart)]
    have hrun : ∀ μ : Dist Deck, FiniteKernel.run g6ThreeRoundFiniteKernel 3 μ =
        FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ g6ThreeRoundFiniteKernel) g6ThreeRoundFiniteKernel) g6ThreeRoundFiniteKernel := by
      intro μ
      rw [FiniteKernel.run_succ, FiniteKernel.run_succ, FiniteKernel.run_succ]
      simp [FiniteKernel.run]
    rw [hrun, hrun]
    rw [apply_segDeck_idealKernel_eq]
  -- telescope
  have hAccum :
      Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                    g6ThreeRoundFiniteRound]))
        (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel])) ≤ 3 * δ1 := by
    exact compList_telescope_nstep_le_n_times_d
      [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound]
      [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel]
      (by simp) δ1 (by rw [δ1_eq_2401_over_8388608]; norm_num)
      (fun a ha => by
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        dsimp at hp
        rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_nil_iff] at hp
        rcases hp with h₁ | h₂ | h₃ | h₄
        · rw [h₁]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · rw [h₂]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · rw [h₃]
          exact hL ▸ g6_threeRound_kernelDiscrepancy_le_δ1
        · exfalso; exact h₄)
      (Dist.pointMass segDeck)
  have hIdeal :
      Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]))
        (GSR.uniformDist Deck) ≤ q3 := by
    rw [hbridge]
    exact g6_threeRound_finiteRun3_tv_le_q3
  calc
    _ ≤ Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                    g6ThreeRoundFiniteRound]))
          (FiniteKernel.apply (Dist.pointMass segDeck)
            (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                      g6ThreeRoundFiniteKernel])) +
        Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]))
          (GSR.uniformDist Deck) := by
      simpa only [Dist.tv] using Dist.tv_triangle
        (p := FiniteKernel.apply (Dist.pointMass segDeck)
              (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound,
                        g6ThreeRoundFiniteRound]))
        (q := FiniteKernel.apply (Dist.pointMass segDeck)
              (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                        g6ThreeRoundFiniteKernel]))
        (r := GSR.uniformDist Deck)
    _ ≤ 3 * δ1 + q3 := add_le_add hAccum hIdeal
    _ < (1 : Rat) / 1000 := by rw [add_comm]; exact gate6_headline_lt_thousandth

/-! ## 6. The relabeling extension -/

/-- The PAK kernels are equivariant under the deck-relabeling `d ↦ d.trans g`. -/
theorem pak_relabel_equivariant (noise : Dist Deck) (g d : Deck) :
    FiniteDeck.permutationActionKernel noise (d.trans g) =
      (FiniteDeck.permutationActionKernel noise d).map (fun x => x.trans g) := by
  unfold FiniteDeck.permutationActionKernel
  rw [Convexity.StdSimplex.map_map]
  have hF : (fun (p : Deck) => Equiv.trans p (d.trans g)) =
      (fun (p : Deck) => (Equiv.trans p d).trans g) := by
    funext p
    exact (Equiv.trans_assoc p d g).symm
  rw [hF]

/-- Applying an equivariant kernel after a pushforward is the pushforward of the
    apply (the kernel-level monadic equivariance). -/
theorem apply_map_equivariant (K : FiniteKernel Deck Deck) (g : Deck) (μ : Dist Deck)
    (hK : ∀ d, K (d.trans g) = (K d).map (fun x => x.trans g)) :
    FiniteKernel.apply (μ.map (fun x => x.trans g)) K = (FiniteKernel.apply μ K).map (fun x => x.trans g) := by
  classical
  have h1 : (μ.map (fun x => x.trans g)).map K = μ.map (fun x => K (x.trans g)) := by
    rw [Convexity.StdSimplex.map_map]
  have h2 : ((μ.map K).join).map (fun x => x.trans g) =
      (μ.map (fun x => (K x).map (fun y => y.trans g))).join := by
    ext1
    simp [Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      Finsupp.smul_sum]
  unfold FiniteKernel.apply
  rw [h1, h2]
  have h3 : (fun x : Deck => K (x.trans g)) = (fun x : Deck => (K x).map (fun y => y.trans g)) := by
    funext x
    exact hK x
  rw [h3]

/-- The finite round kernel is equivariant under the deck-relabeling. -/
theorem finite_kernel_relabel_equivariant (g : Deck) (d : Deck) :
    g6ThreeRoundFiniteRound (d.trans g) =
      (g6ThreeRoundFiniteRound d).map (fun x => x.trans g) := by
  classical
  unfold g6ThreeRoundFiniteRound FiniteKernel.comp
  rw [pak_relabel_equivariant Gate6Crux.swapLaw g d]
  -- LHS: (((PAK swapLaw d).map f).map PAK rho99Finite).join
  have hfun : (fun (x : Deck) => FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite (x.trans g)) =
      (fun (x : Deck) => (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite x).map (fun y => y.trans g)) := by
    funext x
    exact pak_relabel_equivariant Gate6Crux.rho99Finite g x
  have hjoin : (((FiniteDeck.permutationActionKernel Gate6Crux.swapLaw d).map
      (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)).join).map
      (fun x => x.trans g) =
      (((FiniteDeck.permutationActionKernel Gate6Crux.swapLaw d).map
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Finite)).map
        (fun x => x.map (fun y => y.trans g))).join := by
    ext1
    simp [Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      Finsupp.smul_sum]
  rw [Convexity.StdSimplex.map_map, hjoin, hfun]
  rw [Convexity.StdSimplex.map_map]

/-- The run-map relabeling lemma: pushing the start law through the relabeling
    equals running the relabel-invariant kernel. -/
theorem run_map_relabel (g : Deck) (n : Nat) (μ : Dist Deck) :
    FiniteKernel.run g6ThreeRoundFiniteRound n (μ.map (fun x => x.trans g)) =
      (FiniteKernel.run g6ThreeRoundFiniteRound n μ).map (fun x => x.trans g) := by
  induction n generalizing μ with
  | zero =>
    simp [FiniteKernel.run]
  | succ k ih =>
    rw [FiniteKernel.run_succ, ih,
        apply_map_equivariant g6ThreeRoundFiniteRound g (FiniteKernel.run g6ThreeRoundFiniteRound k μ)
          (fun d => finite_kernel_relabel_equivariant g d),
        ← FiniteKernel.run_succ]

/-- **Deterministic Gate 6 headline from ANY deterministic deck.** -/
theorem g6Deterministic_headline_anyDeck (d : Deck) :
    Dist.tv (FiniteKernel.apply (Dist.pointMass d)
        (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound]))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  have hbridge :
      FiniteKernel.apply (Dist.pointMass d)
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound]) =
        (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound, g6ThreeRoundFiniteRound])).map
          (fun x => x.trans d) := by
    rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteRound) (μ := Dist.pointMass d),
        g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteRound) (μ := Dist.pointMass segDeck)]
    have hmap : Dist.pointMass d = (Dist.pointMass segDeck).map (fun x => x.trans d) := by
      simp only [segDeck, Equiv.refl_trans]
      exact (FiniteDeck.pointMassMap segDeck (fun x => x.trans d)).symm
    rw [hmap]
    exact run_map_relabel d 3 (Dist.pointMass segDeck)
  rw [hbridge]
  rw [← uniformDeck_relabel_invariant 99 d]
  have hconv : (fun x : Deck => x.trans d) = (relabel_equiv d).toFun := rfl
  rw [hconv]
  rw [tv_bijective_invariance (relabel_equiv d) _ _]
  exact g6Deterministic_headline

end Shufflemath
end
