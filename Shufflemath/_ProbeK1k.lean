module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.Gate6Crux
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
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
theorem k1b_symm_pointwise (L : Finset (Fin 50)) (_hL : L.card = 25)
    (R : Finset (Fin 49)) (_hR : R.card = 25)
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

/- **k1b_swapPerm_pointwise_sq** (the involution, function level): the swap
  permutation is its own square, pointwise — `swapPerm` is
  `Equiv.ofBijective swapFn …` and `swapFn` is an involution, so each
  `swapPerm`-application reduces to `swapFn` and the result is exactly
  `swapFn_involution`.  (No 99! normalisation: two `rw` steps + `exact`.)
  Used for the `(s ∘ s.symm = id)` retraction, whose `Equiv.symm_apply`
  form does not match the let-unfolded goal shape in this Mathlib. -/
theorem k1b_swapPerm_pointwise_sq (L : Finset (Fin 50)) (hL : L.card = 25)
    (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) (i : Fin 99) :
    (FiniteDeck.swapPerm 99 50 h50le99 L R b)
      ((FiniteDeck.swapPerm 99 50 h50le99 L R b) i) = i := by
  rw [FiniteDeck.swapPerm_apply 99 50 h50le99 L R b,
      FiniteDeck.swapPerm_apply 99 50 h50le99 L R b]
  exact FiniteDeck.swapFn_involution 99 50 h50le99 L R b i

/- **k1b_beta** (the combinatorial heart — PROVED): for every deck `X` and
  25/25 choice, `X` lies in the image of the fiber transport `q ↦ (s_c).trans q`
  over the fiber of `d` iff the 25/25 split of `X` at that choice equals
  `membership d`.  Both directions are retraction chains: the unique preimage
  of `X` is `(s_c).symm.trans X`, and the pure-Equiv retractions
  `(s.symm ∘ s = id)` / `(s ∘ s.symm = id)` — no 99! normalisation anywhere:
  the statement avoids the `(s_c).symm.trans` composite entirely (it is
  carried through by the *proven* equation `k1b_inv_swap_membership`, which
  `rw` matches without whnf).  (4-card Python model: the image condition is
  exactly this split-equality — NOT `newMembership d c = membership X`, which
  mismatches 24/96 pairs — while the headline deck laws still coincide, via
  the counting symmetry `#{c: split_X(c)=m_d} = #{c: split_d(c)=m_X}` the K1b
  assembly must carry.) -/
theorem k1b_beta (d X : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L.card = 25) (R : Finset (Fin 49)) (hR : R.card = 25)
    (b : {i : Fin 50 // i ∈ L} ≃ {j : Fin 49 // j ∈ R}) :
    (∃ q : CommanderPermutation.Deck,
       CommanderMembershipKernels.membership q = CommanderMembershipKernels.membership d ∧
       (FiniteDeck.swapPerm 99 50 h50le99 L R b).trans q = X) ↔
      CommanderPhysicalExchange.newMembership X L hL R hR =
        CommanderMembershipKernels.membership d := by
  let s := FiniteDeck.swapPerm 99 50 h50le99 L R b
  constructor
  · -- (→):  q in the fiber, X = s.trans q.
    rintro ⟨q, hmq, hX⟩
    have hXeq : X = s.trans q := hX.symm
    have hdeck : s.symm.trans (s.trans q) = q := by
      ext1 i
      rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.apply_symm_apply (e := s)]
    -- newMembership X = membership (s.symm.trans X)  [proven, no whnf]
    --               = membership ((s.symm).trans (s.trans q))  [hXeq]
    --               = membership q  [retraction]
    --               = membership d  [hmq]
    calc
      CommanderPhysicalExchange.newMembership X L hL R hR =
        CommanderMembershipKernels.membership (s.symm.trans X) :=
          (k1b_inv_swap_membership X L hL R hR b).symm
      _ = CommanderMembershipKernels.membership (s.symm.trans (s.trans q)) := by rw [hXeq]
      _ = CommanderMembershipKernels.membership q := by rw [hdeck]
      _ = CommanderMembershipKernels.membership d := hmq
  · -- (←):  take q := s.symm.trans X.
    rintro hnm
    refine ⟨s.symm.trans X, ?_, ?_⟩
    · -- membership (s.symm.trans X) = newMembership X = membership d
      rw [k1b_inv_swap_membership X L hL R hR b]
      exact hnm
    · -- X = s.trans (s.symm.trans X)  pointwise:  (f.trans g) a = g (f a),
      --  twice, then e.symm (e i) = i.
      ext1 i
      rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.symm_apply_apply (e := s)]

/- ================================================================
   The 25/25 counting split (k1b_count_split and its pile structure).

   For a deck `d` and a 50-card membership `M`, the number of 25/25
   choices `(L, R)` for which the post-exchange membership equals `M`
   is the indicator of `|leftCards d ∩ M| = 25`: the 25+25 split of `M`
   is forced (the overlap `M ∩ leftCards d` must sit exactly in the
   kept-left part, and `M`'s right-pile part exactly in the pulled-right
   part), giving exactly one `(L, R)` — verified on the 4-card model
   before proving (counts (0,0)/(1,1)/(0,0) by overlap 0/1/2).
   ================================================================ -/

-- The 49 cards occupying the right working positions of deck `d`.
def rightCards (d : CommanderPermutation.Deck) : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 49)).image (fun j => d (rightPosition j))

theorem rightPosition_inj : Function.Injective rightPosition := by
  intro a b h
  apply Fin.ext
  simpa [rightPosition] using congrArg Fin.val h

theorem rightCards_card (d : CommanderPermutation.Deck) : (rightCards d).card = 49 := by
  unfold rightCards
  rw [Finset.card_image_of_injective]
  · simp
  · exact fun j1 j2 h => rightPosition_inj (d.injective h)

-- The left and right piles of a deck are disjoint (distinct positions,
-- injective deck map).
theorem leftCards_rightCards_disjoint (d : CommanderPermutation.Deck) :
    Disjoint (CommanderPermutation.leftCards d) (rightCards d) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.ext
  intro card
  constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨hL, hR⟩
    rcases Finset.mem_image.mp hL with ⟨l, _, heqL⟩
    rcases Finset.mem_image.mp hR with ⟨r, _, heqR⟩
    have heq : d (CommanderPermutation.leftPosition l) =
        d (rightPosition r) := heqL.trans heqR.symm
    have hne : CommanderPermutation.leftPosition l ≠
        rightPosition r := by
      intro heq2
      have hval : (CommanderPermutation.leftPosition l).val =
          (rightPosition r).val := congrArg Fin.val heq2
      have hL : (CommanderPermutation.leftPosition l).val < 50 := by
        simp [CommanderPermutation.leftPosition]
      have hR : 50 ≤ (rightPosition r).val := by
        simp [rightPosition]
      omega
    have hne' : d (CommanderPermutation.leftPosition l) ≠
        d (rightPosition r) :=
      fun heq3 => hne (d.injective heq3)
    exact False.elim (hne' heq)
  · intro h
    have hne : ¬ card ∈ (∅ : Finset (Fin 99)) := by simp
    exact False.elim (hne h)

theorem leftCards_rightCards_union_univ (d : CommanderPermutation.Deck) :
    (CommanderPermutation.leftCards d) ∪ (rightCards d) = (Finset.univ : Finset (Fin 99)) := by
  classical
  apply Finset.ext
  intro card
  simp only [Finset.mem_union, Finset.mem_univ, CommanderPermutation.leftCards,
      rightCards]
  apply Iff.intro
  · intro _
    trivial
  · intro _
    rcases d.surjective card with ⟨p, hp⟩
    by_cases hlt : p.val < 50
    · left
      have hw : p = CommanderPermutation.leftPosition ⟨p.val, hlt⟩ := by
        apply Fin.ext
        simp [CommanderPermutation.leftPosition]
      rw [← hp, hw]
      exact Finset.mem_image_of_mem _ (by simp)
    · right
      have hge : 50 ≤ p.val := by omega
      have hw : p = rightPosition ⟨p.val - 50, by omega⟩ := by
        apply Fin.ext
        simp [rightPosition, Fin.val_mk]
        omega
      rw [← hp, hw]
      exact Finset.mem_image_of_mem _ (by simp)

-- The two parts of a 25/25 exchange, separately: the kept left cards
-- (left positions outside `L`) and the pulled right cards (right
-- positions inside `R`) — the exact two summands of `newLeftCards`.
def swapLeftPart (d : CommanderPermutation.Deck) (L : Finset (Fin 50)) :
    Finset (Fin 99) :=
  Finset.image (fun l => d (CommanderPermutation.leftPosition l))
    ((Finset.univ : Finset (Fin 50)) \ L)

def swapRightPart (d : CommanderPermutation.Deck) (R : Finset (Fin 49)) :
    Finset (Fin 99) :=
  Finset.image (fun r => d (rightPosition r)) R

-- Each part is a 25-card sub-pile: the kept-left part sits in the left
-- pile, the pulled-right part in the right pile.
theorem swapLeftPart_subset (d : CommanderPermutation.Deck) (L : Finset (Fin 50)) :
    swapLeftPart d L ⊆ CommanderPermutation.leftCards d := by
  unfold swapLeftPart CommanderPermutation.leftCards
  exact Finset.image_mono (fun l => d (CommanderPermutation.leftPosition l))
    (fun x hx => Finset.mem_univ x)

theorem swapRightPart_subset (d : CommanderPermutation.Deck) (R : Finset (Fin 49)) :
    swapRightPart d R ⊆ rightCards d := by
  unfold swapRightPart
  exact Finset.image_mono (fun r => d (rightPosition r)) (Finset.subset_univ R)

theorem swapLeftPart_card25 (d : CommanderPermutation.Deck) (L : Finset (Fin 50))
    (hL : L.card = 25) : (swapLeftPart d L).card = 25 := by
  unfold swapLeftPart
  rw [Finset.card_image_of_injective ((Finset.univ : Finset (Fin 50)) \ L)
    (fun l1 l2 h => by
      apply Fin.ext
      simpa [CommanderPermutation.leftPosition] using (congrArg Fin.val ((Equiv.injective d) h)))]
  rw [Finset.card_sdiff_of_subset]
  · norm_num
    rw [hL]
  · exact Finset.subset_univ L

theorem swapRightPart_card25 (d : CommanderPermutation.Deck) (R : Finset (Fin 49))
    (hR : R.card = 25) : (swapRightPart d R).card = 25 := by
  unfold swapRightPart
  rw [Finset.card_image_of_injective R
    (fun r1 r2 h => by
      apply Fin.ext
      simpa [rightPosition] using (congrArg Fin.val ((Equiv.injective d) h)))]
  exact hR

-- The kept-left part is the left pile minus the removed part, where the
-- removed part is the image of `L` (the deck map is injective, so the
-- image of a set difference is the set difference of images).
def removedLeft (d : CommanderPermutation.Deck) (L : Finset (Fin 50)) : Finset (Fin 99) :=
  Finset.image (fun l => d (CommanderPermutation.leftPosition l)) L

theorem swapLeftPart_eq_complement (d : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) :
    swapLeftPart d L =
      CommanderPermutation.leftCards d \ removedLeft d L := by
  unfold swapLeftPart removedLeft CommanderPermutation.leftCards
  rw [Finset.image_sdiff]
  · intro l1 l2 h
    apply Fin.ext
    simpa [CommanderPermutation.leftPosition] using (congrArg Fin.val ((Equiv.injective d) h))

-- The map `L ↦ removedLeft d L` is injective (the position→card map is a
-- bijection between the 50 left positions and the 50 left cards).
theorem leftCards_card (d : CommanderPermutation.Deck) :
    (CommanderPermutation.leftCards d).card = 50 := by
  unfold CommanderPermutation.leftCards
  rw [Finset.card_image_of_injective]
  · simp
  · intro l1 l2 h
    have hpos : CommanderPermutation.leftPosition l1 = CommanderPermutation.leftPosition l2 :=
      d.injective h
    apply Fin.ext
    simp [CommanderPermutation.leftPosition] at hpos ⊢
    exact hpos

theorem removedLeft_injective (d : CommanderPermutation.Deck) :
    Function.Injective (fun (L : Finset (Fin 50)) => removedLeft d L) := by
  have hInjOn : (Set.univ : Set (Fin 50)).InjOn (fun l => d (CommanderPermutation.leftPosition l)) := by
    intro l1 hl1 l2 hl2 h
    apply Fin.ext
    simpa [CommanderPermutation.leftPosition] using (congrArg Fin.val ((Equiv.injective d) h))
  have hInjOn' : (↑(Finset.univ : Finset (Fin 50)) : Set (Fin 50)).InjOn
      (fun l => d (CommanderPermutation.leftPosition l)) := by simpa using hInjOn
  intro L1 L2 h
  dsimp only [removedLeft] at h ⊢
  simpa using (Finset.image_eq_image_iff_of_injOn hInjOn' (Finset.subset_univ L1)
      (Finset.subset_univ L2)).1 h

-- The membership produced by a 25/25 exchange is `M` exactly when the
-- union of the two kept/pulled parts equals `M`'s 50-card set.
theorem newMembership_set_eq (Y : CommanderPermutation.Deck)
    (L : Finset (Fin 50)) (hL : L ∈ CommanderPhysicalExchange.leftChoices)
    (R : Finset (Fin 49)) (hR : R ∈ CommanderPhysicalExchange.rightChoices)
    (M : CommanderMembershipKernels.Membership) :
    CommanderPhysicalExchange.newMembership Y L (CommanderPhysicalExchange.leftCard25 hL) R
      (CommanderPhysicalExchange.rightCard25 hR) = M ↔
      (swapLeftPart Y L) ∪ (swapRightPart Y R) = M.1 := by
  apply Iff.intro
  · intro h
    have h1 : (CommanderPhysicalExchange.newMembership Y L
        (CommanderPhysicalExchange.leftCard25 hL) R
        (CommanderPhysicalExchange.rightCard25 hR)).1 = M.1 := by
      simpa using congrArg (fun (m : CommanderMembershipKernels.Membership) => m.1) h
    simpa [CommanderPhysicalExchange.newMembership, CommanderPhysicalExchange.newLeftCards,
      swapLeftPart, swapRightPart] using h1
  · intro h
    apply Subtype.ext
    simpa [CommanderPhysicalExchange.newMembership, CommanderPhysicalExchange.newLeftCards,
      swapLeftPart, swapRightPart] using h

-- The map `R ↦ swapRightPart d R` is injective (the position→card map is a
-- bijection between the 49 right positions and the 49 right cards).
theorem swapRightPart_injective (d : CommanderPermutation.Deck) :
    Function.Injective (fun (R : Finset (Fin 49)) => swapRightPart d R) := by
  have hInjOn : (Set.univ : Set (Fin 49)).InjOn (fun r => d (rightPosition r)) := by
    intro r1 hr1 r2 hr2 h
    apply Fin.ext
    simpa [rightPosition] using (congrArg Fin.val ((Equiv.injective d) h))
  have hInjOn' : (↑(Finset.univ : Finset (Fin 49)) : Set (Fin 49)).InjOn
      (fun r => d (rightPosition r)) := by simpa using hInjOn
  intro R1 R2 h
  dsimp only [swapRightPart] at h ⊢
  simpa using (Finset.image_eq_image_iff_of_injOn hInjOn' (Finset.subset_univ R1)
      (Finset.subset_univ R2)).1 h


-- The witness sets of the count split: the left positions whose cards are in
-- `leftCards \ O` (the 25 that must move out of the left pile) and the right
-- positions whose cards are in `S` (the 25 that must be pulled in). Their
-- images under the deck map recover exactly the target sets, because the
-- position→card maps are bijections onto the piles.
-- The witness choice sets of the count split, as filters of the position
-- universes (avoids the noncomputable `Finset.preimage` API): the left
-- positions whose cards lie in `C`, the right positions whose cards lie in `S`.
def leftWitness (Y : CommanderPermutation.Deck) (C : Finset (Fin 99)) :
    Finset (Fin 50) :=
  (Finset.univ : Finset (Fin 50)).filter (fun l => Y (CommanderPermutation.leftPosition l) ∈ C)

def rightWitness (Y : CommanderPermutation.Deck) (S : Finset (Fin 99)) :
    Finset (Fin 49) :=
  (Finset.univ : Finset (Fin 49)).filter (fun r => Y (rightPosition r) ∈ S)

theorem k1b_witnessLeft_removed (Y : CommanderPermutation.Deck)
    (O : Finset (Fin 99)) (hOsub : O ⊆ CommanderPermutation.leftCards Y) :
    removedLeft Y (leftWitness Y (CommanderPermutation.leftCards Y \ O)) =
      CommanderPermutation.leftCards Y \ O := by
  apply Finset.ext
  intro card
  apply Iff.intro
  · intro h
    rcases Finset.mem_image.mp h with ⟨l, hmem, heq⟩
    rcases Finset.mem_filter.mp hmem with ⟨_, hP⟩
    simpa [heq.symm] using hP
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨hlc, hnotO⟩
    rcases Finset.mem_image.mp hlc with ⟨l, hmem, heq⟩
    have hP : Y (CommanderPermutation.leftPosition l) ∈ CommanderPermutation.leftCards Y \ O := by
      simpa [heq.symm] using h
    have hmem2 : l ∈ leftWitness Y (CommanderPermutation.leftCards Y \ O) := by
      simpa [leftWitness, Finset.mem_filter, Finset.mem_univ] using hP
    exact Finset.mem_image.mpr ⟨l, hmem2, heq⟩

theorem k1b_witnessRight (Y : CommanderPermutation.Deck)
    (S : Finset (Fin 99)) (hSsub : S ⊆ rightCards Y) :
    swapRightPart Y (rightWitness Y S) = S := by
  apply Finset.ext
  intro card
  apply Iff.intro
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hmem, heq⟩
    rcases Finset.mem_filter.mp hmem with ⟨_, hP⟩
    simpa [heq.symm] using hP
  · intro h
    have hRc : card ∈ rightCards Y := hSsub h
    have hImg : card ∈ Finset.image (fun r2 => Y (rightPosition r2)) (Finset.univ : Finset (Fin 49)) := by
      dsimp only [rightCards] at hRc
      simpa [Finset.mem_image] using hRc
    rcases Finset.mem_image.mp hImg with ⟨r, hmem, heq⟩
    have hP : Y (rightPosition r) ∈ S := by simpa [heq.symm] using h
    have hmem2 : r ∈ rightWitness Y S := by
      simpa [rightWitness, Finset.mem_filter, Finset.mem_univ] using hP
    exact Finset.mem_image.mpr ⟨r, hmem2, heq⟩

-- If `s \ a = s \ b` and both sets sit inside `s`, then `a = b`.
theorem sdiff_cancel (s a b : Finset (Fin 99)) (ha : a ⊆ s) (hb : b ⊆ s)
    (h : s \ a = s \ b) : a = b := by
  apply Finset.ext
  intro x
  apply Iff.intro
  · intro hx
    by_contra hnot
    have hmemB : x ∈ s \ b := by simpa [Finset.mem_sdiff] using ⟨ha hx, hnot⟩
    have hmemA : x ∈ s \ a := by simpa [h] using hmemB
    rcases Finset.mem_sdiff.mp hmemA with ⟨_, hnotA⟩
    exact hnotA hx
  · intro hx
    by_contra hnot
    have hmemA : x ∈ s \ a := by simpa [Finset.mem_sdiff] using ⟨hb hx, hnot⟩
    have hmemB : x ∈ s \ b := by simpa [h] using hmemA
    rcases Finset.mem_sdiff.mp hmemB with ⟨_, hnotB⟩
    exact hnotB hx

end Shufflemath
