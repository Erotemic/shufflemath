module

public import Shufflemath.FiniteDeck.Gate6Deterministic
public import Shufflemath.Gate6K1Bridges
public import Shufflemath.GSRSegHeadline
public import Shufflemath.GSRDeckRound
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.FiniteDeck.Gate6FiniteGSR
public import Shufflemath.FiniteDeck.BinaryStableSort

@[expose] public section

namespace Shufflemath

/-! ## The corrected stable-sort pullback round (M5c/M5d)

The 2026-11-26 finish-line handoff (M5c) records that `gsrPermutationLaw` maps
each label vector to `rank` (old position → new position), so the *physical*
pullback — the permutation the stable sort actually applies to the deck — is
`rank.symm`.  `idealShuffle_canonical_eq_permLaw` confirms this: the sorted
deck is `(List.finRange n).map σ.symm`.  The previously certified Gate-6
certificate (`Gate6Deterministic.lean`) uses the uncorrected law `rhoRoundFinite`
(one label-law per pile, `2 ^ 23` labels, no inversion); this module builds
the **corrected** finite round on top of it and re-derives the
`TV < 1/1000` bound.

The correction is cheap in the exact sense the handoff intends:

* `embed_m_symm` — the per-pile embedding has a clean inverse (sumCongr is
  functorial, `finSplit` is an involution sandwich), so the deck-level law
  inversion is the *product* of the two per-pile inverse laws;
* `rhoRoundIdealCorrected_eq_rhoRoundIdeal` — the embedded ideal law is
  *invariant* under the deck-level inversion (the two per-pile uniform laws
  are bijection-invariant, and the embedding is fixed), so the ideal side of
  the certificate is untouched;
* `correctedRoundFiniteKernel` — the corrected finite round
  `comp (PAK swapLaw) (PAK correctedFinite)`.

The per-round discrepancy bound is unchanged — `tv_bijective_invariance`
with `permInverseEquiv` maps the discrepancy to the uncorrected one, which is
already `≤ δ1` (`oneRoundDeckTV_le_delta1`).

Finally the **M5c certificate**: 23 binary riffles per pile is exactly the
`2 ^ 23`-label stable-sort law.  `binary_composition_eq_ideal` proves this at
the list-level kernel level: `23` binary labels composed = `2 ^ 23` labels,
by repeated `productLabelShuffle_uniform_eq_ideal`.

The finite law is **not** re-proved here by enumeration: the telescope chain
reuses the already-committed `sub-lemma A` (`g6_threeRound_kernelDiscrepancy_le_δ1`
shape, replayed with the corrected leg), `sub-lemma B` (`q3`, the ideal law is
*identical* — the invariance above means the same theorem applies verbatim),
and the length-free telescope (`compList_telescope_nstep_le_n_times_d`).
-/

open CommanderPermutation CommanderMembershipKernels CommanderPhysicalExchange

section Orientation

/-- The inverse of the per-pile embedding: `(embed_m pl pr).symm = embed_m pl.symm pr.symm`.
    This is the concrete form of the "inverse of the pile embedding is conjugation
    through `finSplit`" fact the handoff asks to pin down. -/
theorem embed_m_symm (N m : Nat) (hm : m ≤ N)
    (pl : Equiv.Perm (Fin m)) (pr : Equiv.Perm (Fin (N - m))) :
    (FiniteDeck.embed_m N m hm pl pr).symm = FiniteDeck.embed_m N m hm pl.symm pr.symm := by
  simp only [FiniteDeck.embed_m, Equiv.symm_trans, Equiv.symm_symm, Equiv.sumCongr_symm]
  rw [← Equiv.trans_assoc]

/-- The inverse of the deck-level embedding: `(roundEmbedMap p).symm =
    roundEmbedMap (p.1.symm, p.2.symm)`. -/
theorem roundEmbedMap_symm (N m : Nat) (hm : m ≤ N)
    (p : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m))) :
    (roundEmbedMap N m hm p).symm =
      roundEmbedMap N m hm (p.1.symm, p.2.symm) := by
  simp [roundEmbedMap, embed_m_symm]

end Orientation

section CorrectedLaws

/-- The orientation-corrected finite-GSR round law: the inversion of
    `rhoRoundFinite` — the deck permutation the stable-sort pullback actually applies. -/
noncomputable def rhoRoundFiniteCorrected (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    Dist (Equiv.Perm (Fin N)) :=
  (rhoRoundFinite N m hm hLpos hRpos a ha).map (fun p => p.symm)

/-- The orientation-corrected ideal round law (equal to the ideal law — see
    `rhoRoundIdealCorrected_eq_rhoRoundIdeal` next). -/
noncomputable def rhoRoundIdealCorrected (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    Dist (Equiv.Perm (Fin N)) :=
  (rhoRoundIdeal N m hm hLpos hRpos a ha).map (fun p => p.symm)

/-- The corrected ideal law **is** the ideal law: the embedded uniform product law
    is invariant under the deck-level inversion. -/
theorem rhoRoundIdealCorrected_eq_rhoRoundIdeal (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    rhoRoundIdealCorrected N m hm hLpos hRpos a ha =
      rhoRoundIdeal N m hm hLpos hRpos a ha := by
  have hmap : (fun z : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m)) =>
      (z.1.symm, z.2.symm)) =
      ⇑(Equiv.prodCongr (permInverseEquiv (Fin m)) (permInverseEquiv (Fin (N - m)))) := by
    funext z
    rfl
  have hprod : (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
      (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map
      (fun z : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m)) => (z.1.symm, z.2.symm)) =
      distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
        (GSR.uniformDist (Equiv.Perm (Fin (N - m)))) := by
    rw [distProduct_uniform_is_uniformProd, hmap, GSR.map_bijective_uniformDist]
  have hdef : rhoRoundIdeal N m hm hLpos hRpos a ha =
      (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
        (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map (roundEmbedMap N m hm) := rfl
  have hsplit : (fun z : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m)) =>
      (roundEmbedMap N m hm z).symm) =
      (fun z => roundEmbedMap N m hm (z.1.symm, z.2.symm)) := by
    funext z
    exact roundEmbedMap_symm N m hm z
  unfold rhoRoundIdealCorrected
  rw [hdef, Convexity.StdSimplex.map_map, hsplit]
  -- now the goal is `prodLaw.map (fun z => roundEmbedMap (z.1.symm, z.2.symm)) = prodLaw.map roundEmbedMap`
  have hpush : (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
        (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map
      (fun z : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m)) =>
        roundEmbedMap N m hm (z.1.symm, z.2.symm)) =
      (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
        (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map
        (roundEmbedMap N m hm) := by
    rw [← Convexity.StdSimplex.map_map, hprod]
  rw [hpush]

/-- **The two-pile corrected-law bridge.** The orientation-corrected finite round
    law is exactly the product of the two within-pile pullback laws pushed through
    the two-pile deck embedding:
    `rhoRoundFiniteCorrected = (distProduct (BinaryStableSort.pullLaw m a ha hLpos)
      (BinaryStableSort.pullLaw (N - m) a ha hRpos)).map roundEmbedMap`.

    This is the product-map transport law `distProduct_map_comp` applied to the
    two within-pile `symm` inversions, composed with the map-law `map_map` and the
    per-pile-`symm` `roundEmbedMap_symm` identity — the identification the A2
    binary-riffle follow-up (`t = 23`, the concrete 99-card protocol) stands on. -/
theorem rhoRoundFiniteCorrected_eq_productPullLaw (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    rhoRoundFiniteCorrected N m hm hLpos hRpos a ha =
      (distProduct (BinaryStableSort.pullLaw m a ha hLpos) (BinaryStableSort.pullLaw (N - m) a ha hRpos)).map
        (roundEmbedMap N m hm) := by
  have hprod : distProduct (BinaryStableSort.pullLaw m a ha hLpos) (BinaryStableSort.pullLaw (N - m) a ha hRpos) =
      (distProduct (PermutationLaw.gsrPermutationLaw m a ha hLpos)
                   (PermutationLaw.gsrPermutationLaw (N - m) a ha hRpos)).map
        (fun z => (z.1.symm, z.2.symm)) :=
    (distProduct_map_comp _ _ _ _).symm
  have hmap : (fun z => (roundEmbedMap N m hm z).symm) =
      (fun z => roundEmbedMap N m hm (z.1.symm, z.2.symm)) := by
    funext z
    exact roundEmbedMap_symm N m hm z
  unfold rhoRoundFiniteCorrected rhoRoundFinite
  rw [Convexity.StdSimplex.map_map, hprod, Convexity.StdSimplex.map_map]
  simp only [hmap]

section CorrectedFiniteLaw

/-- The concrete orientation-corrected 99-card finite law: the inversion of the
    uncorrected one — the deck permutation the stable-sort pullback actually applies. -/
noncomputable def correctedFiniteLaw99 : Dist (Equiv.Perm (Fin 99)) :=
  rhoRoundFiniteCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

/-- **The 23-riffle specialization of the bridge.** The concrete 99-card
    orientation-corrected finite law is exactly the product of the two within-pile
    `2^23`-label pullback laws pushed through the two-pile embedding — the concrete
    instance of the binary-riffle reading (23 binary riffles per pile, one corrected
    call per pile) that the A2 follow-up stands on. -/
theorem correctedFiniteLaw99_eq_productPullLaw :
    correctedFiniteLaw99 =
      (distProduct (BinaryStableSort.pullLaw 50 (2 ^ 23) (by norm_num) (by norm_num))
                   (BinaryStableSort.pullLaw 49 (2 ^ 23) (by norm_num) (by norm_num))).map
        (roundEmbedMap 99 50 (by norm_num)) :=
  rhoRoundFiniteCorrected_eq_productPullLaw 99 50 (by norm_num) (by norm_num) (by norm_num)
    (2 ^ 23) (by norm_num)

/-- The concrete orientation-corrected ideal law — equal to the ideal law by invariance. -/
noncomputable def correctedIdealLaw99 : Dist (Equiv.Perm (Fin 99)) :=
  rhoRoundIdealCorrected 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)

/-- The corrected ideal law is the ideal law (inversion invariance). -/
theorem correctedIdealLaw99_eq_rho99Ideal :
    correctedIdealLaw99 = Gate6Crux.rho99Ideal :=
  rhoRoundIdealCorrected_eq_rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num)
    (2 ^ 23) (by norm_num)

/-- The corrected finite/ideal laws are related to the uncorrected ones by a common
    bijective pushforward (`permInverseEquiv`), so their TV is unchanged. -/
theorem correctedFiniteLaw99_tv_eq_rho99Finite :
    Dist.tv correctedFiniteLaw99 correctedIdealLaw99 =
      Dist.tv Gate6Crux.rho99Finite Gate6Crux.rho99Ideal := by
  have hmap : (fun p : Equiv.Perm (Fin 99) => p.symm) =
      (permInverseEquiv (Fin 99)).toFun := rfl
  simp only [correctedFiniteLaw99, correctedIdealLaw99, rhoRoundFiniteCorrected,
    rhoRoundIdealCorrected]
  rw [hmap]
  exact tv_bijective_invariance (permInverseEquiv (Fin 99)) _ _

/-- **The ideal law is independent of the GSR alphabet `a`.**  The body of
    `rhoRoundIdeal` never mentions `a` (it is the product of the two within-pile
    uniform laws pushed through the embedding), so any two alphabets give the
    same ideal law — `rfl`. -/
theorem rhoRoundIdeal_a_independent (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m)
    (hRpos : 0 < N - m) (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    rhoRoundIdeal N m hm hLpos hRpos a ha = rhoRoundIdeal N m hm hLpos hRpos b hb :=
  rfl

/-- **The corrected finite law is TV-equal to the uncorrected one** (the generic
    version of `correctedFiniteLaw99_tv_eq_rho99Finite` for any alphabet `a`). -/
theorem rhoRoundFiniteCorrected_tv_eq_rhoRoundFinite (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    Dist.tv (rhoRoundFiniteCorrected N m hm hLpos hRpos a ha)
        (rhoRoundIdealCorrected N m hm hLpos hRpos a ha) =
      Dist.tv (rhoRoundFinite N m hm hLpos hRpos a ha)
        (rhoRoundIdeal N m hm hLpos hRpos a ha) := by
  classical
  have hmap : (fun p : Equiv.Perm (Fin N) => p.symm) = (permInverseEquiv (Fin N)).toFun := rfl
  simp only [rhoRoundFiniteCorrected, rhoRoundIdealCorrected]
  rw [hmap]
  exact tv_bijective_invariance (permInverseEquiv (Fin N)) _ _

/-- **The corrected finite law is TV-equal to the uncorrected one against the
    plain ideal law** — the direct comparison the A3 cheaper certificates stand on. -/
theorem rhoRoundFiniteCorrected_tv_eq_rhoRoundFiniteIdeal (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    Dist.tv (rhoRoundFiniteCorrected N m hm hLpos hRpos a ha)
        (rhoRoundIdeal N m hm hLpos hRpos a ha) =
      Dist.tv (rhoRoundFinite N m hm hLpos hRpos a ha)
        (rhoRoundIdeal N m hm hLpos hRpos a ha) := by
  have h := rhoRoundFiniteCorrected_tv_eq_rhoRoundFinite N m hm hLpos hRpos a ha
  rw [rhoRoundIdealCorrected_eq_rhoRoundIdeal] at h
  exact h

/-- **The unequal-alphabets orientation-corrected finite law.**  The product of the two
    within-pile pullback laws pushed through the two-pile deck embedding:
    `a_L` labels on the left pile, `a_R` labels on the right pile.  For
    `a_L = a_R = a` this is exactly `rhoRoundFiniteCorrected` (see
    `rhoRoundFiniteCorrectedU_eq_rhoRoundFiniteCorrected`).  This is the definition the
    A3 cheaper certificates (22+22 / 22+21 binary riffles) stand on. -/
noncomputable def rhoRoundFiniteCorrectedU (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m)
    (hRpos : 0 < N - m) (aL : Nat) (haL : 0 < aL) (aR : Nat) (haR : 0 < aR) :
    Dist (Equiv.Perm (Fin N)) :=
  (distProduct (BinaryStableSort.pullLaw m aL haL hLpos)
               (BinaryStableSort.pullLaw (N - m) aR haR hRpos)).map (roundEmbedMap N m hm)

/-- Equal alphabets: the unequal-alphabets law specializes to the corrected law. -/
theorem rhoRoundFiniteCorrectedU_eq_rhoRoundFiniteCorrected (N m : Nat) (hm : m ≤ N)
    (hLpos : 0 < m) (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    rhoRoundFiniteCorrectedU N m hm hLpos hRpos a ha a ha =
      rhoRoundFiniteCorrected N m hm hLpos hRpos a ha :=
  (rhoRoundFiniteCorrected_eq_productPullLaw N m hm hLpos hRpos a ha).symm

/-- **The unequal-alphabets transport bound:** the corrected unequal-alphabet law is within
    `choose(m,2)/aL + choose(N-m,2)/aR` of the ideal round law.  The chain:
    the map-contraction through `roundEmbedMap`, the common `(symm, symm)` pushforward on
    the product (TV invariance), and the per-pile `twoPilePermutationTV_bound`. -/
theorem rhoRoundFiniteCorrectedU_tv_le (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m)
    (hRpos : 0 < N - m) (aL aR : Nat) (haL : 0 < aL) (haR : 0 < aR) :
    Dist.tv (rhoRoundFiniteCorrectedU N m hm hLpos hRpos aL haL aR haR)
        (rhoRoundIdeal N m hm hLpos hRpos aL haL) ≤
      (m.choose 2 : Rat) / aL + ((N - m).choose 2 : Rat) / aR := by
  haveI : DecidableEq (Equiv.Perm (Fin N)) := inferInstance
  have h1 : Dist.tv (rhoRoundFiniteCorrectedU N m hm hLpos hRpos aL haL aR haR)
        (rhoRoundIdeal N m hm hLpos hRpos aL haL) ≤
      Dist.tv (distProduct (BinaryStableSort.pullLaw m aL haL hLpos)
                           (BinaryStableSort.pullLaw (N - m) aR haR hRpos))
        (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                    (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) :=
    Dist.tv_map_contraction _ _ (roundEmbedMap N m hm)
  have h2 : distProduct (BinaryStableSort.pullLaw m aL haL hLpos)
                         (BinaryStableSort.pullLaw (N - m) aR haR hRpos) =
      (distProduct (PermutationLaw.gsrPermutationLaw m aL haL hLpos)
                   (PermutationLaw.gsrPermutationLaw (N - m) aR haR hRpos)).map
        (fun z => (z.1.symm, z.2.symm)) :=
    (distProduct_map_comp _ _ _ _).symm
  have h3 : distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                    (GSR.uniformDist (Equiv.Perm (Fin (N - m)))) =
      (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                    (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map
        (fun z => (z.1.symm, z.2.symm)) := by
    rw [distProduct_map_comp, perm_inverse_uniform, perm_inverse_uniform]
  have hmap : (fun z => (z.1.symm, z.2.symm)) =
      ⇑(Equiv.prodCongr (permInverseEquiv (Fin m)) (permInverseEquiv (Fin (N - m)))) := by
    funext z
    rfl
  have h4 : Dist.tv (distProduct (BinaryStableSort.pullLaw m aL haL hLpos)
                                 (BinaryStableSort.pullLaw (N - m) aR haR hRpos))
        (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                    (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) =
      Dist.tv (distProduct (PermutationLaw.gsrPermutationLaw m aL haL hLpos)
                           (PermutationLaw.gsrPermutationLaw (N - m) aR haR hRpos))
        (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                    (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) := by
    rw [h2]
    conv_lhs => rw [h3]
    rw [hmap]
    exact tv_bijective_invariance (Equiv.prodCongr (permInverseEquiv (Fin m))
                                                (permInverseEquiv (Fin (N - m)))) _ _
  calc Dist.tv (rhoRoundFiniteCorrectedU N m hm hLpos hRpos aL haL aR haR)
            (rhoRoundIdeal N m hm hLpos hRpos aL haL)
      ≤ Dist.tv (distProduct (BinaryStableSort.pullLaw m aL haL hLpos)
                            (BinaryStableSort.pullLaw (N - m) aR haR hRpos))
                (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                            (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) := h1
    _ = Dist.tv (distProduct (PermutationLaw.gsrPermutationLaw m aL haL hLpos)
                             (PermutationLaw.gsrPermutationLaw (N - m) aR haR hRpos))
                 (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                             (GSR.uniformDist (Equiv.Perm (Fin (N - m))))) := h4
    _ ≤ (m.choose 2 : Rat) / aL + ((N - m).choose 2 : Rat) / aR :=
        twoPilePermutationTV_bound N m aL aR (Nat.lt_of_lt_of_le hLpos hm) hm hLpos hRpos haL haR

/-- The corrected finite-GSR round kernel: swap first (left shuffle), then the
    orientation-corrected finite law. -/
noncomputable def correctedFiniteRound : FiniteKernel Deck Deck :=
  FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
    (FiniteDeck.permutationActionKernel correctedFiniteLaw99)

/-- The corrected ideal round kernel — equal to the uncorrected ideal round kernel,
    by the invariance of the ideal law. -/
noncomputable def correctedIdealRound : FiniteKernel Deck Deck :=
  FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
    (FiniteDeck.permutationActionKernel correctedIdealLaw99)

theorem correctedIdealRound_eq :
    correctedIdealRound =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel Gate6Crux.rho99Ideal) := by
  unfold correctedIdealRound
  rw [correctedIdealLaw99_eq_rho99Ideal]

/-- The per-round discrepancy for the corrected round: swap stays first and the two
    legs differ by the same one-round TV budget as the uncorrected round, so this is
    bounded by `δ1`. -/
theorem corrected_kernelDiscrepancy_le_δ1 :
    kernelDiscrepancy correctedFiniteRound correctedIdealRound ≤ δ1 := by
  unfold kernelDiscrepancy
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
  set νx := (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw) x with hνx
  have hK : correctedFiniteRound x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel correctedFiniteLaw99) := by
    simp only [correctedFiniteRound, FiniteKernel.comp, FiniteKernel.apply, hνx]
  have hL : correctedIdealRound x =
      FiniteKernel.apply νx (FiniteDeck.permutationActionKernel correctedIdealLaw99) := by
    simp only [correctedIdealRound, FiniteKernel.comp, FiniteKernel.apply, hνx]
  rw [hK, hL]
  have hA1 := apply_discrepancy_bound
      (FiniteDeck.permutationActionKernel correctedFiniteLaw99)
      (FiniteDeck.permutationActionKernel correctedIdealLaw99) νx
  calc
    _ ≤ kernelDiscrepancy (FiniteDeck.permutationActionKernel correctedFiniteLaw99)
        (FiniteDeck.permutationActionKernel correctedIdealLaw99) := hA1
    _ ≤ Dist.tv correctedFiniteLaw99 correctedIdealLaw99 := by
        unfold kernelDiscrepancy
        apply Finset.max'_le
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨y, _, rfl⟩
        simpa only [FiniteDeck.permutationActionKernel_eq_map]
          using Dist.tv_map_contraction correctedFiniteLaw99 correctedIdealLaw99 (·.trans y)
    _ ≤ Dist.tv Gate6Crux.rho99Finite Gate6Crux.rho99Ideal :=
        correctedFiniteLaw99_tv_eq_rho99Finite.le
    _ ≤ δ1 := by
        rw [δ1_eq_2401_over_8388608]
        simpa only [Gate6Crux.rho99Finite, Gate6Crux.rho99Ideal] using oneRoundDeckTV_le_delta1

end CorrectedFiniteLaw

section CorrectedHeadline

/-- The corrected finite round is equivariant under the deck-relabeling
    `d ↦ d.trans g` (the same equivariance as the uncorrected round, applied to the
    corrected finite law). -/
theorem correctedFiniteRound_relabel_equivariant (g : Deck) (d : Deck) :
    correctedFiniteRound (d.trans g) =
      (correctedFiniteRound d).map (fun x => x.trans g) := by
  classical
  unfold correctedFiniteRound FiniteKernel.comp
  rw [pak_relabel_equivariant Gate6Crux.swapLaw g d]
  have hfun : (fun (x : Deck) => FiniteDeck.permutationActionKernel correctedFiniteLaw99 (x.trans g)) =
      (fun (x : Deck) => (FiniteDeck.permutationActionKernel correctedFiniteLaw99 x).map (fun y => y.trans g)) := by
    funext x
    exact pak_relabel_equivariant correctedFiniteLaw99 g x
  have hjoin : (((FiniteDeck.permutationActionKernel Gate6Crux.swapLaw d).map
      (FiniteDeck.permutationActionKernel correctedFiniteLaw99)).join).map
      (fun x => x.trans g) =
      (((FiniteDeck.permutationActionKernel Gate6Crux.swapLaw d).map
        (FiniteDeck.permutationActionKernel correctedFiniteLaw99)).map
        (fun x => x.map (fun y => y.trans g))).join := by
    ext1
    simp [Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      Finsupp.smul_sum]
  rw [Convexity.StdSimplex.map_map, hjoin, hfun]
  rw [Convexity.StdSimplex.map_map]

/-- The run-map relabeling lemma for the corrected kernel: pushing the start law
    through the relabeling equals running the relabel-invariant kernel. -/
theorem corrected_run_map_relabel (g : Deck) (n : Nat) (μ : Dist Deck) :
    FiniteKernel.run correctedFiniteRound n (μ.map (fun x => x.trans g)) =
      (FiniteKernel.run correctedFiniteRound n μ).map (fun x => x.trans g) := by
  induction n generalizing μ with
  | zero =>
    simp [FiniteKernel.run]
  | succ k ih =>
    rw [FiniteKernel.run_succ, ih,
        apply_map_equivariant correctedFiniteRound g (FiniteKernel.run correctedFiniteRound k μ)
          (fun d => correctedFiniteRound_relabel_equivariant g d),
        ← FiniteKernel.run_succ]

/-- **Corrected three-round headline** (M5c): three rounds of the corrected
    stable-sort round from the deterministic reference segregated deck land within
    total variation `< 1/1000` of the uniform `99!` deck.  Mirrors
    `g6Deterministic_headline` — the same assemble (telescope + sub-lemma B +
    numeric close), with the corrected finite kernel in place of the uncorrected one.
    The ideal leg is unchanged (the invariance theorem), so the fiber-uniform
    transport and `q3` sub-lemma apply verbatim. -/
theorem corrected_threeRound_headline :
    Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
        (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  have hL : g6ThreeRoundFiniteKernel =
      FiniteKernel.comp (FiniteDeck.permutationActionKernel Gate6Crux.swapLaw)
        (FiniteDeck.permutationActionKernel correctedIdealLaw99) := by
    dsimp only [g6ThreeRoundFiniteKernel]
    rw [correctedIdealLaw99_eq_rho99Ideal]
    exact g6_3round_idealKernel_eq_fullRound
  -- one-step bridge: the fiber-uniform start derives the same post-exchange law
  have hbridge :
      FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel]) =
        FiniteKernel.apply g6ThreeRoundStart
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel]) := by
    rw [g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel) (μ := Dist.pointMass segDeck),
        g6_threeRound_compList3_eq_run (K := g6ThreeRoundFiniteKernel) (μ := g6ThreeRoundStart)]
    have hrun : ∀ μ : Dist Deck, FiniteKernel.run g6ThreeRoundFiniteKernel 3 μ =
        FiniteKernel.apply (FiniteKernel.apply (FiniteKernel.apply μ g6ThreeRoundFiniteKernel) g6ThreeRoundFiniteKernel) g6ThreeRoundFiniteKernel := by
      intro μ
      rw [FiniteKernel.run_succ, FiniteKernel.run_succ, FiniteKernel.run_succ]
      simp [FiniteKernel.run]
    rw [hrun, hrun]
    rw [apply_segDeck_idealKernel_eq]
  -- telescope + ideal leg
  have hAccum :
      Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]))
        (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel])) ≤ 3 * δ1 := by
    exact compList_telescope_nstep_le_n_times_d
      [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]
      [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel]
      (by simp) δ1 (by rw [δ1_eq_2401_over_8388608]; norm_num)
      (fun a ha => by
        rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
        dsimp at hp
        rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_nil_iff] at hp
        rcases hp with h₁ | h₂ | h₃ | h₄
        · rw [h₁, hL]
          exact corrected_kernelDiscrepancy_le_δ1
        · rw [h₂, hL]
          exact corrected_kernelDiscrepancy_le_δ1
        · rw [h₃, hL]
          exact corrected_kernelDiscrepancy_le_δ1
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
          (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]))
          (FiniteKernel.apply (Dist.pointMass segDeck)
            (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                      g6ThreeRoundFiniteKernel])) +
        Dist.tv (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                    g6ThreeRoundFiniteKernel]))
          (GSR.uniformDist Deck) := by
      simpa only [Dist.tv] using Dist.tv_triangle
        (p := FiniteKernel.apply (Dist.pointMass segDeck)
              (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]))
        (q := FiniteKernel.apply (Dist.pointMass segDeck)
              (compList [g6ThreeRoundFiniteKernel, g6ThreeRoundFiniteKernel,
                        g6ThreeRoundFiniteKernel]))
        (r := GSR.uniformDist Deck)
    _ ≤ 3 * δ1 + q3 := add_le_add hAccum hIdeal
    _ < (1 : Rat) / 1000 := by rw [add_comm]; exact gate6_headline_bound

/-- **Corrected headline from EVERY deterministic deck** (M5d): three rounds of the
    orientation-corrected stable-sort round applied to any deterministic `N`-card deck
    land within total variation `< 1/1000` of the uniform `99!` deck.  This is
    `corrected_threeRound_headline` transported from the reference segregated deck
    through the relabeling `d ↦ d.trans g` — the relabel-invariance of the uniform
    full-deck law (`uniformDeck_relabel_invariant`) and the equivariance of the
    corrected kernel. -/
theorem corrected_threeRound_headline_anyDeck (d : Deck) :
    Dist.tv (FiniteKernel.apply (Dist.pointMass d)
        (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]))
      (GSR.uniformDist Deck) < (1 : Rat) / 1000 := by
  have hbridge :
      FiniteKernel.apply (Dist.pointMass d)
          (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound]) =
        (FiniteKernel.apply (Dist.pointMass segDeck)
          (compList [correctedFiniteRound, correctedFiniteRound, correctedFiniteRound])).map
          (fun x => x.trans d) := by
    rw [g6_threeRound_compList3_eq_run (K := correctedFiniteRound) (μ := Dist.pointMass d),
        g6_threeRound_compList3_eq_run (K := correctedFiniteRound) (μ := Dist.pointMass segDeck)]
    have hmap : Dist.pointMass d = (Dist.pointMass segDeck).map (fun x => x.trans d) := by
      simp only [segDeck]
      exact (FiniteDeck.pointMassMap segDeck (fun x => x.trans d)).symm
    rw [hmap]
    exact corrected_run_map_relabel d 3 (Dist.pointMass segDeck)
  rw [hbridge]
  rw [← uniformDeck_relabel_invariant 99 d]
  have hconv : (fun x : Deck => x.trans d) = (relabel_equiv d).toFun := rfl
  rw [hconv]
  rw [tv_bijective_invariance (relabel_equiv d) _ _]
  exact corrected_threeRound_headline

end CorrectedHeadline

end CorrectedLaws

end Shufflemath
