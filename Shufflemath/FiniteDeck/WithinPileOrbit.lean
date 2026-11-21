module

public import Shufflemath.FiniteDeck.TwoPile
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# The two-pile split `Fin N ≃ Fin m ⊕ Fin (N - m)` — generic `(N, m)`

Generalizes the 50/49 `pileRelabelEquiv` (`Shufflemath/CommanderLocalGSR`) to an
arbitrary `(N, m)` split, the building block for the F5 within-pile orbit action
(`docs/planning/proof-strategies/2026-11-20-deep-structural-hints-for-qwen.md`, §2).
The split is the 99-card `finSumFinEquiv` composed with the value-preserving cast
`Fin (m + (N - m)) ≃ Fin N`, so that left (resp. right) positions map to the `inl`
(resp. `inr`) summand.  `embed_m` (composing `(pl, pr)` through this split) and the
free-orbit F5 theorem build on it next.
-/

/-- The value-preserving `Fin (m + (N - m)) ≃ Fin N` cast. -/
def splitCast (N m : Nat) (hm : m ≤ N) : Fin (m + (N - m)) ≃ Fin N :=
  finCongr (Nat.add_sub_of_le hm)

/-- `finCongr` (hence `splitCast`) preserves the numeric value. -/
theorem splitCast_val (N m : Nat) (hm : m ≤ N) (x : Fin (m + (N - m))) :
    (splitCast N m hm x).val = x.val := by
  dsimp only [splitCast, finCongr]
  unfold Fin.cast
  rfl

theorem splitCast_symm_val (N m : Nat) (hm : m ≤ N) (x : Fin N) :
    ((splitCast N m hm).symm x).val = x.val := by
  dsimp only [splitCast, finCongr, finCongr_symm]
  unfold Fin.cast
  rfl

/-- Value facts for the project's own position embeddings. -/
theorem leftPosition_val (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    (leftPosition N m hm i).val = i.val := by
  dsimp only [leftPosition, Fin.castLE]

theorem rightPosition_val (N m : Nat) (hm : m ≤ N) (j : Fin (N - m)) :
    (rightPosition N m hm j).val = m + j.val := by
  dsimp only [rightPosition]

/-- The two-pile split (a deck position as a tagged pile index) and its inverse,
  via the 99-card `finSumFinEquiv` and the `m + (N - m) = N` cast. -/
def finSplitToFun (N m : Nat) (hm : m ≤ N) (x : Fin N) : Fin m ⊕ Fin (N - m) :=
  (finSumFinEquiv (m := m) (n := N - m)).symm ((splitCast N m hm).symm x)

def finSplitInvFun (N m : Nat) (hm : m ≤ N) (s : Fin m ⊕ Fin (N - m)) : Fin N :=
  (splitCast N m hm) (finSumFinEquiv (m := m) (n := N - m) s)

/-- The two-pile split as an `Equiv` (hence a bijection). -/
def finSplit (N m : Nat) (hm : m ≤ N) : Fin N ≃ Fin m ⊕ Fin (N - m) where
  toFun := finSplitToFun N m hm
  invFun := finSplitInvFun N m hm
  left_inv s := by
    simp only [finSplitToFun, finSplitInvFun, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv x := by
    simp only [finSplitToFun, finSplitInvFun, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The split is value-faithful at the level of `Fin.castAdd` / `Fin.natAdd`. -/
theorem hval_left (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    (splitCast N m hm).symm (leftPosition N m hm i) = Fin.castAdd (N - m) i := by
  apply Fin.ext
  simp only [splitCast_symm_val, leftPosition_val, Fin.castAdd, Fin.castLE, Nat.cast]

theorem hval_right (N m : Nat) (hm : m ≤ N) (j : Fin (N - m)) :
    (splitCast N m hm).symm (rightPosition N m hm j) = Fin.natAdd m j := by
  apply Fin.ext
  simp only [splitCast_symm_val, rightPosition_val, Fin.natAdd, Nat.cast]

/-- A left (resp. right) position splits to the `inl` (resp. `inr`) tag. -/
theorem finSplit_left (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    finSplit N m hm (leftPosition N m hm i) = Sum.inl i := by
  simp [finSplit, finSplitToFun]
  rw [hval_left, finSumFinEquiv_symm_apply_castAdd]

theorem finSplit_right (N m : Nat) (hm : m ≤ N) (j : Fin (N - m)) :
    finSplit N m hm (rightPosition N m hm j) = Sum.inr j := by
  simp [finSplit, finSplitToFun]
  rw [hval_right, finSumFinEquiv_symm_apply_natAdd]

/-- The `inl` (resp. `inr`) tag recombines to the corresponding left (resp.
  right) position. -/
theorem finSplit_symm_left (N m : Nat) (hm : m ≤ N) (i : Fin m) :
    (finSplit N m hm).symm (Sum.inl i) = leftPosition N m hm i := by
  simp [finSplit, finSplitInvFun]
  apply Fin.ext
  simp [splitCast_val, leftPosition_val, finSumFinEquiv_apply_left, Fin.castAdd, Fin.castLE, Nat.cast]

theorem finSplit_symm_right (N m : Nat) (hm : m ≤ N) (j : Fin (N - m)) :
    (finSplit N m hm).symm (Sum.inr j) = rightPosition N m hm j := by
  simp [finSplit, finSplitInvFun]
  apply Fin.ext
  simp [splitCast_val, rightPosition_val, finSumFinEquiv_apply_right, Fin.natAdd, Nat.cast]

/-- `Equiv.sumCongr` acts on each summand (within-pile relabel). -/
theorem sumCongr_left (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) (i : Fin m) :
    Equiv.sumCongr pl pr (Sum.inl i) = Sum.inl (pl i) := by
  dsimp only [Equiv.sumCongr, Sum.map]
  exact Sum.map_inl pl pr i

theorem sumCongr_right (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) (j : Fin (N - m)) :
    Equiv.sumCongr pl pr (Sum.inr j) = Sum.inr (pr j) := by
  dsimp only [Equiv.sumCongr, Sum.map]
  exact Sum.map_inr pl pr j

/-- The within-pile orbit action: conjugate a pair of within-pile permutations
  `(pl, pr)` through the two-pile split.  The generic version of the 99-card
  `pileRelabelEquiv` (`Shufflemath/CommanderLocalGSR`) — a bijection of `Fin N`
  that relabels left (resp. right) positions by `pl` (resp. `pr`) and fixes the
  pile membership of every position. -/
def embed_m (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) : Deck N :=
  ((finSplit N m hm).trans (Equiv.sumCongr pl pr)).trans ((finSplit N m hm).symm)

/-- `embed_m` relabels left (resp. right) positions by `pl` (resp. `pr`) within
  the left (resp. right) pile. -/
theorem embed_m_left (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) (i : Fin m) :
    embed_m N m hm pl pr (leftPosition N m hm i) = leftPosition N m hm (pl i) := by
  dsimp only [embed_m]
  simp only [Equiv.trans_apply]
  rw [finSplit_left N m hm i, sumCongr_left N m hm pl pr i]
  exact finSplit_symm_left N m hm (pl i)

theorem embed_m_right (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) (j : Fin (N - m)) :
    embed_m N m hm pl pr (rightPosition N m hm j) = rightPosition N m hm (pr j) := by
  dsimp only [embed_m]
  simp only [Equiv.trans_apply]
  rw [finSplit_right N m hm j, sumCongr_right N m hm pl pr j]
  exact finSplit_symm_right N m hm (pr j)

/-- `Equiv.sumCongr` determines both of its within-pile permutations: the left
  summand is read off on the `inl` positions and the right on `inr`. This is the
  two-pile analogue of the 99-card `pileRelabelEquiv` injection fact. -/
theorem sumCongr_pairInjective (N m : Nat) (hm : m ≤ N)
    (pl pl' : Equiv.Perm (Fin m)) (pr pr' : Equiv.Perm (Fin (N - m))) :
    Equiv.sumCongr pl pr = Equiv.sumCongr pl' pr' → pl = pl' ∧ pr = pr' := by
  intro h
  constructor
  · apply Equiv.ext
    intro i
    have hi := congrArg (fun e => e (Sum.inl i)) h
    simpa [sumCongr_left N m hm pl pr i, sumCongr_left N m hm pl' pr' i] using hi
  · apply Equiv.ext
    intro j
    have hj := congrArg (fun e => e (Sum.inr j)) h
    simpa [sumCongr_right N m hm pl pr j, sumCongr_right N m hm pl' pr' j] using hj

/-- `embed_m` is injective in the pair of within-pile permutations: two within-
  pile pairs that produce the same `Fin N` rearrangement are equal. This is the
  arbitrary-`(N, m)` generalization of the 99-card `pileRelabelEquiv_pairInjective`.
  It holds by cancelling the fixed `finSplit` / `finSplit.symm` sandwich around
  `Equiv.sumCongr` and reading the summands back off. -/
theorem embed_m_pairInjective (N m : Nat) (hm : m ≤ N)
    (pl pl' : Equiv.Perm (Fin m)) (pr pr' : Equiv.Perm (Fin (N - m))) :
    embed_m N m hm pl pr = embed_m N m hm pl' pr' → pl = pl' ∧ pr = pr' := by
  intro h
  dsimp only [embed_m] at h
  set A := finSplit N m hm
  set B := Equiv.sumCongr pl pr
  set B' := Equiv.sumCongr pl' pr'
  have hBB' : B = B' := by
    apply Equiv.ext
    intro z
    have hx := congrArg (fun (e : Fin N ≃ Fin N) => e (A.symm z)) h
    simpa using hx
  simpa [B, B'] using sumCongr_pairInjective N m hm pl pl' pr pr' hBB'

/-- Membership in `leftPositions` is "is a left-pile position": a position is in
  the left-pile set exactly when it is some `leftPosition`. -/
theorem memLeftPositions_iff (N m : Nat) (hm : m ≤ N) (x : Fin N) :
    x ∈ leftPositions N m hm ↔ ∃ i : Fin m, x = leftPosition N m hm i := by
  dsimp only [leftPositions, leftPosition]
  rw [Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨i, _mem, heq⟩
    use i
    exact heq.symm
  · intro h
    rcases h with ⟨i, heq⟩
    use i
    constructor
    · simp only [Finset.mem_univ]
    · exact heq.symm

/-- `embed_m` maps the left-pile positions onto themselves: it rearranges the
  left pile among left positions (never sending a left position to a right one).
  This is the `Finset`-image form of `embed_m_left`, and is what makes a
  within-pile pair act by conjugation on a deck's left-card set. -/
theorem embed_m_imageLeft (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) :
    (leftPositions N m hm).image (embed_m N m hm pl pr) = leftPositions N m hm := by
  apply Finset.ext
  intro x
  constructor
  · intro hImage
    rcases Finset.mem_image.mp hImage with ⟨p, hp, hpx⟩
    rcases (memLeftPositions_iff N m hm p).mp hp with ⟨i, hpi⟩
    have hxl : x = leftPosition N m hm (pl i) := by
      calc
        x = embed_m N m hm pl pr p := hpx.symm
        _ = embed_m N m hm pl pr (leftPosition N m hm i) := by simpa only [hpi]
        _ = leftPosition N m hm (pl i) := embed_m_left N m hm pl pr i
    exact (memLeftPositions_iff N m hm x).mpr ⟨pl i, hxl⟩
  · intro hLP
    rcases (memLeftPositions_iff N m hm x).mp hLP with ⟨j, hxj⟩
    have huse : embed_m N m hm pl pr (leftPosition N m hm (pl.symm j)) = leftPosition N m hm j :=
      by simpa only [embed_m_left N m hm pl pr (pl.symm j), Equiv.apply_symm_apply]
    have hmem : leftPosition N m hm (pl.symm j) ∈ leftPositions N m hm :=
      (memLeftPositions_iff N m hm (leftPosition N m hm (pl.symm j))).mpr ⟨pl.symm j, by rfl⟩
    rw [Finset.mem_image]
    use leftPosition N m hm (pl.symm j)
    constructor
    · exact hmem
    · simpa only [huse, hxj]

/-- A bijection that preserves a set also preserves its complement: if `s.image f
  = s` then `(univ \ s).image f = univ \ s`. The complement half is forced by
  injectivity (a complement point cannot map into `s`, or two preimages would
  collide) and the rest by surjectivity. -/
theorem bijection_imageCompl {α : Type} [Fintype α] [DecidableEq α] (f : Equiv.Perm α)
    (s : Finset α) (hf : s.image f = s) : (Finset.univ \ s).image f = Finset.univ \ s := by
  apply Finset.ext
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image]
  simp
  constructor
  · intro h
    rcases h with ⟨a, hna, hax⟩
    by_contra hx
    have hbx : ∃ b, b ∈ s ∧ f b = x := by
      have hximg : x ∈ s.image f := by simpa [hf] using hx
      exact Finset.mem_image.mp hximg
    rcases hbx with ⟨b, hbs, hbx⟩
    have hab : a = b := f.injective (by simpa [hax, hbx])
    rw [← hab] at hbs
    exact hna hbs
  · intro hnx
    rcases f.surjective x with ⟨a, hax⟩
    have hna : a ∉ s := by
      by_contra hsa
      exact hnx (by simpa [hf] using (Finset.mem_image.mpr ⟨a, hsa, hax⟩))
    exact ⟨a, hna, hax⟩

/-- `embed_m` maps the right-pile positions onto themselves (the mirror of
  `embed_m_imageLeft`): it rearranges the right pile among right positions. Since
  `rightPositions = univ \ leftPositions` and `embed_m` is a bijection preserving
  `leftPositions`, this follows from `bijection_imageCompl`. -/
theorem embed_m_imageRight (N m : Nat) (hm : m ≤ N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) :
    (rightPositions N m hm).image (embed_m N m hm pl pr) = rightPositions N m hm := by
  dsimp only [rightPositions]
  exact bijection_imageCompl (embed_m N m hm pl pr) (leftPositions N m hm)
    (embed_m_imageLeft N m hm pl pr)

/-! ## The within-pile orbit action and its fiber (F5) -/

/-- The within-pile orbit action on decks: conjugate a deck `d` on the left by a
  within-pile permutation `embed_m (pl, pr)`.  This relabels the cards within
  each pile (preserving pile membership) then applies `d`.  It is the group
  action whose orbit is the membership fiber of `d` (the F5 theorem). -/
def act_d (N m : Nat) (hm : m ≤ N) (d : Deck N) (pl : Equiv.Perm (Fin m))
    (pr : Equiv.Perm (Fin (N - m))) : Deck N := (embed_m N m hm pl pr).trans d

/-- The orbit action preserves the membership: conjugating `d` by a within-pile
  permutation does not change which cards sit in the left pile, because
  `embed_m` rearranges the left positions among themselves, so the image of the
  left positions under `embed_m ∘ d` is the same as under `d`. -/
theorem act_d_preservesMembership (N m : Nat) (hm : m ≤ N) (d : Deck N)
    (pl : Equiv.Perm (Fin m)) (pr : Equiv.Perm (Fin (N - m))) :
    membership N m hm (act_d N m hm d pl pr) = membership N m hm d := by
  have hl : leftCards N m hm (act_d N m hm d pl pr) = leftCards N m hm d := by
    unfold leftCards
    dsimp only [act_d]
    have hfun : (fun p : Fin N => ((embed_m N m hm pl pr).trans d) p) =
        (fun p => d ((embed_m N m hm pl pr) p)) := by
      funext p
      simp only [Equiv.trans_apply]
    rw [hfun]
    show (leftPositions N m hm).image (d ∘ (embed_m N m hm pl pr)) = (leftPositions N m hm).image d
    rw [← Finset.image_image, embed_m_imageLeft]
  exact Subtype.ext hl

/-- The orbit action is injective in the within-pile pair: two pairs that
  produce the same conjugate of `d` are equal.  Cancelling `d` from the right
  of `.trans d` (apply `d.symm` pointwise, which is injective) reduces this to
  `embed_m_pairInjective`. -/
theorem act_d_injective (N m : Nat) (hm : m ≤ N) (d : Deck N) :
    Function.Injective (fun p : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m)) =>
      act_d N m hm d p.1 p.2) := by
  intro ⟨pl₁, pr₁⟩ ⟨pl₂, pr₂⟩ h
  dsimp only [act_d] at h
  have he : embed_m N m hm pl₁ pr₁ = embed_m N m hm pl₂ pr₂ := by
    apply Equiv.ext
    intro x
    have hdx : d ((embed_m N m hm pl₁ pr₁) x) = d ((embed_m N m hm pl₂ pr₂) x) := by
      simpa only [Equiv.trans_apply] using (congrArg (fun (e : Deck N) => e x) h)
    simpa only [Equiv.symm_apply_apply] using (congrArg d.symm hdx)
  rcases embed_m_pairInjective N m hm pl₁ pl₂ pr₁ pr₂ he with ⟨hpl, hpr⟩
  rw [hpl, hpr]

/-- The fiber condition (same left-pile cards) is exactly the statement that the
  deck `e.trans d.symm` — the within-pile relabel that carries `d` to `e` —
  preserves the left positions.  Unwinding: applying `d` to the left-pile image
  of `e.trans d.symm` recovers the left-pile cards of `e`, which equal those of
  `d`; and `d` permutes its own left-pile cards back to the left positions. -/
theorem wPreservesLeftOfFiber (N m : Nat) (hm : m ≤ N) (d e : Deck N)
    (hle : leftCards N m hm e = leftCards N m hm d) :
    (leftPositions N m hm).image (e.trans d.symm) = leftPositions N m hm := by
  dsimp [leftCards] at hle
  change (leftPositions N m hm).image (fun p : Fin N => (e.trans d.symm) p) = leftPositions N m hm
  have hfun : (fun p : Fin N => (e.trans d.symm) p) = (fun p => d.symm (e p)) := by
    funext p
    simp only [Equiv.trans_apply]
  rw [hfun]
  show (leftPositions N m hm).image (d.symm ∘ e) = leftPositions N m hm
  rw [← Finset.image_image]
  rw [hle]
  rw [Finset.image_image]
  change (leftPositions N m hm).image (fun p : Fin N => d.symm (d p)) = leftPositions N m hm
  have hidd : (fun p : Fin N => d.symm (d p)) = (fun p : Fin N => p) := by
    funext p
    simp only [Equiv.symm_apply_apply]
  rw [hidd]
  exact Finset.image_id (s := leftPositions N m hm)

/-- Same for the right positions: a bijection that preserves the left positions
  preserves their complement (the right positions), so `e.trans d.symm` preserves
  the right positions too. -/
theorem wPreservesRightOfFiber (N m : Nat) (hm : m ≤ N) (d e : Deck N)
    (hle : leftCards N m hm e = leftCards N m hm d) :
    (rightPositions N m hm).image (e.trans d.symm) = rightPositions N m hm := by
  unfold rightPositions
  exact bijection_imageCompl (e.trans d.symm) (leftPositions N m hm) (wPreservesLeftOfFiber N m hm d e hle)

/-- The image of the i-th left position under a left-position-preserving bijection
  `w` is again a left position (hence has a well-defined left-index in the
  `finSplit` summand decomposition).  This is the existence half of the
  within-pile permutation reconstruction (F5): the within-pile permutation that
  `w` induces on the left pile is well-defined. -/
theorem existsFinSplitLeft (N m : Nat) (hm : m ≤ N) (w : Deck N) (i : Fin m)
    (hwL : (leftPositions N m hm).image w = leftPositions N m hm) :
    ∃ k : Fin m, finSplit N m hm (w (leftPosition N m hm i)) = Sum.inl k := by
  have hmem : w (leftPosition N m hm i) ∈ leftPositions N m hm := by
    rw [← hwL]
    exact Finset.mem_image_of_mem (fun p => w p) (leftPosition_memLeft N m hm i)
  rcases Finset.mem_image.mp hmem with ⟨k, hk, hval⟩
  use k
  rw [show w (leftPosition N m hm i) = leftPosition N m hm k from by simpa [leftPosition] using hval.symm, finSplit_left]

theorem memLeftPositions_val (N m : Nat) (hm : m ≤ N) (x : Fin N) :
    x ∈ leftPositions N m hm ↔ x.val < m := by
  rw [memLeftPositions_iff]
  constructor
  · rintro ⟨i, heq⟩
    rw [heq]
    simpa [leftPosition_val] using i.isLt
  · intro hx
    have h : leftPosition N m hm ⟨x.val, hx⟩ = x := by
      apply Fin.ext
      simpa only [leftPosition_val]
    exact ⟨⟨x.val, hx⟩, h.symm⟩

/-- A deck position is a right-pile position iff its value is `≥ m`. -/
theorem memRightPositions_val (N m : Nat) (hm : m ≤ N) (x : Fin N) :
    x ∈ rightPositions N m hm ↔ x.val ≥ m := by
  dsimp only [rightPositions]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [memLeftPositions_val]
  simpa only [Nat.not_lt]

/-- A deck position is in the image of `rightPosition` iff its value is `≥ m`. -/
theorem memImageRightPosition_val (N m : Nat) (hm : m ≤ N) (x : Fin N) :
    x ∈ (Finset.univ : Finset (Fin (N - m))).image (rightPosition N m hm) ↔ x.val ≥ m := by
  rw [Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  have hxN : x.val < N := x.isLt
  constructor
  · rintro ⟨j, heq⟩
    rw [← heq, rightPosition_val]
    simpa using Nat.le_add_right m (j.val)
  · intro hx
    have hjv : x.val - m < N - m := by omega
    use ⟨x.val - m, hjv⟩
    have h : rightPosition N m hm ⟨x.val - m, hjv⟩ = x := by
      apply Fin.ext
      rw [rightPosition_val, Nat.add_comm]
      exact Nat.sub_add_cancel hx
    exact h

/-- The right-pile positions are exactly the values in `[m, N)`, i.e. the image
  of the right-pile index set under `rightPosition`. -/
theorem rightPositions_eqImage (N m : Nat) (hm : m ≤ N) :
    rightPositions N m hm = (Finset.univ : Finset (Fin (N - m))).image (rightPosition N m hm) := by
  apply Finset.ext
  intro x
  rw [memRightPositions_val, memImageRightPosition_val]

/-- Mirror of `existsFinSplitLeft` for the right pile: the image of the j-th right
  position under a right-position-preserving bijection is again a right position,
  hence has a well-defined right-index in the `finSplit` decomposition. -/
theorem existsFinSplitRight (N m : Nat) (hm : m ≤ N) (w : Deck N) (j : Fin (N - m))
    (hwR : (rightPositions N m hm).image w = rightPositions N m hm) :
    ∃ k : Fin (N - m), finSplit N m hm (w (rightPosition N m hm j)) = Sum.inr k := by
  have hmem : w (rightPosition N m hm j) ∈ rightPositions N m hm := by
    rw [← hwR]
    exact Finset.mem_image_of_mem (fun p => w p) (rightPosition_memRight N m hm j)
  rw [rightPositions_eqImage] at hmem
  rcases Finset.mem_image.mp hmem with ⟨k, hk, hval⟩
  use k
  rw [show w (rightPosition N m hm j) = rightPosition N m hm k from by simpa [rightPosition] using hval.symm, finSplit_right]
