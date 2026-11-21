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
