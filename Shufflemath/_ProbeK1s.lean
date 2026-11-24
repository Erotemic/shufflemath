module
public import Mathlib
public import Shufflemath._ProbeK1k
public import Shufflemath._ProbeK1r

@[expose]
public section

set_option linter.constructorNameAsVariable false

/- WIP / 2026-12-31: this 0-branch still hits the elaboration wall.  The per-`c`
    `swapLeftPart Y c.1.1`/`newMembership Y c = M` term needs far more whnf recursion
    depth than the default (and, when that is raised, >200000 heartbeats) — see the
    handoff note for the full diagnosis.  The 2a shape works in `k1b_count_25` but the
    same proof in this 0-branch context does not; it is an elaborator budget limit,
    not a mathematical one.  Do NOT force it with `maxRecDepth`/`maxHeartbeats` -
    the whnf is pathologically deep (exponential blowup), so raising the limits only
    makes the build hang/OOM.  `linter.constructorNameAsVariable` is disabled here:
    the deep proof term overflows that linter's stack (advisory, per AGENTS.md). -/

namespace Shufflemath

/- K1b 0-branch (2b) (2026-12-31).  Mirrors the 25/25 branch's `hUnique` (in
    `k1b_count_25`, `_ProbeK1r`) in shape: a hit `c` forces
    `swapLeftPart Y c.1.1 = M.1 ∩ leftCards Y`, a 25-element set, so
    `(M.1 ∩ leftCards).card = 25`, contradicting `hnot`.

    The 2026-12-30 wall was that 2b's `⊇` direction cannot use the card argument
    (it needs the `= 25` fact 2b is trying to contradict).  The fix: prove `⊇` by
    MEMBERSHIP + disjointness instead of by cardinality — every term stays a NAMED
    definition (`swapLeftPart`, `swapRightPart`, `leftCards`, `rightCards`), never an
    unfolded `Finset.image`, so the elaborator's whnf budget (the 2a shape) holds. -/

theorem k1b_count_non25 (Y : CommanderPermutation.Deck)
    (M : CommanderMembershipKernels.Membership)
    (hnot : (M.1 ∩ CommanderPermutation.leftCards Y).card ≠ 25) :
    k1b_hitCount Y M = 0 := by
  classical
  unfold k1b_hitCount
  have hEmpty : (Finset.filter (fun c => CommanderPhysicalExchange.newMembership Y c.1.1
      (CommanderPhysicalExchange.leftCard25 c.1.2) c.2.1
      (CommanderPhysicalExchange.rightCard25 c.2.2) = M)
    (Finset.univ : Finset CommanderPhysicalExchange.exchangeChoice)) = ∅ := by
    ext c
    apply Iff.intro
    · intro hx
      have hSet : (swapLeftPart Y c.1.1) ∪ (swapRightPart Y c.2.1) = M.1 :=
        (newMembership_set_eq Y c.1.1 c.1.2 c.2.1 c.2.2 M).1 hx
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
      have hRSubRight : swapRightPart Y c.2.1 ⊆ rightCards Y :=
        swapRightPart_subset Y c.2.1
      -- Non-circular `⊇`: an element of `M.1 ∩ leftCards` lands in the union, and the
      -- left-position membership rules out the right part (the two pile-card sets are
      -- disjoint), so it is in `swapLeftPart`.
      have hLpT : swapLeftPart Y c.1.1 = (M.1 ∩ CommanderPermutation.leftCards Y) := by
        apply Finset.Subset.antisymm hLpSubT
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hM, hlc⟩
        have hU : x ∈ (swapLeftPart Y c.1.1) ∪ (swapRightPart Y c.2.1) := by
          rw [← hSet]
          exact hM
        rcases Finset.mem_union.mp hU with hLeft | hRight
        · exact hLeft
        · exfalso
          have hRc : x ∈ rightCards Y := Finset.mem_of_subset hRSubRight hRight
          have hboth : x ∈ CommanderPermutation.leftCards Y ∩ rightCards Y :=
            Finset.mem_inter.mpr ⟨hlc, hRc⟩
          rw [Finset.disjoint_iff_inter_eq_empty.1 (leftCards_rightCards_disjoint Y)] at hboth
          simp at hboth
      have hEq25 : (M.1 ∩ CommanderPermutation.leftCards Y).card = 25 := by
        rw [hLpT, hLpCard]
      exact hnot hEq25
    · intro hx
      exfalso
      exact hx
  rw [hEmpty, Finset.card_empty]

end Shufflemath
