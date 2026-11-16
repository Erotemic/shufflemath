module

public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderMembershipOrbits
public import Shufflemath.BernoulliLaplace
public import Shufflemath.FiberDisintegration
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace CommanderMembershipExchange

/-!
# The `hMembershipExchange` kernel equality (F3 item 3 / Spec C, A3)

The two-layer physical-perfect capstone
`two_physical_perfect_exchanges_uniform_of_counts`
(`Shufflemath.CommanderFullDeckDisintegration`) takes the membership-exchange law
`hMembershipExchange` as a hypothesis.  **The concrete law (A3) is not yet
proved**; this module currently contains the *supporting ingredients* it will
be assembled from and the assembly plan below: the group-uniformity tools
(`map_equiv_mass`, `distUniform_ofInvariantTransitive`), the fiber-card bridge
(`membershipFiber_card`), the lift projection (`membershipLift_count`), and the
RHS count-fiber cardinality (`commanderCountFiber_card`).  The open F3 gate is
the concrete `hMembershipExchange` equality (A3) and the physical-perfect
corollary it discharges; the combinatorial/orbit ingredients it depends on
(F1b fiber counts, `generalCL`/`fiberSum_eq_overlap`, `membershipFiber_transitive`)
are complete in the other modules.

The 3a reduction (`hMembershipExchange_lhs_reduces`) already shows the LHS is the
uniform `project`-fiber deck law pushed through the membership-level exchange:

    comp (fiberLaw project) rawExchangeMembership

so the target is

    comp (fiberLaw project project_surjective) rawExchangeMembership
      = comp commanderExchange25 membershipLift                                    (A3)

Both sides are kernels `CommanderState → Membership`.  A source macro state `x`
has count `c_x = commanderLeftCount x`; every deck in the `x`-fiber has
membership count `c_x` (`membershipCount_of_project`), and `rawExchangeMembership`
pushes each such deck through a uniform 25-25 position exchange.

The proof has two parts, matching F3 item 3's two halves:
* **counting (part (i))** — the *count* of the post-exchange membership,
  averaged over the uniform `x`-fiber and the uniform 25-25 choice, is exactly
  the `commanderExchange25` transition from `c_x`.
* **within-count uniformity (part (ii))** — conditioned on landing on count `c`,
  the membership is *uniform* over the `c`-fiber, because the exchange law is
  equivariant under the deck-relabeling group (`newLeftCards_conjugate`) and that
  group acts transitively on each count-fiber (`membershipFiber_transitive`).

`comp commanderExchange25 membershipLift` is precisely "transition the count by
`commanderExchange25`, then lift uniformly to the membership fiber," which is the
sum of those two parts.
-/

open BernoulliLaplace
open CommanderMembershipKernels
open CommanderPhysicalExchange
open FiberDisintegration
open FiniteKernel

/-
## Assembly plan for `hMembershipExchange`

Mass-at-a-point, the two sides are:

    LHS  x at m  =  (1 / (|fiber project x| * N_LR)) *
                    sum {d : project d = x} |{(L,R) : newLeftCards d L R = m.1}|
    RHS  x at m  =  transitionWeight 99 50 25 (count x) (count m) /
                    membershipFiberCount (count m)

where `N_LR = choose 50 25 * choose 49 25 = transitionDenominator 99 50 25`
and `count := commanderLeftCount`.  The identity therefore splits:

* **Part (i) — count total.**  Push the LHS to the count level; the total mass
  over the `count m`-fiber equals `transitionWeight 99 50 25 (count x) (count m)`.
  The counting core is the general CL (`transitionNumerator = overlap_count`)
  already proved in `BernoulliLaplaceGeneral` / `BernoulliLaplaceFiber`.
* **Part (ii) — within-count uniformity.**  Conditioned on the new count, the
  LHS is uniform over that count-fiber: the exchange law is equivariant under
  the deck-relabeling group (`newLeftCards_conjugate`) which acts transitively
  on each count-fiber (`membershipFiber_transitive` / `orbitMap`), so
  `distUniform_ofInvariantTransitive` (proved here) gives the uniform mass.

### Committed this module
* `map_equiv_mass` — pushforward mass under a bijection.
* `distUniform_ofInvariantTransitive` — invariant + transitive = uniform on the
  fiber (the group-uniformity tool for part (ii)).
* `membershipFiber_card` — `# {m // count m = k} = membershipFiberCount k`.
* `membershipLift_count` — `comp membershipLift (det membershipCount) =
  det commanderLeftCount` (the lift projects back to its count).

### Next concrete lemmas
1. **`rawExchangeMembership_count`** (part i, count total): prove
       `comp (comp (fiberLaw project project_surjective) rawExchangeMembership)
          (deterministic membershipCount) =
         comp commanderExchange25 (deterministic commanderLeftCount)`.
2. **`hMembershipExchange`** (the capstone): assemble (1) + part (ii) into the
       full kernel equality, then instantiate
       `two_physical_perfect_exchanges_uniform_of_counts`.
-/

/-- Pushforward mass at a point, for a bijection: moving a distribution by an
    equiv `e` and reading at `y` is the original mass at `e.symm y`.  The
    `Finsupp.mapDomain` of a bijective map collapses the preimage sum to a single
    term (`mapDomain_equiv_apply`). -/
@[simp]
theorem map_equiv_mass {X : Type*} [DecidableEq X] (e : Equiv X X) (μ : Dist X) (y : X) :
    Dist.mass (μ.map e) y = Dist.mass μ (e.symm y) := by
  dsimp only [Dist.mass, Convexity.StdSimplex.map]
  rw [Finsupp.mapDomain_equiv_apply]

/-- **Group uniformity (the distributional form of the orbit argument).**  A
    Fintype probability `μ` supported on a fiber `S` that is invariant under a
    family `E` of equivs of `X` and that `E` acts transitively on `S` is
    *uniform* on `S`: every `x ∈ S` carries mass `1 / #S`.  Transitivity makes the
    mass constant on `S` (invariance + a witnessing equiv move any point to any
    other), and the total-mass-one constraint then fixes that constant.  This is
    Spec A2 in the abstract: the within-count uniformity of the physical exchange
    follows once the exchange law is shown equivariant (A2 core) and the deck
    relabelings act transitively on the count-fiber (A1). -/
theorem distUniform_ofInvariantTransitive
    {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (μ : Dist X) (E : Set (Equiv X X))
    (hSupp : μ.weights.support ⊆ S)
    (hInvar : ∀ e, e ∈ E → μ.map e = μ)
    (hTrans : ∀ x y, x ∈ S → y ∈ S → ∃ e, e ∈ E ∧ e x = y)
    (hS : S.Nonempty) :
    ∀ x ∈ S, (↑S.card : Rat) * Dist.mass μ x = 1 := by
  obtain ⟨x0, hx0⟩ := hS
  -- (1) μ is supported on S, so its total mass is carried by S.
  have hOut (z : X) (hz : z ∉ S) : Dist.mass μ z = 0 := by
    dsimp only [Dist.mass]
    by_contra hnz
    have hmem : z ∈ μ.weights.support := by
      rw [Finsupp.mem_support_iff]
      exact hnz
    have habs : False := hz (hSupp hmem)
    exact habs.elim
  have hOutSum : (Finset.univ \ S).sum (fun z => Dist.mass μ z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hzm
    have hzS : z ∉ S := by
      rw [Finset.mem_sdiff] at hzm
      exact hzm.2
    exact hOut z hzS
  have hSumS : S.sum (fun x => Dist.mass μ x) = 1 := by
    have hsdiff : (Finset.univ \ S).sum (fun z => Dist.mass μ z) + S.sum (fun x => Dist.mass μ x) =
        (Finset.univ : Finset X).sum (fun z => Dist.mass μ z) :=
      Finset.sum_sdiff (Finset.subset_univ S)
    linarith [hsdiff, hOutSum, Dist.sum_mass μ]
  -- (2) μ is constant on S: invariance + a witnessing equiv moves any x to y.
  have hConst (x y : X) (hx : x ∈ S) (hy : y ∈ S) : Dist.mass μ y = Dist.mass μ x := by
    obtain ⟨e, he, hxy⟩ := hTrans x y hx hy
    have hinvar : μ.map e = μ := hInvar e he
    calc
      Dist.mass μ y = Dist.mass μ (e x) := by rw [hxy]
      _ = Dist.mass (μ.map e) (e x) := by rw [hinvar]
      _ = Dist.mass μ (e.symm (e x)) := by rw [map_equiv_mass]
      _ = Dist.mass μ x := by rw [Equiv.symm_apply_apply]
  -- (3) the common value, times #S, is the total mass 1.
  have hc (x : X) (hx : x ∈ S) : Dist.mass μ x = Dist.mass μ x0 := by
    rw [hConst x x0 hx hx0]
  have hConstSum : S.sum (fun x => Dist.mass μ x) = (S.card : Rat) * Dist.mass μ x0 := by
    rw [Finset.sum_congr rfl (fun x hx => hc x hx)]
    rw [Finset.sum_const]
    ring_nf
  have hVal : (S.card : Rat) * Dist.mass μ x0 = 1 := by
    linarith [hSumS, hConstSum]
  intro x hx
  calc
    (↑S.card : Rat) * Dist.mass μ x = (↑S.card : Rat) * Dist.mass μ x0 := by
      rw [hc x hx]
    _ = 1 := hVal

/-!
## Count-level projection (A3 part (i), RHS side)

The lift is *uniform within each count-fiber*; projecting it back to the
count is therefore the identity on counts.  This is the RHS half of the
`hMembershipExchange` count projection.
-/

/-- The membership fiber `{m // membershipCount m = k}` has the F1b card
    `membershipFiberCount k`.  Bridges the Fintype subtype count through
    `MembershipFiber_card` to the standalone choose product. -/
theorem membershipFiber_card (k : Nat) :
    ((Finset.univ : Finset Membership).filter (fun m => membershipCount m = k)).card =
      membershipFiberCount k := by
  have hfin : ((Finset.univ : Finset Membership).filter (fun m => membershipCount m = k)).card =
      Fintype.card (MembershipFiber k) := by
    exact (@Fintype.card_ofFinset Membership (fun m => membershipCount m = k)
        ((Finset.univ : Finset Membership).filter (fun m => membershipCount m = k))
        (fun m => by
          simp [Finset.mem_filter, Finset.mem_univ]
          exact Iff.rfl)).symm
  calc
    ((Finset.univ : Finset Membership).filter (fun m => membershipCount m = k)).card =
        Fintype.card (MembershipFiber k) := hfin
    _ = (fiberMembershipSets k).card := MembershipFiber_card k
    _ = membershipFiberCount k := (membershipFiberCount_eq_fiberMembershipSets k).symm

/-- Pushing `membershipLift` back through the marked count recovers
    `deterministic commanderLeftCount`: the lift only puts mass on the
    `commanderLeftCount x`-fiber, on which the marked count is constant, so the
    pushforward is a point mass at that count. -/
theorem membershipLift_count :
    FiniteKernel.comp membershipLift (FiniteKernel.deterministic membershipCount) =
      FiniteKernel.deterministic commanderLeftCount := by
  classical
  funext x
  apply (Convexity.StdSimplex.weights_inj
      (f := (FiniteKernel.comp membershipLift (FiniteKernel.deterministic membershipCount)) x)
      (g := (FiniteKernel.deterministic commanderLeftCount) x)).mp
  apply Finsupp.ext
  intro k
  rw [← Dist.mass, ← Dist.mass]
  -- Read the LHS as the `apply` of the lift against the deterministic count map.
  have hLHS : Dist.mass (FiniteKernel.comp membershipLift (FiniteKernel.deterministic membershipCount) x) k =
      Dist.mass (FiniteKernel.apply (membershipLift x) (FiniteKernel.deterministic membershipCount)) k := by
    dsimp only [FiniteKernel.comp, FiniteKernel.apply]
  rw [hLHS, apply_mass_eq_sum]
  simp only [FiniteKernel.deterministic, Dist.mass_pointMass, membershipLift_mass]
  -- Goal:
  --   sum over m of
  --     (if membershipCount m = commanderLeftCount x then 1 / fc else 0)   [m-count LEFT]
  --       * (if k = membershipCount m then 1 else 0)                       [k LEFT]
  --     =  (if k = commanderLeftCount x then 1 else 0).
  by_cases hk : k = commanderLeftCount x
  · -- k equals the source count: the second ite matches the first, so the sum
    --   collapses to the lift's total mass, `1`.
    have hsum : (∑ m : Membership,
        (if membershipCount m = commanderLeftCount x
          then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0) *
        (if k = membershipCount m then (1 : Rat) else 0)) = 1 := by
      have h1 : (∑ m : Membership,
          (if membershipCount m = commanderLeftCount x
            then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0) *
          (if k = membershipCount m then (1 : Rat) else 0)) =
          (∑ m : Membership,
            (if membershipCount m = commanderLeftCount x
              then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0)) := by
        apply Finset.sum_congr rfl
        intro m _
        by_cases hm : membershipCount m = commanderLeftCount x
        · simp [hm, hk, mul_one]
        · simp [hm, mul_zero]
      have h2 : (∑ m : Membership,
          (if membershipCount m = commanderLeftCount x
            then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0)) =
          (∑ m : Membership, Dist.mass (membershipLift x) m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← membershipLift_mass]
      calc
        (∑ m : Membership,
          (if membershipCount m = commanderLeftCount x
            then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0) *
          (if k = membershipCount m then (1 : Rat) else 0)) =
          (∑ m : Membership,
            (if membershipCount m = commanderLeftCount x
              then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0)) := h1
        _ = (∑ m : Membership, Dist.mass (membershipLift x) m) := h2
        _ = 1 := Dist.sum_mass _
    have hRHS : (if k = commanderLeftCount x then (1 : Rat) else 0) = 1 := by simp [hk]
    simpa [hRHS] using hsum
  · -- k differs from the source count: no membership carries both counts, so
    --   every summand is `0`.
    have hsum : (∑ m : Membership,
        (if membershipCount m = commanderLeftCount x
          then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0) *
        (if k = membershipCount m then (1 : Rat) else 0)) = 0 := by
      have hpoint : (∑ m : Membership,
          (if membershipCount m = commanderLeftCount x
            then 1 / (↑(membershipFiberCount (commanderLeftCount x)) : Rat) else 0) *
          (if k = membershipCount m then (1 : Rat) else 0)) =
          (∑ m : Membership, (0 : Rat)) := by
        apply Finset.sum_congr rfl
        intro m _
        by_cases hm1 : membershipCount m = commanderLeftCount x
        · simp [hm1, hk, mul_zero]
        · simp [hm1, mul_zero]
      rw [hpoint]
      simp
    have hRHS : (if k = commanderLeftCount x then (1 : Rat) else 0) = 0 := by simp [hk]
    simpa [hRHS] using hsum
/-!
## Count-projection of `commanderExchange25` (A3 part (i), RHS helper)

Each count `1 ≤ c ≤ 50` is realized by exactly one `Fin 50` state and no count
outside that range is realized at all, so the count fiber has cardinality
`1` (resp. `0`).  This is the RHS helper for the part-(i) count-total identity
`rawExchangeMembership_count`.
-/

/-- The fiber of `commanderLeftCount` over `c` is a singleton (one `Fin 50`
    state per count in `1..50`) or empty (no state realizes a count outside
    `1..50`). -/
theorem commanderCountFiber_card (c : Nat) :
    ((Finset.univ : Finset CommanderState).filter (fun y => commanderLeftCount y = c)).card =
      if 1 ≤ c ∧ c ≤ 50 then 1 else 0 := by
  by_cases hc : 1 ≤ c ∧ c ≤ 50
  · rw [if_pos hc]
    -- `count y = c <-> y.val = c - 1` under `1 ≤ c`
    have hIff (y : CommanderState) : commanderLeftCount y = c ↔ y.val = c - 1 := by
      constructor
      · intro h
        have hc_eq : c = y.val + 1 := by
          simp only [commanderLeftCount] at h
          exact h.symm
        rw [hc_eq, Nat.add_sub_cancel_right]
      · intro h
        simp only [commanderLeftCount]
        rw [h, Nat.sub_add_cancel hc.1]
    -- Rewrite the count-filter to the val-filter, then to the singleton
    -- {⟨c - 1⟩}; the Fin bound `c - 1 < 50` follows from `1 ≤ c ≤ 50`.
    have hfin : c - 1 < 50 := by
      have hle : c - 1 ≤ 50 - 1 := Nat.sub_le_sub_right hc.2 1
      exact Nat.lt_of_le_of_lt hle (by norm_num)
    have hf : (Finset.univ : Finset CommanderState).filter (fun y => commanderLeftCount y = c) =
        {Fin.mk (c - 1) hfin} := by
      apply Finset.ext
      intro y
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton,
        Fin.ext_iff, hIff]
      simp
    rw [hf]
    simp
  · rw [if_neg hc]
    have hempty : (Finset.univ : Finset CommanderState).filter (fun y => commanderLeftCount y = c) = ∅ := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        simp only [Finset.mem_filter, Finset.mem_univ] at hz
        simp only [commanderLeftCount] at hz
        have h1 : 1 ≤ c := by omega
        have h2 : c ≤ 50 := by omega
        exact False.elim (hc ⟨h1, h2⟩)
      · intro hz
        simp at hz
    rw [hempty]
    simp

end CommanderMembershipExchange
end Shufflemath
