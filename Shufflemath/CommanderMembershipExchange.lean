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
* `commanderExchange25_mass` — `commanderExchange25 x y`'s mass is the exact
  `transitionWeight 99 50 25 (count x) (count y)` (the `ofRowStochastic` bridge).
* `hMembershipExchange_rhs_mass` — A3 **part (i) RHS**: the mass at `(x, m)` of
  `comp commanderExchange25 membershipLift` is
  `transitionWeight (count x) (count m) / membershipFiberCount (count m)` for
  feasible `count m`, else `0` (the fiber average is deck-independent).
* `commanderExchange25_countMass` — the **count-level** A3 RHS: the mass at
  `(x, c)` of `comp commanderExchange25 (det commanderLeftCount)` is
  `transitionWeight (count x) c` for feasible `c`, else `0` (the count fiber is a
  singleton, so the fiber sum collapses with no division).

### Next concrete lemmas
1. **`rawExchangeMembership_count`** (part i, count total): prove
       `comp (comp (fiberLaw project project_surjective) rawExchangeMembership)
          (deterministic membershipCount) =
         comp commanderExchange25 (deterministic commanderLeftCount)`.
       **RHS committed** (`commanderExchange25_countMass`: the mass at `(x, c)` is
       `transitionWeight 99 50 25 (count x) c` for feasible `c`); the **LHS** fiber-
       average post-exchange count distribution is the remaining step (deck-
       independent given the source count).
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

/-!
## The `hMembershipExchange` RHS pointwise mass (A3, count level)

The RHS of the A3 is `comp commanderExchange25 membershipLift`: it transitions
the macro count by the 25-card exchange, then lifts uniformly to the membership
fiber of the new count.  At a source macro state `x` and a target membership
`m` its mass is the `commanderExchange25` transition weight to `m`'s marked
count, divided by that count's membership-fiber size.  Both halves of the A3
proof (the count total and the within-count uniformity) reduce to this
pointwise form.
-/ -- close doc section

/-- The 25-card exchange kernel's mass is exactly the rational
    Bernoulli--Laplace transition weight between the two macro counts.  The
    kernel is `ofRowStochastic` of `commanderExchange25Matrix`, whose entries
    are those transition weights, so the matrix-recovery lemma gives the point
    mass. -/
@[simp]
theorem commanderExchange25_mass (x y : CommanderState) :
    Dist.mass (commanderExchange25 x) y =
      transitionWeight 99 50 25 (commanderLeftCount x) (commanderLeftCount y) := by
  change toMatrix commanderExchange25 x y = _
  rw [commanderExchange25, toMatrix_ofRowStochastic, commanderExchange25Matrix]
  rfl

/-- The A3 RHS `comp commanderExchange25 membershipLift` puts, at a source macro
    state `x` and a target membership `m`, the `commanderExchange25` transition
    weight to `m`'s marked count divided by that count's membership-fiber size
    (zero when `m`'s count is not a feasible macro count): the transition picks
    the count, the lift distributes uniformly within it.  This is the
    count-level half of the `hMembershipExchange` equality. -/
theorem hMembershipExchange_rhs_mass (x : CommanderState) (m : Membership) :
    Dist.mass (FiniteKernel.comp commanderExchange25 membershipLift x) m =
      (if 1 ≤ membershipCount m ∧ membershipCount m ≤ 50
        then transitionWeight 99 50 25 (commanderLeftCount x) (membershipCount m) /
             (membershipFiberCount (membershipCount m) : Rat)
        else 0) := by
  classical
  set k := membershipCount m
  set c := transitionWeight 99 50 25 (commanderLeftCount x) k / (membershipFiberCount k : Rat)
  set F := (Finset.univ : Finset CommanderState).filter (fun y => k = commanderLeftCount y)
  -- (A) the product of the two point masses is the fiber indicator times `c`.
  have hVal (y : CommanderState) :
      Dist.mass (commanderExchange25 x) y * Dist.mass (membershipLift y) m =
        (if k = commanderLeftCount y then c else 0) := by
    by_cases hyk : k = commanderLeftCount y
    · -- on the fiber: `count y = k`, so both point masses reduce to the
      -- transition weight to `k` times the uniform fiber lift, which is `c`.
      have hcnt : commanderLeftCount y = k := hyk.symm
      rw [commanderExchange25_mass, membershipLift_mass, hcnt]
      have hLc : membershipCount m = k := by simp [k]
      have hRc : k = k := by rfl
      rw [ite_eq_left hLc, ite_eq_left hRc]
      -- now: TW (count x) k * (1 / fc k) = c,  with c := TW (count x) k / fc k
      have hc : c =
          (transitionWeight 99 50 25 (commanderLeftCount x) k) / (membershipFiberCount k : Rat) := rfl
      rw [hc, one_div, div_eq_mul_inv]
    · -- off the fiber: the lift assigns `0` mass to `m` from `y`.
      have hnot : membershipCount m ≠ commanderLeftCount y := by
        intro h
        exact hyk h
      rw [commanderExchange25_mass, membershipLift_mass, ite_eq_right hnot, ite_eq_right hyk]
      simp [mul_zero]
  -- (B) the fiber `{y // k = count y}` has the singleton-or-empty card.
  have hCard : F.card = (if 1 ≤ k ∧ k ≤ 50 then 1 else 0) := by
    have hF : F = (Finset.univ : Finset CommanderState).filter (fun y => commanderLeftCount y = k) := by
      apply Finset.ext
      intro y
      simp [F, Finset.mem_filter, Finset.mem_univ]
      tauto
    rw [hF, commanderCountFiber_card]
  calc
    Dist.mass (FiniteKernel.comp commanderExchange25 membershipLift x) m =
        (∑ y : CommanderState, Dist.mass (commanderExchange25 x) y * Dist.mass (membershipLift y) m) :=
      apply_mass_eq_sum (commanderExchange25 x) membershipLift m
    _ = (∑ y : CommanderState, (if k = commanderLeftCount y then c else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact hVal y
    _ = (∑ y ∈ F, c) := by
      -- swap the indicator for the fiber-membership test, then restrict to the fiber
      have hIte (y : CommanderState) :
          (if k = commanderLeftCount y then c else 0) = (if y ∈ F then c else 0) := by
        by_cases hk : k = commanderLeftCount y
        · -- k = count y  ⟹  y ∈ F; both ites take their `then` branch
          have hmem : y ∈ F := by simp [F, Finset.mem_filter, Finset.mem_univ, hk]
          rw [ite_eq_left hk, ite_eq_left hmem]
        · -- k ≠ count y  ⟹  y ∉ F; both ites take their `else` branch
          have hnot : y ∉ F := by
            intro hmem
            have hk' : k = commanderLeftCount y := by
              simpa [F, Finset.mem_filter, Finset.mem_univ] using hmem
            contradiction
          rw [ite_eq_right hk, ite_eq_right hnot]
      have h1 : (∑ y : CommanderState, (if k = commanderLeftCount y then c else 0)) =
          (∑ y : CommanderState, (if y ∈ F then c else 0)) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hIte y
      rw [h1]
      have h2 : (∑ y : CommanderState, (if y ∈ F then c else 0)) =
          (∑ y ∈ (Finset.univ : Finset CommanderState), (if y ∈ F then c else 0)) := rfl
      rw [h2, ← Finset.sum_filter]
      have hF2 : (Finset.univ : Finset CommanderState).filter (fun y => y ∈ F) = F := by
        apply Finset.ext
        intro y
        simp [F, Finset.mem_filter, Finset.mem_univ]
      rw [hF2]
    _ = F.card * c := Finset.sum_const _
    _ = (if 1 ≤ k ∧ k ≤ 50 then 1 else 0) * c := by rw [hCard, Nat.cast_ite]; rfl
    _ = (if 1 ≤ k ∧ k ≤ 50 then c else 0) := by
      by_cases hk : 1 ≤ k ∧ k ≤ 50
      · have hL : ((if 1 ≤ k ∧ k ≤ 50 then 1 else 0) : Rat) = 1 := ite_eq_left hk
        have hR : ((if 1 ≤ k ∧ k ≤ 50 then c else 0) : Rat) = c := ite_eq_left hk
        rw [hL, hR]
        simp only [one_mul]
      · have hL : ((if 1 ≤ k ∧ k ≤ 50 then 1 else 0) : Rat) = 0 := ite_eq_right hk
        have hR : ((if 1 ≤ k ∧ k ≤ 50 then c else 0) : Rat) = 0 := ite_eq_right hk
        rw [hL, hR]
        simp only [zero_mul]

/-- The A3 RHS **count-mass**: the mass at `(x, c)` of the count distribution
    `comp commanderExchange25 (deterministic commanderLeftCount)` — the
    probability that a `commanderExchange25` step from macro state `x` lands on
    a state of left count `c` — is the `commanderExchange25` transition weight
    to `c`, and `0` for an infeasible count.  This is the count-level companion
    of `hMembershipExchange_rhs_mass`: the macro count-fiber at a feasible `c`
    has exactly one member (`commanderCountFiber_card`), so the fiber sum
    collapses to `transitionWeight 99 50 25 (count x) c`. -/
theorem commanderExchange25_countMass (x : CommanderState) (c : Nat) :
    Dist.mass (FiniteKernel.comp commanderExchange25 (FiniteKernel.deterministic commanderLeftCount) x) c =
      (if 1 ≤ c ∧ c ≤ 50 then transitionWeight 99 50 25 (commanderLeftCount x) c else 0) := by
  classical
  set K := transitionWeight 99 50 25 (commanderLeftCount x) c
  set F := (Finset.univ : Finset CommanderState).filter (fun y => c = commanderLeftCount y)
  -- (A) the per-y term is the fiber indicator times `K`.
  have hVal (y : CommanderState) :
      Dist.mass (commanderExchange25 x) y * Dist.mass (FiniteKernel.deterministic commanderLeftCount y) c =
        (if c = commanderLeftCount y then K else 0) := by
    by_cases hyc : c = commanderLeftCount y
    · -- on the fiber: `count y = c`; the deterministic point mass is `1`.
      have hcnt : commanderLeftCount y = c := hyc.symm
      rw [FiniteKernel.deterministic, commanderExchange25_mass, Dist.mass_pointMass, hcnt]
      -- now: TW (count x) c * (if c = c then 1 else 0) = (if c = c then K else 0)
      simp [K]
    · -- off the fiber: the deterministic point mass is `0`.
      rw [FiniteKernel.deterministic, commanderExchange25_mass, Dist.mass_pointMass, ite_eq_right hyc, ite_eq_right hyc]
      simp [mul_zero]
  -- (B) the count fiber `{y // count y = c}` has the singleton-or-empty card.
  have hCard : F.card = (if 1 ≤ c ∧ c ≤ 50 then 1 else 0) := by
    have hF : F = (Finset.univ : Finset CommanderState).filter (fun y => commanderLeftCount y = c) := by
      apply Finset.ext
      intro y
      simp [F, Finset.mem_filter, Finset.mem_univ]
      tauto
    rw [hF, commanderCountFiber_card]
  calc
    Dist.mass (FiniteKernel.comp commanderExchange25 (FiniteKernel.deterministic commanderLeftCount) x) c =
        (∑ y : CommanderState, Dist.mass (commanderExchange25 x) y * Dist.mass (FiniteKernel.deterministic commanderLeftCount y) c) :=
      apply_mass_eq_sum (commanderExchange25 x) (FiniteKernel.deterministic commanderLeftCount) c
    _ = (∑ y : CommanderState, (if c = commanderLeftCount y then K else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact hVal y
    _ = (∑ y ∈ F, K) := by
      -- swap the indicator for the fiber-membership test, then restrict to the fiber
      have hIte (y : CommanderState) :
          (if c = commanderLeftCount y then K else 0) = (if y ∈ F then K else 0) := by
        by_cases hk : c = commanderLeftCount y
        · -- c = count y  ⟹  y ∈ F; both ites take their `then` branch
          have hmem : y ∈ F := by simp [F, Finset.mem_filter, Finset.mem_univ, hk]
          rw [ite_eq_left hk, ite_eq_left hmem]
        · -- c ≠ count y  ⟹  y ∉ F; both ites take their `else` branch
          have hnot : y ∉ F := by
            intro hmem
            have hk' : c = commanderLeftCount y := by
              simpa [F, Finset.mem_filter, Finset.mem_univ] using hmem
            contradiction
          rw [ite_eq_right hk, ite_eq_right hnot]
      have h1 : (∑ y : CommanderState, (if c = commanderLeftCount y then K else 0)) =
          (∑ y : CommanderState, (if y ∈ F then K else 0)) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hIte y
      rw [h1]
      have h2 : (∑ y : CommanderState, (if y ∈ F then K else 0)) =
          (∑ y ∈ (Finset.univ : Finset CommanderState), (if y ∈ F then K else 0)) := rfl
      rw [h2, ← Finset.sum_filter]
      have hF2 : (Finset.univ : Finset CommanderState).filter (fun y => y ∈ F) = F := by
        apply Finset.ext
        intro y
        simp [F, Finset.mem_filter, Finset.mem_univ]
      rw [hF2]
    _ = F.card * K := Finset.sum_const _
    _ = (if 1 ≤ c ∧ c ≤ 50 then 1 else 0) * K := by rw [hCard, Nat.cast_ite]; rfl
    _ = (if 1 ≤ c ∧ c ≤ 50 then K else 0) := by
      by_cases hk : 1 ≤ c ∧ c ≤ 50
      · have hL : ((if 1 ≤ c ∧ c ≤ 50 then 1 else 0) : Rat) = 1 := ite_eq_left hk
        rw [hL]
        simp only [one_mul, if_pos hk]
      · have hL : ((if 1 ≤ c ∧ c ≤ 50 then 1 else 0) : Rat) = 0 := ite_eq_right hk
        rw [hL]
        simp only [zero_mul, if_neg hk]
    _ = (if 1 ≤ c ∧ c ≤ 50 then transitionWeight 99 50 25 (commanderLeftCount x) c else 0) := by
      simp [K]

end CommanderMembershipExchange
end Shufflemath
