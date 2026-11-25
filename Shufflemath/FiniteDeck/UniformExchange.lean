module

public import Shufflemath.FiniteDeck.MultiExchange
public import Shufflemath.FiniteDeck.BlockPartition
public import Shufflemath.GSR
public import Shufflemath.Markov
public import Shufflemath.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

@[expose]
public section

namespace Shufflemath
namespace FiniteDeck

open Classical

variable {N p : Nat} {n : Fin p → Nat}

/-- The **uniform-transposition exchange kernel** on the allocation carrier: from a
    state `A`, pick two card indices `(a, b)` uniformly at random from
    `Fin N × Fin N` (all `N^2` pairs, the `a = b` pair being the no-op) and move
    to the swapped state `swapPiles A a b`.  A pushforward of a distribution, so
    each row is a genuine `Dist` (row-mass sums to 1 by construction).  The
    `0 < N` argument exists only to name the uniform law on the (nonempty) pair
    type; a positive deck is the natural domain of the exchange. -/
noncomputable def swapKernel (hN : 0 < N) (A : Allocation N p n) : Dist (Allocation N p n) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  exact (GSR.uniformDist (Fin N × Fin N)).map (fun ab => swapPiles A ab.1 ab.2)

/-- Swapping the piles of `a` and `b` and then swapping them again restores the
    original allocation owner function: `swapOwner ∘ swapOwner = A.val`.  Uses
    only `swapOwner_eq_cardTransposition` + the involution of `cardTransposition`. -/
theorem swapOwner_involutive (A : Allocation N p n) (a b x : Fin N) :
    swapOwner (swapPiles A a b) a b x = A.val x := by
  have h1 : swapOwner (swapPiles A a b) a b x =
      (swapPiles A a b).val (cardTransposition a b x) :=
    swapOwner_eq_cardTransposition (swapPiles A a b) a b x
  have h2 : (swapPiles A a b).val (cardTransposition a b x) =
      swapOwner A a b (cardTransposition a b x) := by
    simp [swapPiles]
  have h3 : swapOwner A a b (cardTransposition a b x) =
      A.val (cardTransposition a b (cardTransposition a b x)) :=
    swapOwner_eq_cardTransposition A a b (cardTransposition a b x)
  rw [h1, h2, h3]
  rw [cardTransposition_involution]

/-- The exchange operation is an **involution** on the allocation carrier:
    `swapPiles (swapPiles A a b) a b = A`. -/
theorem swapPiles_involution (A : Allocation N p n) (a b : Fin N) :
    swapPiles (swapPiles A a b) a b = A := by
  apply Subtype.ext
  funext x
  simpa [swapPiles] using swapOwner_involutive A a b x

/-- Swapping `a` and `b` sends `A` to `A'` iff it sends `A'` back to `A`: the
    involution, stated as an `iff` on the outcome.  This is the fiber-symmetry
    fact that makes the uniform-transposition kernel **symmetric**. -/
theorem swapPiles_swap_iff (A A' : Allocation N p n) (a b : Fin N) :
    (swapPiles A a b = A') ↔ (swapPiles A' a b = A) := by
  constructor
  · intro h
    rw [← h]
    exact swapPiles_involution A a b
  · intro h
    rw [← h]
    exact swapPiles_involution A' a b

/-- Explicit mass of the swap kernel at `A'`: the sum, over all `N^2` card pairs,
    of the uniform pair-mass `(N^2)⁻¹` times the indicator that the pair's swap
    lands exactly on `A'`.  Follows directly from `GSR.map_uniform_mass`. -/
theorem swapKernel_mass (hN : 0 < N) (A A' : Allocation N p n) :
    Dist.mass (swapKernel hN A) A' =
      (Finset.univ : Finset (Fin N × Fin N)).sum
        (fun s => (N * N : Rat)⁻¹ * if A' = swapPiles A s.1 s.2 then 1 else 0) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  show Dist.mass ((GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => swapPiles A ab.1 ab.2)) A' =
      (Finset.univ : Finset (Fin N × Fin N)).sum
        (fun s => (N * N : Rat)⁻¹ * if A' = swapPiles A s.1 s.2 then 1 else 0)
  have hcard : Fintype.card (Fin N × Fin N) = N * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [GSR.map_uniform_mass]
  simp [hcard]

/-! ### A1.4 — the uniform swap kernel is equivariant under relabeling

The headline of the A1.4 program: relabeling the cards (`relabel σ`) preserves the
uniform swap kernel's mass.  Push the kernel's output distribution forward by
`relabel σ` — i.e. swap the piles with a uniform pair of indices, then relabel —
and the mass that lands on the relabelled target `relabel σ B` is exactly the mass
the original kernel `swapKernel hN A` puts on `B`.  The `swapRelabel` def bakes in
the `Nonempty (Fin N × Fin N)` instance (the same pattern as `swapKernel`), so the
distribution is usable bare in statements.  The proof uses only the **injectivity**
of `relabel σ` (a bijection, by `relabel_symm_relabel`): the two families of
indicators — `relabel σ B = relabel σ (swapPiles A ab.1 ab.2)` and
`B = swapPiles A ab.1 ab.2` — are equivalent *term-by-term* over the same `ab`
pairs, so no sum reindexing is needed.  Together with `swapKernel_symmetric` this
is the content of "the kernel is invariant under relabeling." -/

/-- The distribution "swap the piles with a uniform pair of indices, then relabel
    by `σ`".  Consumes the `[Nonempty (Fin N × Fin N)]` instance inside the def
    (the same pattern as `swapKernel`), leaving a bare `Dist (Allocation N p n)`
    usable in statements. -/
noncomputable def swapRelabel (hN : 0 < N) (σ : Equiv.Perm (Fin N)) (A : Allocation N p n) :
    Dist (Allocation N p n) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  exact (GSR.uniformDist (Fin N × Fin N)).map (fun ab => relabel σ (swapPiles A ab.1 ab.2))

/-- Relabeling preserves the uniform swap kernel's mass: the distribution
    `swapRelabel hN σ A` (swap with a uniform pair of indices, then relabel by
    `σ`) has, at the relabelled state `relabel σ B`, exactly the mass that
    `swapKernel hN A` has at `B`. -/
theorem swapKernel_equivariant (hN : 0 < N) (σ : Equiv.Perm (Fin N)) (A B : Allocation N p n) :
    Dist.mass (swapRelabel hN σ A) (relabel σ B) = Dist.mass (swapKernel hN A) B := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  have hcard : Fintype.card (Fin N × Fin N) = N * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [swapRelabel, GSR.map_uniform_mass, swapKernel_mass hN A B, hcard, Nat.cast_mul]
  -- both sides are now `∑ (N*N)⁻¹ · 1[·]` over the *same* `ab` pairs; the two indicators
  -- agree term-by-term because `relabel σ` is a bijection (`relabel_eq_iff`): for each
  -- pair, `relabel σ B = relabel σ (swapPiles A a b) ↔ B = swapPiles A a b`.  No
  -- reindexing is needed — the goal already carries the `relabel σ (swapPiles …)`
  -- indicator, so the iff rewrites it to the plain `swapPiles` one and the sums match.
  refine Finset.sum_congr rfl fun ab _ => by
    simp [relabel_eq_iff σ B (swapPiles A ab.1 ab.2)]

/-- The uniform-transposition kernel is **symmetric** (doubly stochastic):
    `mass (swapKernel A) A' = mass (swapKernel A') A`.  The two fiber indicators
    are pointwise equivalent by `swapPiles_swap_iff` (the involution). -/
theorem swapKernel_symmetric (hN : 0 < N) (A A' : Allocation N p n) :
    Dist.mass (swapKernel hN A) A' = Dist.mass (swapKernel hN A') A := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  rw [swapKernel_mass hN A A', swapKernel_mass hN A' A]
  refine Finset.sum_congr rfl fun s _ => by
    by_cases h : A' = swapPiles A s.1 s.2
    · have h2 : A = swapPiles A' s.1 s.2 :=
        ((swapPiles_swap_iff A A' s.1 s.2).1 h.symm).symm
      rw [ite_eq_left h, ite_eq_left h2]
    · have h2 : A ≠ swapPiles A' s.1 s.2 := by
        intro hc
        exact h ((swapPiles_swap_iff A A' s.1 s.2).2 hc.symm).symm
      rw [ite_eq_right h, ite_eq_right h2]

/-- The **uniform law over the allocation carrier** with feasible capacities
    (`∑ i, n i = N`).  Wraps `GSR.uniformDist` so the `[Nonempty]` instance (from the
    block-partition witness `nonemptyOfSumCapacities`) is consumed inside the def,
    leaving a bare `Dist (Allocation N p n)` usable in statements — the same pattern
    as `swapKernel` consuming `0 < N` for the uniform pair law. -/
noncomputable def uniformAlloc (hsum : (∑ i, n i) = N) : Dist (Allocation N p n) := by
  letI : Nonempty (Allocation N p n) := nonemptyOfSumCapacities N p n hsum
  exact GSR.uniformDist (Allocation N p n)

/-- The **A1 capstone**: for feasible capacities (`∑ i, n i = N`), the uniform law
    over the allocation carrier is **stationary** under the swap transition.
    `swapKernel hN` is symmetric (`swapKernel_symmetric`), and a symmetric kernel
    has its uniform measure stationary (`detailedBalance_implies_stationary`): the
    detailed-balance equation `mass mu x * mass (K x) y = mass mu y * mass (K y) x`
    has both uniform masses equal to the same constant `1 / card (Allocation N p n)`,
    so it reduces to `mass (K x) y = mass (K y) x`, i.e. exactly the symmetry. -/
theorem swapKernel_uniformStationary (hN : 0 < N) (hsum : (∑ i, n i) = N)
    (A : Allocation N p n) :
    Dist.mass (FiniteKernel.apply (uniformAlloc hsum) (swapKernel hN)) A
      = Dist.mass (uniformAlloc hsum) A := by
  letI hnon : Nonempty (Allocation N p n) := nonemptyOfSumCapacities N p n hsum
  exact Shufflemath.detailedBalance_implies_stationary
      (uniformAlloc hsum) (swapKernel hN)
      (by
        intro x y
        have hmx : Dist.mass (uniformAlloc hsum) x = (Fintype.card (Allocation N p n) : Rat)⁻¹ := by
          change Dist.mass (GSR.uniformDist (Allocation N p n)) x =
            (Fintype.card (Allocation N p n) : Rat)⁻¹
          exact GSR.mass_uniformDist x
        have hmy : Dist.mass (uniformAlloc hsum) y = (Fintype.card (Allocation N p n) : Rat)⁻¹ := by
          change Dist.mass (GSR.uniformDist (Allocation N p n)) y =
            (Fintype.card (Allocation N p n) : Rat)⁻¹
          exact GSR.mass_uniformDist y
        have hsym : Dist.mass (swapKernel hN x) y = Dist.mass (swapKernel hN y) x :=
          swapKernel_symmetric hN x y
        rw [hmx, hmy, hsym])
      A

end FiniteDeck
end Shufflemath
