module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

noncomputable section

/-- An exact finite probability distribution with rational weights.

`Convexity.StdSimplex` carries nonnegativity and total mass one in the type, so
there is no separate probability-validity predicate to keep synchronized. -/
abbrev Dist (alpha : Type*) := Convexity.StdSimplex Rat alpha

namespace Dist

variable {alpha beta : Type*}

/-- The rational mass assigned to a point. -/
def mass (mu : Dist alpha) (x : alpha) : Rat :=
  mu.weights x

@[simp]
theorem mass_nonneg (mu : Dist alpha) (x : alpha) : 0 <= mass mu x := by
  exact mu.weights_nonneg x

@[simp]
theorem sum_mass [Fintype alpha] (mu : Dist alpha) :
    Finset.sum Finset.univ (fun x => mass mu x) = 1 := by
  simp [mass]

/-- Construct an exact finite distribution from a normalized rational function.

This is the boundary used to turn a computational vector or stochastic-matrix row
into the semantic `Dist` representation. -/
noncomputable def ofFun [Fintype alpha]
    (f : alpha -> Rat)
    (hnonneg : forall x, 0 <= f x)
    (htotal : Finset.sum Finset.univ f = 1) : Dist alpha where
  weights := Finsupp.equivFunOnFinite.symm f
  nonneg x := by
    simpa using hnonneg x
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using htotal

@[simp]
theorem mass_ofFun [Fintype alpha]
    (f : alpha -> Rat)
    (hnonneg : forall x, 0 <= f x)
    (htotal : Finset.sum Finset.univ f = 1)
    (x : alpha) :
    mass (ofFun f hnonneg htotal) x = f x := by
  rfl

/-- Point mass at `x`. -/
def pointMass (x : alpha) : Dist alpha :=
  Convexity.StdSimplex.single x

@[simp]
theorem mass_pointMass [DecidableEq alpha] (x y : alpha) :
    mass (pointMass x) y = if y = x then 1 else 0 := by
  simp [mass, pointMass, Finsupp.single_apply, eq_comm]

-- `sConvexComb` for the `StdSimplex` convex-space instance is `join` by
-- definition of the instance, but the class field does not unfold under `simp`
-- on its own. This bridge (proved on weights, where both sides are the same
-- pushforward sum) lets simp move freely between the `join` and
-- `sConvexComb` notations.
@[simp]
theorem join_sConvexComb {X : Type*} (f : Dist (Dist X)) : f.join = f.sConvexComb := by
  ext
  simp only [Convexity.StdSimplex.join, Convexity.StdSimplex.weights_sConvexComb]

/-- Joining a point mass of distributions recovers the distribution.

This is the unit law for `join`, used by the kernel identity laws below. -/
@[simp]
theorem join_pointMass {X : Type*} (sigma : Dist X) : (pointMass sigma).join = sigma := by
  simp only [pointMass, join_sConvexComb]
  exact Convexity.ConvexSpace.sConvexComb_single sigma

end Dist

/-- A finite exact Markov kernel. Each row is a probability distribution by
construction. -/
abbrev FiniteKernel (alpha beta : Type*) := alpha -> Dist beta

namespace FiniteKernel

variable {alpha beta gamma delta : Type*}

/-- Kernel induced by a deterministic state transformation. -/
def deterministic (f : alpha -> beta) : FiniteKernel alpha beta :=
  fun x => Dist.pointMass (f x)

/-- Identity kernel. -/
def identity : FiniteKernel alpha alpha :=
  deterministic id

/-- Apply a finite kernel to an input distribution. -/
def apply (mu : Dist alpha) (K : FiniteKernel alpha beta) : Dist beta :=
  (mu.map K).join

/-- Compose kernels in execution order: first `K`, then `L`. -/
def comp (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma) :
    FiniteKernel alpha gamma :=
  fun x => ((K x).map L).join

/-- Repeatedly apply a homogeneous kernel:

`run K 0 mu = mu` and `run K (n + 1) mu = run K n (apply mu K)`.

Written with an explicit `Nat.recOn` (rather than pattern matching) so that
the kernel reduces `run K (Nat.succ n) _` by clean recursor steps; the
compiler's default big-recursion form stalls on variable-level successors
inside the heavy `StdSimplex` proof terms. -/
def run (K : FiniteKernel alpha alpha) (n : Nat) (mu : Dist alpha) : Dist alpha :=
  Nat.recOn n (fun d => d)
    (fun _ ih => fun d => ih (apply d K))
    mu

@[simp]
theorem apply_pointMass (x : alpha) (K : FiniteKernel alpha beta) :
    apply (Dist.pointMass x) K = K x := by
  simp [apply, Dist.pointMass]

/-- Pushing a distribution through a kernel and then reading a mass is the
`μ`-weighted sum of the corresponding kernel-row masses: the mass of the
kernel pushforward (the `μ`-weighted mixture of rows) at `x` is
`∑_j μ(j) K(j, x)`. -/
theorem apply_mass [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (mu : Dist alpha) (K : FiniteKernel alpha beta) (x : beta) :
    Dist.mass (apply mu K) x = Finset.sum Finset.univ (fun j => Dist.mass mu j * Dist.mass (K j) x) := by
  unfold apply
  unfold Dist.mass
  simp only [Convexity.StdSimplex.weights_join, Convexity.StdSimplex.weights_map]
  rw [Finsupp.sum_apply]
  simp [Finsupp.mapDomain, Finsupp.sum_fintype, Finsupp.smul_apply]
  have h1 : ((Finset.sum Finset.univ fun i => Finsupp.single (K i) (mu.weights i)).sum
      (fun a₁ b => b * a₁.weights x)) =
      Finset.sum Finset.univ fun i => (Finsupp.single (K i) (mu.weights i)).sum
        (fun a₁ b => b * a₁.weights x) := by
    rw [Finsupp.sum_finsetSum]
    · intro a
      ring
    · intro a m₁ m₂
      ring
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.sum_single_index (h_zero := by ring)

/-- The same row-mass formula as `apply_mass`, but without the (unused) `Fintype`/`DecidableEq`
  instances on the codomain `beta`. The sum is only over the domain `alpha`, so the codomain can
  be any type (e.g. `List (Fin n)`, which is not `Fintype`). This is what lets the joint-
distribution bridge apply to the deck level. -/
theorem apply_mass_dom [Fintype alpha] [DecidableEq alpha]
    (mu : Dist alpha) (K : FiniteKernel alpha beta) (x : beta) :
    Dist.mass (apply mu K) x = Finset.sum Finset.univ (fun j => Dist.mass mu j * Dist.mass (K j) x) := by
  unfold apply
  unfold Dist.mass
  simp only [Convexity.StdSimplex.weights_join, Convexity.StdSimplex.weights_map]
  rw [Finsupp.sum_apply]
  simp [Finsupp.mapDomain, Finsupp.sum_fintype, Finsupp.smul_apply]
  have h1 : ((Finset.sum Finset.univ fun i => Finsupp.single (K i) (mu.weights i)).sum
      (fun a₁ b => b * a₁.weights x)) =
      Finset.sum Finset.univ fun i => (Finsupp.single (K i) (mu.weights i)).sum
        (fun a₁ b => b * a₁.weights x) := by
    rw [Finsupp.sum_finsetSum]
    · intro a
      ring
    · intro a m₁ m₂
      ring
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.sum_single_index (h_zero := by ring)

/-- Fintype-free row-mass formula for the Giry bind: the mass of the kernel
pushforward `apply mu K` at `y` is the `mu`-weighted sum of the corresponding
kernel-row masses, summed over `mu`'s **finite support** rather than over
`Finset.univ`.  This is the same statement as `apply_mass`/`apply_mass_dom`
but with no `[Fintype alpha]` hypothesis, so it applies to non-Fintype state
spaces such as `List (Fin n)`.  It follows from the `StdSimplex` `map`/`join`
`Finsupp` weight definitions (no `apply_mass_dom` detour).  The F4.5
Fintype-free kernel-contraction argument rests on this. -/
theorem apply_mass_finsupp (mu : Dist alpha) (K : FiniteKernel alpha beta) (y : beta) :
    Dist.mass (apply mu K) y = (mu.weights.support).sum (fun j => Dist.mass mu j * Dist.mass (K j) y) := by
  unfold apply
  unfold Dist.mass
  simp only [Convexity.StdSimplex.weights_join, Convexity.StdSimplex.weights_map,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  let h (d : Convexity.StdSimplex Rat beta) : Rat →+ Rat :=
    AddMonoidHom.mk (ZeroHom.mk (fun (b : Rat) => b * d.weights y) (by ring)) (by intro x x2; ring)
  have hsum : (fun (d : Convexity.StdSimplex Rat beta) (b : Rat) => b * d.weights y) = fun d b => (h d) b := by
    ext d b
    dsimp only [h]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hsum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  simp only [Finsupp.sum]
  dsimp only [h]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

@[simp]
theorem deterministic_apply_pointMass (x : alpha) (f : alpha -> beta) :
    apply (Dist.pointMass x) (deterministic f) = Dist.pointMass (f x) := by
  simp [deterministic]

/-! ## Associativity, identity, and iteration

`FiniteKernel` is the Giry-style distribution monad: `apply` is monadic bind
and `comp` is monadic composition. The proofs below use the monad laws that
mathlib already proves for `Convexity.StdSimplex` (as the convex-space
structure whose convex combination is `join`), plus two private Finsupp-level
normalizations that carry the `map`/`join` definitions down to pushforward
sums.
-/

-- Private monad-law normalizations at the `StdSimplex` level.
-- Each is exactly the statement mathlib proves privately for the distribution
-- monad; the proofs unfold `map`/`join` to pushforward sums and let simp
-- rearrange the finite sums (`mapDomain`, `add_smul`, and the `Finsupp` sum
-- Fubini lemmas).

theorem map_join_kernels {X Y : Type*} (sigma : Dist (Dist X)) (L : X -> Dist Y) :
    (sigma.join).map L = (sigma.map fun d => d.map L).join := by
  ext1
  simp [Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
    Finsupp.smul_sum]

theorem join_join_kernels {X : Type*} (sigma : Dist (Dist (Dist X))) :
    (sigma.join).join = (sigma.map fun d => d.join).join := by
  ext1
  simp [Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
    Finsupp.smul_sum, mul_smul]

/-- Associativity of kernel application:

`apply (apply mu K) L = apply mu (comp K L)`.

This is the monad associativity law for the distribution monad, and it is the
workhorse that makes protocol-level reasoning possible: the distance after an
`n`-step protocol depends only on the composed kernel, never on the order in
which intermediate distributions were formed. -/
@[simp]
theorem apply_comp (mu : Dist alpha) (K : FiniteKernel alpha beta)
    (L : FiniteKernel beta gamma) :
    apply (apply mu K) L = apply mu (comp K L) := by
  unfold apply
  unfold comp
  calc
    (((mu.map K).join).map L).join = (((mu.map K).map (fun d => d.map L)).join).join := by
      rw [map_join_kernels]
    _ = (((mu.map K).map (fun d => d.map L)).map (fun e => e.join)).join := by
      rw [join_join_kernels]
    _ = (mu.map (fun x => ((K x).map L).join)).join := by
      rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
    _ = (mu.map (comp K L)).join := by
      rfl

/-- Associativity of kernel composition: `comp (comp K L) M = comp K (comp L M)`.

Follows by applying `apply_comp` at a point mass, which makes `comp` a genuine
monoid structure on homogeneous kernels. -/
@[simp]
theorem comp_assoc (K : FiniteKernel alpha beta) (L : FiniteKernel beta gamma)
    (M : FiniteKernel gamma delta) :
    comp (comp K L) M = comp K (comp L M) := by
  funext x
  have h1 : (comp (comp K L) M) x = apply (Dist.pointMass x) (comp (comp K L) M) :=
    (apply_pointMass x _).symm
  have h2 : (comp K (comp L M)) x = apply (Dist.pointMass x) (comp K (comp L M)) :=
    (apply_pointMass x _).symm
  rw [h1, h2]
  calc
    apply (Dist.pointMass x) (comp (comp K L) M) = apply (apply (Dist.pointMass x) (comp K L)) M :=
      (apply_comp _ (comp K L) M).symm
    _ = apply (apply (apply (Dist.pointMass x) K) L) M := by
      rw [(apply_comp _ K L).symm]
    _ = apply (apply (Dist.pointMass x) K) (comp L M) :=
      apply_comp _ L M
    _ = apply (Dist.pointMass x) (comp K (comp L M)) :=
      apply_comp _ K _

/-- `comp K identity = K`: the identity kernel is a right unit for composition. -/
@[simp]
theorem comp_id_right (K : FiniteKernel alpha beta) : comp K identity = K := by
  funext x
  simp only [comp, identity, Dist.join_sConvexComb]
  exact Convexity.StdSimplex.iConvexComb_single (K x)

/-- `comp identity K = K`: the identity kernel is a left unit for composition. -/
@[simp]
theorem comp_id_left (K : FiniteKernel alpha beta) : comp identity K = K := by
  funext x
  simp [comp, identity, deterministic, Dist.pointMass, Convexity.StdSimplex.map_single]

/-- Applying the identity kernel to a distribution is the identity:

`apply mu identity = mu`. -/
@[simp]
theorem apply_id_left (mu : Dist alpha) : apply mu identity = mu := by
  simp only [apply, identity, Dist.join_sConvexComb]
  exact Convexity.StdSimplex.iConvexComb_single mu

/-- The one-step recursion equation of `run`:

`run K (n + 1) x = run K n (apply x K)`.

This is not definitional (`n + 1` is not a `Nat` constructor), but it is the
bridge that lets the induction lemmas below move between the `n + 1` form
that `induction` produces and the `Nat.succ` form the kernel reduces. -/
theorem run_rec_eq (n : Nat) (K : FiniteKernel alpha alpha) (x : Dist alpha) :
    run K (n + 1) x = run K n (apply x K) := by
  cases n with
  | zero =>
    rfl
  | succ n =>
    rw [← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
    rfl

/-- Simultaneous induction hypothesis for `run`: both the "self-apply" and the
    "one more step" equations, proved together because each one-step case is
    the other at the previous level. -/
theorem run_apply_self_and_succ (n : Nat) (K : FiniteKernel alpha alpha) :
    (forall mu : Dist alpha, run K n (apply mu K) = apply (run K n mu) K) ∧
    (forall mu : Dist alpha, run K (Nat.succ n) mu = apply (run K n mu) K) := by
  induction n with
  | zero =>
    constructor
    · intro mu
      rfl
    · intro mu
      rfl
  | succ n ih =>
    rcases ih with ⟨ihT, _⟩
    constructor
    · intro mu
      rw [run_rec_eq]
      exact ihT (apply mu K)
    · intro mu
      rw [Nat.succ_eq_add_one]
      rw [run_rec_eq, run_rec_eq]
      exact ihT (apply mu K)

/-- Iterating the same kernel: `run K n (apply mu K)` carries the extra step
    through, because the `n` iterations act on the already-advanced
    distribution. -/
@[simp]
theorem run_apply_self (n : Nat) (K : FiniteKernel alpha alpha) :
    forall mu : Dist alpha, run K n (apply mu K) = apply (run K n mu) K :=
    (run_apply_self_and_succ n K).1

/-- One more iteration of a homogeneous kernel is the same as one more
    application:

`run K (n + 1) mu = apply (run K n mu) K` (stated with `Nat.succ n`,
    which the kernel reduces cleanly). -/
@[simp]
theorem run_succ (n : Nat) (K : FiniteKernel alpha alpha) (mu : Dist alpha) :
    run K (Nat.succ n) mu = apply (run K n mu) K :=
    (run_apply_self_and_succ n K).2 mu

/-- Same as `run_succ`, in `n + 1` form. -/
@[simp]
theorem run_succ_add (n : Nat) (K : FiniteKernel alpha alpha) (mu : Dist alpha) :
    run K (n + 1) mu = apply (run K n mu) K := by
  rw [← Nat.succ_eq_add_one]
  exact run_succ n K mu


/-- The `n`-fold composition of a homogeneous kernel in execution order.

`compPow K 0` is the identity kernel and `compPow K (n + 1) = comp (compPow K n) K`,
so `compPow K n` is the kernel that runs `K` exactly `n` times. -/
def compPow (K : FiniteKernel alpha alpha) : Nat -> FiniteKernel alpha alpha
  | 0 => identity
  | n + 1 => comp (compPow K n) K

@[simp]
theorem compPow_zero (K : FiniteKernel alpha alpha) : compPow K 0 = identity := rfl

@[simp]
theorem compPow_succ (K : FiniteKernel alpha alpha) (n : Nat) :
    compPow K (n + 1) = comp (compPow K n) K := rfl

/-- `run` and `compPow` agree: running the kernel `n` times from `mu` equals
    applying the `n`-fold composition to `mu`. -/
@[simp]
theorem run_compPow (n : Nat) (K : FiniteKernel alpha alpha) (mu : Dist alpha) :
    run K n mu = apply mu (compPow K n) := by
  induction n with
  | zero =>
    rw [compPow_zero, apply_id_left]
    rfl
  | succ n ih =>
    -- `induction` hands over the goal in `n + 1` form, so no `Nat.succ`
    -- rewriting is needed; every step is a pure syntactic rewrite, and the
    -- final goal is definitionally `rfl`.
    rw [run_succ_add, ih, apply_comp, ← compPow_succ]


end FiniteKernel

/-- The independent (tensor) product distribution: draw `a` from `μ`, then `b`
from `ν`.  A valid probability law (total mass 1) because the total factors as
`(∑_a μ a)·(∑_b ν b) = 1·1`.  This is the missing F4.2/F4.3 machinery for
composing the two within-pile shuffles into a single deck-level law.  Defined
as an explicit `ofFun` term (not a tactic-built `by`) so the mass simp-lemma
below unfolds it. -/
noncomputable def distProduct {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (μ : Dist α) (ν : Dist β) : Dist (α × β) :=
  Dist.ofFun (fun p : α × β => Dist.mass μ p.1 * Dist.mass ν p.2)
    (fun p => Rat.mul_nonneg (Dist.mass_nonneg μ p.1) (Dist.mass_nonneg ν p.2))
    (by
      classical
      haveI : DecidableEq (α × β) := inferInstance
      have hUniv : (Finset.univ : Finset (α × β)) =
          (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β) := by
        ext p
        simp [Finset.mem_univ]
      have hFac : (∑ a ∈ (Finset.univ : Finset α), ∑ b ∈ (Finset.univ : Finset β),
                Dist.mass μ a * Dist.mass ν b) =
          (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ a * (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν b)) := by
        rw [Finset.sum_congr rfl (fun a _ => (Finset.mul_sum (Finset.univ) (fun b => Dist.mass ν b) (Dist.mass μ a)).symm)]
      have hC : (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν b) = 1 := by simp [Dist.sum_mass]
      have hV : (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ a) = 1 := by simp [Dist.sum_mass]
      calc
        (∑ p ∈ (Finset.univ : Finset (α × β)), Dist.mass μ p.1 * Dist.mass ν p.2) =
          (∑ p ∈ (Finset.univ : Finset α) ×ˢ (Finset.univ : Finset β), Dist.mass μ p.1 * Dist.mass ν p.2) := by rw [hUniv]
        _ = (∑ a ∈ (Finset.univ : Finset α), ∑ b ∈ (Finset.univ : Finset β), Dist.mass μ a * Dist.mass ν b) := by rw [Finset.sum_product]
        _ = (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ a * (∑ b ∈ (Finset.univ : Finset β), Dist.mass ν b)) := hFac
        _ = (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ a * 1) := by rw [hC]
        _ = (∑ a ∈ (Finset.univ : Finset α), Dist.mass μ a) := by rw [Finset.sum_congr rfl (fun a _ => mul_one (Dist.mass μ a))]
        _ = 1 := hV)

/-- The mass of the independent product at `(a, b)` is the product of the
marginal masses, `μ(a)·ν(b)` — the defining property that makes it a tensor
product.  Immediate from the `ofFun` construction. -/
@[simp]
theorem distProduct_mass {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (μ : Dist α) (ν : Dist β) (a : α) (b : β) :
    Dist.mass (distProduct μ ν) (a, b) = Dist.mass μ a * Dist.mass ν b := by
  simp [distProduct, Dist.mass_ofFun]

end


/-- The Fintype-free independent (tensor) product distribution.  `distProduct`
    above requires `[Fintype α] [Fintype β]` (built with `Dist.ofFun`); this
    variant builds the same law directly from the `StdSimplex` `map`/`join`
    machinery, whose total mass Mathlib preserves, so it works over types that
    are *not* fintypes: in particular `List (Fin n)`, the state space of
    `GSR.idealShuffle` and the two-pile `CommanderLocalGSR.gsrProductKernel`.
    `Dist.map`/`Dist.join` are Finsupp-level and need no `Fintype`. -/
noncomputable def distProductFinsupp (p : Dist α) (q : Dist β) : Dist (α × β) :=
  (p.map (fun (a : α) => q.map (fun (b : β) => (a, b)))).join

/-- The mass of `distProductFinsupp` at `(a, b)` is the product of the two
    marginal masses `p a * q b`, the defining tensor property, proved directly
    from the `Finsupp` `mapDomain`/`join` weight definitions (no `Fintype`, no
    `apply_mass_dom`).  This is the F4.3 core: it lets the two-pile GSR product
    kernel's point-mass be read as a product of per-pile masses. -/
@[simp]
theorem distProductFinsupp_mass [DecidableEq α] [DecidableEq β] (p : Dist α) (q : Dist β) (a : α) (b : β) :
    ((distProductFinsupp p q)).weights (a, b) = p.weights a * q.weights b := by
  dsimp only [distProductFinsupp]
  -- (p.map (fun a => q.map (fun b => (a,b)))).join (a,b)
  let g (x : α) : Dist (α × β) := q.map (fun (r : β) => (x, r))
  have hmg : p.map (fun (x : α) => q.map (fun (r : β) => (x, r))) = p.map g := rfl
  rw [hmg]
  simp only [Convexity.StdSimplex.map, Convexity.StdSimplex.join, Finsupp.mapDomain,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  let h (a₁ : Dist (α × β)) : Rat →+ Rat :=
    AddMonoidHom.mk (ZeroHom.mk (fun (bb : Rat) => bb * a₁.weights (a, b)) (by ring))
      (by intro x y; ring)
  have hsum : (fun (a₁ : Dist (α × β)) (bb : Rat) => bb * a₁.weights (a, b)) = fun a₁ bb => (h a₁) bb := by
    ext a₁ bb
    dsimp only [h]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Finsupp.mapDomain, hsum, Finsupp.sum_mapDomain_index_addMonoidHom h]
  simp only [Finsupp.sum]
  have hsum_eq : ∑ aa ∈ p.weights.support, (h (g aa)) (p.weights aa) =
      ∑ aa ∈ p.weights.support, (p.weights aa * (g aa).weights (a, b)) := by
    apply Finset.sum_congr rfl
    intro aa _
    change (fun (c : Rat) => c * (g aa).weights (a, b)) (p.weights aa) =
      p.weights aa * (g aa).weights (a, b)
    ring
  rw [hsum_eq]
  -- inner: (q.map (fun r => (aa, r))).weights (a,b) for an explicit first-coordinate aa
  have hinner (aa : α) : (q.map (fun (r : β) => (aa, r))).weights (a, b) = if aa = a then q.weights b else 0 := by
    simp only [Convexity.StdSimplex.map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
    have hrew : (fun (r₁ : β) (c : Rat) => if (aa, r₁) = (a, b) then c else 0) =
        (fun r₁ c => if aa = a then (if r₁ = b then c else 0) else 0) := by
      ext r₁ c; by_cases ha : aa = a <;> by_cases hb : r₁ = b <;> simp [ha, hb]
    rw [hrew]
    by_cases ha : aa = a
    · have hfun : (fun (r₁ : β) (c : Rat) => if aa = a then (if r₁ = b then c else 0) else 0) =
          (fun r₁ c => if r₁ = b then c else 0) := by funext r₁ c; exact ite_eq_left ha
      rw [hfun, Finsupp.sum_ite_self_eq', ite_eq_left ha]
    · have hzero : (fun (r₁ : β) (c : Rat) => if aa = a then (if r₁ = b then c else 0) else 0) =
          fun _ _ => 0 := by funext r₁ c; exact ite_eq_right ha
      rw [hzero, Finsupp.sum, Finset.sum_const_zero, ite_eq_right ha]
  rw [show ∑ aa ∈ p.weights.support, p.weights aa * (g aa).weights (a, b) =
        ∑ aa ∈ p.weights.support, p.weights aa * (if aa = a then q.weights b else 0) from by
    apply Finset.sum_congr rfl
    intro aa _
    dsimp only [g]
    rw [hinner aa]]
  rw [show ∑ aa ∈ p.weights.support, p.weights aa * (if aa = a then q.weights b else 0) =
        ∑ aa ∈ p.weights.support, (if aa = a then p.weights aa else 0) * q.weights b from by
    apply Finset.sum_congr rfl
    intro aa _; by_cases ha : aa = a <;> simp [ha, mul_zero, mul_comm]]
  have hfactor : ∑ aa ∈ p.weights.support, (if aa = a then p.weights aa else 0) * q.weights b =
      (∑ aa ∈ p.weights.support, (if aa = a then p.weights aa else 0)) * q.weights b := by
    rw [show ∑ aa ∈ p.weights.support, (if aa = a then p.weights aa else 0) * q.weights b =
          ∑ aa ∈ p.weights.support, q.weights b * (if aa = a then p.weights aa else 0) from by
      apply Finset.sum_congr rfl; intro aa _; ring]
    rw [← Finset.mul_sum, mul_comm]
  rw [hfactor]
  have hsumL : ∑ aa ∈ p.weights.support, (if aa = a then p.weights aa else 0) = p.weights a := by
    change p.weights.sum (fun (aa : α) (v : Rat) => (if aa = a then v else 0)) = p.weights a
    exact Finsupp.sum_ite_self_eq' _ a
  rw [hsumL]

end Shufflemath

end
