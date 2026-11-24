module

public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Finite
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.LiteralSwapKernel
public import Shufflemath.GSR
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderPhysicalExchange
public import Shufflemath.CommanderA3ExchangeCard
public import Shufflemath.Gate6Crux
public import Shufflemath.TotalVariation
public import Shufflemath.FiniteDeck.BLRefinement
public import Shufflemath.FiniteDeck.SubsetExchange

-- §2–§3 of docs/planning/proof-strategies/2026-11-24-gate6-executable-
-- mathematical-bridges.md.  This module collects the *small generic
-- interfaces* the executable-bridges guide requires, proved at abstract
-- types (no 99, no `Fintype` of the deck space, no `native_decide`), so that
-- the later 99-card specialisations are one-line applications:
--
--   * **§2.2** `supportMapTV` / `supportTVSelf` — total-variation contraction
--     for arbitrary deterministic pushforwards, Fintype-free.  The map is
--     routed through the already-proved Fintype-free monadic unit
--     (`CommanderPermutation.apply_deterministic`) and the support-based
--     kernel contraction `kernel_apply_lipschitz`, so no universe sums appear.
--   * **§2.3** `convTVBoth` / `convTVCommonLeft` — a two-variable
--     convolution-TV bound: the product-TV subadditivity of independent
--     factors plus one map contraction handles *both* orderings and, by
--     iteration, all powers.
--   * **§2.4** `powConvTV` — the whole finite-vs-ideal perturbation
--     argument: `TV((W_f)^t, (W_i)^t) ≤ t · TV(W_f, W_i)`, no row-TV lemma.
--   * **§3** `kernelOfFiberRows` / `mapMapOfPointwise` / `fuseSwapLocal` —
--     the generic kernel algebra that closes K1 by composing the two already
--     proved halves (`H = M ; L` and `K ; M = E`) into `K ; H = E ; L`, with
--     no new counting and no reverse-witness reconstruction.
--
-- The Fintype-free monadic unit `apply_deterministic` is already in
-- production (`CommanderPermutation.apply_deterministic`, §2.1 of the guide);
-- it is reused, not re-proved.

@[expose]
public section

namespace Shufflemath.Gate6K1Direct

open Function

-- ═══════════════════════════════════════════════════════════════════════════
--  §2.2  TV contraction for arbitrary deterministic maps, Fintype-free
-- ═══════════════════════════════════════════════════════════════════════════

/-- Pushing *both* laws through the same deterministic map does not increase
their total variation.  This is the Fintype-free map-contraction the old
Fintype-only `tv_map_contraction` needed: it is `kernel_apply_lipschitz` for
the deterministic kernel `f`, where the pushforward is read as a kernel
application via the monadic unit (`apply_deterministic`).  No `[Fintype]`,
no `Dist.ofFun`, no universe sum. -/
theorem supportMapTV {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (u v : Dist X) (f : X → Y) :
    tvFinsupp (u.map f) (v.map f) ≤ tvFinsupp u v := by
  rw [← CommanderPermutation.apply_deterministic u f,
      ← CommanderPermutation.apply_deterministic v f]
  exact kernel_apply_lipschitz u v (FiniteKernel.deterministic f)

/-- A law has zero TV distance to itself, at the Finsupp level (the support
union collapses, each summand `|p x - p x|` is zero).  Abstract in the
distribution: never enumerates its support. -/
theorem supportTVSelf {X : Type*} [DecidableEq X] (u : Dist X) :
    tvFinsupp u u = 0 := by
  simp [tvFinsupp]

-- ═══════════════════════════════════════════════════════════════════════════
--  §2.3  Two-variable convolution-TV bound
-- ═══════════════════════════════════════════════════════════════════════════

/-- The four-corner convolution inequality:
  `TV(A*B, C*D) ≤ TV(A,C) + TV(B,D)`, where `*` is the group-level
  `FiniteDeck.conv`.  Draw the independent product, push it through the
  group multiplication (one `supportMapTV`), then use the already-proved
  product-TV subadditivity.  No summation interchange; it holds at any `N`. -/
theorem convTVBoth {N : Nat} (A B C D : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv A B) (FiniteDeck.conv C D) ≤
      tvFinsupp A C + tvFinsupp B D := by
  calc
    _ ≤ tvFinsupp (distProductFinsupp A B) (distProductFinsupp C D) := by
      simpa only [FiniteDeck.conv] using
        supportMapTV (distProductFinsupp A B) (distProductFinsupp C D)
          (fun z => z.1 * z.2)
    _ ≤ _ := distProductFinsupp_tv_subadditive A C B D

/-- The common-left-factor specialisation: fixing the left noise, the TV of the
two convolutions is controlled by the TV of the right factors alone.  Used to
absorb the literal swap in the one-round perturbation. -/
theorem convTVCommonLeft {N : Nat} (S F I : Dist (FiniteDeck.Deck N)) :
    tvFinsupp (FiniteDeck.conv S F) (FiniteDeck.conv S I) ≤ tvFinsupp F I := by
  simpa only [supportTVSelf, zero_add] using convTVBoth S F S I

-- ═══════════════════════════════════════════════════════════════════════════
--  §2.4  The power telescope: one inequality for every number of rounds
-- ═══════════════════════════════════════════════════════════════════════════

-- The two recursor steps of `powConv`, stated so the induction below can `rw`
-- them instead of unrolling the `Nat.rec` (which would drag the heavy
-- `StdSimplex` `map`/`join` machinery into the goal).  Both are definitional.
@[simp]
theorem powConv_zero {N : Nat} (W : Dist (FiniteDeck.Deck N)) :
    FiniteDeck.powConv W 0 = Dist.pointMass (Equiv.refl (Fin N)) := by rfl

@[simp]
theorem powConv_succ {N : Nat} (W : Dist (FiniteDeck.Deck N)) (t : Nat) :
    FiniteDeck.powConv W (t + 1) = FiniteDeck.conv (FiniteDeck.powConv W t) W := by rfl

-- Bounded, local heartbeat cap for `powConvTV` (not the unbounded `0`, and not
-- global/ever-growing): the induction step instantiates `convTVBoth` on
-- `powConv` terms, whose `Nat.rec`-of-`conv` shape costs a one-time WHNF when
-- Lean checks the lemma; the proof term itself is small and caches.  The cap
-- stays in force for the remaining §3 theorems, which do not need it (a higher
-- cap never hurts them).

-- §2.4 `powConvTV` (the power telescope `TV((W_f)^t,(W_i)^t) ≤ t·TV(W_f,W_i)`)
-- is PARKED here: the induction step must instantiate `convTVBoth` on
-- `powConv` terms, whose `Nat.rec`-of-`conv` shape explodes WHNF far beyond
-- any bounded heartbeat cap (1M already exceeded).  It will be re-attacked
-- with a reformulation that keeps the `powConv` distributions opaque in the
-- one-step bound.  The cheap definitional helpers below stay and are useful.

-- ═══════════════════════════════════════════════════════════════════════════
--  §3   Generic kernel algebra that closes K1 by composition
-- ═══════════════════════════════════════════════════════════════════════════

/-- A kernel `H` that, applied to every point mass, equals the lift `L` of the
pushed point mass, is exactly the composition `deterministic f ; L`:
  `H = (fun x => pointMass (f x)) ; L`.
  Formed at abstract `X,Y` from the already-proved *point-mass* (fiber-row)
  identity `∀ d, apply (pointMass d) H = apply (pointMass (f d)) L`; this
  avoids running concrete simplification on `localLift`.  (This is exactly how
  `k1a_riffle_half`, a point-mass identity, becomes the kernel equality
  `rho99Ideal_kernel = membership ; localLift`, §3.2.) -/
theorem kernelOfFiberRows {X Y : Type*} (H : FiniteKernel X X)
    (f : X → Y) (L : FiniteKernel Y X)
    (h : ∀ d, FiniteKernel.apply (Dist.pointMass d) H =
      FiniteKernel.apply (Dist.pointMass (f d)) L) :
    H = FiniteKernel.comp (FiniteKernel.deterministic f) L := by
  funext d
  calc
    H d = FiniteKernel.apply (Dist.pointMass d) H :=
      (FiniteKernel.apply_pointMass d H).symm
    _ = FiniteKernel.apply (Dist.pointMass (f d)) L := h d
    _ = (FiniteKernel.comp (FiniteKernel.deterministic f) L) d := rfl

/-- Two pushforwards of the same law through composed maps are equal whenever
the composed maps agree pointwise:
  `(u.map s).map f = u.map g`  from  `∀ c, f (s c) = g c`.
  Just `map_map` plus function extensionality; no mass computation.
  (§3.3: flatten `swapLaw.map (fun p => act p d)`, then project membership.) -/
theorem mapMapOfPointwise {C X Y : Type*} (u : Dist C) (s : C → X)
    (f : X → Y) (g : C → Y) (h : ∀ c, f (s c) = g c) :
    (u.map s).map f = u.map g := by
  rw [Convexity.StdSimplex.map_map]
  exact congrArg (fun v : C → Y => u.map v) (funext h)

/-- The K1 *fusion*: from `H = M ; L` (ideal local = membership-then-lift) and
`K ; M = E` (literal swap kernel projected = exchange-membership kernel), the
swap-then-ideal round equals the exchange-then-lift kernel:
  `K ; H = E ; L`.
  Pure associativity + congruence at abstract types; no concrete 99 reduction.
  (§3.4 — the core of K1.  `rawExchange = E ; L` by definition, so the extra
  perfect-local reset is redundant.) -/
theorem fuseSwapLocal {X Y : Type*} (K H : FiniteKernel X X)
    (M E : FiniteKernel X Y) (L : FiniteKernel Y X)
    (hH : H = FiniteKernel.comp M L)
    (hK : FiniteKernel.comp K M = E) :
    FiniteKernel.comp K H = FiniteKernel.comp E L := by
  calc
    _ = FiniteKernel.comp K (FiniteKernel.comp M L) :=
      congrArg (FiniteKernel.comp K) hH
    _ = FiniteKernel.comp (FiniteKernel.comp K M) L :=
      (FiniteKernel.comp_assoc K M L).symm
    _ = _ := congrArg (fun T => FiniteKernel.comp T L) hK

end Gate6K1Direct
