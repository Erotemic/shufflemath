module
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Shufflemath.UniformFiber
public import Shufflemath.Finite
public import Mathlib.Tactic

-- `uniformOrbitLaw` registers an explicit `Nonempty` instance for `d`'s
-- membership fiber (witnessed by `d` itself); that is a genuine instance, so the
-- haveILetI style linter is a false positive here.
set_option linter.style.haveILetI false

@[expose] public section

namespace Shufflemath

open FiniteDeck
open GSR

/-!
## A uniform orbit is a fiber law (Gate 6, Nov 23 plan §2)

Pushing the **uniform law on the within-pile orbit group** through the orbit
action gives exactly the **`fiberLaw` of the membership observation** — the
conditionally-uniform law on `d`'s left-pile fiber. This is the reusable
"orbit = fiber law" identity the Gate 6 headline instantiates.

The proof composes two previously-proved building blocks:

- `GSR.map_bijective_uniformDist`: a uniform law pushed through the orbit
  equiv `membershipOrbit_equiv` becomes the uniform law on the membership fiber;
- `Shufflemath.uniformFiberMapEqFiberLaw`: the uniform law on that fiber pushed
  through `Subtype.val` is the `fiberLaw` of the membership observation.

The only new content here is the equiv itself: the within-pile orbit group is in
bijection with `d`'s membership fiber, via `act_d` (which preserves the
membership). `Finsupp.mapDomain` / `StdSimplex.map_map` carry the composition,
with no `99!` / Fintype unrolling — the fiber is nonempty (witnessed by `d`).
-/

/-- The orbit group: independent left/right within-pile permutations. -/
abbrev MOrbit (N m : Nat) :=
  Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m))

/-- Orbit → membership-fiber forward map: `p` acts on `d` via `act_d`, which
  preserves the membership (left pile). -/
def membershipOrbit_fwd (N m : Nat) (hm : m ≤ N) (d : Deck N) (p : MOrbit N m) :
    { e : Deck N // membership N m hm e = membership N m hm d } :=
  ⟨act_d N m hm d p.1 p.2, act_d_preservesMembership N m hm d p.1 p.2⟩

/-- The forward map is injective: two orbit elements acting on `d` give the same
  deck iff they are the same pair (`act_d_injective`). -/
theorem mof_injective (N m : Nat) (hm : m ≤ N) (d : Deck N) :
    Function.Injective (membershipOrbit_fwd N m hm d) := by
  intro p q h
  have hval : act_d N m hm d p.1 p.2 = act_d N m hm d q.1 q.2 := by
    have := congrArg (fun s : {e : Deck N // _} => s.val) h
    dsimp only [membershipOrbit_fwd, act_d] at this
    exact this
  exact (act_d_injective N m hm d) hval

/-- The forward map is surjective: every deck in `d`'s membership fiber is
  `act_d d p.1 p.2` for some orbit element `p` (reuses `fiberOrbit_surjective`,
  since membership is determined by the left cards). -/
theorem mof_surjective (N m : Nat) (hm : m ≤ N) (d : Deck N) :
    Function.Surjective (membershipOrbit_fwd N m hm d) := by
  intro e
  have hlc : leftCards N m hm e.val = leftCards N m hm d :=
    (leftCards_eq_iffMembership N m hm e.val d).2 e.property
  obtain ⟨p, hp⟩ := fiberOrbit_surjective N m hm d ⟨e.val, hlc⟩
  refine' ⟨p, _⟩
  apply Subtype.ext
  dsimp only [membershipOrbit_fwd]
  have hval : (fiberMap N m hm d p).val = e.val := by
    have := congrArg (fun s : {e : Deck N // _} => s.val) hp
    dsimp only [fiberMap] at this
    exact this
  dsimp only [fiberMap] at hval
  exact hval

/-- The within-pile orbit group is in bijection with `d`'s membership fiber.
  Kept as a *transparent* term (an `Equiv.ofBijective` of the forward map) so that
  `(membershipOrbit_equiv _ _ _ _).toFun` reduces to `membershipOrbit_fwd`. -/
noncomputable def membershipOrbit_equiv (N m : Nat) (hm : m ≤ N) (d : Deck N) :
    MOrbit N m ≃ { e : Deck N // membership N m hm e = membership N m hm d } :=
  Equiv.ofBijective (membershipOrbit_fwd N m hm d)
    ⟨mof_injective N m hm d, mof_surjective N m hm d⟩

/-- **A uniform orbit is a fiber law.** Pushing the uniform law on the
  within-pile orbit group `MOrbit N m` through the orbit action (each orbit
  element `h` acting on `d` via `embed_m`) gives the `fiberLaw` of the
  membership observation at `d`'s membership — the conditionally-uniform law on
  `d`'s left-pile fiber. Assembled from `map_bijective_uniformDist` (uniform is
  invariant under the orbit equiv) and `uniformFiberMapEqFiberLaw` (the fiber
  uniform pushed through `Subtype.val` is the `fiberLaw`). -/
theorem uniformOrbitLaw (N m : Nat) (hm : m ≤ N) (d : Deck N) :
    ((uniformDist (MOrbit N m)).map (fun h => act (embed_m N m hm h.1 h.2) d))
    = FiberDisintegration.fiberLaw (membership N m hm) (membership_surjective N m hm)
        (membership N m hm d) := by
  classical
  let e := membershipOrbit_equiv N m hm d
  -- the membership fiber is inhabited by `d` itself (needed for the equiv-map step)
  letI : Nonempty {e : Deck N // membership N m hm e = membership N m hm d} :=
    ⟨⟨d, rfl⟩⟩
  -- (1) the LHS forward map h ↦ act (embed_m ... h.1 h.2) d equals (e h).val
  have hLHSmap : (fun h : MOrbit N m => act (embed_m N m hm h.1 h.2) d)
               = fun h => (e h).val := by
    funext h
    dsimp only [e, membershipOrbit_equiv, Equiv.ofBijective, membershipOrbit_fwd, act_d, act]
    rfl
  rw [hLHSmap]
  -- (2) composition: (uniformDist H).map (fun x => (e x).val)
  --          = ((uniformDist H).map e).map Subtype.val
  rw [← Convexity.StdSimplex.map_map (uniformDist (MOrbit N m)) e Subtype.val]
  -- (3) (uniformDist H).map e = uniformDist (membership fiber)   [map invariance under equiv]
  rw [map_bijective_uniformDist e]
  -- (4) (uniformDist (membership fiber)).map Subtype.val = fiberLaw (membership ...) (membership d)
  exact (Shufflemath.uniformFiberMapEqFiberLaw (α := Membership N m) (β := Deck N)
      (observe := membership N m hm)
      (hsurj := membership_surjective N m hm) (x := membership N m hm d))

end Shufflemath
