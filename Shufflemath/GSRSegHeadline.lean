module

public import Shufflemath.GSRSegFiber
public import Shufflemath.GSRSegMembership
public import Shufflemath.GSRDeckRound
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.FiberDisintegration
public import Shufflemath.GSR
public import Shufflemath.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-!
## Gate 6 batch 5b — scaffolding for `rhoRoundIdeal = localLift segMembership`

The within-pile *ideal* round law `rhoRoundIdeal 99 50 …` is the pushforward of
the product of the two within-pile *uniform* laws through the pile-embedding
`roundEmbedMap`.  The perfect-local kernel `localLift segMembership` is the
uniform measure over the segregated-membership fiber.  These coincide.

This module lands the two **structural bridge lemmas** the headline reduces to:

* `distProduct_uniform_is_uniformProd` — the independent product of two uniform
  laws is the uniform law on the product type.
* `roundEmbedMap_eq_fiberOrbit_val` — for the segregated (identity) start deck,
  `roundEmbedMap N m hm (pl, pr)` equals the value of the fiber-orbit bijection
  `fiberOrbit_equiv N m hm id` at `(pl, pr)`.  This is the exact bridge between
  the GSR `roundEmbedMap` machinery and the `fiberOrbit_equiv` (within-pile
  orbit) machinery: `act_d d pl pr = (embed_m pl pr).trans d`, and for
  `d = Equiv.refl` the trailing `.trans d` is the identity.

**The headline itself** (`rhoRoundIdeal 99 50 … = localLift segMembership`) then
is a direct mass computation on top of these, reduced to three remaining pieces
(all identified, none yet landed here):

1. `roundImage_iff_segMembership (d)`: a deck is a `roundEmbedMap 99 50` image
   iff `membership d = segMembership`.  Forward uses `roundEmbedMap_eq_fiberOrbit_val`
   + the `fiberMap` proof component (the image keeps the start fiber) +
   `leftCards_id_eq_segLeft`; reverse uses `fiberOrbit_surjective 99 50 id` +
   `leftCards_eq_iffMembership`.
2. `roundEmbedMap 99 50` is **injective** in its pair argument (from
   `fiberMap_injective 99 50 id` + `roundEmbedMap_eq_fiberOrbit_val`), so the
   pushforward fiber over a fiber-point is a singleton.
3. `(fiberSet membership segMembership).card = 50!·49!` (the Finset-of-fiber
   cardinality; the subtype version is already `fiberSegMembership_card`).

With these, `mass (rhoRoundIdeal …) d = (if membership d = segMembership then
1/50!/49! else 0) = mass (localLift segMembership) d` (`map_mass_eq_univ_fiber`
+ `localLift_mass`), giving the headline by `Dist.ext`.
-/

open GSR
open FiniteDeck
open Finset
open scoped Nat

/-- The independent product of two uniform laws is the uniform law on the
  product type (each pair gets mass `1/(#A·#B) = 1/#(A×B)`). -/
theorem distProduct_uniform_is_uniformProd {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] :
    distProduct (uniformDist A) (uniformDist B) = uniformDist (A × B) := by
  ext p
  change Dist.mass (distProduct (uniformDist A) (uniformDist B)) p =
    Dist.mass (uniformDist (A × B)) p
  have hLHS : Dist.mass (distProduct (uniformDist A) (uniformDist B)) p =
      (Fintype.card A : Rat)⁻¹ * (Fintype.card B : Rat)⁻¹ := by
    rw [distProduct_mass]
    simp only [Dist.mass, uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  have hRHS : Dist.mass (uniformDist (A × B)) p = (Fintype.card (A × B) : Rat)⁻¹ := by
    simp only [Dist.mass, uniformDist, Dist.ofFun, Finsupp.coe_equivFunOnFinite_symm]
  rw [hLHS, hRHS]
  simp [Fintype.card_prod]
  ring

/-- For the segregated (identity) start deck, the fiber map `fiberMap` — and
  hence the value of the fiber-orbit bijection `fiberOrbit_equiv` — reduces to
  the pile-embedding `roundEmbedMap`: `act_d d pl pr = (embed_m pl pr).trans d`,
  and for `d = Equiv.refl (Fin N)` the trailing `.trans d` is the identity. -/
theorem roundEmbedMap_eq_fiberOrbit_val (N m : Nat) (hm : m ≤ N)
    (pl : Equiv.Perm (Fin m)) (pr : Equiv.Perm (Fin (N - m))) :
    roundEmbedMap N m hm (pl, pr) =
      (fiberOrbit_equiv N m hm (Equiv.refl (Fin N)) (pl, pr)).val := by
  dsimp only [roundEmbedMap, fiberOrbit_equiv, fiberMap, act_d]
  have htr : (embed_m N m hm pl pr).trans (Equiv.refl (Fin N)) = embed_m N m hm pl pr := by
    apply Equiv.ext
    intro x
    simp [Equiv.refl]
  simpa only [htr, Prod.fst, Prod.snd]

/-! **Frame bridge.**  The 99-card frame (`CommanderPermutation`: `leftCards`,
  `leftPosition`, `Deck = Equiv.Perm (Fin 99)`) and the parameterized `FiniteDeck`
  frame (`leftCards N m hm`, `leftPositions N m hm`, `Deck N`) coincide at
  `N = 99, m = 50`: both `leftCards` are the image of the deck over the 50 left
  positions, and `Fin.castLE hm5099 i` and the 99-card `leftPosition i` are both
  `⟨i.val, _⟩ : Fin 99`.  This single definitional bridge is what lets the
  `rhoRoundIdeal = localLift segMembership` headline move between the two frames. -/

/-- The parameterized `FiniteDeck.leftCards` at `N = 99, m = 50` equals the
  99-card `CommanderPermutation.leftCards`. -/
theorem finiteDeck_leftCards_99_50_eq_commander (d : CommanderPermutation.Deck) :
    FiniteDeck.leftCards 99 50 hm5099 d = CommanderPermutation.leftCards d := by
  have hposI (i : Fin 50) : (Fin.castLE hm5099 i : Fin 99) = CommanderPermutation.leftPosition i := by
    dsimp only [CommanderPermutation.leftPosition]
    rfl
  dsimp only [FiniteDeck.leftCards, FiniteDeck.leftPositions, CommanderPermutation.leftCards]
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, hposI]
  constructor
  · rintro ⟨a, ⟨a_1, _, ha⟩, hda⟩
    exact ⟨a_1, True.intro, by simpa [ha] using hda⟩
  · rintro ⟨a, _, hda⟩
    exact ⟨CommanderPermutation.leftPosition a, ⟨⟨a, True.intro, rfl⟩, hda⟩⟩

end Shufflemath
