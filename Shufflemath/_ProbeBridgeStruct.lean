module

public import Shufflemath.GSRSegMembership
public import Shufflemath.GSRDeckBridge
public import Shufflemath.FiberDisintegration
public import Shufflemath.CommanderFiberCount
public import Shufflemath.CommanderFiberMembership
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.CommanderPermutation
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.Finite
public import Shufflemath.GSR
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

open Finset
open scoped Nat
open CommanderPermutation
open CommanderMembershipKernels

/-- `Fin.castLE` is proof-term-independent: the two `Fin.castLE` embeddings built from
  different proofs `m ≤ N` are the same function (each maps `i` to the `Fin N` with
  value `i.val`). This dissolves the proof-term friction between the `hm`- and
  `hm5099`-instantiated left-position / left-set definitions. -/
theorem castLE_fun_indep (N m : Nat) (h1 h2 : m ≤ N) :
    (Fin.castLE h1 : Fin m → Fin N) = (Fin.castLE h2) := by
  funext i
  apply Fin.ext
  simp only [Fin.val_castLE]

/-- The left-position finset `leftPositions N m` is independent of the proof term. -/
theorem leftPositions_indep (N m : Nat) (h1 h2 : m ≤ N) :
    FiniteDeck.leftPositions N m h1 = FiniteDeck.leftPositions N m h2 := by
  dsimp only [FiniteDeck.leftPositions]

/-- The within-pile `segregatedLeftSet` (built from `hm`) and the GSR-seg
  `segLeft` (built from `hm5099`) are the same finset `{0..49}`. -/
theorem segregatedLeftSet_eq_segLeft :
    segregatedLeftSet = segLeft := by
  dsimp only [segregatedLeftSet, segLeft, FiniteDeck.leftPositions]

/-- The two `leftCards` families — the specialized 99/50 `CommanderPermutation.leftCards`
  and the parameterized `FiniteDeck.leftCards` — agree on a 99-card deck: both reduce
  to `(univ : Finset (Fin 50)).image (fun i => d (Fin.castLE hm i))`. -/
theorem leftCards_reconcile (d : Deck) :
    leftCards d = FiniteDeck.leftCards 99 50 hm d := by
  have hLP : (leftPosition : Fin 50 → Fin 99) = (Fin.castLE hm) := by
    funext i
    apply Fin.ext
    simp only [leftPosition, Fin.val_castLE]
  have hA : leftCards d = (Finset.univ : Finset (Fin 50)).image
      (fun i : Fin 50 => d (Fin.castLE hm i)) := by
    unfold leftCards
    rw [hLP]
  have hB : FiniteDeck.leftCards 99 50 hm d = (Finset.univ : Finset (Fin 50)).image
      (fun i : Fin 50 => d (Fin.castLE hm i)) := by
    unfold FiniteDeck.leftCards FiniteDeck.leftPositions
    rw [Finset.image_image]
    simpa only [Function.comp_apply]
  rw [hA, hB]

/-- The image of the within-pile embedding has the segregated fiber's cardinality
  `50! · 49!`: the embedding is injective in the within-pile permutations, so its image
  has the cardinality of the source product type. -/
theorem image_roundEmbed_card :
    Finset.card ((Finset.univ : Finset (Equiv.Perm (Fin 50) × Equiv.Perm (Fin 49))).image
      (roundEmbedMap 99 50 hm)) = Nat.factorial 50 * Nat.factorial 49 := by
  have hinj : Function.Injective (roundEmbedMap 99 50 hm) := by
    unfold roundEmbedMap
    exact embed_m_injective 99 50 hm
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod]
  simp only [Fintype.card_perm, Fintype.card_fin]

-- NEXT STEP (deferred): `image_roundEmbed_eq_fiberSet` — the finset equality
-- `(univ).image (roundEmbedMap 99 50 hm) = FiberDisintegration.fiberSet membership
-- segMembership` (the structural core of the within-pile↔GSR-seg bridge). All of its
-- component lemmas above are proved (the reconciliation + the two cardinalities, so the
-- equality reduces to a subset argument), but the subset proof `image ⊆ fiberSet`
-- triggers a genuine Lean elaboration wall: the `rw` of `roundEmbedMap`/`embed_m` terms
-- (an `Equiv (Fin 99)` built from two `Perm`s) hits a non-terminating WHNF that
-- `set_option maxRecDepth` does not bound (tried up to 10000). This is an elaborator
-- limitation on the specific `embed_m` definition, not a logical gap — the math is
-- complete. Next: reformulate the subset step to avoid unfolding `roundEmbedMap`
-- (e.g. via `Finset.image_ofInjective`-style characterisation or a `Finset.ext` on the
-- decsSubtype), or prove the headline
-- `rhoRoundIdeal 99 50 (univ).toProbMass = localLift segMembership` by the per-element
-- mass route once the support characterisation is available.

end Shufflemath
