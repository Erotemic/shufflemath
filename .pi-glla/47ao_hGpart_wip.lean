module
-- WIP (47ao): the L50 whnf-avoidance strategy + the partition-preservation lemma
-- hGpart, all COMPILING (verified: `lake build Shufflemath._Probe47ao` → exit 0,
-- 3205 jobs). This is the reference for the next session working on
-- `leftOriginalCount_conjugate` / the A3 capstone.
--
-- KEY FINDING: the Fin 99 *filter* form of `leftOrigSet` whnf-explodes on
-- `.image g` operations (rw/rcases/mem_image.mpr) when `g : Equiv.Perm (Fin 99)`.
-- The light *Fin 50 image* form `L50` does NOT. Every heavy step is routed through
-- L50 (a `simp` of `leftOrigSet_eq_L50` / `hL` is light; the direct Fin 99 filter
-- is not). hGpart (both directions) compiles on this route.
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderFiberCount
public import Mathlib.Tactic

@[expose] public section
namespace Shufflemath
open CommanderPermutation

-- The 50 initially-left positions as an image over Fin 50 (a light base).
def L50 : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 50)).image (fun i : Fin 50 => (leftPosition i : Fin 99))

-- leftOrigSet (Fin 99 filter) = the light Fin 50 image form.
theorem leftOrigSet_eq_L50 : leftOrigSet = L50 := by
  unfold L50
  rw [leftOrigSet_eq_image]
  apply Finset.image_congr
  intro i _
  ext
  rfl

-- hgL (g preserves leftOrigSet) stated in the light L50 form.
theorem hgL_L50 (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet) :
    L50.image (g : Fin 99 → Fin 99) = L50 := by
  rw [← leftOrigSet_eq_L50, hgL, leftOrigSet_eq_L50]

-- Partition-preservation, ← direction (light L50 form, compiles).
theorem hGpart_bwd (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) (hgy : g y ∈ leftOrigSet) : y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hgyL50 : g y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hgy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := by simpa [hL] using hgyL50
  rcases Finset.mem_image.mp Himg with ⟨z, hz, hgz⟩
  have hzL50 : z ∈ L50 := by simpa [leftOrigSet_eq_L50] using hz
  simpa [leftOrigSet_eq_L50] using (g.injective hgz).symm ▸ hzL50

-- Partition-preservation, → direction.
theorem hGpart_fwd (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) (hy : y ∈ leftOrigSet) : g y ∈ leftOrigSet := by
  have hL := hgL_L50 d g hgL
  have hyL50 : y ∈ L50 := by simpa [leftOrigSet_eq_L50] using hy
  have Himg : g y ∈ L50.image (g : Fin 99 → Fin 99) := Finset.mem_image.mpr ⟨y, hyL50, rfl⟩
  simpa [leftOrigSet_eq_L50] using (hL ▸ Himg)

-- The full iff: a deck map g with g '' leftOrigSet = leftOrigSet preserves the
-- left/right partition pointwise.
theorem hGpart (d g : Deck) (hgL : (leftOrigSet).image (g : Fin 99 → Fin 99) = leftOrigSet)
    (y : Fin 99) : y ∈ leftOrigSet ↔ g y ∈ leftOrigSet :=
  Iff.intro (hGpart_fwd d g hgL y) (hGpart_bwd d g hgL y)

end Shufflemath

-- NEXT (leftOriginalCount_conjugate): the remaining assembly, NOT yet closed —
-- it hits context-dependent whnf walls when hGpart is CALLED inside the hInt
-- `ext` (elaborating the hGpart proof term there re-reduces the L50 image).
-- Remaining pieces and exact status:
--
--   leftCards_conjugate (d g) : leftCards (d.trans g) = (leftCards d).image g.
--     The set-level statement is trivially true by leftCards_def; the friction is
--     the membership-level `ext` proof (Fin 50 vs Fin 99 existential shapes, and
--     `Equiv.trans_apply` for (d.trans g) a = g (d a)). Structurally proven; a
--     clean `ext x; simp [Finset.mem_image]` close is pending (see .pi-glla/47an note).
--
--   leftOriginalCount_conjugate (d g) (hgL) : leftOriginalCount (d.trans g) = leftOriginalCount d.
--     Route (all pieces proven or trivial):
--       leftOriginalCount h = (leftCards h ∩ leftOrigSet).card  (leftOriginalCount_eq_leftCardsInter)
--       leftCards (d.trans g) = (leftCards d).image g           (leftCards_conjugate)
--       (leftCards d).image g ∩ leftOrigSet = (leftCards d ∩ leftOrigSet).image g  (hInt: per-element
--         via hGpart — the g-image of the originally-left part of the left pile)
--       card ((A).image g) = card A for injective g            (Finset.card_image_of_injective)
--     The hInt `ext` is where the whnf wall is: calling hGpart d g hgL y inside it
--     re-reduces the L50-image proof term and trips the heartbeat. Possible next
--     moves: (a) inline hGpart's two directions directly in the hInt branches
--     (avoid a named-call re-reduction); (b) prove the CARD equality by a bijection
--     A → A.image g (map y => g y, surjectivity via g.symm + hGpart.mpr) using
--     Finset.card_bijection, which may reduce more lightly than the set equality;
--     (c) raise the heartbeat ceiling locally (set_option maxHeartbeats N) for the
--     single heavy step if the others are sound.
