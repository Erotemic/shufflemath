import Shufflemath.CommanderMembershipOrbits
import Shufflemath.CommanderPermutation
import Shufflemath.CommanderFiberCount
import Mathlib.Tactic

namespace Shufflemath
open CommanderPermutation

-- WIP (47am): leftOriginalCount_conjugate — `leftOriginalCount (d.trans g) = leftOriginalCount d`
-- for g preserving leftOrigSet.  STRATEGY (all pieces identified, proof ~90% assembled):
--
--   set S := (Finset.univ : Finset (Fin 50))
--   set P : Fin 99 → Prop := fun x => (d x).val < 50          -- "card d x is originally-left"
--
--   (0) hImg : S.image leftPosition = leftOrigSet.  (≡ existing leftOrigSet_eq_image; the
--       backward witness is the one Fin-equality that needs care:)
--         intro h; refine ⟨⟨x.val, h⟩, ?_, ?_⟩; · simp only [S, Finset.mem_univ]
--         · apply Fin.ext; simp only [leftPosition]     -- works (see leftPosition_injective)
--
--   (1) hLHS : leftOriginalCount d = (leftOrigSet.filter P).card.
--         unfold leftOriginalCount  -- LHS = (Finset.univ.filter (P ∘ leftPosition) S).card
--         reindex: (Finset.filter (P ∘ leftPosition) S).card
--                 = (Finset.image leftPosition (Finset.filter (P ∘ leftPosition) S)).card  [←card_image_of_injective _ leftPosition_injective]
--                 = (Finset.filter P (Finset.image leftPosition S)).card  [←filter_image]
--                 = (Finset.filter P leftOrigSet).card  [hImg]
--
--   (2) hRHS : leftOriginalCount (d.trans g) = ((leftOrigSet.image g).filter P).card.
--         unfold leftOriginalCount; simp only [Equiv.trans_apply]
--         reindex via (g ∘ leftPosition): image_comp → (S.image leftPosition).image g → hImg → (leftOrigSet.image g)
--
--   (3) final: (leftOrigSet.image g).filter P = leftOrigSet.filter P  via
--               rw [←filter_image, ←card_image_of_injective _ g.injective, filter_image, hgL]
--
--  *** KEY API CAVEAT (the actual blocker) ***
--   Finset.filter (p) (s)  and  Finset.image (f) (s)  are FUNCTION-FIRST (f/p first, Finset 2nd)
--   in this Mathlib.  The theorems are stated in DOT notation:
--     filter_image : (s.image f).filter p = (s.filter fun a => p (f a)).image f
--     image_comp   : s.image (g ∘ f) = (s.image f).image g
--     card_image_of_injective (s) (H : Injective f) : #(s.image f) = #s
--   BUT `Finset.univ.filter p` (as in the leftOriginalCount def) elaborates/reduces to a
--   SET-BUILDER  #{i | p i}, so a naive `change` to the `Finset.filter (P ∘ f) S` form does not
--   fire ("not definitionally equal").  Next session: either (a) prove the reindexing in the
--   set-builder / `Finset.card_congr` idiom, or (b) `dsimp`/`change` step-by-step (unfolding
--   `leftOriginalCount` and the `P` def explicitly) to bridge #{i | p i} ↔ Finset.filter p S,
--   OR (c) avoid it entirely by proving hLHS/hRHS as `# {x ∈ leftOrigSet | P x}` set-card
--   equalities and using Finset.card_congr + leftOrigSet_eq_image.  (c) is cleanest.
--
--   hImg forward direction is done (rintro ⟨p,_,hpx⟩; have hx1 := by rw [←hpx,leftPosition]; exact hx1.symm ▸ p.isLt).
--   The Fin equality (backward) is DONE (apply Fin.ext; simp only [leftPosition]).
--   Only the set-builder↔Finset.filter bridging (item 1/2 above) remains.
--
-- If it closes, promote to Shufflemath/CommanderPermutation.lean (or CommanderFiberCount.lean,
-- which owns leftOrigSet) and it unblocks the specific μ_x invariance:
--   μ_x = comp (fiberLaw project project_surjective) rawExchangeMembership x, and the deck-equiv
--   e d = d.trans f preserves project (via project = ⟨leftOriginalCount-1, _⟩ + this lemma), so
--   fiberLaw_invariant_underFiberEquiv + rawExchangeMembership_conjugate give μ_x.map (relabelMembership_equiv f hf) = μ_x.
