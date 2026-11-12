module

public import Shufflemath.GSR
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace GSR

/-!
# Isolated F4.1 proof candidate

This development file is intentionally absent from the default library import
and `dev/verify_next_phase.sh` graph. Compile it independently first:

    lake env lean dev/QwenGSRBridge.lean

After compilation, copy the two lemmas into `Shufflemath/GSR.lean`, rename
them to the intended exported names, and delete this trial file. The existing
`combineVal_pred_eq` and `rangeMap_divmod_eq_nested` are the only substantive
inputs. Do not use `simp [combineLabels, decodeLabel]` (recursive reduction).
-/

/-- A proposition-level iff determines equality of these two Bool predicates.
This deliberately uses `Bool.eq_iff_iff`, avoiding eight cases on beq values. -/
theorem qwen_combinedLabel_bool_bridge {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (c : Fin n) (k : Nat) :
    ((combineLabels ha hb minor major c).val == k) =
      (((major c).val == k / a) && ((minor c).val == k % a)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.beq_eq, Bool.and_eq_true_iff]
  exact combineVal_pred_eq ha hb minor major c k

/-- Product-label stable sorting equals lexicographic stable sorting. -/
theorem qwen_stableBuckets_combine_eq_lex {n a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (minor : Fin n → Fin a) (major : Fin n → Fin b) (deck : List (Fin n)) :
    stableBuckets (a*b) (combineLabels ha hb minor major) deck =
      lexBuckets a b minor major deck := by
  let bucket : Nat × Nat → List (Fin n) :=
    fun p => deck.filter (fun c => ((major c).val == p.1) && ((minor c).val == p.2))
  have hfilter (k : Nat) :
      deck.filter (fun c => (combineLabels ha hb minor major c).val == k) =
        bucket (k / a, k % a) := by
    dsimp only [bucket]
    apply congrArg (fun p : Fin n → Bool => deck.filter p)
    funext c
    exact qwen_combinedLabel_bool_bridge ha hb minor major c k
  have hfun :
      (fun k : Nat => deck.filter (fun c => (combineLabels ha hb minor major c).val == k)) =
        (fun k : Nat => bucket (k / a, k % a)) := by
    funext k
    exact hfilter k
  calc
    stableBuckets (a*b) (combineLabels ha hb minor major) deck =
        (List.range (a*b)).flatMap (fun k => bucket (k/a, k%a)) := by
      unfold stableBuckets
      rw [hfun]
    _ = ((List.range (a*b)).map (fun k => (k/a, k%a))).flatMap bucket := by
      rw [List.flatMap_map]
    _ = ((List.range b).flatMap
          (fun j => (List.range a).map (fun i => (j, i)))).flatMap bucket := by
      rw [rangeMap_divmod_eq_nested a b ha]
    _ = (List.range b).flatMap
          (fun j => (List.range a).flatMap (fun i => bucket (j, i))) := by
      rw [List.flatMap_assoc]
      simp only [List.flatMap_map]
    _ = lexBuckets a b minor major deck := rfl

end GSR
end Shufflemath
end
