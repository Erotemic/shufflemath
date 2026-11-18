module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Shufflemath

/-! WIP (53rd session): the general fiber-sum / double-count identity.
    TARGET: `∑ m ∈ S, #{x : f x = m} = #{x : f x ∈ S}` (fiber-sum = preimage),
    the combinatorial core of the A3 part-(i) inner-sum `rawExchange_membershipCount_mass`.
    NOT YET BUILT — two approaches were tried and both hit Finset-mechanics friction:

    (A) **biUnion / disjoint-union**: `F m = univ.filter (f · = m)`; the fibers over
        distinct m are disjoint, so `∑ (F m).card = (biUnion S F).card`, and
        `biUnion S F = univ.filter (f · ∈ S)`.  Stuck on: the exact `card_biUnion`/
        `sum_card_biUnion` lemma name (not found by grep in Data/Finset/), the
        `Pairwise (fun m h _ => Disjoint (F m) (F (↑h)))` shape, and summing over the
        subtype `↥S` (`∑ (m : ↥S), (F m).card`) rather than over `S : Finset Y`.

    (B) **indicator / sum-swap**: `∑_{m∈S} ∑_x [f x = m] = ∑_x ∑_{m∈S} [f x = m]`
        (Finset.sum_comm) then the inner sum `∑_{m∈S} [f x = m] = [f x ∈ S]`
        (by_cases on `f x ∈ S`; in the pos branch `S.filter (f x = ·) = {f x}`).
        Stuck on: there is NO clean simp lemma for `(s.filter p).card = ∑_{x∈s} [p x]`
        — `Finset.sum_ite` has the split-into-two-sums form, not this.  A clean route
        would prove that small lemma once (`Finset.card_filter_sum`?) and reuse it, or
        use `Fintype.card {x // p x}` + `Fintype.card_bijection` on the explicit
        bijection `{x // f x ∈ S} ≃ {p : S, x // f x = p}` (the fiber product), which is
        the most robust form (no booleans, no biUnion lemma hunting).

    NEXT SESSION: try the **fiber-product equiv** form — it avoids both dead ends:
    `Fintype.card {x // f x ∈ S} = Fintype.card {p : S, x // f x = ↑p}` via the bijection
    `x ↦ (⟨f x, f x ∈ S⟩, x)` / `⟨p, x⟩ ↦ x`, then reduce the RHS to the fiber sum via
    `Fintype.card_subtype` / a product decomposition.  The A3 fiber mass then needs this
    PLUS the subtype-product ↔ `leftChoices ×ˢ rightChoices` equiv (see
    docs/agent_handoff.md "specific next lemma"). -/

end Shufflemath
