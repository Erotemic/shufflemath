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

    NEXT SESSION: the **fiber-product sigma** form is the most robust, but its
    crux is one lemma that has NO mathlib name I found:
      * `hCard`: `{x // f x ∈ S} ≃ {t : ↥S × X // f t.2 = t.1.val}` (the bijection
        `x ↦ (⟨f x, f x ∈ S⟩, x)` / `⟨t, ht⟩ ↦ (t.2, by rwa [← ht])`), then
        `Fintype.card_congr hCard` (NOT `Fintype.card_bijection` — that name doesn't
        exist; `Fintype.card_equiv` is about the card of the equivalence *group*,
        not card-preservation-by-equiv).  The structure-literal `{p : ↥S, x : X // …}`
        does NOT parse (comma after a `↥S` field); use the **product-subtype**
        `{t : ↥S × X // f t.2 = t.1.val}` (single field, valid).
      * `hSum` (the real double-count): `Fintype.card {t : ↥S × X // f t.2 = t.1.val}
        = ∑ m ∈ S, Fintype.card {x // f x = m}`.  The product-subtype ≃ the sigma
        `Σ (p : ↥S), {x // f x = p.val}`, and that sigma's card is the sum of the fiber
        cards — but **`Fintype.card_sigma` / `card_subtype` are NOT in
        Data/Fintype/Basic.lean** (grep came up empty).  So the sigma-card-as-sum is
        either a simp-normalization of the Fintype instance (try `simp [Fintype.card]`
        on `Σ (p : ↥S), {x // f x = p.val}` and see if it unfolds to the sum) or must
        be proved by `Fintype.card_bijection`-style induction on the sigma.  After that,
        `∑ p : ↥S, … = ∑ m ∈ S, …` via `Finset.sum_subtype` (`[DecidableEq Y]` and
        `Finset.mem_coe` needed).
    Both (A) biUnion and (B) indicator/`sum_ite` are dead ends (see above). -/

end Shufflemath
