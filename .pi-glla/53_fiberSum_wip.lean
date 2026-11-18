module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Shufflemath

/-! WIP (54th session) — the general fiber-sum / double-count identity.
    TARGET: `∑ m ∈ S, #{x : f x = m} = #{x : f x ∈ S}` (fiber-sum = preimage),
    the combinatorial core of the A3 part-(i) inner-sum `rawExchange_membershipCount_mass`.
    (53rd session: approaches (A) biUnion and (B) indicator/sum_ite were dead ends,
     see git log; the fiber-product-sigma form was identified as most robust but its
     "sigma card = sum of fiber cards" step was thought to lack a mathlib lemma.)

    ============================ 54TH-SESSION FINDINGS ============================

    1. **KEY DISCOVERY — the missing lemma DOES exist: `Fintype.card_sigma`.**
       It is a `@[simp]` lemma in `Data/Fintype/Defs.lean:161` (NOT `Basic.lean`, which
       is why the 53rd-session grep missed it):
         `Fintype.card_sigma {ι} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)] :
              Fintype.card (Σ i, α i) = ∑ i, Fintype.card (α i)`
       Also confirmed present:
         * `Finset.card_subtype` (`Data/Finset/Basic.lean:275`): `#(s.subtype p) = #(s.filter p)`.
         * `Fintype.card_subtype_eq` / `_eq'` / `_true` (`Data/Fintype/Basic.lean:160,164,209`).
         * `Finset.card_biUnion` (used at `Data/Finset/Slice.lean:152` and `Powerset.lean:334`).
         * `Finset.sum_subtype_eq_sum_filter` (exists; grep it in `Data/Finset/`).
       ⇒ The "sigma card = sum of fiber cards" step is just `rw [Fintype.card_sigma]`.

    2. **State of the fiber-product-`Equiv` route (cleanest statement):**
         `Fintype.card {x : X // f x ∈ S} = ∑ (m : ↥S), Fintype.card {x : X // f x = m.val}`
       via the `Equiv` `toF / invF`:
         `toF ⟨x, hx⟩   = ⟨⟨f x, hx⟩, ⟨x, rfl⟩⟩`
         `invF ⟨m, x⟩   = ⟨x.1, by rw [x.2]; exact m.property⟩`   (x.2 : f (x.1) = m.val)
       Then `Fintype.card_congr` + `rw [Fintype.card_sigma]`.
       - `left_inv` is **definitional `rfl`** (value is `x`, proof is `hx`) — WORKS.
       - injectivity (for the `Equiv.ofBijective` variant) works via
         `congrArg (fun t => t.2.1) hab` (gives `x = y`) + `Subtype.ext rfl` — WORKS.
       - **BLOCKER (the ONLY remaining error): the `right_inv` second component.**
         `Sigma.ext (Subtype.ext x.2) (Subtype.ext rfl)` fails: the 2nd argument is
         expected to have type
             `(toF (invF ⟨m, x⟩)).snd ≍ (⟨m, x⟩).snd`
         i.e. an **`HEq` (≍)**, not an `Eq`, because the two fiber types
         `{y // f y = f (x.1)}` and `{y // f y = m.val}` are only *propositionally*
         equal (via `x.2 : f (x.1) = m.val`), not definitionally. `Subtype.ext rfl`
         produces an `Eq`, which does not typecheck against the `HEq`. The first
         sigma component is only propositionally equal (`⟨f (x.1), p⟩ = m` via
         `Subtype.ext x.2`), which is exactly what forces the non-trivial transport
         (HEq) on the second component.

    3. **NEXT STEPS (in preference order):**
       (a) **Fix the HEq on the `right_inv` second component.** After `dsimp only [toF, invF]`,
           the goal is `⟨⟨f (x.1), p⟩, ⟨x.1, rfl⟩⟩ = ⟨m, x⟩` with `x = ⟨x.1, x.2⟩`.
           The second-component `HEq` `⟨x.1, rfl⟩ ≍ ⟨x.1, x.2⟩` has the SAME value `x.1`
           on both sides and both proofs are Props. To make it an `Eq`: first rewrite
           the fiber TYPE so both sides live in `{y // f y = m.val}` (use `x.2` to
           transport `⟨x.1, rfl⟩` into that type — it becomes `⟨x.1, x.2⟩`), THEN it is
           `Subtype.ext rfl` / `rfl`. Concretely try:
             `fun ⟨m, x⟩ => by change _ = _; rw [Subtype.ext_iff]; subst ...; simp`
           or build the `HEq` explicitly. If this resists, go to (b).
       (b) **`Finset.card_biUnion` route — NO sigma, NO HEq at all (RECOMMENDED).**
           Let `F m := (Finset.univ : Finset X).filter (fun x => f x = m)`. The fibers over
           distinct `m` are pairwise disjoint, and `biUnion S F = univ.filter (f · ∈ S)`.
           Then:  `∑ m ∈ S, (F m).card = (biUnion S F).card`  by `Finset.card_biUnion`
           (find its exact signature: `grep -rn "theorem.*card_biUnion" .lake/packages/mathlib/Mathlib/Data/Finset/`).
           and `(biUnion S F).card = (univ.filter (f · ∈ S)).card = #{x // f x ∈ S}`.
           This is a purely non-dependent `Finset` argument — no `Equiv`, no transport, no HEq.
       (c) **`Finset.sum_subtype_eq_sum_filter`** — if any step needs the `∑ (m : ↥S)` ↔
           `∑ m ∈ S` bridge (the subtype-vs-Finset reindex).
       (d) **Once the general double-count is proven** (in whichever form), adapt it to the
           concrete A3 statement `rawExchange_membershipCount_mass`: there
           `f : exchangeChoice → Membership` is `F`, `S` is the membership-count fiber
           `{m | membershipCount m = c}`, and each fiber `#{x : F x = m}` is a single point
           mass (already proved `rawExchangeMembership_pointMass` in 53rd session).

    ============================ RESUME POINTER ============================
    The exact last-compiling probe (54th session, 6 attempts) is this file's git history;
    the last form used `refine ⟨toF, invF, fun _ => rfl, fun ⟨m, x⟩ => Sigma.ext (Subtype.ext x.2) (Subtype.ext rfl)⟩`
    and failed ONLY on the `Subtype.ext rfl` (needs to be an HEq, see §2). -/

end Shufflemath
