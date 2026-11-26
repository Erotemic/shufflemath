module

public import Shufflemath.FiniteDeck.ChangingPiles

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G7: the joint two-position uniform law

The single-card conditional-uniform fact (the card at a fixed position of a
uniform deck is uniform over the card universe, `topCard_uniform_law` in
`ChangingPiles.lean`) has a two-position sibling, the generalization the
gameplay story needs for the top two cards of the deck: the **joint** law of
a fixed pair of positions `(p, q)` under the uniform deck.  For two *distinct*
positions the decks are an ordered pair of *distinct* cards, every distinct
ordered pair has the same mass — the uniform law on the ordered-distinct-pairs
set — so

`Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => (d p, d q))) (c, c') = 1 / (N * (N - 1))`

for `p ≠ q` and `c ≠ c'`.  The diagonal pairs `(c, c)` carry zero mass.

Proof shape (mirroring the single-card law):

1. **`pairPerm`** — the two-card transfer permutation sending `(c, c')` to
   `(c₀, c₁)` (a transcomposition), and **`pairPerm_c`** / **`pairPerm_c'`** —
   its card-image equivariance (`pairPerm c c' c₀ c₁` applied to the decks
   around it moves the pair in lockstep);
2. **`twoPositions_fiber_card`** — the fibers of the pair observation
   (`{d | (d p, d q) = (c, c')}`) for distinct targets are all the same
   cardinality, via the `d ↦ d.trans (pairPerm …)` bijection;
3. **`diag_fiber_empty`** — the diagonal fiber is empty (an injective deck
   cannot put the same card at two positions);
4. **`twoPositions_uniform_law`** — the sum over all pairs is `N!`
   (`FiberDisintegration.sum_fiber_card`), the sum over distinct pairs is
   `N * (N - 1) * K` (`Finset.sum_product'` + the `N - 1`-card erase count),
   so the common fiber cardinality `K` equals `N! / (N * (N - 1))` and the
   pushforward mass is `1 / (N * (N - 1))`.

`topTwoCards_uniform_law` specializes the joint law to the top two deck
positions — the sound conditional-uniform fact for the drawn pair: the deck must
be **uniform**.  A two-position draw from a *nonuniformly ordered* deck is not
uniform in general.
-/

variable {N : Nat}

/-- The two-card transfer permutation: the deck-automorphism that moves the
ordered pair `(c, c')` to `(c₀, c₁)`, composed as a transcomposition through
the card swap — swap `c` to `c₀`, then swap the image of `c'` (under the first
swap) to `c₁`. -/
def pairPerm (c c' c₀ c₁ : Fin N) : Equiv.Perm (Fin N) :=
  (Equiv.swap c c₀).trans (Equiv.swap ((Equiv.swap c c₀) c') c₁)

/-- **Equivariance — the target card moves.**  Applied to the card `c`, the
transcomposition sends `c` to `c₀`. -/
theorem pairPerm_c (c c' c₀ c₁ : Fin N) (hc : c ≠ c') (hc₀ : c₀ ≠ c₁) :
    (pairPerm c c' c₀ c₁) c = c₀ := by
  change (Equiv.swap ((Equiv.swap c c₀) c') c₁) ((Equiv.swap c c₀) c) = c₀
  rw [Equiv.swap_apply_left]
  by_cases h1 : c' = c₀
  · have hs : (Equiv.swap c c₀) c' = c := by
      rw [h1, Equiv.swap_apply_right]
    rw [hs]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact hc (h1.trans h).symm
    · exact hc₀
  · have hs : (Equiv.swap c c₀) c' = c' := by
      apply Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) h1
    rw [hs]
    apply Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) hc₀

/-- **Equivariance — the companion card moves.**  Applied to the card `c'`, the
transcomposition sends `c'` to `c₁`. -/
theorem pairPerm_c' (c c' c₀ c₁ : Fin N) (hc : c ≠ c') (hc₀ : c₀ ≠ c₁) :
    (pairPerm c c' c₀ c₁) c' = c₁ := by
  change (Equiv.swap ((Equiv.swap c c₀) c') c₁) ((Equiv.swap c c₀) c') = c₁
  by_cases h1 : c' = c₀
  · have hs : (Equiv.swap c c₀) c' = c := by
      rw [h1, Equiv.swap_apply_right]
    rw [hs, Equiv.swap_apply_left]
  · have hs : (Equiv.swap c c₀) c' = c' := by
      apply Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) h1
    rw [hs, Equiv.swap_apply_left]

/-- **Equal-fiber cardinality for pairs.**  The fibers of the pair
observation `{d | (d p, d q) = (c, c')}` for distinct target pairs have all the
same cardinality: the `d ↦ d.trans (pairPerm c c' c₀ c₁)` bijection carries
one fiber onto the other. -/
theorem twoPositions_fiber_card (p q : Fin N) (hpq : p ≠ q)
    (c c' c₀ c₁ : Fin N) (hc : c ≠ c') (hc₀ : c₀ ≠ c₁) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = (c, c'))).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = (c₀, c₁))).card := by
  let τ := pairPerm c c' c₀ c₁
  have hind : Function.Injective (fun d : Equiv.Perm (Fin N) => d.trans τ) := by
    intro a b h
    apply Equiv.ext
    intro x
    have hx := congrArg (fun f => f x) h
    rw [Equiv.trans_apply, Equiv.trans_apply] at hx
    exact Equiv.injective τ hx
  have himg : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = (c, c'))).image (fun d => d.trans τ) =
      (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => (d p, d q) = (c₀, c₁)) := by
    ext e2
    constructor
    · intro he2
      rw [Finset.mem_image] at he2
      rcases he2 with ⟨d, hd, hd0⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hd0]
      simp only [Equiv.trans_apply]
      obtain ⟨hp, hq⟩ := Prod.ext_iff.mp hd
      have hpp : d p = c := hp
      have hqq : d q = c' := hq
      rw [hpp, hqq]
      exact Prod.ext (pairPerm_c c c' c₀ c₁ hc hc₀) (pairPerm_c' c c' c₀ c₁ hc hc₀)
    · intro he0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he0
      obtain ⟨hp, hq⟩ := Prod.ext_iff.mp he0
      have hpp : e2 p = c₀ := hp
      have hqq : e2 q = c₁ := hq
      rw [Finset.mem_image]
      refine ⟨e2.trans τ.symm, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [Equiv.trans_apply]
        rw [hpp, hqq]
        have h1 : τ.symm c₀ = c := by
          have hm := Equiv.symm_apply_apply τ c
          rw [pairPerm_c c c' c₀ c₁ hc hc₀] at hm
          exact hm
        have h2 : τ.symm c₁ = c' := by
          have hm := Equiv.symm_apply_apply τ c'
          rw [pairPerm_c' c c' c₀ c₁ hc hc₀] at hm
          exact hm
        exact Prod.ext h1 h2
      · ext x
        simp [Equiv.trans_apply]
  rw [← himg, Finset.card_image_of_injective _ hind]

/-- **The diagonal fiber is empty.**  An injective deck cannot put the same
card at two distinct positions — no deck maps `(d p, d q)` to `(c, c)`. -/
theorem diag_fiber_empty (p q : Fin N) (hpq : p ≠ q) (c : Fin N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = (c, c))) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro d _
  intro h
  obtain ⟨hp, hq⟩ := Prod.ext_iff.mp h
  have hp' : d p = c := hp
  have hq' : d q = c := hq
  have heq : d p = d q := hp'.trans hq'.symm
  exact hpq (Equiv.injective d heq)

/-- **The joint two-position law.**  Under the uniform deck law, the ordered
pair of cards at two distinct positions `(p, q)` is uniform over the ordered
distinct pairs: every `(c, c')` with `c ≠ c'` carries mass `1 / (N * (N - 1))`. -/
theorem twoPositions_uniform_law (N : Nat) (hN : 0 < N) [Nonempty (Equiv.Perm (Fin N))]
    (p q : Fin N) (hpq : p ≠ q) (c c' : Fin N) (hne : c ≠ c') :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map (fun d => (d p, d q))) (c, c') =
      (1 : Rat) / ((N : Rat) * ((N : Rat) - 1)) := by
  have hN2 : 2 ≤ N := by omega
  -- The common fiber cardinality.
  set K := ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => (d p, d q) = (c, c'))).card with hK
  -- The equal-fiber fact for any distinct pair.
  have hEq : ∀ x : Fin N × Fin N, x.1 ≠ x.2 →
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => (d p, d q) = x)).card = K := by
    intro x hx
    exact (twoPositions_fiber_card p q hpq c c' x.1 x.2 hne hx).symm
  -- The sum over all pairs is N!.
  have hsumExact : (∑ x : Fin N × Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = x)).card : Rat) = (Nat.factorial N : Rat) := by
    have h := Shufflemath.FiberDisintegration.sum_fiber_card (fun d : Equiv.Perm (Fin N) => (d p, d q))
    have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [hcard_eq] at h
    exact h
  -- Rewrite the sum over pairs as a sum over distinct pairs of K.
  have hsum : (∑ x : Fin N × Fin N, ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = x)).card : Rat) = (∑ x : Fin N × Fin N, (if x.1 ≠ x.2 then (K : Rat) else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x.1 = x.2
    · rw [show (if x.1 ≠ x.2 then (K : Rat) else 0) = 0 from by simp [hx]]
      have h0 : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => (d p, d q) = x)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro d _
        intro h
        obtain ⟨hp, hq⟩ := Prod.ext_iff.mp h
        have hp' : d p = x.1 := hp
        have hq' : d q = x.2 := hq
        rw [hx.symm] at hq'
        have heq : d p = d q := hp'.trans hq'.symm
        exact hpq (Equiv.injective d heq)
      rw [h0]
      simp
    · rw [ite_eq_left hx]
      exact_mod_cast hEq x hx
  -- The sum over distinct pairs equals N * (N - 1) * K.
  have hsum_alt : (∑ x : Fin N × Fin N, (if x.1 ≠ x.2 then (K : Rat) else 0)) =
      (N : Rat) * ((N : Rat) - 1) * (K : Rat) := by
    have hprod : (∑ x : Fin N × Fin N, (if x.1 ≠ x.2 then (K : Rat) else 0)) =
        ∑ c : Fin N, ∑ c' : Fin N, (if c ≠ c' then (K : Rat) else 0) := by
      rw [← Finset.univ_product_univ]
      exact Finset.sum_product' (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N))
        (fun c c' => if c ≠ c' then (K : Rat) else 0)
    rw [hprod]
    have hsum_card : ∀ c : Fin N, (∑ c' : Fin N, (if c ≠ c' then (K : Rat) else 0)) =
        (K : Rat) * ((N : Rat) - 1) := by
      intro c
      classical
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ : Finset (Fin N)).filter (fun a : Fin N => c ≠ a) =
          (Finset.univ : Finset (Fin N)).erase c := by
        ext a
        simp [ne_comm]
      rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      -- card of {c' | c ≠ c'} = N - 1, cast to Rat
      have hcast : ((N - 1 : Nat) : Rat) = (N : Rat) - 1 := by
        have h1 : 1 ≤ N := by omega
        rw [Nat.cast_sub h1]
        ring
      rw [hcast]
      ring
    rw [Finset.sum_congr rfl (fun c _ => hsum_card c)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  -- Putting it together: N! = N * (N - 1) * K.
  have hfact : (Nat.factorial N : Rat) = (N : Rat) * ((N : Rat) - 1) * (K : Rat) := by
    have h := hsum.symm.trans hsumExact
    rw [hsum_alt] at h
    exact h.symm
  -- The common fiber cardinality is nonzero (the (p,q) diagonal fiber
  -- contains the identity, and all distinct-pair fibers are equal).
  have hpos : 0 < ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d p, d q) = (c, c'))).card := by
    have hex := twoPositions_fiber_card p q hpq p q c c' hpq hne
    have hpos' : 0 < ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => (d p, d q) = (p, q))).card := by
      apply Finset.card_pos.mpr
      refine ⟨Equiv.refl _, ?_⟩
      simp [Equiv.refl]
    rw [hex] at hpos'
    exact hpos'
  have hk0 : (K : Rat) ≠ 0 := by
    have hpos' : 0 < K := hpos
    exact Nat.cast_ne_zero.mpr (by omega)
  -- The mass formula.
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [hcard_eq, hfact, ← hK]
  have hNne : (N : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hKn : (N : Rat) - 1 ≠ 0 := by
    have h2 : 2 ≤ (N : Rat) := by exact_mod_cast hN2
    linarith
  have hKne : (K : Rat) ≠ 0 := hk0
  field_simp [hNne, hKn, hKne]

/-- **The drawn pair is uniform under the uniform deck law.**  The pair of
cards at the top two deck positions (`⟨0, hN⟩`, `⟨1, hN2⟩`) of a uniform deck:
every ordered distinct pair carries mass `1 / (N * (N - 1))` — the top-card
two-position specialization that underlies the two-card draw.  The sound
conditional-uniform hypothesis: the deck must be **uniform**. -/
theorem topTwoCards_uniform_law (N : Nat) (hN : 0 < N) (hN2 : 2 ≤ N)
    [Nonempty (Equiv.Perm (Fin N))] (c c' : Fin N) (hne : c ≠ c') :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
        (fun d => (d ⟨0, hN⟩, d ⟨1, hN2⟩))) (c, c') =
      (1 : Rat) / ((N : Rat) * ((N : Rat) - 1)) :=
  twoPositions_uniform_law N hN ⟨0, hN⟩ ⟨1, hN2⟩ (by simp) c c' hne

/-- **The top two cards of a uniform deck carry zero mass on the diagonal.**
The diagonal pair `(c, c)` at two distinct deck positions is impossible — the
diagonal fiber is empty — so its mass is `0`, which is exactly the gap the
joint law's `1 / (N (N - 1))` formula misses at the diagonal. -/
theorem topTwoCards_diag_mass_zero (N : Nat) (hN : 0 < N) (hN2 : 2 ≤ N)
    [Nonempty (Equiv.Perm (Fin N))] (c : Fin N) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
        (fun d => (d ⟨0, hN⟩, d ⟨1, hN2⟩))) (c, c) = 0 := by
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => (d ⟨0, hN⟩, d ⟨1, hN2⟩) = (c, c))) = ∅ := by
    exact diag_fiber_empty ⟨0, hN⟩ ⟨1, hN2⟩ (by simp) c
  rw [this, Finset.card_empty]
  norm_num

end FiniteDeck
end Shufflemath
