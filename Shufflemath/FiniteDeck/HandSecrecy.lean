module

public import Shufflemath.FiniteDeck.Fiber
public import Shufflemath.GSR
public import Shufflemath.FiberDisintegration
public import Shufflemath.FiniteDeck.HistogramKernel
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath
namespace FiniteDeck

/-!
# G7: the hand secrecy law

`TwoPositionLaw.lean` proved the joint law of two deck positions — the two-card
"peek" is uniform over ordered distinct pairs.  The batch deal
(`DealBatch.lean`) moves the first `k` deck positions to the hand in one typed
action and proved the marginal card law of the first *remaining* position.
The remaining sound statement a hand can carry — and the roadmap's next T7
step — is:

**The card set of the hand is uniform over the `k`-subsets of the card
universe.**  Whatever the order of the deal, the hand is exactly the k-set of
cards at the first `k` deck positions; under the uniform deck law that k-set
is uniform over the `Nat.choose N k` k-subsets, each carrying mass
`1 / (Nat.choose N k)`.  This is the *hand secrecy* law: the observer who sees
the hand's card set — not the order — has learned nothing beyond "some
`k`-subset".

Proof shape (mirroring `twoPositions_uniform_law`):

1. **`handPositions` / `handSet`** — the first `k` deck positions (as a finset
   of positions) and the card set of the hand (that finset, imaged by the
   deck permutation);
2. **`handSet_card`** — the hand set is a `k`-element subset (injectivity of
   the deck);
3. **`handSet_trans`** — the transcomposition `e ↦ e.trans τ` acts on the hand
   set by `image τ` (the `img_comp` idiom from `Fiber.lean`);
4. **`handSet_fiber_card`** — the fibers of the hand-set observation for every
   `k`-subset are all the same cardinality (the `d ↦ d.trans τ` bijection with
   the `fibTransitive` transcomposition);
5. **`handSet_uniform_law`** — the sum over all finsets is `N!`
   (`FiberDisintegration.sum_fiber_card`); only `k`-subsets contribute
   (empty fibers otherwise), and the `k`-subsets number `Nat.choose N k`, so
   the common fiber cardinality is `N! / Nat.choose N k` and the pushforward
   mass is `1 / Nat.choose N k`.

A `k = 0` (empty hand) or `k = N` (whole hand) is degenerate but sound: the
fiber is the whole deck and the mass formula holds (`Nat.choose N k = 1`).
-/

/-- The first `k` deck positions — `0, 1, …, k - 1` — as a finset of positions,
for `k ≤ N`. -/
def handPositions (N k : Nat) (hk : k ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)

/-- The card set of the hand after a batch deal of the first `k` deck
positions: the cards at those positions.  Positional — the order of the hand
is discarded (that is exactly the secrecy statement). -/
def handSet (N k : Nat) (hk : k ≤ N) (d : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  (handPositions N k hk).image d

/-- The first `k` positions are exactly `k` positions. -/
theorem handPositions_card (N k : Nat) (hk : k ≤ N) :
    (handPositions N k hk).card = k := by
  rw [handPositions, Finset.card_image_of_injective _ (Fin.castLE_injective hk),
    Finset.card_univ, Fintype.card_fin]

/-- The hand set is a `k`-element subset of the card universe. -/
theorem handSet_card (N k : Nat) (hk : k ≤ N) (d : Equiv.Perm (Fin N)) :
    (handSet N k hk d).card = k := by
  rw [handSet, Finset.card_image_of_injective _ (Equiv.injective d), handPositions_card]

/-- Transcomposition acts on the hand set by the permutation: the hand set of
the deck-after-transposition is the hand set of the original deck, imaged by
the permutation. -/
theorem handSet_trans (N k : Nat) (hk : k ≤ N) (d : Equiv.Perm (Fin N))
    (τ : Equiv.Perm (Fin N)) :
    handSet N k hk (d.trans τ) = (handSet N k hk d).image (fun a => τ a) := by
  rw [handSet, handSet]
  exact img_comp N τ d (handPositions N k hk)

/-- **Equal-fiber cardinality for the hand set.**  The fibers of the hand-set
observation for two distinct `k`-subsets are all the same cardinality: the
`d ↦ d.trans τ` bijection (with the `fibTransitive` transcomposition) carries
one fiber onto the other. -/
theorem handSet_fiber_card (N k : Nat) (hk : k ≤ N)
    (S T : Finset (Fin N)) (hS : S.card = k) (hT : T.card = k) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handSet N k hk d = S)).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handSet N k hk d = T)).card := by
  obtain ⟨τ, hTB⟩ := fibTransitive_finset N k hk ⟨S, hS⟩ ⟨T, hT⟩
  have hTB' : S.image (fun a => τ a) = T := hTB
  have hind : Function.Injective (fun d : Equiv.Perm (Fin N) => d.trans τ) := by
    intro a b h
    apply Equiv.ext
    intro x
    have hx := congrArg (fun f => f x) h
    rw [Equiv.trans_apply, Equiv.trans_apply] at hx
    exact Equiv.injective τ hx
  have himg : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handSet N k hk d = S)).image (fun d => d.trans τ) =
      (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => handSet N k hk d = T) := by
    ext e2
    constructor
    · intro he2
      rw [Finset.mem_image] at he2
      obtain ⟨d, hd, hd0⟩ := he2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hd0, handSet_trans]
      rw [hd]
      exact hTB' 
    · intro he0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he0
      rw [Finset.mem_image]
      refine ⟨e2.trans τ.symm, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [handSet_trans]
        rw [he0]
        rw [← hTB']
        exact (img_symm_img N τ S)
      · ext x
        simp [Equiv.trans_apply]
  rw [← himg, Finset.card_image_of_injective _ hind]

/-- **Hand secrecy.**  Under the uniform deck law, the card set of the hand
(after a batch deal of the first `k` deck positions) is uniform over the
`k`-subsets of the card universe: every `k`-subset carries mass
`1 / Nat.choose N k` — the hand-set analog of the joint two-position law. -/
theorem handSet_uniform_law (N : Nat) [Nonempty (Equiv.Perm (Fin N))]
    (k : Nat) (hk : k ≤ N) (S : Finset (Fin N)) (hS : S.card = k) :
    Dist.mass ((GSR.uniformDist (Equiv.Perm (Fin N))).map
      (fun d => handSet N k hk d)) S =
      (1 : Rat) / (Nat.choose N k : Rat) := by
  set K := ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun d => handSet N k hk d = S)).card with hK
  -- The sum over all finsets is the total deck count N!.
  have hsumExact : (∑ S' : Finset (Fin N), ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handSet N k hk d = S')).card) = Nat.factorial N := by
    have h := Shufflemath.FiberDisintegration.sum_fiber_card
      (fun d : Equiv.Perm (Fin N) => handSet N k hk d)
    have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [hcard_eq] at h
    exact_mod_cast h
  -- Non-k-subsets have empty fibers.
  have hEmpty : ∀ S' : Finset (Fin N), S'.card ≠ k →
      ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun d => handSet N k hk d = S')).card = 0 := by
    intro S' hSk'
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hd
    have hcard := congrArg Finset.card hd
    rw [handSet_card N k hk d] at hcard
    exact hSk' hcard.symm
  -- The number of k-subsets of the card universe is Nat.choose N k.
  have hcard_filter : (Finset.univ.filter (fun S' : Finset (Fin N) => S'.card = k)).card =
      Nat.choose N k := by
    have hEq : (Finset.univ.filter (fun S' : Finset (Fin N) => S'.card = k) :
        Finset (Finset (Fin N))) =
        Finset.powersetCard k (Finset.univ : Finset (Fin N)) := by
      ext S'
      simp [Finset.mem_powersetCard, Finset.subset_univ]
    rw [hEq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- The sum over all finsets is the sum over k-subsets of the common K.
  have hsumN : (∑ S' : Finset (Fin N), ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun d => handSet N k hk d = S')).card) = Nat.choose N k * K := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun S' : Finset (Fin N) => S'.card = k)]
    have hNot : ∑ S' ∈ Finset.univ.filter (fun S' : Finset (Fin N) => ¬ (S'.card = k)),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => handSet N k hk d = S')).card = 0 := by
      apply Finset.sum_eq_zero
      intro S' h'
      exact hEmpty S' (Finset.mem_filter.mp h').2
    rw [hNot, add_zero]
    have hPer : ∑ S' ∈ Finset.univ.filter (fun S' : Finset (Fin N) => S'.card = k),
        ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => handSet N k hk d = S')).card =
        ∑ S' ∈ Finset.univ.filter (fun S' : Finset (Fin N) => S'.card = k), K := by
      apply Finset.sum_congr rfl
      intro S' h'
      have hcard' := handSet_fiber_card N k hk S' S (Finset.mem_filter.mp h').2 hS
      have hKK : ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
          (fun d => handSet N k hk d = S)).card = K := hK.symm
      rw [hKK] at hcard'
      exact hcard'
    rw [hPer, Finset.sum_const, hcard_filter]
    ring
  -- N! = choose N k * K — the common fiber cardinality.
  have hfactN : Nat.factorial N = Nat.choose N k * K := hsumExact.symm.trans hsumN
  have hchoose_pos : 0 < Nat.choose N k := Nat.choose_pos hk
  have hKpos : 0 < K := by
    by_contra h
    have hK0 : K = 0 := by omega
    have hzero : Nat.factorial N = 0 := by
      rw [hfactN, hK0, mul_zero]
    have hNfact : 0 < Nat.factorial N := Nat.factorial_pos N
    omega
  -- The mass formula.
  rw [Shufflemath.GenericPairObservation.uniformMap_mass_card]
  have hcard_eq : (Fintype.card (Equiv.Perm (Fin N)) : Rat) = (Nat.factorial N : Rat) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hfactRat : (Nat.factorial N : Rat) = (Nat.choose N k : Rat) * (K : Rat) := by
    exact_mod_cast hfactN
  have hK_ne : (K : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  have hchoose_ne : (Nat.choose N k : Rat) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  rw [hcard_eq, hfactRat, ← hK]
  field_simp [hchoose_ne, hK_ne]

end FiniteDeck
end Shufflemath
