module

public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.GSRPermutationLaw
public import Shufflemath.Gate6F
public import Shufflemath.FiniteDeck.WithinPileOrbit

@[expose] public section

namespace Shufflemath

/-!
## Gate 6 (G6.1) — the deck-level GSR round law and its transport bound

The **deck-level** finite-GSR round law, built from the within-pile machinery.
A physical GSR round on an `N`-card deck split into a left pile of size `m` and a
right pile of size `N - m` relabels the two piles independently by within-pile
permutations and then re-interleaves; the *state-independent position-permutation
law* of that round is exactly the push-forward of the product of the two
within-pile permutation laws through the pile-embedding `FiniteDeck.embed_m`:

* `roundEmbedMap N m` — the deterministic map `(pl, pr) ↦ embed_m N m hm pl pr`,
  embedding a pair of within-pile permutations into a full-deck permutation.
* `rhoRoundFinite N m hm a` — the finite-GSR round law: push the product of the
  two within-pile GSR permutation laws (`PermutationLaw.gsrPermutationLaw`)
  through `roundEmbedMap`.
* `rhoRoundIdeal N m hm a` — the ideal round law: push the product of the two
  within-pile **uniform** laws through the same map.

The headline is a **deck-level transport bound** that reuses the two batch-3
TotalVariation pieces (`tv_map_contraction` and `twoPilePermutationTV_bound`):
because `roundEmbedMap` is a deterministic map, `tv_map_contraction` shows that
applying it cannot raise the total variation, so the deck-level round stays
within the per-pile collision budget of the two-pile permutation laws,

```
Dist.tv (rhoRoundFinite N m) (rhoRoundIdeal N m)
    ≤ choose(m, 2) / a + choose(N - m, 2) / a.
```

`oneRoundDeckTV_le_delta1` instantiates this at the concrete 99-card protocol
(`N = 99`, `m = 50`, `a = 2 ^ 23`) and evaluates the right-hand side to the
per-round collision budget `δ1 = 2401 / 8388608` — the one-round physical-vs-
perfect error budget called for in the Gate 6 plan, now at the **deck level**
(full-deck permutations) rather than at the within-pile permutation level.
-/

/-- The deterministic map embedding a pair of within-pile permutations into a
  full-deck permutation: `roundEmbedMap N m hm (pl, pr) = embed_m N m hm pl pr`. -/
def roundEmbedMap (N m : Nat) (hm : m ≤ N)
    (p : Equiv.Perm (Fin m) × Equiv.Perm (Fin (N - m))) : Equiv.Perm (Fin N) :=
  FiniteDeck.embed_m N m hm p.1 p.2

/-- The finite-GSR round law on `N` decks: push the product of the two within-pile
  GSR permutation laws through the pile-embedding `roundEmbedMap`. -/
noncomputable def rhoRoundFinite (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m) (hRpos : 0 < N - m)
    (a : Nat) (ha : 0 < a) : Dist (Equiv.Perm (Fin N)) :=
  (distProduct (PermutationLaw.gsrPermutationLaw m a ha hLpos)
               (PermutationLaw.gsrPermutationLaw (N - m) a ha hRpos)).map (roundEmbedMap N m hm)

/-- The ideal (uniform) round law: push the product of the two within-pile uniform
  laws through the same embedding. -/
noncomputable def rhoRoundIdeal (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m) (hRpos : 0 < N - m)
    (a : Nat) (ha : 0 < a) : Dist (Equiv.Perm (Fin N)) :=
  (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
               (GSR.uniformDist (Equiv.Perm (Fin (N - m))))).map (roundEmbedMap N m hm)

/-- The deck-level transport bound (Gate 6, G6.1): because `roundEmbedMap` is a
  deterministic map, `tv_map_contraction` shows the deck-level round law stays
  within the per-pile collision budget of the two-pile permutation laws,

```
Dist.tv (rhoRoundFinite N m) (rhoRoundIdeal N m)
    ≤ choose(m, 2) / a + choose(N - m, 2) / a.
```

Composed from `Dist.tv_map_contraction` (batch 3, step 2) applied to
`roundEmbedMap`, and `twoPilePermutationTV_bound` (batch 3, step 3). -/
theorem rhoRoundTransport_le_twoPile (N m : Nat) (hm : m ≤ N) (hLpos : 0 < m)
    (hRpos : 0 < N - m) (a : Nat) (ha : 0 < a) :
    Dist.tv (rhoRoundFinite N m hm hLpos hRpos a ha) (rhoRoundIdeal N m hm hLpos hRpos a ha) ≤
      (m.choose 2 : Rat) / a + ((N - m).choose 2 : Rat) / a := by
  haveI : DecidableEq (Equiv.Perm (Fin N)) := inferInstance
  have hTrans := Dist.tv_map_contraction
      (distProduct (PermutationLaw.gsrPermutationLaw m a ha hLpos)
                   (PermutationLaw.gsrPermutationLaw (N - m) a ha hRpos))
      (distProduct (GSR.uniformDist (Equiv.Perm (Fin m)))
                   (GSR.uniformDist (Equiv.Perm (Fin (N - m)))))
      (roundEmbedMap N m hm)
  have hProd := twoPilePermutationTV_bound N m a a (Nat.lt_of_lt_of_le hLpos hm) hm hLpos hRpos ha ha
  exact le_trans hTrans hProd

/-- The explicit one-round deck-level bound for the concrete 99-card protocol
(`N = 99`, `m = 50`, `a = 2 ^ 23`): the finite-GSR round law is within the
per-round collision budget `δ1 = 2401 / 8388608` of the fully-uniform round law.
This is `rhoRoundTransport_le_twoPile` with the symbolic right-hand side
`choose(50,2)/2^23 + choose(49,2)/2^23` evaluated to the concrete rational
`2401 / 8388608`. -/
theorem oneRoundDeckTV_le_delta1 :
    Dist.tv (rhoRoundFinite 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num))
            (rhoRoundIdeal 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)) ≤
      2401 / 8388608 := by
  have hSym := rhoRoundTransport_le_twoPile 99 50 (by norm_num) (by norm_num) (by norm_num) (2 ^ 23) (by norm_num)
  have hRHS : (Nat.choose 50 2 : Rat) / 8388608 + (Nat.choose 49 2 : Rat) / 8388608 = 2401 / 8388608 := by
    rw [Nat.choose_two_right, Nat.choose_two_right]
    norm_num
  simpa [hRHS] using hSym

end Shufflemath
