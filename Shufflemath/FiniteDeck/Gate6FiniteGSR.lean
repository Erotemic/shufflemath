module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Shufflemath

open Finset

/-!
## Gate 6 — the concrete 99-card finite-GSR protocol: the exact target bound

**Target theorem** (deep-structural-hints §8; lean_plan "Next after F5 (b)"):

```
  TV (FiniteKernel.run finiteRound 3 (Dist.pointMass d0)) (GSR.uniformDist Deck)
    ≤ q3 + δ3  <  1/1000
```

where

* `finiteRound` is one physical round over the 50/49 split — a uniform choice
  of 25 positions in each pile + a fixed pairing swap, then **23 independent
  binary inverse-GSR riffles per pile** — defined as a deck-valued kernel with
  **no** perfect reset hidden inside it;
* `d0` is any ordered deck whose left 50 positions hold the 50 distinguished
  cards;
* `q3` is the exact **ideal** three-round TV constant;
* `δ3` is the three-round finite-riffle **collision** budget.

This module pins those exact rational constants and proves the headline
inequality the whole theorem reduces to — the §8 "exact inequality is a
rational arithmetic goal, not a stochastic proof."  It is intentionally
self-contained (pure `Rat` arithmetic, no heavy-module imports), so it is the
first committed increment of Gate 6; the construction and the per-round
collision bound land as follow-ups in the same module:

1. **`q3`** — the proven three-round physical-perfect-exchange TV
   (`CommanderFullDeckDisintegration.three_physical_perfect_exchanges_uniform_unconditional`
   = `172379… / 669183…`).
2. **`δ1`** — the per-round two-pile collision budget
   `= (C(50,2) + C(49,2)) / 2^23 = 2401/8388608` (one of each pile).
3. **`δ3`** — three rounds, `= 3 · δ1 = 7203/8388608`.
4. **headline** — `q3 + δ3 < 1/1000` (a `norm_num` goal).

**Remaining construction (follow-up increments, same module):**
* (i) define the deck-valued `finiteRound` kernel (swap + 23 per-pile
  inverse-GSR riffles) over the 50/49 split, using the F4.2 GSR kernel
  (`gsrProductKernel`) — no perfect-reset hidden inside;
* (ii) prove the per-round physical-vs-ideal TV ≤ `δ1` (the F4.2 GSR
  collision bound — the deferred sub-wall);
* (iii) telescope three rounds with `TelescopeF5.telescopeTV_le_idealPlusN`
  to obtain `TV(run finiteRound 3 d0, uniform) ≤ q3 + δ3 < 1/1000`.

No Dobrushin coefficient or full-deck `Finset.univ` maxima are needed for the
bound itself.  The cost is stated separately (see §8: three exchanges + 23+23
binary riffles per round). -/

/-- The exact three-round **ideal** TV constant: three perfect
    (perfect-local) exchanges from the segregated start drive the deck to this
    TV against the uniform 99! target.  It is the value of the already-proved
    `three_physical_perfect_exchanges_uniform_unconditional`. -/
def q3 : Rat :=
  172379525755689183991816396516567920780192827919620440221147749 /
  6691837923759692633601708022649918108038775216019298375918637677488

/-- The per-round two-pile finite-riffle **collision** budget: a 23-riffle
    pile fails to fully separate two of its cards with probability
    `C(50,2)/2^23 + C(49,2)/2^23` summed over the left (50) and right (49)
    piles, i.e. `(1225 + 1176)/8388608 = 2401/8388608`. -/
def δ1 : Rat := ((Nat.choose 50 2 + Nat.choose 49 2) : Rat) / (2 ^ 23 : Rat)

/-- The three-round collision budget: `3 · δ1 = 7203/8388608`. -/
def δ3 : Rat := 3 * δ1

/-- `C(50,2) = 1225` (via `choose n 2 = n(n-1)/2`). -/
theorem choose50_2 : Nat.choose 50 2 = 1225 := by norm_num [Nat.choose_two_right]

/-- `C(49,2) = 1176` (via `choose n 2 = n(n-1)/2`). -/
theorem choose49_2 : Nat.choose 49 2 = 1176 := by norm_num [Nat.choose_two_right]

/-- The per-round collision budget is exactly `2401 / 2^23`. -/
theorem δ1_eq_2401_over_8388608 : δ1 = 2401 / 8388608 := by
  norm_num [δ1, choose50_2, choose49_2]

/-- The three-round collision budget is exactly `7203 / 8388608`. -/
theorem δ3_eq_7203_over_8388608 : δ3 = 7203 / 8388608 := by
  norm_num [δ3, δ1, choose50_2, choose49_2]

/-- **Gate 6 headline (the rational core of the target bound).**  The exact
    three-round finite-GSR budget `q3 + δ3` is **strictly below `1/1000`**:
    `q3 + 7203/8388608 ≈ 0.0008844 < 1/1000`.  Pure `Rat` arithmetic — the
    §8 "exact inequality is a rational arithmetic goal, not a stochastic
    proof" — so the full Gate 6 theorem (once `finiteRound` and the per-round
    collision bound land) closes by this inequality plus a three-round
    telescope. -/
theorem gate6_headline_lt_thousandth : q3 + δ3 < (1 : Rat) / 1000 := by
  norm_num [q3, δ3, δ1, choose50_2, choose49_2]

/-- §4, sub-lemma: the `n-2` complement count — `# {k : Fin n // k ≠ i ∧ k ≠ j} = n-2`
    for `i ≠ j`, `n ≥ 2`.  (The subtype is written inline: a `def` alias does not
    synthesize the `Fintype.Subtype` instance during typeclass search.) -/
theorem cardComplement2 (n : Nat) (i j : Fin n) (hne : i ≠ j) (hn : 1 < n) :
    Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j} = n - 2 := by
  have hsub : ({i, j} : Finset (Fin n)) ⊆ (Finset.univ : Finset (Fin n)) := by simp
  have hcard : ((Finset.univ : Finset (Fin n)) \ {i, j}).card = n - 2 := by
    rw [Finset.card_sdiff_of_subset hsub]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show ({i, j} : Finset (Fin n)).card = 2 from Finset.card_pair hne]
  have hfs : (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i ∧ k ≠ j) =
      (Finset.univ : Finset (Fin n)) \ {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_and_or]
    tauto
  calc Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j}
      = ((Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i ∧ k ≠ j)).card := by
        simpa [Fintype.card_subtype] using rfl
      _ = ((Finset.univ : Finset (Fin n)) \ {i, j}).card := by simpa [hfs]
      _ = n - 2 := hcard

/-- §4: map `f` (with `f i = f j`) to the shared value `f i` and its restriction to
    the `n-2` positions other than `i, j`. -/
noncomputable def pairEqToFun (n a : Nat) (i j : Fin n) :
    {f : Fin n → Fin a // f i = f j} → Fin a × ({k : Fin n // k ≠ i ∧ k ≠ j} → Fin a) :=
  fun f => ⟨f.1 i, fun x => f.1 x.1⟩

/-- §4: the inverse — rebuild `f` from the shared value `p.1` and the restriction `p.2`. -/
noncomputable def pairEqInvFun (n a : Nat) (i j : Fin n) (hne : i ≠ j) :
    (Fin a × ({k : Fin n // k ≠ i ∧ k ≠ j} → Fin a)) → {f : Fin n → Fin a // f i = f j} :=
  fun p =>
    ⟨fun k => if hki : k = i then p.1 else if hkj : k = j then p.1
             else p.2 ⟨k, hki, hkj⟩,
     by
       have hi : ((fun k => if hki : k = i then p.1 else if hkj : k = j then p.1
                            else p.2 ⟨k, hki, hkj⟩) i) = p.1 := by simp
       have hj : ((fun k => if hki : k = i then p.1 else if hkj : k = j then p.1
                            else p.2 ⟨k, hki, hkj⟩) j) = p.1 := by simp [hne]
       simpa using hi.trans hj.symm⟩

/-- §4: a function `f : Fin n → Fin a` with `f i = f j` (i ≠ j) is in bijection with
    the shared value `f i` × its restriction to the `n-2` other positions. -/
noncomputable def pairEqEquiv (n a : Nat) (i j : Fin n) (hne : i ≠ j) :
    {f : Fin n → Fin a // f i = f j} ≃ Fin a × ({k : Fin n // k ≠ i ∧ k ≠ j} → Fin a) :=
  ⟨pairEqToFun n a i j, pairEqInvFun n a i j hne,
    fun f => by
      apply Subtype.ext
      funext k
      dsimp only [pairEqToFun, pairEqInvFun]
      by_cases hki : k = i
      · simp [hki]
      · by_cases hkj : k = j
        · simpa [hkj] using f.2
        · simp [hki, hkj],
    fun p => by
      cases p with
      | mk a g =>
        apply Prod.ext
        · simp [pairEqToFun, pairEqInvFun]
        · funext x
          dsimp only [pairEqToFun, pairEqInvFun]
          by_cases hxi : x.1 = i
          · exfalso; apply x.2.1; exact hxi
          · by_cases hxj : x.1 = j
            · exfalso; apply x.2.2; exact hxj
            · simp [hxi, hxj]⟩

/-- **Gate 6 §4, sub-lemma 1b — proven.**  `# {f : Fin n → Fin a // f i = f j} = a^(n-1)`
    for `i ≠ j`, `n ≥ 2` (combinatorially `a * a^(n-2) = a^(n-1)`: pick the shared
    value for `(i, j)` in `a` ways, then the remaining `n-2` positions freely). -/
theorem cardPairEqSet (n a : Nat) (i j : Fin n) (hne : i ≠ j) (hn : 1 < n) :
    Fintype.card {f : Fin n → Fin a // f i = f j} = a ^ (n - 1) := by
  have hc2 : Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j} = n - 2 := cardComplement2 n i j hne hn
  have h : Fintype.card {f : Fin n → Fin a // f i = f j} = a * (a ^ (n - 2)) := by
    rw [Fintype.card_congr (pairEqEquiv n a i j hne)]
    rw [Fintype.card_prod]
    rw [Fintype.card_fin]
    rw [Fintype.card_fun]
    rw [Fintype.card_fin]
    rw [hc2]
  have hfin : a * (a ^ (n - 2)) = a ^ (n - 1) := by
    have hexp : n - 1 = (n - 2) + 1 := by omega
    rw [hexp, Nat.pow_succ]
    apply Nat.mul_comm
  rw [h]
  exact hfin

end Shufflemath
end
