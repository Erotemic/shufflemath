# F4.2 relabeling-invariance — batch 1 DONE (this session), batch 2/3 next

## What this session proved (committed in `Shufflemath/FiniteDeck/RelabelInvariance.lean`)

The **wall-free generic core** of the §7 relabeling-invariance / right-convolution bridge
(2026-11-21 gate-6 proof-hints §7; G6.6/G6.7 endgame) that transports the on-mission
`TV < 1/1000` headline from a fiber-uniform start to **any** deterministic start:

| theorem | statement | role in F4.2 |
|---|---|---|
| `map_bijection_inverse` | `(μ.map e).map e.symm = μ` | reverse-direction TV-invariance ingredient |
| `tv_bijective_invariance` | `tv (μ.map e) (ν.map e) = tv μ ν` for a bijection `e` | **`TV` is invariant under a *common* bijective pushforward** — the `=`, not just the `≤` of `tv_map_contraction` |
| `relabel_bijective` / `relabel_equiv` | `e ↦ g ∘ e` (`e.trans g`) is a bijection of `Equiv.Perm (Fin n)` | the deck-relabeling action is a group action |
| `uniformDeck_relabel_invariant` | `(uniformDist (Perm (Fin n))).map (e ↦ e.trans g) = uniformDist (Perm (Fin n))` | **the uniform full-deck law is fixed by the relabeling** (via `GSR.map_bijective_uniformDist`) |

All four are **polymorphic in `n`** (no `99`-card `Equiv.Perm (Fin 99)` term is forced),
so they compile **wall-free at any size**. Full verify green: 3277 jobs build, 37 unittests
pass, `./dev/verify_next_phase.sh` exit 0.

Key proof technique (batch 1): to show `(e₁.trans g) = (e₂.trans g) → e₁ = e₂`, pull the
function-equality apart with `Equiv.congr_fun h x` (NOT the `.toFun` structure field, which
is definitionally equal but not provably so under `only`), `simpa [Equiv.trans_apply]` to
get `g (e₁ x) = g (e₂ x)`, then pre-compose with `g.symm` and `simpa [Equiv.symm_apply_apply]`.
Surjectivity: `d = g ∘ (g.symm ∘ d)` via `simp [Equiv.trans]` (the `Equiv.trans` simp lemma
unfolds `f.trans g = g ∘ f`, so the goal reduces to `g ∘ (g.symm ∘ d) = d`).

## Batch 2 (NEXT) — the kernel equivariance

F4.2's theorem statement (per the 2026-11-21 hints §7) is:

```
TV(K^t(d), U_deck) = TV(K^t(d'), U_deck)   for every pair of deterministic ordered decks d, d'
```

with `K` the GSR ideal-shuffle kernel (or, for the on-mission 99-card headline, the
41-step physical-exchange kernel) and `U_deck = GSR.uniformDist (Equiv.Perm (Fin n))`.

The two batch-1 ingredients above give the conclusion **iff** the kernel is equivariant
under the same relabeling:

```
K(g ∘ d) = g_* K(d)          (i.e. K(g∘d).map (·∘g)⁻¹ = K(d), or K(g∘d) = (K d).map (·∘g))
```

for `g = d' ∘ d⁻¹` the card-identity relabeling sending `d` to `d'` (all random choices in
the exchange/shuffle are **position-based**, so the law is colorblind).

### The wall
The concrete `N=99` kernel-equality terms hit the **N=99 whnf wall** (a kernel
elaborator limitation on 99-card deck-*equality* terms, not a logic gap — the batch-5b
2026-12-09 note). So batch 2 should be proved **generic in `n`** (polymorphic `n`, no
99-card term forced), exactly as batch 1 was. The kernel for the GSR ideal shuffle is
`GSR.idealShuffle n a` (= `labelShuffle a (uniformLabels n a)` =
`fun deck => uniformLabels.map (fun labels => stableBuckets a labels deck)`).

### The subtlety (why batch 1 was not enough)
`uniformLabels n a` assigns a *random label per card identity* (a `Fin n → Fin a` function
over card identities, not positions). So the shuffle is **not** colorblind at the
deterministic `stableBuckets` level (the labels depend on card identity). It is colorblind
only at the **law** level: the label *distribution* is exchange-invariant (independent
uniform per identity), so relabeling the deck commutes with the shuffle **in law**, i.e.

```
(idealShuffle n a d).map (· ∘ g)  =  idealShuffle n a (g ∘ d)        for g a card-identity Perm
```

because both sides are `uniformLabels.map (fun labels => …)` and the `labels` law is
invariant under pre-composition with `g` (`uniformLabels` is uniform over
`Fin n → Fin a`, which is fixed by relabeling its domain). Proving this requires
showing `uniformLabels.map (labels ↦ labels ∘ g) = uniformLabels` — i.e. the label law is
invariant under a domain relabeling (a `map_bijection`/`map_bijective_uniformDist`-style
argument on the label type `Fin n → Fin a`, which IS a permutation space, so batch 1's
`uniformDeck_relabel_invariant` generalizes to it).

**This is the concrete next theorem to write:**

```lean
theorem idealShuffle_relabelEquiv (n a : Nat) (ha : 0 < a) (g : Equiv.Perm (Fin n)) (d : List (Fin n)) :
  (GSR.idealShuffle n a ha d).map (fun d' => (fun x => g x) <$> d') =
  GSR.idealShuffle n a ha ((fun x => g x) <$> d)
```

Note the domain of the labels is **positions** (`Fin n`), and the relabeling `g` acts on
*card identities* which are also `Fin n` in this model — the two `Fin n` roles (position
vs card-identity) coincide in the `List (Fin n)` deck model, so `g` can serve both. If
the label source is truly position-based (labels indexed by position, not card), the
equivariance is immediate (labels unchanged under a card relabeling); if it is
card-identity-based, the label law must be shown invariant under the domain relabeling.
Check which `GSR.idealShuffle` uses (it uses `uniformLabels n a : Dist (Fin n → Fin a)` —
indexed by `Fin n`, so the `Fin n` here is the **card-identity** index; the equivariance
then needs the label-law relabeling-invariance lemma).

## Batch 3 (AFTER batch 2) — the all-starts headline

Compose batch 2 (kernel equivariance) + batch 1 (TV invariance + uniform-law invariance) to
get `TV(K^t(d), U) = TV(K^t(d'), U)` for any deterministic `d`, then apply the on-mission
`DobrushinDecay99.physicalExchange_decay_41_lt_thousand` (from the fiber-uniform start of a
segregated `d0`) to conclude `TV(K^41(d), U) < 1/1000` for **any** deterministic `d`.
This is the genuinely worst-case-start theorem the hint doc's boxed equation states.

## Status
- batch 1 (generic core): **DONE, committed** (this session, `RelabelInvariance.lean`).
- batch 2 (kernel equivariance `idealShuffle_relabelEquiv`): **TODO** (write the
  label-law relabeling-invariance lemma, then the kernel equivariance, generic `n`).
- batch 3 (all-starts headline `TV(K^41(d), U) < 1/1000` for any `d`): **TODO** (compose).
