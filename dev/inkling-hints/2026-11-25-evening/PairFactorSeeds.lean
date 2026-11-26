module

public import Shufflemath.GSR
public import Shufflemath.FiniteDeck.UniformExchange
public import Shufflemath.FiniteDeck.Histograms
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath.InklingHints

/-! Uncompiled candidates. Compile these independently, keep types abstract,
then migrate successful lemmas into the canonical library. Do not import this
file by path from a production module. See the evening handoff for the fallback
proof of each assertion. -/

open Classical

section Uniform

variable {X Y Z : Type*} [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq Y]

/-- Uniform pushforward via cardinality, valid even when Y is not a Fintype. -/
theorem uniformMap_mass_card (f : X → Y) (y : Y) :
    Dist.mass ((GSR.uniformDist X).map f) y =
      ((Finset.univ.filter (fun x : X => f x = y)).card : Rat) /
        (Fintype.card X : Rat) := by
  classical
  rw [GSR.map_uniform_mass, ← Finset.mul_sum]
  have hfilter : (Finset.univ : Finset X).filter (fun x => y = f x) =
      Finset.univ.filter (fun x => f x = y) := by
    ext x
    simp [eq_comm]
  have hcount : (∑ x : X, if y = f x then (1 : Rat) else 0) =
      ((Finset.univ.filter (fun x : X => f x = y)).card : Rat) := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [hcount, div_eq_mul_inv, mul_comm]

/-- Cardinality of a fiber of two independent observations. Prove the finite
set equality before taking cardinalities; no double summation. -/
theorem pairFiber_card (f : X → Y) (z : Y × Y) :
    ((Finset.univ : Finset (X × X)).filter
      (fun ab => (f ab.1, f ab.2) = z)).card =
      (Finset.univ.filter (fun a : X => f a = z.1)).card *
      (Finset.univ.filter (fun b : X => f b = z.2)).card := by
  classical
  have h : (Finset.univ : Finset (X × X)).filter
      (fun ab => (f ab.1, f ab.2) = z) =
      (Finset.univ.filter (fun a : X => f a = z.1)) ×ˢ
      (Finset.univ.filter (fun b : X => f b = z.2)) := by
    ext ab
    rcases ab with ⟨a, b⟩
    rcases z with ⟨u, v⟩
    simp [Finset.mem_product]
  rw [h, Finset.card_product]

/-- The law of a pair of observed cells depends only on their cardinalities. -/
theorem uniformPairMap_eq_of_counts (f g : X → Y)
    (h : ∀ y : Y, (Finset.univ.filter (fun x : X => f x = y)).card =
      (Finset.univ.filter (fun x : X => g x = y)).card) :
    (GSR.uniformDist (X × X)).map (fun ab => (f ab.1, f ab.2)) =
      (GSR.uniformDist (X × X)).map (fun ab => (g ab.1, g ab.2)) := by
  classical
  ext z
  change Dist.mass ((GSR.uniformDist (X × X)).map
      (fun ab => (f ab.1, f ab.2))) z =
    Dist.mass ((GSR.uniformDist (X × X)).map
      (fun ab => (g ab.1, g ab.2))) z
  rw [uniformMap_mass_card, uniformMap_mass_card, pairFiber_card, pairFiber_card,
    h z.1, h z.2]

/-- Generic deterministic factorization of a uniform experiment. This is the
only probability-algebra step needed once the signed histogram update holds. -/
theorem uniformPair_factor (f : X → Y) (step : Y × Y → Z) (out : X × X → Z)
    (h : ∀ ab, out ab = step (f ab.1, f ab.2)) :
    (GSR.uniformDist (X × X)).map out =
      ((GSR.uniformDist (X × X)).map (fun ab => (f ab.1, f ab.2))).map step := by
  rw [Convexity.StdSimplex.map_map]
  have heq : out = step ∘ (fun ab : X × X => (f ab.1, f ab.2)) := funext h
  rw [heq]

end Uniform

/-- Transport uniform sampling through an equivalence, in the correct direction.
This supplies the missing input equivariance proof for UniformExchange. -/
theorem uniformMap_reparam {X Y Z : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ Y) (f : X → Z) (g : Y → Z)
    (h : ∀ x, f x = g (e x)) :
    (GSR.uniformDist X).map f = (GSR.uniformDist Y).map g := by
  have heq : f = g ∘ e := funext h
  rw [heq, ← Convexity.StdSimplex.map_map, GSR.map_bijective_uniformDist e]

open FiniteDeck

variable {N p c : Nat} {n : Fin p → Nat}

/-- The actual missing pointwise conjugation lemma, as opposed to an equality
of masses after relabeling the output only. -/
theorem swapPiles_relabel (σ : Equiv.Perm (Fin N)) (A : Allocation N p n)
    (a b : Fin N) :
    swapPiles (relabel σ A) (σ a) (σ b) = relabel σ (swapPiles A a b) := by
  apply Subtype.ext
  funext x
  change swapOwner (relabel σ A) (σ a) (σ b) x = swapOwner A a b (σ.symm x)
  rw [relabel_commute_owner, swapOwner_eq_cardTransposition]

/-- Full input/output equivariance of the normalized transposition kernel. -/
theorem swapKernel_relabel (hN : 0 < N) (σ : Equiv.Perm (Fin N))
    (A : Allocation N p n) :
    (swapKernel hN A).map (relabel σ) = swapKernel hN (relabel σ A) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  change ((GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => swapPiles A ab.1 ab.2)).map (relabel σ) =
    (GSR.uniformDist (Fin N × Fin N)).map
      (fun ab => swapPiles (relabel σ A) ab.1 ab.2)
  rw [Convexity.StdSimplex.map_map]
  apply uniformMap_reparam (Equiv.prodCongr σ σ)
  intro ab
  exact (swapPiles_relabel σ A ab.1 ab.2).symm

/-- Canonical finite card-cell map on the owner carrier. -/
def ownerCell (color : Fin N → Fin c) (A : Allocation N p n) (x : Fin N) : Fin p × Fin c :=
  (A.val x, color x)

def ownerHist (color : Fin N → Fin c) (A : Allocation N p n) (z : Fin p × Fin c) : Nat :=
  (Finset.univ.filter (fun x : Fin N => ownerCell color A x = z)).card

/-- The histogram is a signed function in the update lemma only. It need not
be used as the finite histogram carrier. Dist.map accepts arbitrary types. -/
def signedHist (color : Fin N → Fin c) (A : Allocation N p n) (z : Fin p × Fin c) : Int :=
  Int.ofNat (ownerHist color A z)

def unitCell (z u : Fin p × Fin c) : Int := if z = u then 1 else 0

/-- Simultaneous signed update: handles even a=b, same-pile, and same-color
cases without Nat subtraction underflow. -/
def signedSwapStep (H : (Fin p × Fin c) → Int) (uv : (Fin p × Fin c) × (Fin p × Fin c))
    (z : Fin p × Fin c) : Int :=
  H z - unitCell z uv.1 - unitCell z uv.2 +
    unitCell z (uv.2.1, uv.1.2) + unitCell z (uv.1.1, uv.2.2)

/-- Once the elementary signed update identity is proved, this gives strong
lumpability of the raw signed observation by a two-line pushforward argument.
The main guide explains how to prove hstep using deletion of two cards. -/
theorem signedHist_lumpable_of_update (hN : 0 < N) (color : Fin N → Fin c)
    (hstep : ∀ (A : Allocation N p n) (a b : Fin N),
      signedHist color (swapPiles A a b) = signedSwapStep (signedHist color A)
        (ownerCell color A a, ownerCell color A b))
    (A B : Allocation N p n) (h : ownerHist color A = ownerHist color B) :
    (swapKernel hN A).map (signedHist color) = (swapKernel hN B).map (signedHist color) := by
  letI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  have hpair := uniformPairMap_eq_of_counts (ownerCell color A) (ownerCell color B)
    (fun z => congrFun h z)
  have hH : signedHist color A = signedHist color B := by
    funext z
    exact congrArg Int.ofNat (congrFun h z)
  change ((GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => swapPiles A ab.1 ab.2)).map (signedHist color) =
    ((GSR.uniformDist (Fin N × Fin N)).map
      (fun ab => swapPiles B ab.1 ab.2)).map (signedHist color)
  simp only [Convexity.StdSimplex.map_map]
  have hA := uniformPair_factor (ownerCell color A) (signedSwapStep (signedHist color A))
    (fun ab => signedHist color (swapPiles A ab.1 ab.2)) (fun ab => hstep A ab.1 ab.2)
  have hB := uniformPair_factor (ownerCell color B) (signedSwapStep (signedHist color B))
    (fun ab => signedHist color (swapPiles B ab.1 ab.2)) (fun ab => hstep B ab.1 ab.2)
  change (GSR.uniformDist (Fin N × Fin N)).map
    (fun ab => signedHist color (swapPiles A ab.1 ab.2)) =
    (GSR.uniformDist (Fin N × Fin N)).map
      (fun ab => signedHist color (swapPiles B ab.1 ab.2))
  rw [hA, hB, hpair, hH]

end Shufflemath.InklingHints
