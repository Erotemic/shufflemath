module

public import Shufflemath.Dobrushin
public import Shufflemath.TotalVariation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Shufflemath

/-- The maximum of a nonempty finite set of `Rat`s, every member of which is
    strictly below `1`, is itself strictly below `1` (the maximum is one of
    the members). -/
lemma max'_lt_one_of_all_lt_one (s : Finset Rat) (hne : s.Nonempty)
    (h : ∀ x ∈ s, x < 1) : s.max' hne < 1 := by
  have hmem : s.max' hne ∈ s := Finset.max'_mem _ hne
  exact h (s.max' hne) hmem

/-- **TV < 0.001 pipeline, Dobrushin-`<1` reduction.**  The Dobrushin
    contraction coefficient of a finite kernel is the maximum of the *finite*
    set of all pairwise row total variations (`pairDistances`).  A finite
    maximum is strictly below `1` iff every member is, so:

    if **every** pair of rows has total variation strictly below `1` (i.e. no
    two rows are mutually singular — equivalently every pair of rows has
    overlapping support), then `dobrushinCoeff K < 1`.

    This is the bridge the 99-card TV < 0.001 certificate needs: once the
    Bernoulli-Laplace exchange kernel is shown to have overlapping 1-step
    support for every pair of macrostates (which holds whenever the exchange
    window `2 k` dominates the state span `blHi - blLo`), the Dobrushin
    coefficient is a strict contraction `d < 1`, and `physicalExchange_dobrushinDecay`
    then bounds the physical `n`-exchange deck-TV by `d^n`, which tends to `0`. -/
theorem dobrushinCoeff_lt_one_of_allPairsLtOne
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [Nonempty alpha]
    (K : FiniteKernel alpha beta) (h : ∀ i j, Dist.tv (K i) (K j) < 1) :
    Dobrushin.dobrushinCoeff K < 1 := by
  unfold Dobrushin.dobrushinCoeff
  apply max'_lt_one_of_all_lt_one _ (Dobrushin.pairDistances_nonempty K)
  intro d hd
  dsimp only [Dobrushin.pairDistances] at hd
  rcases Finset.mem_image.mp hd with ⟨ij, _, rfl⟩
  exact h ij.1 ij.2

end Shufflemath
