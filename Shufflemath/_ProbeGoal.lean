module

public import Shufflemath.GSR
public import Shufflemath.GSRF42

@[expose]
public section

namespace Shufflemath

theorem keyBelow_repro (n a : Nat) (ell : Fin n → Fin a)
    (hinj : Function.Injective ell) (i : Fin n) (k : Fin n) :
    keyNat n a ell k < keyNat n a ell i ↔ ell k < ell i := by
  rw [keyNat_lex]
  simp only [Fin.lt_def]
  apply Iff.intro
  · intro h
    cases h
    · exact h
    · rcases h with ⟨heq, hval⟩
      have hki : k = i := hinj (Fin.ext heq)
      subst hki
      omega
  · intro h
    exact Or.inl h

end Shufflemath
