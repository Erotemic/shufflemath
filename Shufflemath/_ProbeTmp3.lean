module

public import Shufflemath.GSR
public import Shufflemath.TotalVariation

open Shufflemath
open Convexity

section T
variable (n a : Nat) (ha : 0 < a) (hn : 0 < n)
variable (hFinPi : Fintype (Fin n → Fin a)) (hFinPerm : Fintype (Equiv.Perm (Fin n)))

include ha hn in
def T (n a : Nat) (ha : 0 < a) (hn : 0 < n)
    (hFinPi : Fintype (Fin n → Fin a)) (hFinPerm : Fintype (Equiv.Perm (Fin n)))
    : Dist (ΩTieRank n a) := by
  letI hΩ : Fintype (ΩTieRank n a) :=
    Fintype.mk (Finset.univ ×ˢ Finset.univ) fun p =>
      Finset.mem_product.2 ⟨hFinPi.complete p.1, hFinPerm.complete p.2⟩
  letI hNonempty : Nonempty (ΩTieRank n a) := hNonemptyΩ n a ha
  exact GSR.uniformDist (ΩTieRank n a)

#check (GSR.uniformDist (Fin n → Fin a) : Dist (Fin n → Fin a)).map Prod.fst
