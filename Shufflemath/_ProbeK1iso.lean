module
public import Mathlib
public import Shufflemath.Finite
public import Shufflemath.TotalVariation
public import Shufflemath.GSR
public import Shufflemath.GSRDeckRound
public import Shufflemath.GSRSegHeadline
public import Shufflemath.GSRSegMembership
public import Shufflemath.CommanderPermutation
public import Shufflemath.CommanderMembershipKernels
public import Shufflemath.FiniteDeck.WithinPileOrbit
public import Shufflemath.FiniteDeck.TwoPile
public import Shufflemath.FiniteDeck.PositionAction
public import Shufflemath.FiniteDeck.ActionConvolution
public import Shufflemath.Gate6Crux
public import Shufflemath.FiberDisintegration

@[expose]
public section

namespace Shufflemath

abbrev P99c : Type := Equiv.Perm (Fin 50) × Equiv.Perm (Fin (99 - 50))

noncomputable def rifflePush2 (d' : Equiv.Perm (Fin 99)) (z : P99c) : Equiv.Perm (Fin 99) :=
  (roundEmbedMap 99 50 hm5099 z).trans d'

variable (d' X : Equiv.Perm (Fin 99))

#check (FiberDisintegration.fiberSet (rifflePush2 d') X)
#check ((FiberDisintegration.fiberSet (rifflePush2 d') X).card ≤ 1)

end Shufflemath
