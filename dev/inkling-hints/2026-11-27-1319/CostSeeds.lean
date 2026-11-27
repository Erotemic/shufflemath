import Shufflemath.FiniteDeck.TerminalReset

/-! Uncompiled arithmetic-only certificate. This is optimum of a sufficient
bound, not a lower bound on the actual finite-shuffle TV. -/
namespace Shufflemath.Nov27Seeds
open FiniteDeck

def terminalBound (r s : Nat) : Rat := q3 + 1225 / (2 : Rat)^r + 1176 / (2 : Rat)^s

theorem terminalBound_22_21 : terminalBound 22 21 < (1 : Rat)/1000 := by
  norm_num [terminalBound, q3]

theorem terminalBound_requires_43 (r s : Nat)
    (h : terminalBound r s < (1 : Rat)/1000) : 43 ≤ r+s := by
  have hq : 0 ≤ q3 := by norm_num [q3]
  have hr0 : 0 ≤ (1225 : Rat) / 2^r := by positivity
  have hs0 : 0 ≤ (1176 : Rat) / 2^s := by positivity
  unfold terminalBound at h
  have hr : 21 ≤ r := by
    by_contra hn
    have hr20 : r ≤ 20 := by omega
    have hp : (2 : Rat)^r ≤ 2^20 := by gcongr
    have hd : (1225 : Rat) / 2^r < 1/1000 := by linarith
    have hh := (div_lt_iff₀ (by positivity : 0 < (2 : Rat)^r)).mp hd
    norm_num at hp hh
    linarith
  have hs : 21 ≤ s := by
    by_contra hn
    have hs20 : s ≤ 20 := by omega
    have hp : (2 : Rat)^s ≤ 2^20 := by gcongr
    have hd : (1176 : Rat) / 2^s < 1/1000 := by linarith
    have hh := (div_lt_iff₀ (by positivity : 0 < (2 : Rat)^s)).mp hd
    norm_num at hp hh
    linarith
  by_contra hn
  have hre : r = 21 := by omega
  have hse : s = 21 := by omega
  subst r
  subst s
  norm_num [q3] at h

end Shufflemath.Nov27Seeds
