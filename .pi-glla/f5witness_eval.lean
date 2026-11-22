module

public import Shufflemath.BernoulliLaplace
public meta import Shufflemath.BernoulliLaplace
public import Mathlib.Tactic

@[expose] public section

-- Concrete verification of the extreme-pair common-successor witness for the
-- 99-card exchange kernel (N = 99, m = 50, k = 25).  The state space is
-- x in [blLo, blHi] = [1, 50].  The common successor z = 25 is reachable
-- from both endpoints:
#eval Shufflemath.BernoulliLaplace.transitionWeight 99 50 25 1 25
#eval Shufflemath.BernoulliLaplace.transitionWeight 99 50 25 50 25
#eval (Shufflemath.BernoulliLaplace.transitionWeight 99 50 25 1 25 > 0)
#eval (Shufflemath.BernoulliLaplace.transitionWeight 99 50 25 50 25 > 0)
-- The denominator is positive (choose 50 25 * choose 49 25).
#eval (Shufflemath.BernoulliLaplace.transitionDenominator 99 50 25 > 0)
