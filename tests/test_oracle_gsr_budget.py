"""Regression tests for conservative exact-rational protocol error bounds."""
import importlib.util
from fractions import Fraction
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
sys.path.insert(0, str(ROOT / "visualizations"))
from shuffleviz.model import gsr_tv
from commander_pair_search import pair_distance
from oracle_gsr_budget import conservative_bound, local_phase_error, best_under_target


class TestOracleGSRBudget(unittest.TestCase):
    def test_zero_rounds_error(self):
        self.assertEqual(local_phase_error(0),
                         Fraction(1) - Fraction(1, __import__('math').factorial(49))
                         + Fraction(1) - Fraction(1, __import__('math').factorial(50)))

    def test_exact_decomposition(self):
        rounds = (14, 15, 16)
        bound = conservative_bound((25, 25), rounds)
        self.assertEqual(bound, pair_distance(25, 25) + sum(
            (gsr_tv(49, r) + gsr_tv(50, r) for r in rounds), Fraction()))

    def test_search_is_feasible_and_minimal_bounded(self):
        maximum_rounds = 17
        target = Fraction(1, 100)
        answer = best_under_target(target, maximum_rounds=maximum_rounds)
        self.assertIsNotNone(answer)
        count, bound, rounds = answer
        self.assertLessEqual(bound, target)
        self.assertEqual(count, 2 * sum(rounds) + 2)
        # Exhaustively check all smaller totals by dynamic programming over
        # total riffle count, not by trusting the search's tie breaker.
        per_round = [local_phase_error(r) for r in range(maximum_rounds + 1)]
        floor = pair_distance(25, 25)
        for a in range(maximum_rounds + 1):
            for b in range(maximum_rounds + 1):
                for c in range(maximum_rounds + 1):
                    if a + b + c < sum(rounds):
                        self.assertGreater(floor + per_round[a] + per_round[b] + per_round[c],
                                           target)

    def test_not_a_full_deck_certificate(self):
        self.assertGreater(conservative_bound((25, 25), (0, 0, 0)), Fraction(1))


if __name__ == "__main__":
    unittest.main()
