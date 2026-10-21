"""Exact two-exchange protocol search, separate from Lean proof checking."""
import importlib.util
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


PAIR = load("commander_pair_search", "experiments/commander_pair_search.py")
BL = load("bernoulli_laplace", "experiments/bernoulli_laplace.py")


class TestExactCommanderPair(unittest.TestCase):
    def test_single_sum_agrees_with_two_sum_reference(self):
        for n, m, k in [(99, 50, 1), (99, 50, 25), (99, 50, 49)]:
            for x in [1, 10, 25, 40, 50]:
                row = PAIR.weight_row(k, x)
                self.assertEqual(sum(row), 1)
                for y, p in zip(range(1, 51), row):
                    self.assertEqual(p, BL.transition_probability(n, m, k, x, y))

    def test_two_step_collapse_matches_reference(self):
        for k1, k2 in [(1, 49), (25, 25), (49, 1), (12, 37)]:
            self.assertEqual(PAIR.pair_distance(k1, k2),
                             BL.protocol_distance(99, 50, [k1, k2]))

    def test_unique_best_pair_exact(self):
        best, second = PAIR.exact_search()[:2]
        self.assertEqual((best[1], best[2]), (25, 25))
        self.assertEqual(best[0], Fraction(
            12255318415559330995522631403472464258192877,
            4933350368865509640837610315994582805439728012,
        ))
        self.assertGreater(second[0], best[0])


if __name__ == "__main__":
    unittest.main()
