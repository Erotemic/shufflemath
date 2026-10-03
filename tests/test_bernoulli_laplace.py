import importlib.util
from pathlib import Path
import unittest


MODULE_PATH = Path(__file__).parents[1] / "experiments" / "bernoulli_laplace.py"
SPEC = importlib.util.spec_from_file_location("bernoulli_laplace", MODULE_PATH)
BL = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(BL)


class TestBernoulliLaplace(unittest.TestCase):
    def test_rows_normalize_commander_k25(self):
        BL.validate_matrix(99, 50, 25)

    def test_stationary_normalizes(self):
        _, stationary = BL.stationary_distribution(99, 50)
        self.assertEqual(sum(stationary), 1)

    def test_two_k25_exchanges(self):
        d = BL.protocol_distance(99, 50, [25, 25])
        self.assertAlmostEqual(float(d), 0.00248418, places=8)

    def test_three_k25_exchanges(self):
        d = BL.protocol_distance(99, 50, [25, 25, 25])
        self.assertAlmostEqual(float(d), 0.0000257597, places=10)

    def test_best_pair_is_25_25(self):
        d, seq = BL.best_pair_protocol(99, 50)
        self.assertEqual(seq, (25, 25))
        self.assertAlmostEqual(float(d), 0.00248418, places=8)


if __name__ == "__main__":
    unittest.main()
