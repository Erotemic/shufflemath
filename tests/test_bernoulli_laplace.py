import importlib.util
from fractions import Fraction
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

    def test_stationary_is_fixed_by_k25(self):
        xs, stationary = BL.stationary_distribution(99, 50)
        _, matrix = BL.transition_matrix(99, 50, 25)
        self.assertEqual(BL.row_apply(stationary, matrix), stationary)
        self.assertEqual(xs, list(BL.states(99, 50)))

    def test_two_k25_exchanges_exact(self):
        d = BL.protocol_distance(99, 50, [25, 25])
        self.assertEqual(
            d,
            Fraction(
                12255318415559330995522631403472464258192877,
                4933350368865509640837610315994582805439728012,
            ),
        )

    def test_three_k25_exchanges_exact(self):
        d = BL.protocol_distance(99, 50, [25, 25, 25])
        self.assertEqual(
            d,
            Fraction(
                172379525755689183991816396516567920780192827919620440221147749,
                6691837923759692633601708022649918108038775216019298375918637677488,
            ),
        )

    def test_four_k25_exchanges_exact(self):
        d = BL.protocol_distance(99, 50, [25, 25, 25, 25])
        self.assertEqual(
            d,
            Fraction(
                38950709285263598605412682775546001018285458904284075272070592084472126289080469529,
                148259896488975809340025734299846927510315001659639477959688861464546794510241654850373696,
            ),
        )

    def test_best_pair_is_25_25(self):
        d, seq = BL.best_pair_protocol(99, 50)
        self.assertEqual(seq, (25, 25))
        self.assertEqual(d, BL.protocol_distance(99, 50, [25, 25]))


if __name__ == "__main__":
    unittest.main()
