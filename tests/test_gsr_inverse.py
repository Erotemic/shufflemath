"""Executable exact-rational sanity checks of the Lean GSR conventions."""
import importlib.util
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb
from pathlib import Path
import unittest

ROOT = Path(__file__).parents[1]
PATH = ROOT / "experiments" / "gsr_inverse.py"
SPEC = importlib.util.spec_from_file_location("gsr_inverse", PATH)
GSR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GSR)


class TestInverseGSR(unittest.TestCase):
    def test_stable_groups_are_an_actual_permutation(self):
        for n in range(5):
            deck = tuple(range(n))
            for a in range(1, 4):
                for labels in GSR.all_labels(n, a):
                    result = GSR.stable_buckets(deck, labels, a)
                    self.assertCountEqual(result, deck)

    def test_combined_lex_labels_are_second_first_order(self):
        for n in range(5):
            deck = tuple(range(n))
            for a, b in [(2, 2), (2, 3), (3, 2)]:
                for minor in GSR.all_labels(n, a):
                    first = GSR.stable_buckets(deck, minor, a)
                    for major in GSR.all_labels(n, b):
                        sequential = GSR.stable_buckets(first, major, b)
                        combined = GSR.lex_buckets(deck, minor, major, a, b)
                        numeric = GSR.stable_buckets(
                            deck, GSR.fused_labels(minor, major, a), a * b)
                        self.assertEqual(sequential, combined)
                        self.assertEqual(sequential, numeric)

    def test_distribution_composition(self):
        for n in range(5):
            deck = tuple(range(n))
            for a, b in [(1, 3), (2, 2), (2, 3), (3, 2)]:
                self.assertEqual(
                    GSR.two_round_law(deck, a, b),
                    GSR.shuffle_law(deck, a * b),
                )

    def test_probability_formula_and_tv(self):
        for n in range(1, 6):
            deck = tuple(range(n))
            for a in range(1, 5):
                law = GSR.shuffle_law(deck, a)
                self.assertEqual(sum(law.values()), 1)
                for permutation in permutations(deck):
                    rising = GSR.rising_sequences_of_inverse(permutation)
                    expected = Fraction(comb(a + n - rising, n) if a >= rising else 0, a**n)
                    self.assertEqual(law.get(permutation, Fraction()), expected,
                                     (n, a, permutation, rising))

    def test_uniform_is_stationary_for_riffles(self):
        n = 3
        decks = list(permutations(range(n)))
        incoming = Counter()
        for deck in decks:
            for out, mass in GSR.shuffle_law(deck, 2).items():
                incoming[out] += mass
        self.assertEqual(set(incoming), set(decks))
        self.assertTrue(all(incoming[x] == 1 for x in decks))


if __name__ == "__main__":
    unittest.main()
