"""Exact checks of the concrete fiber witnesses and membership refinement."""
from __future__ import annotations

import unittest
from fractions import Fraction
from itertools import permutations
from math import factorial

from experiments.commander_fiber_witness import (
    deck_for_commander_state,
    raw_position_exchange_membership_law,
    predicted_uniform_membership_law,
    verify_membership_intertwining,
)
from experiments.full_deck_oracle import (
    admissible_counts,
    fiber_decks,
    macro_stationary,
    macrostate,
    ordered_fiber_size,
)


class CommanderFiberWitnessTests(unittest.TestCase):
    def test_all_50_canonical_permutations(self):
        for x in range(50):
            with self.subTest(x=x):
                deck = deck_for_commander_state(x)
                self.assertEqual(len(deck), 99)
                self.assertEqual(set(deck), set(range(99)))
                self.assertEqual(macrostate(deck, 50, 50), x + 1)

    def test_bad_commander_states(self):
        for x in (-1, 50):
            with self.assertRaises(ValueError):
                deck_for_commander_state(x)

    def test_finite_uniform_disintegration(self):
        # Every microstate receives probability 1/n! after uniform fiber
        # sampling at the exact macro-marginal frequency.
        for n, m, r in ((4, 2, 2), (5, 3, 3), (6, 3, 3)):
            with self.subTest(n=n):
                macro = macro_stationary(n, m, r)
                for deck in permutations(range(n)):
                    x = macrostate(deck, m, r)
                    p = macro[x] / ordered_fiber_size(n, m, r, x)
                    self.assertEqual(p, Fraction(1, factorial(n)))
                self.assertEqual(sum(macro.values(), Fraction()), 1)
                self.assertEqual(list(macro), list(admissible_counts(n, m, r)))

    def test_uniform_membership_refinement(self):
        for n, m, r, k in ((4, 2, 2, 1), (5, 3, 3, 1),
                           (6, 3, 3, 1), (6, 3, 3, 2)):
            with self.subTest(n=n, k=k):
                self.assertTrue(verify_membership_intertwining(n, m, r, k))

    def test_member_law_normalization(self):
        for n, m, r, k in ((4, 2, 2, 1), (5, 3, 3, 1),
                           (6, 3, 3, 1)):
            for x in admissible_counts(n, m, r):
                actual = raw_position_exchange_membership_law(n, m, r, k, x)
                expected = predicted_uniform_membership_law(n, m, r, k, x)
                self.assertEqual(sum(actual.values(), Fraction()), 1)
                self.assertEqual(actual, expected)


if __name__ == '__main__':
    unittest.main()
