"""Exact oracle/physical exchange checks on small complete permutation spaces."""
from __future__ import annotations

import unittest
from fractions import Fraction
from itertools import permutations
from math import comb, factorial

from experiments.full_deck_oracle import (
    admissible_counts,
    apply_micro_to_fiber,
    exact_intertwining_small_deck,
    fiber_decks,
    full_tv_after_via_lift,
    lift_macro_step,
    macro_exchange,
    macro_stationary,
    macro_tv_after,
    micro_exchange_oracle_counts,
    micro_exchange_oracle,
    macrostate,
    finite_gsr_pile_counts,
    finite_vs_perfect_local_row_error,
    finite_vs_perfect_error_bound,
    local_gsr_error,
    micro_exchange_finite_gsr,
    ordered_fiber_size,
    verify_uniform_fiber_identity,
)


class FullDeckOracleTests(unittest.TestCase):
    def test_uniform_99_card_fiber_partition(self):
        self.assertTrue(verify_uniform_fiber_identity(99, 50, 50))
        self.assertEqual(sum(ordered_fiber_size(99, 50, 50, x)
                             for x in admissible_counts(99, 50, 50)), factorial(99))
        self.assertEqual(len(list(admissible_counts(99, 50, 50))), 50)
        self.assertEqual(macro_stationary(99, 50, 50)[50], Fraction(1, comb(99, 50)))

    def test_fiber_count_exact_small(self):
        for n, m, r in [(4, 2, 2), (5, 3, 3), (6, 3, 3)]:
            self.assertTrue(verify_uniform_fiber_identity(n, m, r))
            for x in admissible_counts(n, m, r):
                self.assertEqual(len(fiber_decks(n, m, r, x)),
                                 ordered_fiber_size(n, m, r, x))

    def test_micro_oracle_kernel_is_stochastic(self):
        deck = (0, 1, 2, 3, 4)
        counts = micro_exchange_oracle_counts(deck, 3, 1)
        self.assertEqual(sum(counts.values()), comb(3, 1) * comb(2, 1) * factorial(3) * factorial(2))
        self.assertTrue(all(set(d) == set(deck) for d in counts))

    def test_micro_exchange_is_not_pointwise_canonical_oracle(self):
        # The intertwining identity is for fiber-uniform starts. An arbitrary
        # ordered deck is not itself a uniform draw from its macro fiber.
        deck = (0, 1, 3, 2, 4)
        physical = micro_exchange_oracle(deck, 3, 1)
        oracle = lift_macro_step(5, 3, 3, 1, macrostate(deck, 3, 3))
        difference = sum((abs(physical.get(y, Fraction()) -
                              oracle.get(y, Fraction()))
                          for y in physical.keys() | oracle.keys()), Fraction()) / 2
        self.assertEqual(difference, Fraction(13, 36))

    def test_99_card_macro_distances_match_existing_certificates(self):
        two = macro_tv_after(99, 50, 50, 25, 50, 2)
        three = macro_tv_after(99, 50, 50, 25, 50, 3)
        self.assertEqual(
            two,
            Fraction(12255318415559330995522631403472464258192877,
                     4933350368865509640837610315994582805439728012),
        )
        self.assertEqual(
            three,
            Fraction(172379525755689183991816396516567920780192827919620440221147749,
                     6691837923759692633601708022649918108038775216019298375918637677488),
        )

    def test_finite_gsr_pile_law(self):
        self.assertEqual(sum(finite_gsr_pile_counts((1, 9, 4), 2).values()), 8)
        self.assertEqual(local_gsr_error(3, 1), Fraction(5, 6))
        self.assertEqual(local_gsr_error(2, 2), Fraction(1, 4))

    def test_finite_gsr_vs_perfect_piles(self):
        # Exhaustive row checks, not merely fiber-uniform input checks.
        # The relevant comparison is actual-vs-physical-perfect, NOT the
        # canonical oracle. Exact maximum row distances are stable
        # regression values for the future Lean kernel-discrepancy theorem.
        cases = [
            (4, 2, 1, 2, Fraction(5, 16)),
            (5, 3, 1, 2, Fraction(3, 8)),
            (5, 3, 1, 4, Fraction(13, 64)),
            (6, 3, 1, 2, Fraction(1, 2)),
        ]
        for n, m, k, alphabet, expected_max in cases:
            with self.subTest(n=n, alphabet=alphabet):
                bound = finite_vs_perfect_error_bound(n, m, alphabet)
                worst = Fraction()
                for deck in permutations(range(n)):
                    err = finite_vs_perfect_local_row_error(
                        deck, m, k, alphabet)
                    worst = max(worst, err)
                    self.assertLessEqual(err, bound)
                self.assertEqual(worst, expected_max)

    def test_macro_transition_is_stochastic(self):
        for n, m, r, k in [(4, 2, 2, 1), (5, 3, 3, 1), (6, 3, 3, 1), (6, 3, 3, 2)]:
            for x in admissible_counts(n, m, r):
                p = macro_exchange(n, m, r, k, x)
                self.assertEqual(sum(p.values(), Fraction()), Fraction(1))
                self.assertTrue(set(p) <= set(admissible_counts(n, m, r)))

    def test_exact_intertwining_exhaustive(self):
        for n, m, r, k in [(4, 2, 2, 1), (5, 3, 3, 1), (6, 3, 3, 1)]:
            with self.subTest(n=n, k=k):
                self.assertTrue(exact_intertwining_small_deck(n, m, r, k))

    def test_full_tv_equals_macro_tv(self):
        for n, m, r, k in [(4, 2, 2, 1), (5, 3, 3, 1), (6, 3, 3, 1)]:
            for nsteps in range(4):
                for x in admissible_counts(n, m, r):
                    self.assertEqual(full_tv_after_via_lift(n, m, r, k, x, nsteps),
                                     macro_tv_after(n, m, r, k, x, nsteps))

    def test_macro_law_equals_micro_for_particular_row(self):
        self.assertEqual(apply_micro_to_fiber(5, 3, 3, 1, 2),
                         lift_macro_step(5, 3, 3, 1, 2))


if __name__ == "__main__":
    unittest.main()
