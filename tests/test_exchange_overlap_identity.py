"""Independent exact checks for the reversible-membership F3 proof route.

A k-for-k exchange moves membership S to T iff |S intersection T| = m-k.
For a fixed target T with y marked cards, the number of starting memberships
S with x marked cards and that overlap is transitionNumerator(y, x).
This relates the F3 pointwise law to already-proved BL detailed balance.

No permutations of a 99-card deck are enumerated. All values are exact ints.
"""

import itertools
import math
import unittest


def choose(n: int, k: int) -> int:
    return math.comb(n, k) if 0 <= k <= n else 0


def fiber_size(n: int, m: int, r: int, count: int) -> int:
    return choose(r, count) * choose(n - r, m - count)


def transition_numerator(n: int, m: int, r: int, k: int, x: int, y: int) -> int:
    """Match BernoulliLaplaceGeneral.transitionNumerator on valid states."""
    total = 0
    for a in range(k + 1):
        remaining = max(0, x - a)  # Lean Nat subtraction.
        if remaining <= y:
            b = y - remaining
            if b <= k:
                total += (
                    choose(x, a)
                    * choose(m - x, k - a)
                    * choose(r - x, b)
                    * choose((n - m) - (r - x), k - b)
                )
    return total


def overlap_count(n: int, m: int, r: int, k: int, x: int, y: int) -> int:
    """Count S of size m with x marked cards and |S intersect T| = m-k.

    T is any m-card membership containing y of the r marked identities.
    Split S into four independent bins: marked/unmarked inside/outside T.
    """
    plain_outside_target = (n - r) - (m - y)
    total = 0
    for t in range(m - k + 1):
        plain_overlap = (m - k) - t
        total += (
            choose(y, t)
            * choose(r - y, x - t)
            * choose(m - y, plain_overlap)
            * choose(plain_outside_target, (m - x) - plain_overlap)
        )
    return total


class TestExchangeOverlapIdentity(unittest.TestCase):
    def test_commander_all_2500_macro_pairs(self):
        n, m, r, k = 99, 50, 50, 25
        normalizer = choose(m, k) * choose(n - m, k)
        for x in range(1, 51):
            self.assertEqual(
                sum(transition_numerator(n, m, r, k, x, y) for y in range(1, 51)),
                normalizer,
            )
            for y in range(1, 51):
                with self.subTest(x=x, y=y):
                    count = overlap_count(n, m, r, k, x, y)
                    self.assertEqual(count, transition_numerator(n, m, r, k, y, x))
                    # Equivalent to uniformity within each output-count fiber.
                    self.assertEqual(
                        count * fiber_size(n, m, r, y),
                        transition_numerator(n, m, r, k, x, y)
                        * fiber_size(n, m, r, x),
                    )

    def test_small_decks_against_actual_membership_pairs(self):
        for n, m, r, k in [(6, 3, 2, 1), (7, 4, 4, 2), (8, 4, 3, 1)]:
            marked = frozenset(range(r))
            members = [frozenset(s) for s in itertools.combinations(range(n), m)]
            for target in members:
                y = len(target & marked)
                for x in range(max(0, r - (n - m)), min(r, m) + 1):
                    direct = sum(
                        len(s & marked) == x and len(s & target) == m - k
                        for s in members
                    )
                    self.assertEqual(
                        direct, overlap_count(n, m, r, k, x, y),
                        (n, m, r, k, x, y, sorted(target)),
                    )
                    self.assertEqual(
                        direct, transition_numerator(n, m, r, k, y, x),
                        (n, m, r, k, x, y, sorted(target)),
                    )


if __name__ == "__main__":
    unittest.main()
