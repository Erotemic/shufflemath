#!/usr/bin/env python3
"""Exact finite Bernoulli--Laplace calculations for the shufflemath project.

The state x is the number of cards from the original left pile (size m) currently
in the left pile.  At each exchange, k uniformly chosen cards from each pile are
swapped.  All calculations use fractions.Fraction.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction
from math import comb


def states(N: int, m: int) -> range:
    """Feasible values of x = original-left cards currently in the left pile."""
    right = N - m
    return range(max(0, m - right), m + 1)


def choose(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    return comb(n, k)


def transition_probability(N: int, m: int, k: int, x: int, y: int) -> Fraction:
    """Exact P[X_{t+1}=y | X_t=x] for exchanging k cards from each pile."""
    right = N - m
    denom = choose(m, k) * choose(right, k)
    if denom == 0:
        return Fraction(0)

    # Left currently has x A-cards and m-x B-cards.
    # Right currently has m-x A-cards and right-(m-x) B-cards.
    total = 0
    for a in range(k + 1):
        # a = A-cards moved left -> right
        ways_left = choose(x, a) * choose(m - x, k - a)
        if not ways_left:
            continue
        for b in range(k + 1):
            # b = A-cards moved right -> left
            if x - a + b != y:
                continue
            ways_right = choose(m - x, b) * choose(right - (m - x), k - b)
            total += ways_left * ways_right
    return Fraction(total, denom)


@lru_cache(maxsize=None)
def transition_matrix(N: int, m: int, k: int):
    xs = list(states(N, m))
    return xs, [
        [transition_probability(N, m, k, x, y) for y in xs]
        for x in xs
    ]


def stationary_distribution(N: int, m: int):
    """Hypergeometric stationary law induced by a uniformly random N-card deck."""
    xs = list(states(N, m))
    denom = choose(N, m)
    return xs, [
        Fraction(choose(m, x) * choose(N - m, m - x), denom)
        for x in xs
    ]


def point_mass(xs, x0: int):
    return [Fraction(int(x == x0), 1) for x in xs]


def row_apply(dist, matrix):
    width = len(matrix[0])
    return [sum(dist[i] * matrix[i][j] for i in range(len(dist))) for j in range(width)]


def total_variation(p, q) -> Fraction:
    return sum(abs(a - b) for a, b in zip(p, q)) / 2


def protocol_distance(N: int, m: int, exchanges: list[int]) -> Fraction:
    xs = list(states(N, m))
    dist = point_mass(xs, m)
    _, target = stationary_distribution(N, m)
    for k in exchanges:
        _, matrix = transition_matrix(N, m, k)
        dist = row_apply(dist, matrix)
    return total_variation(dist, target)


def validate_matrix(N: int, m: int, k: int) -> None:
    xs, matrix = transition_matrix(N, m, k)
    for x, row in zip(xs, matrix):
        assert sum(row) == 1, (x, sum(row))
        assert all(v >= 0 for v in row)


def best_pair_protocol(N: int, m: int):
    """Search all two-exchange schedules using floating point, then evaluate the
    winning candidate exactly.  This is a conjecture generator, not a proof of
    optimality; the corresponding finite optimality statement belongs in Lean.
    """
    xs = list(states(N, m))
    _, target_exact = stationary_distribution(N, m)
    target = [float(v) for v in target_exact]
    limit = min(m, N - m)

    float_matrices = {}
    first_rows = {}
    for k in range(1, limit + 1):
        _, matrix = transition_matrix(N, m, k)
        float_matrices[k] = [[float(v) for v in row] for row in matrix]
        first_rows[k] = float_matrices[k][xs.index(m)]

    best = None
    for k1 in range(1, limit + 1):
        dist1 = first_rows[k1]
        for k2 in range(1, limit + 1):
            matrix = float_matrices[k2]
            dist2 = [
                sum(dist1[i] * matrix[i][j] for i in range(len(xs)))
                for j in range(len(xs))
            ]
            d = 0.5 * sum(abs(a - b) for a, b in zip(dist2, target))
            candidate = (d, (k1, k2))
            if best is None or candidate < best:
                best = candidate

    assert best is not None
    seq = best[1]
    return protocol_distance(N, m, list(seq)), seq


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--N", type=int, default=99)
    parser.add_argument("--m", type=int, default=50)
    parser.add_argument("--k", type=int, default=25)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--search-pairs", action="store_true")
    args = parser.parse_args()

    validate_matrix(args.N, args.m, args.k)
    print(f"N={args.N}, m={args.m}, exchange k={args.k}")
    for step in range(1, args.steps + 1):
        d = protocol_distance(args.N, args.m, [args.k] * step)
        print(f"steps={step}: TV={float(d):.12g} exact={d}")

    if args.search_pairs:
        d, seq = best_pair_protocol(args.N, args.m)
        print(f"best pair={seq}: TV={float(d):.12g} exact={d}")


if __name__ == "__main__":
    main()
