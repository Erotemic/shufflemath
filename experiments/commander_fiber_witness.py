#!/usr/bin/env python3
"""Independent finite checks for the next Commander permutation proof tranche.

The 99-card deck witness is a cyclic rotation. The membership-level
physical-exchange reference is deliberately kept separate from a global
macro-fiber reset: a perfect local shuffle preserves the exact card set
in each pile, even though it randomizes the order within the two piles.
All probabilities are exact Fractions. No 99! permutations are enumerated.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb

from experiments.full_deck_oracle import (
    fiber_decks,
    macro_exchange,
    macrostate,
    membership_fiber_size,
)


def deck_for_commander_state(state: int) -> tuple[int, ...]:
    """Full 99-card permutation with ``state + 1`` marked cards on left."""
    if not 0 <= state < 50:
        raise ValueError("Commander macrostate must be in range(50)")
    shift = 49 - state
    return tuple((position + shift) % 99 for position in range(99))


def left_membership(deck: tuple[int, ...], left_size: int) -> frozenset[int]:
    return frozenset(deck[:left_size])


def raw_position_exchange_membership_law(
    n: int, m: int, r: int, k: int, count: int,
) -> dict[frozenset[int], Fraction]:
    """Average raw position exchanges over the uniform macro-count fiber.

    Exchange is before local pile shuffles. Local shuffling cannot affect
    membership, so this is the intermediate distribution relevant to the
    Lean `PhysicalExchangeReduction` obligation.
    """
    initial = fiber_decks(n, m, r, count)
    outcomes: Counter[frozenset[int]] = Counter()
    for deck in initial:
        for left in combinations(range(m), k):
            for right in combinations(range(m, n), k):
                current = list(deck)
                for i, j in zip(left, right):
                    current[i], current[j] = current[j], current[i]
                outcomes[left_membership(tuple(current), m)] += 1
    den = len(initial) * comb(m, k) * comb(n - m, k)
    return {membership: Fraction(multiplicity, den)
            for membership, multiplicity in outcomes.items()}


def predicted_uniform_membership_law(
    n: int, m: int, r: int, k: int, count: int,
) -> dict[frozenset[int], Fraction]:
    """Macro transition followed by uniform membership at the new count."""
    macrolaw = macro_exchange(n, m, r, k, count)
    result: dict[frozenset[int], Fraction] = {}
    for membership_tuple in combinations(range(n), m):
        membership = frozenset(membership_tuple)
        x = len(membership & frozenset(range(r)))
        p = macrolaw.get(x, Fraction())
        if p:
            result[membership] = p / membership_fiber_size(n, m, r, x)
    return result


def verify_membership_intertwining(n: int, m: int, r: int, k: int) -> bool:
    """Exhaustive *small-deck* check of the membership-level identity."""
    lo = max(0, m + r - n)
    hi = min(m, r)
    for x in range(lo, hi + 1):
        if raw_position_exchange_membership_law(n, m, r, k, x) != \
                predicted_uniform_membership_law(n, m, r, k, x):
            return False
    return True
