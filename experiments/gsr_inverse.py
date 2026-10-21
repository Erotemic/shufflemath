#!/usr/bin/env python3
"""Exact small-deck inverse GSR reference for the Lean product-label model.

Assign a label to each *card identity*, then group the current deck stably by
label. For two rounds, the later/major label is sorted first, and the earlier
label is the minor tie-breaker. This is the same convention as `GSR.lean`.

For small n these functions enumerate all assignments and produce exact
Fraction-valued probability laws. They are independent checks, not proofs.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import product
from math import factorial
from typing import Iterable

Deck = tuple[int, ...]
Labels = tuple[int, ...]


def stable_buckets(deck: Deck, labels: Labels, alphabet: int) -> Deck:
    if alphabet < 1:
        raise ValueError("alphabet must be positive")
    if any(not 0 <= label < alphabet for label in labels):
        raise ValueError("label outside alphabet")
    return tuple(c for key in range(alphabet) for c in deck if labels[c] == key)


def lex_buckets(deck: Deck, minor: Labels, major: Labels, a: int, b: int) -> Deck:
    return tuple(
        c for j in range(b) for i in range(a) for c in deck
        if major[c] == j and minor[c] == i
    )


def fused_labels(minor: Labels, major: Labels, a: int) -> Labels:
    # Later labels are the more significant digit.
    return tuple(g * a + f for f, g in zip(minor, major))


def all_labels(n: int, alphabet: int) -> Iterable[Labels]:
    if n < 0 or alphabet < 1:
        raise ValueError("n must be nonnegative, alphabet must be positive")
    return product(range(alphabet), repeat=n)


def shuffle_law(deck: Deck, alphabet: int) -> dict[Deck, Fraction]:
    n = len(deck)
    if set(deck) != set(range(n)):
        raise ValueError("deck must be a permutation of 0..n-1")
    counts = Counter(stable_buckets(deck, labs, alphabet)
                     for labs in all_labels(n, alphabet))
    return {state: Fraction(count, alphabet ** n) for state, count in counts.items()}


def two_round_law(deck: Deck, a: int, b: int) -> dict[Deck, Fraction]:
    first = shuffle_law(deck, a)
    result: dict[Deck, Fraction] = {}
    for middle, mass in first.items():
        for end, q in shuffle_law(middle, b).items():
            result[end] = result.get(end, Fraction()) + mass * q
    return result


def tv_from_uniform(law: dict[Deck, Fraction], n: int) -> Fraction:
    # Omitted permutations have zero mass; there are n! possible outputs.
    u = Fraction(1, factorial(n))
    return (sum((abs(p - u) for p in law.values()), Fraction())
            + (factorial(n) - len(law)) * u) / 2


def rising_sequences_of_inverse(deck: Deck) -> int:
    """Number of rising sequences in the *inverse-shuffle output* list.

    Our output is the inverse riffle permutation (the stable-sorted card
    identities), not the forward physical interleaving permutation. Its own
    descents determine the Bayer--Diaconis inverse-shuffle probability. The
    forward permutation would require taking the inverse before counting.
    """
    return 1 + sum(x > y for x, y in zip(deck, deck[1:]))
