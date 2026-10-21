#!/usr/bin/env python3
"""Exact small-deck oracle/exchange model and symbolic 99-card fiber counts.

A deck is a permutation of card identities 0..N-1, with the first ``m``
positions in the left working pile. The originally-left cards are identities
0..r-1. A macrostate records the number of marked cards in the left pile.

``physical_exchange_then_local_oracle`` chooses ``k`` positions uniformly
from each pile, swaps matching positions, then uniformly reorders *each*
pile. This is a specified stochastic operation: the exchange selection is
position-based and the post-exchange local randomization is perfect.

``macro_exchange`` counts the possible exchange-position pairs. ``fiber_law``
conditions the uniform distribution on all deck permutations on the macro
count. The equality of applying a physical ideal exchange to ``fiber_law(x)``
and of applying the macro kernel then ``fiber_law`` is computed exhaustively
for small decks. These Python tests are independent executable evidence; they
are not a general Lean proof for N=99.

The 99-card fiber/cardinality identities are additionally checked with exact
integers, without enumerating permutations.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial
from functools import lru_cache
from typing import TypeAlias

Deck: TypeAlias = tuple[int, ...]
Law: TypeAlias = dict[Deck, Fraction]


def validate_parameters(n: int, m: int, r: int, k: int | None = None) -> None:
    if not (0 < m < n and 0 < r < n):
        raise ValueError("need 0 < pile size, marked size < deck size")
    if k is not None and not (0 <= k <= min(m, n - m)):
        raise ValueError("invalid exchange size")


def admissible_counts(n: int, m: int, r: int) -> range:
    validate_parameters(n, m, r)
    return range(max(0, m + r - n), min(m, r) + 1)


def macrostate(deck: Deck, m: int, r: int) -> int:
    if len(deck) != len(set(deck)) or set(deck) != set(range(len(deck))):
        raise ValueError("a deck must be a permutation of 0..N-1")
    return sum(card < r for card in deck[:m])


def membership_fiber_size(n: int, m: int, r: int, x: int) -> int:
    if not (0 <= x <= min(m, r)) or not (0 <= m - x <= n - r):
        return 0
    return comb(r, x) * comb(n - r, m - x)


def ordered_fiber_size(n: int, m: int, r: int, x: int) -> int:
    return membership_fiber_size(n, m, r, x) * factorial(m) * factorial(n - m)


def macro_stationary(n: int, m: int, r: int) -> dict[int, Fraction]:
    return {x: Fraction(membership_fiber_size(n, m, r, x), comb(n, m))
            for x in admissible_counts(n, m, r)}


def verify_uniform_fiber_identity(n: int, m: int, r: int) -> bool:
    """Check the exact Vandermonde/uniform-permutation disintegration."""
    sizes = [ordered_fiber_size(n, m, r, x)
             for x in admissible_counts(n, m, r)]
    if sum(sizes) != factorial(n):
        return False
    macro = macro_stationary(n, m, r)
    return (sum(macro.values(), Fraction()) == 1
            and all(Fraction(ordered_fiber_size(n, m, r, x), factorial(n)) == macro[x]
                    for x in macro))


@lru_cache(maxsize=None)
def fiber_decks(n: int, m: int, r: int, x: int) -> tuple[Deck, ...]:
    validate_parameters(n, m, r)
    result = tuple(d for d in permutations(range(n)) if macrostate(d, m, r) == x)
    assert len(result) == ordered_fiber_size(n, m, r, x)
    return result


def fiber_law(n: int, m: int, r: int, x: int) -> Law:
    decks = fiber_decks(n, m, r, x)
    if not decks:
        raise ValueError("empty fiber")
    p = Fraction(1, len(decks))
    return dict.fromkeys(decks, p)


def micro_exchange_oracle_counts(deck: Deck, m: int, k: int) -> Counter[Deck]:
    """Integer-valued output multiplicities for one microstate.

    Each choice of positions and independent left/right rearrangements is
    equally likely. Counting multiplicities instead of fractions keeps this
    computation exact and efficient.
    """
    n = len(deck)
    validate_parameters(n, m, m, k)
    outcomes: Counter[Deck] = Counter()
    for lidx in combinations(range(m), k):
        for ridx in combinations(range(m, n), k):
            exchanged = list(deck)
            for li, ri in zip(lidx, ridx):
                exchanged[li], exchanged[ri] = exchanged[ri], exchanged[li]
            for left in permutations(exchanged[:m]):
                for right in permutations(exchanged[m:]):
                    outcomes[left + right] += 1
    denom = comb(m, k) * comb(n - m, k) * factorial(m) * factorial(n - m)
    assert sum(outcomes.values()) == denom
    return outcomes


def micro_exchange_oracle(deck: Deck, m: int, k: int) -> Law:
    counts = micro_exchange_oracle_counts(deck, m, k)
    return {dest: Fraction(v, sum(counts.values())) for dest, v in counts.items()}


@lru_cache(maxsize=None)
def finite_gsr_pile_counts(pile: Deck, alphabet: int) -> Counter[Deck]:
    """One inverse-GSR ``alphabet``-label shuffle on an ordered pile.

    Cards are distinct *original identities*, even when the pile is a
    noncontiguous subset of the full deck. All independent label assignments
    are counted exactly, without normalizing to a local identity set.
    """
    if alphabet < 1:
        raise ValueError("alphabet must be positive")
    indices = {card: idx for idx, card in enumerate(pile)}
    if len(indices) != len(pile):
        raise ValueError("pile cards must be distinct")
    outcomes: Counter[Deck] = Counter()
    for labels in product(range(alphabet), repeat=len(pile)):
        result = tuple(card for key in range(alphabet) for card in pile
                       if labels[indices[card]] == key)
        outcomes[result] += 1
    assert sum(outcomes.values()) == alphabet ** len(pile)
    return outcomes


def micro_exchange_finite_gsr_counts(deck: Deck, m: int, k: int,
                                     alphabet: int) -> Counter[Deck]:
    """Exchange selected positions, then finite inverse-GSR on both piles.

    Uses independent card-identity labels within each working pile.
    Returns integer outcome multiplicities; the common denominator is
    ``C(m,k) C(n-m,k) alphabet**n``.
    """
    n = len(deck)
    validate_parameters(n, m, m, k)
    if alphabet < 1:
        raise ValueError("alphabet must be positive")
    outcomes: Counter[Deck] = Counter()
    for left_positions in combinations(range(m), k):
        for right_positions in combinations(range(m, n), k):
            exchanged = list(deck)
            for li, ri in zip(left_positions, right_positions):
                exchanged[li], exchanged[ri] = exchanged[ri], exchanged[li]
            left_law = finite_gsr_pile_counts(tuple(exchanged[:m]), alphabet)
            right_law = finite_gsr_pile_counts(tuple(exchanged[m:]), alphabet)
            for left, left_count in left_law.items():
                for right, right_count in right_law.items():
                    outcomes[left + right] += left_count * right_count
    denominator = comb(m, k) * comb(n - m, k) * alphabet ** n
    assert sum(outcomes.values()) == denominator
    return outcomes


def micro_exchange_finite_gsr(deck: Deck, m: int, k: int,
                              alphabet: int) -> Law:
    counts = micro_exchange_finite_gsr_counts(deck, m, k, alphabet)
    den = sum(counts.values())
    return {dest: Fraction(v, den) for dest, v in counts.items()}


def exact_tv(p: Law, q: Law) -> Fraction:
    return sum((abs(p.get(deck, Fraction()) - q.get(deck, Fraction()))
                for deck in p.keys() | q.keys()), Fraction()) / 2


def local_gsr_error(pile_size: int, alphabet: int) -> Fraction:
    """Exact TV from a uniform pile permutation of one GSR alphabet round."""
    canonical = tuple(range(pile_size))
    counts = finite_gsr_pile_counts(canonical, alphabet)
    mass = Fraction(1, alphabet ** pile_size)
    ideal_mass = Fraction(1, factorial(pile_size))
    return (sum((abs(Fraction(count) * mass - ideal_mass)
                 for count in counts.values()), Fraction())
            + (factorial(pile_size) - len(counts)) * ideal_mass) / 2


def finite_vs_perfect_local_row_error(deck: Deck, m: int, k: int,
                                      alphabet: int) -> Fraction:
    """Discrepancy of finite GSR versus perfect pile shuffles *per row*."""
    return exact_tv(micro_exchange_finite_gsr(deck, m, k, alphabet),
                    micro_exchange_oracle(deck, m, k))


def finite_vs_perfect_error_bound(n: int, m: int, alphabet: int) -> Fraction:
    """Safe additive local error, independent of the exchange size."""
    return local_gsr_error(m, alphabet) + local_gsr_error(n - m, alphabet)


def macro_exchange(n: int, m: int, r: int, k: int, x: int) -> dict[int, Fraction]:
    """Hypergeometric exchange obtained by counting marked/unmarked moves."""
    validate_parameters(n, m, r, k)
    if x not in admissible_counts(n, m, r):
        raise ValueError("invalid macrostate")
    den = comb(m, k) * comb(n - m, k)
    counts: Counter[int] = Counter()
    for outgoing_marked in range(k + 1):
        out = comb(x, outgoing_marked) * comb(m - x, k - outgoing_marked)
        for incoming_marked in range(k + 1):
            into = (comb(r - x, incoming_marked)
                    * comb(n - m - r + x, k - incoming_marked))
            if out and into:
                counts[x - outgoing_marked + incoming_marked] += out * into
    assert sum(counts.values()) == den
    return {y: Fraction(v, den) for y, v in counts.items()}


def apply_micro_to_fiber(n: int, m: int, r: int, k: int, x: int) -> Law:
    source = fiber_decks(n, m, r, x)
    counts: Counter[Deck] = Counter()
    for deck in source:
        counts.update(micro_exchange_oracle_counts(deck, m, k))
    den = len(source) * comb(m, k) * comb(n - m, k) * factorial(m) * factorial(n - m)
    assert sum(counts.values()) == den
    return {d: Fraction(v, den) for d, v in counts.items()}


def lift_macro_step(n: int, m: int, r: int, k: int, x: int) -> Law:
    macro = macro_exchange(n, m, r, k, x)
    result: Law = {}
    for y, weight in macro.items():
        for deck, pfiber in fiber_law(n, m, r, y).items():
            assert deck not in result  # distinct fibers form a partition
            result[deck] = weight * pfiber
    return {deck: p for deck, p in result.items() if p}


def exact_intertwining_small_deck(n: int, m: int, r: int, k: int) -> bool:
    """Exhaustively compare true micro exchange + local oracles to macro lift."""
    for x in admissible_counts(n, m, r):
        if apply_micro_to_fiber(n, m, r, k, x) != lift_macro_step(n, m, r, k, x):
            return False
    return True


def macro_tv_after(n: int, m: int, r: int, k: int, x0: int,
                   steps: int) -> Fraction:
    dist = {x0: Fraction(1)}
    for _ in range(steps):
        out: dict[int, Fraction] = {}
        for x, px in dist.items():
            for y, q in macro_exchange(n, m, r, k, x).items():
                out[y] = out.get(y, Fraction()) + px * q
        dist = out
    target = macro_stationary(n, m, r)
    return sum((abs(dist.get(x, Fraction()) - p) for x, p in target.items()),
               Fraction()) / 2


def full_tv_after_via_lift(n: int, m: int, r: int, k: int, x0: int,
                           steps: int) -> Fraction:
    """Construct exact full-deck distribution from the macro chain's fibers."""
    dist = {x0: Fraction(1)}
    for _ in range(steps):
        out: dict[int, Fraction] = {}
        for x, px in dist.items():
            for y, q in macro_exchange(n, m, r, k, x).items():
                out[y] = out.get(y, Fraction()) + px * q
        dist = out
    u = Fraction(1, factorial(n))
    return (sum((abs(dist.get(x, Fraction()) / ordered_fiber_size(n, m, r, x) - u)
                 * ordered_fiber_size(n, m, r, x)
                 for x in admissible_counts(n, m, r)), Fraction()) / 2)


def main() -> None:
    for n, m, r in [(5, 3, 3), (6, 3, 3), (99, 50, 50)]:
        assert verify_uniform_fiber_identity(n, m, r)
        print(f"N={n}, m={m}, marked={r}: uniform fiber identity verified")
    for n, m, r, k in [(4, 2, 2, 1), (5, 3, 3, 1), (6, 3, 3, 1)]:
        assert exact_intertwining_small_deck(n, m, r, k)
        print(f"N={n}, m={m}, marked={r}, exchange={k}: exact micro/macro intertwining verified")


if __name__ == "__main__":
    main()
