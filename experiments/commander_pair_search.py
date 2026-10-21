#!/usr/bin/env python3
"""Exhaustive, exact two-exchange Commander search with a reusable certificate.

Starting from complete segregation, the first exchange of k1 cards gives
X = 50-k1 with probability one. The two-step TV objective therefore depends
only on one row of the k2 transition matrix, not on a matrix product.

This program is a *conjecture/certificate generator*; exact Python arithmetic
is not a substitute for Lean checking the resulting finite theorem.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path


N, M = 99, 50


@lru_cache(maxsize=None)
def choose(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def weight_numerator(k: int, x: int, y: int) -> int:
    total = 0
    for a in range(k + 1):
        remaining = x - a
        if remaining > y or a > x:
            continue
        b = y - remaining
        if b < 0 or b > k:
            continue
        total += (
            choose(x, a)
            * choose(M - x, k - a)
            * choose(M - x, b)
            * choose((N - M) - (M - x), k - b)
        )
    return total


def weight_row(k: int, x: int) -> tuple[Fraction, ...]:
    denominator = choose(M, k) * choose(N - M, k)
    return tuple(Fraction(weight_numerator(k, x, y), denominator) for y in range(1, 51))


STATIONARY = tuple(
    Fraction(choose(50, y) * choose(49, 50 - y), choose(99, 50))
    for y in range(1, 51)
)


def tv(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> Fraction:
    assert len(p) == len(q)
    return sum((abs(a - b) for a, b in zip(p, q)), Fraction()) / 2


def pair_distance(k1: int, k2: int) -> Fraction:
    if not (1 <= k1 <= 49 and 1 <= k2 <= 49):
        raise ValueError("both exchange sizes must be 1..49")
    # First exchange is deterministic on the macrostate, from x0=50.
    return tv(weight_row(k2, 50 - k1), STATIONARY)


def exact_search() -> list[tuple[Fraction, int, int]]:
    pairs = [
        (pair_distance(k1, k2), k1, k2)
        for k1 in range(1, 50)
        for k2 in range(1, 50)
    ]
    pairs.sort()
    return pairs


def write_certificate(output: Path) -> dict:
    results = exact_search()
    best, k1, k2 = results[0]
    ties = [(x, y) for d, x, y in results if d == best]
    second = next(((d, x, y) for d, x, y in results if d > best), None)
    payload = {
        "model": "Commander 99/50, complete segregation, two ideal exchanges",
        "state_definition": "x=original-left cards in the 50-card left pile; states 1..50",
        "search_domain": {"k1_min": 1, "k1_max": 49, "k2_min": 1, "k2_max": 49},
        "examined": len(results),
        "best": {"k1": k1, "k2": k2, "tv_num": best.numerator, "tv_den": best.denominator},
        "ties": ties,
        "next_strictly_worse": None if second is None else {
            "k1": second[1], "k2": second[2],
            "tv_num": second[0].numerator, "tv_den": second[0].denominator,
        },
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output:
        print(json.dumps(write_certificate(args.output), indent=2))
    else:
        for distance, k1, k2 in exact_search()[:10]:
            print(f"({k1:2d},{k2:2d}) TV={distance} (~{float(distance):.12f})")


if __name__ == "__main__":
    main()
