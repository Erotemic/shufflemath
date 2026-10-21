#!/usr/bin/env python3
"""Exact conservative GSR-vs-oracle error budgets for a fixed exchange pair.

Given the two-exchange Commander macro TV `D(k1,k2)` and three local shuffle
phases with r0,r1,r2 ideal riffles per pile, use the conservative bound

    D + sum_{phase i} [GSR_TV(49, r_i) + GSR_TV(50, r_i)].

This is a *candidate* upper bound conditional on proving the full-deck
oracle lifting/intertwining and local-kernel discrepancy hypotheses in Lean.
It does NOT imply a full-deck theorem by itself. The cost is counted as two
physical pile-riffles per phase, plus the cost of the two exchanges.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "visualizations"))
from shuffleviz.model import gsr_tv  # noqa: E402
from commander_pair_search import pair_distance  # noqa: E402


def local_phase_error(rounds: int) -> Fraction:
    if rounds < 0:
        raise ValueError("riffle rounds must be nonnegative")
    return gsr_tv(49, rounds) + gsr_tv(50, rounds)


def conservative_bound(exchanges: tuple[int, int], rounds: tuple[int, int, int]) -> Fraction:
    if len(rounds) != 3:
        raise ValueError("two exchanges require three local-randomization phases")
    return pair_distance(*exchanges) + sum((local_phase_error(r) for r in rounds), Fraction())


def cost(rounds: tuple[int, int, int], cross_cost: Fraction) -> Fraction:
    if cross_cost < 0:
        raise ValueError("cross cost must be nonnegative")
    return 2 * sum(rounds) + 2 * cross_cost


def best_under_target(target: Fraction, maximum_rounds: int = 20,
                      exchanges: tuple[int, int] = (25, 25),
                      cross_cost: Fraction = Fraction(1)):
    if maximum_rounds < 0:
        raise ValueError("maximum rounds must be nonnegative")
    local_errors = [local_phase_error(r) for r in range(maximum_rounds + 1)]
    floor = pair_distance(*exchanges)
    best = None
    for r0, r1, r2 in product(range(maximum_rounds + 1), repeat=3):
        bound = floor + local_errors[r0] + local_errors[r1] + local_errors[r2]
        if bound > target:
            continue
        rounds = (r0, r1, r2)
        candidate = (cost(rounds, cross_cost), bound, rounds)
        if best is None or candidate < best:
            best = candidate
    return best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="1/100", help="exact rational target, e.g. 1/100")
    parser.add_argument("--max-rounds", type=int, default=20)
    parser.add_argument("--exchange-cost", default="1", help="relative cost of each exchange")
    args = parser.parse_args()
    target = Fraction(args.target)
    cross = Fraction(args.exchange_cost)
    found = best_under_target(target, args.max_rounds, cross_cost=cross)
    if found is None:
        print("No feasible candidate in the search region")
        return
    total_cost, bound, rounds = found
    print(f"two exchanges (25,25); local riffles per pile by phase: {rounds}")
    print(f"exact conservative bound: {bound} (~{float(bound):.12g})")
    print(f"cost: {total_cost} units (riffle=1, exchange={cross})")
    print("Unproved obligations: full-deck oracle lifting, kernel discrepancy bounds.")


if __name__ == "__main__":
    main()
